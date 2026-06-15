// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Regtest apply-path harness for tests that need the consensus apply path to accept (or
// commit/defer/duplicate-handle) a BTC header. Once the apply path enforces proof-of-work
// (CheckBTCHeaderBatchPoWForNetwork), a header must meet its claimed target to be accepted — infeasible
// to mine at testnet3/mainnet difficulty (~2^32 work/header), so the synthetic-header testnet3 harness
// can only produce rejects. Regtest's PowLimit (~2^255) is met by ~2 random nonces, so here we mine real
// (cheap) PoW and exercise the full path: PoW + contextual + AddExternalHeaders + rollback. The
// testnet3-specific contextual rules (20-min rule, retarget boundaries) stay covered by the
// validator-level tests (TestHvmBtcDiffFloorAwareAgainstRealLightweightNode + core/vm); these cover apply-path
// wiring, which is network-agnostic. Regtest is PoWNoRetargeting, so the expected difficulty is always
// PowLimitBits — every mined header carries 0x207fffff.

import (
	"context"
	"math/big"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/params"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

const regtestPowBits = uint32(0x207fffff) // chaincfg.RegressionNetParams.PowLimitBits

// mineRegtestChild returns a header extending prev with valid regtest proof-of-work (hash <= target),
// found in ~2 nonces. Version 4 clears every regtest BIP version gate; the timestamp advances so the
// median-time-past check passes.
func mineRegtestChild(t *testing.T, prev *wire.BlockHeader, nonceBase uint32) *wire.BlockHeader {
	return mineRegtestChildBits(t, prev, regtestPowBits, nonceBase)
}

// mineRegtestChildBits is mineRegtestChild with an explicit Bits — used to build a header that passes the
// PoW gate (its hash meets its claimed target) but fails the contextual check (Bits != the regtest
// expected PowLimitBits). bits must be at least as hard as PowLimitBits (target <= PowLimit) so it is in
// range and still cheaply mineable (~2^255 target => ~2 nonces).
func mineRegtestChildBits(t *testing.T, prev *wire.BlockHeader, bits, nonceBase uint32) *wire.BlockHeader {
	t.Helper()
	h := &wire.BlockHeader{
		Version:    4,
		PrevBlock:  prev.BlockHash(),
		MerkleRoot: chainhash.Hash{},
		Timestamp:  prev.Timestamp.Add(60 * time.Second),
		Bits:       bits,
	}
	target := blockchain.CompactToBig(bits)
	for i := uint32(0); i < 1<<22; i++ {
		h.Nonce = nonceBase + i
		hash := h.BlockHash()
		if blockchain.HashToBig(&hash).Cmp(target) <= 0 {
			return h
		}
	}
	t.Fatal("failed to mine a regtest child within 2^22 nonces")
	return nil
}

// newRegtestChainWithLightTBC stands up a BlockChain + a real lightweight TBC node configured for the
// localnet/regtest difficulty rule, seated at the regtest genesis (offset 0). The genesis-pairing guard
// allows localnet's custom pairing (WARN + start). Returns the chain and the genesis header.
func newRegtestChainWithLightTBC(t *testing.T, hvm0Time uint64) (*BlockChain, *wire.BlockHeader) {
	t.Helper()

	cfg := *params.TestChainConfig
	cfg.Hvm0Time = &hvm0Time
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}
	chain, err := NewBlockChain(rawdb.NewMemoryDatabase(), gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)

	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header
	tbcCfg := tbc.NewDefaultConfig()
	tbcCfg.ExternalHeaderMode = true
	tbcCfg.EffectiveGenesisBlock = genesis
	tbcCfg.GenesisHeightOffset = 0
	tbcCfg.LevelDBHome = t.TempDir()
	tbcCfg.BlockheaderCacheSize = "0"
	tbcCfg.BlockCacheSize = "0"
	tbcCfg.AutoIndex = false
	tbcCfg.BlockSanity = true
	tbcCfg.MaxCachedTxs = 0
	tbcCfg.MempoolEnabled = false
	tbcCfg.Network = "localnet"

	chain.initHvmHeaderNode(tbcCfg)
	t.Cleanup(func() { _ = chain.tbcHeaderNode.ExternalHeaderTearDown() })
	require.True(t, chain.hvmEnabled, "initHvmHeaderNode must proceed on the localnet pair (genesis-pairing guard WARN-and-start)")
	return chain, genesis
}

// seedRegtestAboveFloor mines a contiguous regtest chain PAST floorClearance (so a candidate extending the
// tip is contextually ENFORCED, not deferred) and adds it to the lightweight node. Returns the seeded tip.
func seedRegtestAboveFloor(t *testing.T, chain *BlockChain, genesis *wire.BlockHeader) *wire.BlockHeader {
	t.Helper()
	total := 2*2016 + 11 + 8 // generous over-seed: comfortably > floorClearance(regtest)
	hdrs := make([]*wire.BlockHeader, 0, total)
	prev := genesis
	for i := 0; i < total; i++ {
		h := mineRegtestChild(t, prev, uint32(i)*7+1)
		hdrs = append(hdrs, h)
		prev = h
	}
	for start := 0; start < len(hdrs); start += 1000 {
		end := start + 1000
		if end > len(hdrs) {
			end = len(hdrs)
		}
		last := hdrs[end-1].BlockHash()
		_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: hdrs[start:end]}, last[:])
		require.NoError(t, err, "seeding regtest headers chunk [%d:%d]", start, end)
	}
	h, tip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hdrs[len(hdrs)-1].BlockHash(), tip.BlockHash())
	regtestClearance, fcerr := vm.BTCFloorClearanceForNetwork("localnet")
	require.NoError(t, fcerr)
	require.Greater(t, h, regtestClearance, "seeded tip must clear the floor-enforcement threshold (production value, not a hardcoded copy)")
	return tip
}

// applyRegtestBtcAttr builds an L2 block carrying a BtcAttr tx for the given headers + claimed canonical
// tip and drives it through the consensus apply path with enforcement on.
func applyRegtestBtcAttr(t *testing.T, chain *BlockChain, num int64, canonicalTip *chainhash.Hash, headers []wire.BlockHeader) error {
	t.Helper()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(canonicalTip, headers)
	require.NoError(t, err)
	hdr := &types.Header{Number: big.NewInt(num), Time: btcDiffTestHvm0Time}
	blk := types.NewBlockWithHeader(hdr).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blk.Hash().String()] = blk
	chain.tempHeaders[blk.Hash().String()] = blk.Header()
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))
	return chain.applyHvmHeaderConsensusUpdate(blk.Header(), false, true)
}

// TestHvmApplyPathAcceptsValidMinedAboveFloor: a fully-valid (real-PoW, correct-difficulty) above-floor
// header passes BOTH the PoW gate and the contextual validator and is committed, advancing the BTC tip and
// the upstream-state-id. This is the apply-path ACCEPT coverage under real proof-of-work.
func TestHvmApplyPathAcceptsValidMinedAboveFloor(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	tip := seedRegtestAboveFloor(t, chain, genesis)

	cand := *mineRegtestChild(t, tip, 999_000)
	canon := cand.BlockHash()
	blkHash := mustApplyRegtestBtcAttrBlockHash(t, chain, 11, &canon, []wire.BlockHeader{cand}, true)
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, cand.BlockHash(), tipAfter.BlockHash(), "an accepted block must advance the BTC tip")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blkHash.Bytes(), sid[:], "an accepted block must advance the upstream-state-id")
}

// TestHvmApplyPathRollsBackOnWrongCanonicalTipRegtest drives the post-commit rollback branch with real
// PoW: a valid mined above-floor header passes the PoW gate and the contextual validator and is
// committed, after which the CanonicalTip the BtcAttr claims (the parent, not the resulting tip)
// mismatches -> the just-added header must be removed and the tip + upstream-state-id restored, then the
// block rejected.
func TestHvmApplyPathRollsBackOnWrongCanonicalTipRegtest(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	tip := seedRegtestAboveFloor(t, chain, genesis)

	cand := *mineRegtestChild(t, tip, 999_000)
	wrongClaim := tip.BlockHash() // claims the PARENT, but adding cand makes cand the real canonical tip
	require.NotEqual(t, cand.BlockHash(), wrongClaim)

	btcAttr, err := types.MakeBtcAttributesDepositedTx(&wrongClaim, []wire.BlockHeader{cand})
	require.NoError(t, err)
	hdr := &types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time}
	blk := types.NewBlockWithHeader(hdr).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blk.Hash().String()] = blk
	chain.tempHeaders[blk.Hash().String()] = blk.Header()
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))
	sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)

	require.ErrorIs(t, chain.applyHvmHeaderConsensusUpdate(blk.Header(), false, true), consensus.ErrInvalidHVMHeaders,
		"a wrong-CanonicalTip claim must reject after rolling back the committed header")
	// INVARIANT 1: the just-added header was REMOVED (rollback).
	_, _, err = chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, cand.BlockHash())
	require.Error(t, err, "the rolled-back header must be absent after reject")
	// INVARIANT 2: the canonical tip was restored to the pre-apply tip.
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, tip.BlockHash(), tipAfter.BlockHash(), "rollback must restore the BTC tip")
	// INVARIANT 3: the upstream-state-id was restored.
	sid1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, sid0[:], sid1[:], "rollback must restore the upstream-state-id")
}

// mustApplyRegtestBtcAttrBlockHash builds + applies a BtcAttr block and returns the L2 block hash (for
// upstream-state-id assertions). Asserts the apply succeeds.
func mustApplyRegtestBtcAttrBlockHash(t *testing.T, chain *BlockChain, num int64, canonicalTip *chainhash.Hash, headers []wire.BlockHeader, enforce bool) common.Hash {
	t.Helper()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(canonicalTip, headers)
	require.NoError(t, err)
	hdr := &types.Header{Number: big.NewInt(num), Time: btcDiffTestHvm0Time}
	blk := types.NewBlockWithHeader(hdr).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blk.Hash().String()] = blk
	chain.tempHeaders[blk.Hash().String()] = blk.Header()
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blk.Header(), false, enforce))
	return blk.Hash()
}

// TestHvmApplyPathPoWRejectsUnminedHeader: an above-floor header with a correct Bits but no real PoW
// (hash exceeds target) is rejected by the PoW gate before any commit — the forged-Bits/zero-PoW case —
// without advancing the BTC tip.
func TestHvmApplyPathPoWRejectsUnminedHeader(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	tip := seedRegtestAboveFloor(t, chain, genesis)

	// A header at a low (testnet3-PowLimit) target — in range under regtest's PowLimit, but its 256-bit
	// hash almost surely exceeds the ~2^224 target (no work done): the forged/zero-PoW case. We anti-mine
	// (find a nonce whose hash exceeds target) so the un-mined precondition is deterministic, not the ~50%
	// coin flip a regtest-target nonce would be.
	const lowBits = uint32(0x1d00ffff)
	forged := wire.BlockHeader{Version: 4, PrevBlock: tip.BlockHash(), MerkleRoot: chainhash.Hash{}, Timestamp: tip.Timestamp.Add(60 * time.Second), Bits: lowBits}
	target := blockchain.CompactToBig(lowBits)
	found := false
	for n := uint32(1); n < 1<<16; n++ {
		forged.Nonce = n
		hh := forged.BlockHash()
		if blockchain.HashToBig(&hh).Cmp(target) > 0 {
			found = true
			break
		}
	}
	require.True(t, found, "could not construct an un-mined header (hash > 2^224 target)")
	hash := forged.BlockHash()
	require.Positive(t, blockchain.HashToBig(&hash).Cmp(target), "fixture must be un-mined (hash > target)")
	canon := forged.BlockHash()
	require.ErrorIs(t, applyRegtestBtcAttr(t, chain, 11, &canon, []wire.BlockHeader{forged}), consensus.ErrInvalidHVMHeaders,
		"a forged/zero-PoW header must be REJECTED by the PoW gate")
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, tip.BlockHash(), tipAfter.BlockHash(), "a PoW-rejected block must NOT advance the BTC tip")
}
