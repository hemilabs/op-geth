// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package core

import (
	"context"
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"

	"github.com/hemilabs/heminetwork/service/tbc"
)

// newHvmTestChainWithLightTBC builds a real BlockChain with hVM Phase 0 activating at hvm0Time and a real
// embedded lightweight (external-header-mode) TBC node attached, returning the chain and the lightweight
// node's current best (genesis-checkpoint) BTC tip header. It does not use the full SetupHvmHeaderNode
// (which would try a state restore against the EVM tip); it attaches the node directly via
// initHvmHeaderNode, which is what the empty-but-present BtcAttr fix's apply/unapply paths exercise.
func newHvmTestChainWithLightTBC(t *testing.T, hvm0Time uint64) (*BlockChain, *wire.BlockHeader) {
	t.Helper()

	cfg := *params.TestChainConfig
	cfg.Hvm0Time = &hvm0Time
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}

	chain, err := NewBlockChain(rawdb.NewMemoryDatabase(), gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)

	// Attach a real lightweight TBC node, mirroring eth/backend.go's external-header config. Use the
	// synthetic min-difficulty testnet3 genesis (hvmSynthetic*, the old 3488421/0x1d00ffff), not the
	// production canonical genesis (now 3522419, a retarget-difficulty block), because the synthetic seeding
	// mines min-difficulty children that must be contextually valid building on the genesis. Temporarily
	// override the testnet3 checkpoint to this pair so initHvmHeaderNode's genesis-pairing assertion accepts
	// it (restored on cleanup; safe — package tests are sequential, none t.Parallel). This decouples the
	// synthetic harness from the production genesis value.
	savedCp := hvmGenesisCheckpoints["testnet3"]
	hvmGenesisCheckpoints["testnet3"] = []btcGenesisCheckpoint{{height: hvmSyntheticGenesisHeight, hash: hvmSyntheticGenesisHash}}
	t.Cleanup(func() { hvmGenesisCheckpoints["testnet3"] = savedCp })
	tbcCfg := tbc.NewDefaultConfig()
	tbcCfg.ExternalHeaderMode = true
	tbcCfg.EffectiveGenesisBlock = hvmSyntheticGenesisHeader(t)
	tbcCfg.GenesisHeightOffset = hvmSyntheticGenesisHeight
	tbcCfg.LevelDBHome = t.TempDir()
	tbcCfg.BlockheaderCacheSize = "0"
	tbcCfg.BlockCacheSize = "0"
	tbcCfg.AutoIndex = false
	tbcCfg.BlockSanity = true
	tbcCfg.MaxCachedTxs = 0
	tbcCfg.MempoolEnabled = false
	tbcCfg.Network = "testnet3"

	chain.initHvmHeaderNode(tbcCfg)
	t.Cleanup(func() { _ = chain.tbcHeaderNode.ExternalHeaderTearDown() })

	height, lightTip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)

	// Canonical-arm oracle (load-bearing for every empty-present / revert / unapply / contextual-difficulty test using this
	// harness): initHvmHeaderNode above ran the genesis-pairing assertion on the canonical production config;
	// any verdict but Canonical would have log.Crit-exited. Pin that the real node seated the canonical
	// (offset, header) pair so the Canonical-accept arm cannot silently regress (e.g. into the localnet warn
	// arm). Without this, the only proof the wrapper accepted is "the process did not exit".
	require.True(t, chain.hvmEnabled, "initHvmHeaderNode must have proceeded (hVM enabled) on the (overridden) canonical pair")
	require.Equal(t, hvmSyntheticGenesisHeight, height,
		"lightweight node must seat the effective genesis at the synthetic GenesisHeightOffset")
	require.Equal(t, hvmSyntheticGenesisHeader(t).BlockHash().String(), lightTip.BlockHash().String(),
		"best header at startup must be the synthetic effective-genesis header")
	// The integration accept/reject/defer difficulty oracles (TestHvmBtcDiffFloorAwareAgainstRealLightweightNode, TestHvmApplyPath*) assume the
	// seed carries testnet3 PowLimitBits (min difficulty). Anchor it here so a genesis re-pin to a
	// non-min-diff header cannot silently vacate those oracles (e.g. make a wrong-difficulty header
	// accidentally correct).
	require.Equal(t, uint32(0x1d00ffff), lightTip.Bits,
		"effective-genesis header must carry testnet3 PowLimitBits (0x1d00ffff)")
	return chain, lightTip
}

// TestHvmEmptyPresentApplyUnapplyRoundTrip is the integration regression for the empty-but-present BtcAttr
// fix against a real embedded TBC node. An "empty-but-present" Bitcoin Attributes Deposited tx (present,
// zero headers) must:
//   - forward-apply by advancing the TBC upstream-state-id to this block (the original bug left it at the
//     parent, which then crashed the next block / state restore); and
//   - reorg-unapply as a no-op that rolls the state-id back, without calling RemoveExternalHeaders (which
//     a zero-header set is an invalid RemoveExternalHeaders call -> crash on unfixed code).
//
// Drives the real applyHvmHeaderConsensusUpdate / unapplyHvmHeaderConsensusUpdate against a real *tbc.Server
// and asserts the upstream-state-id round-trips genesis -> N -> genesis with no crash. The activation-block
// geometry (parent pre-activation) keeps the apply on the genesis "first hVM header update" branch and the
// unapply on the activation special-case (rolls to genesis), exercising the empty-but-present edits.
func TestHvmEmptyPresentApplyUnapplyRoundTrip(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)

	// Sanity: a freshly initialized lightweight node reports the genesis upstream-state-id.
	sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId[:], sid0[:], "fresh lightweight TBC must start at the genesis upstream-state-id")

	// Build an empty-but-present BtcAttr tx whose CanonicalTip matches the lightweight tip (so the
	// forward CanonicalTip acceptance check passes) and carries zero headers.
	canon := lightTip.BlockHash()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, nil)
	require.NoError(t, err)
	tx := types.NewTx(btcAttr)

	// Activation block N (Time >= hvm0Time), built on a pre-activation parent (Time < hvm0Time).
	parentHeader := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	nHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: parentHeader.Hash()}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{tx}})

	// Confirm the tx really is an empty-but-present BtcAttr.
	btcAttrDep, err := blockN.Transactions().ExtractBtcAttrData()
	require.NoError(t, err)
	require.NotNil(t, btcAttrDep, "BtcAttr tx must be present")
	require.Len(t, btcAttrDep.Headers, 0, "this must be the empty-but-present (zero-header) case")
	require.True(t, btcAttrDepIsHeaderless(btcAttrDep))

	// Make the block + parent retrievable via the holding pen (apply/unapply look them up). The parent is
	// seeded as both a header and a block: the fixed unapply only needs the parent header (its no-op branch
	// reads getHeaderFromDiskOrHoldingPen for the rollback target), but pre-fix code falls through to the
	// backward-walk, which fetches the parent block via getBlockFromDiskOrHoldingPen and would otherwise
	// nil-deref there instead of reaching the RemoveExternalHeaders-empty log.Crit. Seeding the parent block
	// makes the pre-fix failure the genuine empty-header crash this test guards against.
	chain.tempHeaders[parentHeader.Hash().String()] = parentHeader
	chain.tempBlocks[parentHeader.Hash().String()] = types.NewBlockWithHeader(parentHeader)
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()

	// Forward apply: must not crash and must advance the upstream-state-id to block N.
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true),
		"forward-apply of an empty-but-present BtcAttr block must succeed")
	sid1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sid1[:],
		"forward-apply must advance the upstream-state-id to this block (the state-id-advance fix)")

	// Reorg unapply: must not crash and must roll the upstream-state-id back to genesis (parent is
	// pre-activation). Pre-fix failure signature: the bug is a hard crash, so on unfixed code this fails by
	// process abort (log.Crit -> os.Exit when RemoveExternalHeaders is called with the zero-header set), not
	// a clean require failure — that abort is the empty-header-crash regression this asserts is gone.
	require.NoError(t, chain.unapplyHvmHeaderConsensusUpdate(blockN.Header()),
		"reorg-unapply of an empty-but-present BtcAttr block must succeed (the empty-header unapply no-op fix)")
	sid2, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId[:], sid2[:],
		"unapplying the activation block must roll the upstream-state-id back to genesis")

	// Confirm the crash trigger the unapply fix avoids: RemoveExternalHeaders with a zero-header set returns
	// an error in the pinned TBC node (on the precondition before any write, so it does not mutate state).
	_, _, errEmpty := chain.tbcHeaderNode.RemoveExternalHeaders(chain.ctx, &wire.MsgHeaders{}, lightTip, hVMGenesisUpstreamId[:])
	require.Error(t, errEmpty,
		"empty RemoveExternalHeaders must error — exactly the crash the empty-but-present BtcAttr unapply no-op avoids by skipping the call")
}

// TestHvmEmptyPresentNextBlockAppliesCleanly reproduces the empty-but-present forward-crash case — the more
// severe, no-reorg-needed manifestation. Pre-fix, a mid-chain empty-but-present BtcAttr block (parent
// already hVM-active, so the state-id was at the parent) failed to advance the upstream-state-id, leaving
// it pinned at the grandparent; the next block then tripped the parent-mismatch log.Crit in
// applyHvmHeaderConsensusUpdate because the state-id no longer matched its parent — a crash on unfixed code with no reorg. With the
// fix, the empty block advances the state-id to itself, so the next block applies cleanly. Drives the real
// applyHvmHeaderConsensusUpdate against a real *tbc.Server.
func TestHvmEmptyPresentNextBlockAppliesCleanly(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)
	canon := lightTip.BlockHash()

	// M: activation block, a normal (no-BtcAttr) hVM-active block -> advances state-id to M.
	parent := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1} // pre-activation parent of M
	mHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: parent.Hash()}
	blockM := types.NewBlockWithHeader(mHeader)

	// N: mid-chain empty-but-present BtcAttr block (parent M is already hVM-active).
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, nil)
	require.NoError(t, err)
	nHeader := &types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: mHeader.Hash()}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})

	// N1: the next normal block, built on N.
	n1Header := &types.Header{Number: big.NewInt(13), Time: hvm0Time + 2, ParentHash: nHeader.Hash()}
	blockN1 := types.NewBlockWithHeader(n1Header)

	// Seed M, N, N1 as blocks+headers. Load-bearing: when applying N1 the forward prev-state sanity check
	// resolves the prior-state block via getBlockFromDiskOrHoldingPen and
	// dereferences it, so the intermediate blocks must be present or it would nil-deref instead of
	// exercising the parent-mismatch path.
	chain.tempHeaders[parent.Hash().String()] = parent
	for _, b := range []*types.Block{blockM, blockN, blockN1} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
	}

	// Apply M (activation, no BtcAttr) -> state-id = M.
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockM.Header(), false, true))
	sidM, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockM.Hash().Bytes(), sidM[:])

	// Apply N (empty-but-present, mid-chain) -> must advance state-id to N (the fix).
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true))
	sidN, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sidN[:],
		"mid-chain empty-but-present block must advance the state-id to itself (pre-fix it stayed at M)")

	// The next block must apply without the parent-mismatch crit. Pre-fix the state-id was stuck at M,
	// so block N1 (parent N) found state-id(M) != parent(N) and hit log.Crit (os.Exit).
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN1.Header(), false, true),
		"the block after an empty-but-present block must apply cleanly (pre-fix the stale state-id crashed the parent-mismatch check)")
	sidN1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN1.Hash().Bytes(), sidN1[:])
}

// TestHvmNonEmptyBtcAttrTakesRealHeaderPath is the negative control: it proves the btcAttrDepIsHeaderless
// guard does not swallow a populated BtcAttr block. A block carrying real BTC headers must take the genuine
// AddExternalHeaders path (advancing the lightweight tip), not the headerless no-op — so an over-broadening
// of the guard (the symmetric inverse of the empty-but-present bug) would make this fail (the tip would not
// advance). External-header insertion validates contiguity + cumulative work (CalcWork from Bits), not PoW,
// so synthetic headers chained off the genesis checkpoint with the genesis Bits are accepted. Apply only:
// the unapply of a real-header activation block walks back for a prior BtcAttr tip that does not exist
// (parent is pre-activation), a separate edge; the apply assertion alone proves the non-swallow guard.
func TestHvmNonEmptyBtcAttrTakesRealHeaderPath(t *testing.T) {
	const hvm0Time = uint64(1000)
	// Regtest harness: once the apply path enforces proof-of-work, the headers must be really mined (regtest
	// PoW is mineable in ~2 nonces). These near-genesis headers are below the floor clearance so contextual
	// difficulty defers, exercising the real AddExternalHeaders header path (the fix's subject).
	chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)

	// Build a 3-header mined chain off the lightweight tip (the genesis checkpoint).
	headers := make([]wire.BlockHeader, 0, 3)
	prev := genesis
	for i := 0; i < 3; i++ {
		h := mineRegtestChild(t, prev, uint32(1000+i)*101+1)
		headers = append(headers, *h)
		prev = h
	}
	newTip := headers[len(headers)-1].BlockHash()

	btcAttr, err := types.MakeBtcAttributesDepositedTx(&newTip, headers)
	require.NoError(t, err)

	parentHeader := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	nHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: parentHeader.Hash()}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})

	// Sanity: this is a populated (not headerless) BtcAttr tx.
	dep, err := blockN.Transactions().ExtractBtcAttrData()
	require.NoError(t, err)
	require.Len(t, dep.Headers, 3)
	require.False(t, btcAttrDepIsHeaderless(dep), "a 3-header BtcAttr tx must NOT be classified headerless")

	chain.tempHeaders[parentHeader.Hash().String()] = parentHeader
	chain.tempBlocks[parentHeader.Hash().String()] = types.NewBlockWithHeader(parentHeader)
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()

	// Apply: the populated block must take the real AddExternalHeaders path, advancing the lightweight tip
	// to the new chain tip and the state-id to block N. If the headerless guard wrongly swallowed it, the
	// tip would stay at the genesis checkpoint and this would fail.
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true))
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipAfterHash := tipAfter.BlockHash()
	require.Equal(t, newTip[:], tipAfterHash[:],
		"a real-header BtcAttr block must advance the lightweight tip via AddExternalHeaders (proves it did NOT take the headerless no-op)")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sid[:])
}
