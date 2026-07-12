// Copyright 2024 The go-ethereum Authors
// Copyright 2026 Hemi Labs, Inc.
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
	"bytes"
	"context"
	"encoding/hex"
	"errors"
	"fmt"
	"log/slog"
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
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

// Contextual-difficulty integration tests against a real lightweight TBC node, seeded with a contiguous testnet3
// min-difficulty chain past the floor clearance. These exercise the floor-aware validator and the
// consensus apply-path enforcement at above-floor heights — coverage the in-memory fakeHeaderStore unit
// tests cannot reach. The harness uses GenesisHeightOffset = hvmSyntheticGenesisHeight = 3488421
// (min-difficulty), so the floor and retarget boundaries sit at real, non-zero-residue Bitcoin heights.
// canonicalHvmGenesisHash is the block hash of op-geth's compiled default testnet3 hVM
// EffectiveGenesisBlock (ethconfig.Defaults.HvmGenesisHeader at height 3522419) — the live testnet3
// genesis pairing.
const canonicalHvmGenesisHash = "000000000000000096c98151accc5ee217d7cc4ff1e59a3d91e4c9365c4ea144"

// canonicalHvmGenesisHeaderHex is that same default header (ethconfig.Defaults.HvmGenesisHeader).
const canonicalHvmGenesisHeaderHex = "00c05732cdc3e0d654efe86351f0cbfc6c79325e9f9fa7886a39b552f5c4d90700000000dae4079485e26f1f77425b84a13760038a352d07a0fef92b5188bd04c2999162afca58679121011962b9d0a5"

// canonicalHvmGenesisHeight is the true Bitcoin height of canonicalHvmGenesisHeaderHex.
const canonicalHvmGenesisHeight = uint64(3522419)

// mustEffectiveGenesisHeader parses the canonical effective-genesis header. The lightweight-node harness
// uses it (with offset canonicalHvmGenesisHeight) so the genesis-pairing assertion in initHvmHeaderNode
// accepts the config and the tests exercise the real consensus (offset, retarget alignment) rather than a
// synthetic offset-0 chain.
func mustEffectiveGenesisHeader(t *testing.T) *wire.BlockHeader {
	t.Helper()
	raw, err := hex.DecodeString(canonicalHvmGenesisHeaderHex)
	require.NoError(t, err)
	var h wire.BlockHeader
	require.NoError(t, h.Deserialize(bytes.NewReader(raw)))
	return &h
}

// hvmSynthetic* is a synthetic testnet3 hVM genesis used only by the synthetic-seeding harness
// (newHvmTestChainWithLightTBC): the old pre-re-genesis testnet3 genesis (height 3488421), a
// min-difficulty (PowLimitBits 0x1d00ffff) block. The harness mines min-difficulty children to build a
// contextually-valid synthetic chain, so it needs a min-diff genesis — the canonical genesis (3522419) is
// a retarget-difficulty block and cannot anchor that seeding. Decoupled from the canonical* constants
// (which track the live deployment) so a future production-genesis change does not break the seeding. The
// harness temporarily overrides the testnet3 checkpoint to this pair so the pairing guard accepts it
// (save/restore; safe — the package runs tests sequentially, none call t.Parallel, see
// blockchain_hvm_init_test.go).
const hvmSyntheticGenesisHeaderHex = "00000020715ae5bdcf3d4b3a27cecfc0db309ea522fddbe83946492d0f000000000000000f092c40dc00db9010da6452d0e0688056d5b1cbc287de4ffb6a5acff873cd4b0a3c4467ffff001d04dafc10"
const hvmSyntheticGenesisHeight = uint64(3488421)
const hvmSyntheticGenesisHash = "00000000036fc6f10811f315be5328a8cff7f9204fe3a40a2f9e4ce13637b704"

func hvmSyntheticGenesisHeader(t *testing.T) *wire.BlockHeader {
	t.Helper()
	raw, err := hex.DecodeString(hvmSyntheticGenesisHeaderHex)
	require.NoError(t, err)
	var h wire.BlockHeader
	require.NoError(t, h.Deserialize(bytes.NewReader(raw)))
	return &h
}

// TestClassifyHvmGenesisPairing pins the pure desync detector. The wrapper (initHvmHeaderNode) applies
// the policy: Canonical -> ok; Mismatch -> log.Crit; Custom -> log.Crit on a checkpointed
// (difficulty-enforced) network but log.Warn on a network with no checkpoint (localnet/regtest).
func TestClassifyHvmGenesisPairing(t *testing.T) {
	require.Equal(t, hvmGenesisPairingCanonical, classifyHvmGenesisPairing("testnet3", 3522419, canonicalHvmGenesisHash))
	require.Equal(t, hvmGenesisPairingCanonical, classifyHvmGenesisPairing("upgradetest", 3522419, canonicalHvmGenesisHash),
		"upgradetest shares the testnet3 checkpoint")
	require.Equal(t, hvmGenesisPairingMismatch, classifyHvmGenesisPairing("testnet3", 3522419,
		"00000000000000000000000000000000000000000000000000000000deadbeef"),
		"right height, wrong header = desync (kills the hEq && !sEq XOR direction)")
	require.Equal(t, hvmGenesisPairingMismatch, classifyHvmGenesisPairing("testnet3", 999999, canonicalHvmGenesisHash),
		"right header, wrong height (below) = desync (kills the !hEq && sEq XOR direction)")
	// Wrong height above the checkpoint with the canonical header: also Mismatch. The other two
	// height-mismatch rows sit below the checkpoint (0, 999999); this row kills a `cp.height == height`
	// -> `<=` (or `<`) mutant that would accept any config at-or-above the checkpoint height carrying the
	// canonical header.
	require.Equal(t, hvmGenesisPairingMismatch, classifyHvmGenesisPairing("testnet3", 3522420, canonicalHvmGenesisHash),
		"one block above the checkpoint, canonical header = desync")
	// The real testnet3 genesis @ 0 is a self-consistent pair but not the canonical hVM effective genesis
	// (3522419) — the classifier returns Custom, and the wrapper refuses it on testnet3 (offset 0 would
	// mis-align the retarget boundary vs canonical nodes) rather than failing open on it.
	require.Equal(t, hvmGenesisPairingCustom, classifyHvmGenesisPairing("testnet3", 0,
		"000000000933ea01ad0ee984209779baaec3ced90fa3f408719526f8d77f4943"))
	require.Equal(t, hvmGenesisPairingCustom, classifyHvmGenesisPairing("localnet", 0, canonicalHvmGenesisHash),
		"a network with no checkpoint is custom")
	// No fallback: an uncheckpointed network carrying the exact canonical testnet3 pair (height and
	// header) must still be Custom — the lookup is keyed strictly by network. The localnet row above uses
	// height 0, so it does not pin this; these rows kill a `if len(cps)==0 { cps =
	// hvmGenesisCheckpoints["testnet3"] }` fallback mutant that would let an unpinned network inherit
	// testnet3's checkpoint and classify Canonical.
	require.Equal(t, hvmGenesisPairingCustom, classifyHvmGenesisPairing("mainnet", canonicalHvmGenesisHeight, canonicalHvmGenesisHash),
		"mainnet's checkpoint is the {883092,…eda8} pair, not the testnet3 pair: the testnet3 pair classifies Custom on mainnet (no fallback)")
	require.Equal(t, hvmGenesisPairingCustom, classifyHvmGenesisPairing("localnet", canonicalHvmGenesisHeight, canonicalHvmGenesisHash),
		"localnet has no checkpoint: even the exact canonical testnet3 pair must be Custom (no fallback)")

	// The wrapper (initHvmHeaderNode) refuses (log.Crit) a Custom pairing on every network except the
	// localnet dev network. Enforced networks are pinned (a Custom pairing there = a non-canonical
	// offset/header -> refuse); localnet is unpinned (-> warn). mainnet is pinned with the migrated-state
	// {883092,…eda8} pair (the dual-pin with testnet3[1]); localnet stays unpinned.
	require.NotEmpty(t, hvmGenesisCheckpoints["testnet3"], "testnet3 is pinned/enforced")
	require.NotEmpty(t, hvmGenesisCheckpoints["upgradetest"])
	require.Empty(t, hvmGenesisCheckpoints["localnet"], "localnet is the unpinned dev network (Custom -> warn)")
	require.NotContains(t, hvmGenesisCheckpoints, "localnet", "localnet must not be a key in the checkpoints map (an empty-slice entry would pass the Empty check above)")
	require.Len(t, hvmGenesisCheckpoints["mainnet"], 1, "mainnet is pinned with the migrated-state pair (dual-pin)")
	require.Equal(t, hvmGenesisPairingCanonical, classifyHvmGenesisPairing("mainnet", vm.MainnetHvmGenesisHeight, vm.MainnetHvmGenesisHash),
		"the {883092,…eda8} pair is Canonical on mainnet (the migrated state)")
}

// TestHvmGenesisCheckpointMatchesCanonicalHeader pins the hardcoded checkpoint hash against the block
// hash of the canonical default header hex, so a typo in the literal (or a default change) is caught.
func TestHvmGenesisCheckpointMatchesCanonicalHeader(t *testing.T) {
	h := mustEffectiveGenesisHeader(t)
	cps := hvmGenesisCheckpoints["testnet3"]
	// cps[0] is the compiled default; additional entries (e.g. the backwards-compat fleet pair) may
	// follow it. This test pins the default at [0]; the exact per-network count is asserted by
	// TestHvmGenesisCheckpointsWellFormed.
	require.NotEmpty(t, cps)
	require.Equal(t, canonicalHvmGenesisHeight, cps[0].height)
	require.Equal(t, h.BlockHash().String(), cps[0].hash,
		"testnet3 checkpoint hash must equal the canonical default header's block hash")
	require.Equal(t, canonicalHvmGenesisHash, cps[0].hash, "and the hardcoded literal")
}

const btcDiffTestHvm0Time = uint64(1000)

// seedLightweightAboveFloor brings up an ExternalHeaderMode TBC node at testnet3 genesis and seeds a
// contiguous min-difficulty header chain a few blocks past floorClearance, so subsequent headers are
// above the floor and get enforced. Returns the chain, the genesis (floor) header, and the seeded BTC tip.
func seedLightweightAboveFloor(t *testing.T) (*BlockChain, *wire.BlockHeader, *wire.BlockHeader) {
	t.Helper()
	chain, lightTip := newHvmTestChainWithLightTBC(t, btcDiffTestHvm0Time) // synthetic testnet3 effective genesis @ height 3488421 (min-difficulty; see hvmSynthetic*)

	total := 2*2016 + 11 + 8 // generous over-seed: comfortably > floorClearance(testnet3) so the candidate is enforced
	hdrs := make([]*wire.BlockHeader, 0, total)
	prev := lightTip.BlockHash()
	ts := lightTip.Timestamp
	for i := 0; i < total; i++ {
		ts = ts.Add(600 * time.Second) // 600s < 1200s -> within the testnet3 20-min reduction window
		h := &wire.BlockHeader{Version: lightTip.Version, PrevBlock: prev, MerkleRoot: lightTip.MerkleRoot, Timestamp: ts, Bits: lightTip.Bits, Nonce: uint32(i)}
		hdrs = append(hdrs, h)
		prev = h.BlockHash()
	}
	for start := 0; start < len(hdrs); start += 1000 {
		end := start + 1000
		if end > len(hdrs) {
			end = len(hdrs)
		}
		last := hdrs[end-1].BlockHash()
		_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: hdrs[start:end]}, last[:])
		require.NoError(t, err, "seeding external headers chunk [%d:%d]", start, end)
	}
	btcTipHeight, btcTip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hdrs[len(hdrs)-1].BlockHash(), btcTip.BlockHash(), "lightweight tip must advance to the seeded chain head")

	// Pin the floor-clearance margin so the accept/reject enforce oracles below cannot turn vacuous
	// (defer instead of enforce) if floorClearance or the seed count drifts. The gate enforces only at
	// minHeight >= floorHeight + floorClearance. Derive the threshold from the production source
	// (vm.BTCFloorClearanceForNetwork -> vm.floorClearance) so it tracks the value automatically. The
	// candidate header the enforce tests build extends btcTip (height btcTipHeight+1) and must sit
	// strictly above floorHeight+floorClearance, or "enforce" silently becomes "defer".
	floorClearanceTestnet3, ferr := vm.BTCFloorClearanceForNetwork("testnet3")
	require.NoError(t, ferr, "testnet3 must resolve a floor clearance")
	require.Equal(t, hvmSyntheticGenesisHeight+uint64(total), btcTipHeight,
		"seeded tip height = effective-genesis floor + number of seeded headers")
	require.Greater(t, btcTipHeight+1, hvmSyntheticGenesisHeight+floorClearanceTestnet3,
		"the candidate (btcTip+1) must clear the floor-enforcement threshold, else the enforce oracles are vacuous")
	return chain, lightTip, btcTip
}

func TestHvmBtcDiffFloorAwareAgainstRealLightweightNode(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: seeds >floorClearance headers into a real lightweight TBC leveldb")
	}
	chain, lightTip, tip := seedLightweightAboveFloor(t)

	mk := func(bits uint32, nonce uint32) []*wire.BlockHeader {
		return []*wire.BlockHeader{{
			Version: tip.Version, PrevBlock: tip.BlockHash(), MerkleRoot: tip.MerkleRoot,
			Timestamp: tip.Timestamp.Add(600 * time.Second), Bits: bits, Nonce: nonce,
		}}
	}

	// ACCEPT: correct (PowLimitBits) difficulty, above the floor.
	require.NoError(t, vm.ValidateBTCHeaderBatchForNetwork(chain.ctx, chain.tbcHeaderNode, "testnet3", hvmSyntheticGenesisHeight, mk(lightTip.Bits, 1)),
		"a valid above-floor testnet3 min-difficulty header must accept against the real node")

	// REJECT: wrong (harder) difficulty, above the floor -> a btcd RuleError (ErrUnexpectedDifficulty).
	rerr := vm.ValidateBTCHeaderBatchForNetwork(chain.ctx, chain.tbcHeaderNode, "testnet3", hvmSyntheticGenesisHeight, mk(0x1d00fffe, 2))
	require.Error(t, rerr)
	require.NotErrorIs(t, rerr, vm.ErrBTCBatchBelowFloor, "an above-floor header must be enforced, not deferred")
	require.NotErrorIs(t, rerr, vm.ErrBTCHeaderContextUnavailable, "ancestry is present; not a skip")
	var re blockchain.RuleError
	require.ErrorAs(t, rerr, &re, "a wrong-difficulty above-floor header must be a btcd RuleError")
	require.Equal(t, blockchain.ErrUnexpectedDifficulty, re.ErrorCode)

	// DEFER: a near-genesis batch (off the floor) is within the clearance -> ErrBTCBatchBelowFloor.
	below := []*wire.BlockHeader{{
		Version: lightTip.Version, PrevBlock: lightTip.BlockHash(), MerkleRoot: lightTip.MerkleRoot,
		Timestamp: lightTip.Timestamp.Add(600 * time.Second), Bits: lightTip.Bits, Nonce: 3,
	}}
	require.ErrorIs(t, vm.ValidateBTCHeaderBatchForNetwork(chain.ctx, chain.tbcHeaderNode, "testnet3", hvmSyntheticGenesisHeight, below), vm.ErrBTCBatchBelowFloor,
		"a near-floor batch must defer, even against the real node")

	// DEFER-over-REJECT precedence: a WRONG-difficulty batch BELOW the floor must STILL defer (the floor gate runs
	// BEFORE the contextual validator), not eagerly reject. The existing below-floor case uses CORRECT difficulty, so
	// a mutant that contextually-rejects wrong difficulty before the floor check would survive it.
	belowWrong := []*wire.BlockHeader{{
		Version: lightTip.Version, PrevBlock: lightTip.BlockHash(), MerkleRoot: lightTip.MerkleRoot,
		Timestamp: lightTip.Timestamp.Add(600 * time.Second), Bits: 0x1d00fffe, Nonce: 4,
	}}
	bwErr := vm.ValidateBTCHeaderBatchForNetwork(chain.ctx, chain.tbcHeaderNode, "testnet3", hvmSyntheticGenesisHeight, belowWrong)
	require.ErrorIs(t, bwErr, vm.ErrBTCBatchBelowFloor, "a wrong-difficulty batch below the floor must DEFER, not contextually reject (floor-gate precedence)")
	var bwRe blockchain.RuleError
	require.NotErrorAs(t, bwErr, &bwRe, "the floor gate must short-circuit before any contextual RuleError")
}

// TestHvmApplyPathEnforcesAndReplaySuppresses drives the consensus apply path end-to-end (the switch
// the unit/validator tests do not reach): an above-floor wrong-difficulty header in a
// BtcAttributesDeposited tx must make the block invalid (consensus.ErrInvalidHVMHeaders) without
// advancing the BTC tip or the upstream state id; and with enforceBTCDiff=false (the restore/replay path)
// the same block must not be difficulty-rejected.
func TestHvmApplyPathEnforcesAndReplaySuppresses(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: seeds >floorClearance headers into a real lightweight TBC leveldb")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	tip := seedRegtestAboveFloor(t, chain, genesis)

	// An above-floor header mined for a wrong difficulty (0x207ffffe, one step harder than regtest's
	// expected PowLimitBits 0x207fffff): it passes the floor-independent PoW gate (its hash meets its own
	// claimed target) but fails the contextual check (Bits != expected). This un-shadows the apply-path
	// contextual-reject arm — an un-mined header would be rejected by the PoW gate first.
	wrong := *mineRegtestChildBits(t, tip, 0x207ffffe, 1)
	require.NoError(t, vm.CheckBTCHeaderBatchPoWForNetwork("localnet", []*wire.BlockHeader{&wrong}),
		"precondition: the wrong-difficulty header must PASS PoW, so the CONTEXTUAL arm (not the PoW gate) is what rejects")
	canon := wrong.BlockHash()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, []wire.BlockHeader{wrong})
	require.NoError(t, err)
	nHeader := &types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()

	// Take the "first hVM header update" apply branch (no parent-state check) by resetting the node's
	// upstream state id to genesis.
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))
	sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)

	// ENFORCE: reject the block, leaving the consensus view untouched.
	err = chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true)
	require.ErrorIs(t, err, consensus.ErrInvalidHVMHeaders,
		"an above-floor wrong-difficulty BtcAttr header must reject the block via the apply-path switch")
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, tip.BlockHash(), tipAfter.BlockHash(), "a rejected block must NOT advance the BTC tip (reject is before AddExternalHeaders)")
	sid1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, sid0[:], sid1[:], "a rejected block must NOT advance the upstream state id")

	// REPLAY SUPPRESSION: with enforceBTCDiff=false the same wrong-difficulty block is suppressed and
	// committed (the restore/replay path re-applies already-canonical blocks). Assert the full commit (no
	// error, BTC tip advanced to the wrong header, upstream-state-id advanced to the block) so a
	// regression to ErrCorruptHVMHeaderOnlyModeState or any non-commit is caught; a bare NotErrorIs would
	// pass green on that.
	err = chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, false)
	require.NoError(t, err, "restore/replay (enforceBTCDiff=false) must suppress contextual-difficulty validation and commit the block")
	_, tipReplay, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, wrong.BlockHash(), tipReplay.BlockHash(), "replay must commit the (un-validated) header, advancing the BTC tip")
	sidReplay, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sidReplay[:], "replay commit must advance the upstream-state-id to the block")
}

// TestHvmSequencerBtcDiffPrefixAgainstRealLightweightNode drives the sequencer build-path truncation helper
// (longestEnforceableBTCHeaderPrefix) with the real floor-aware validator closure against a real
// lightweight node — the same closure getBitcoinAttributesForNextBlock uses. Proves truncation is correct
// end-to-end (not just against a fake classifier): a chain extending the seeded above-floor tip with a
// wrong-difficulty header in the middle is truncated to the honest prefix; a leading wrong-difficulty
// header yields an empty prefix; an all-valid chain is kept.
func TestHvmSequencerBtcDiffPrefixAgainstRealLightweightNode(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: seeds >floorClearance headers into a real lightweight TBC leveldb")
	}
	chain, lightTip, btcTip := seedLightweightAboveFloor(t)

	// The real validator closure, identical to the one wired into getBitcoinAttributesForNextBlock.
	classify := func(batch []*wire.BlockHeader) error {
		return vm.ValidateBTCHeaderBatchForNetwork(chain.ctx, chain.tbcHeaderNode, "testnet3",
			hvmSyntheticGenesisHeight, batch)
	}

	// build returns a contiguous chain extending btcTip; bits[i] is the difficulty of header i. All are
	// 600s-spaced (inside the testnet3 20-min reduction window), so the expected difficulty is
	// PowLimitBits and any other value is a contextual RuleError.
	build := func(bits []uint32) []*wire.BlockHeader {
		hdrs := make([]*wire.BlockHeader, len(bits))
		prev := btcTip.BlockHash()
		ts := btcTip.Timestamp
		for i, b := range bits {
			ts = ts.Add(600 * time.Second)
			h := &wire.BlockHeader{Version: lightTip.Version, PrevBlock: prev, MerkleRoot: lightTip.MerkleRoot, Timestamp: ts, Bits: b, Nonce: uint32(100 + i)}
			hdrs[i] = h
			prev = h.BlockHash()
		}
		return hdrs
	}
	const good = uint32(0x1d00ffff) // testnet3 PowLimitBits (== lightTip.Bits)
	const bad = uint32(0x1d00fffe)  // harder-than-expected -> ErrUnexpectedDifficulty

	t.Run("all valid keeps the whole chain", func(t *testing.T) {
		in := build([]uint32{good, good, good, good})
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, classify)
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 4)
	})

	t.Run("wrong-difficulty header in the middle truncates to the honest prefix", func(t *testing.T) {
		in := build([]uint32{good, good, bad, good}) // index 2 invalid
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, classify)
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 2, "must truncate to the prefix before the forged header")
		require.Same(t, in[0], got[0])
		require.Same(t, in[1], got[1])
	})

	t.Run("leading wrong-difficulty header yields an empty prefix", func(t *testing.T) {
		in := build([]uint32{bad, good, good})
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, classify)
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 0, "no honest prefix to advance the BTC view this round")
	})

	// A near-floor batch (extending lightTip, at the effective-genesis floor) is below the clearance, so
	// the real validator returns ErrBTCBatchBelowFloor; the helper must treat that as an acceptable
	// verdict (defer) and keep all headers — exercising isAcceptableBTCBatchVerdict against the real
	// validator, not just a fake sentinel.
	t.Run("near-floor batch defers and keeps all headers", func(t *testing.T) {
		nearFloor := []*wire.BlockHeader{{
			Version: lightTip.Version, PrevBlock: lightTip.BlockHash(), MerkleRoot: lightTip.MerkleRoot,
			Timestamp: lightTip.Timestamp.Add(600 * time.Second), Bits: lightTip.Bits, Nonce: 77,
		}}
		// Sanity: the real validator must actually DEFER this batch (else the case is vacuous).
		require.ErrorIs(t, classify(nearFloor), vm.ErrBTCBatchBelowFloor)
		got, skip, err := longestEnforceableBTCHeaderPrefix(nearFloor, classify)
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 1, "a deferred (below-floor) batch must be kept whole, not truncated")
	})
}

// Unit tests for the pure loader-control-flow helpers (no live TBC node):
//   - longestEnforceableBTCHeaderPrefix: the sequencer build-path truncation logic.
//   - btcEnforceableSuffix:              the snap-sync enforce/defer split.
//
// The contextual-difficulty validator itself is exercised against a real lightweight node in
// blockchain_hvm_btcdiff_test.go and core/vm; these tests pin the control flow that wraps it.
// TestClassifySnapBtcDiffObservation pins the snap-sync observe-only verdict routing: only a RuleError
// (snapObsReject) is the alertable arm (the one SnapSyncHvm marks on the meter), and the
// benign/incomplete verdicts never reach it. Pure seam for the otherwise-inline snap dispatch (no live
// TBC node). A wrapped sentinel must still classify correctly.
func TestClassifySnapBtcDiffObservation(t *testing.T) {
	require.Equal(t, snapObsClean, classifySnapBtcDiffObservation(nil))
	require.Equal(t, snapObsBelowFloor, classifySnapBtcDiffObservation(vm.ErrBTCBatchBelowFloor))
	require.Equal(t, snapObsIncomplete, classifySnapBtcDiffObservation(vm.ErrBTCBatchUnconnected))
	require.Equal(t, snapObsIncomplete, classifySnapBtcDiffObservation(vm.ErrBTCHeaderContextUnavailable))
	// Any non-sentinel error is a btcd RuleError -> the alertable arm.
	require.Equal(t, snapObsReject, classifySnapBtcDiffObservation(errors.New("simulated btcd RuleError")))
	// Wrapped sentinels must still route by identity, not collapse to reject.
	require.Equal(t, snapObsBelowFloor, classifySnapBtcDiffObservation(fmt.Errorf("ctx: %w", vm.ErrBTCBatchBelowFloor)))
	require.Equal(t, snapObsIncomplete, classifySnapBtcDiffObservation(fmt.Errorf("ctx: %w", vm.ErrBTCHeaderContextUnavailable)))
	require.Equal(t, snapObsReject, classifySnapBtcDiffObservation(fmt.Errorf("ctx: %w", errors.New("rule"))))
}

// mkHeaders returns n distinct (non-nil) header pointers. The pure helpers never dereference header
// contents, so empty headers are sufficient to test the control flow.
func mkHeaders(n int) []*wire.BlockHeader {
	hs := make([]*wire.BlockHeader, n)
	for i := range hs {
		hs[i] = &wire.BlockHeader{}
	}
	return hs
}

func TestLongestEnforceableBTCHeaderPrefix(t *testing.T) {
	ruleErr := errors.New("simulated btcd RuleError")

	// rejectFromIndex models a contiguous chain whose first contextually-invalid header is at index k: the
	// apply path's whole-batch gate rejects any prefix that includes index k (len > k). A header's
	// validity is prefix-monotonic, so this matches the real validator's shape.
	rejectFromIndex := func(k int) btcHeaderBatchClassifier {
		return func(headers []*wire.BlockHeader) error {
			if len(headers) > k {
				return ruleErr
			}
			return nil
		}
	}

	t.Run("all valid returns full slice", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, rejectFromIndex(8))
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 8)
	})

	t.Run("first header invalid returns empty prefix", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, rejectFromIndex(0))
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 0)
	})

	t.Run("middle invalid truncates to prefix before it", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, rejectFromIndex(3))
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 3)
		// The returned prefix must be the leading sub-slice (alias the same backing pointers).
		require.Same(t, in[0], got[0])
		require.Same(t, in[2], got[2])
	})

	t.Run("last header invalid keeps all but the last", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, rejectFromIndex(7))
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 7)
	})

	t.Run("below-floor is acceptable (no truncation)", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, func([]*wire.BlockHeader) error {
			return vm.ErrBTCBatchBelowFloor
		})
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 8, "below-floor means the apply path DEFERS, so keep all headers")
	})

	t.Run("unconnected is acceptable (no truncation)", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, func([]*wire.BlockHeader) error {
			return vm.ErrBTCBatchUnconnected
		})
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 8, "unconnected is preserved for AddExternalHeaders to decide, not truncated")
	})

	t.Run("context-unavailable signals skip, never truncates", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, func([]*wire.BlockHeader) error {
			return vm.ErrBTCHeaderContextUnavailable
		})
		require.True(t, skip)
		require.ErrorIs(t, err, vm.ErrBTCHeaderContextUnavailable)
		require.Nil(t, got, "a transient read must not silently drop honest headers")
	})

	t.Run("empty input returns empty", func(t *testing.T) {
		got, skip, err := longestEnforceableBTCHeaderPrefix(nil, rejectFromIndex(0))
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 0)
	})

	// A context-unavailable verdict that only appears once the prefix has shrunk past the reject point
	// must still abort (skip), never silently accept a shorter prefix. (Defends the dominance of the
	// recoverable check over truncation across iterations.)
	t.Run("late context-unavailable still skips", func(t *testing.T) {
		in := mkHeaders(5)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, func(headers []*wire.BlockHeader) error {
			switch len(headers) {
			case 5, 4, 3:
				return errors.New("rule error")
			default:
				return vm.ErrBTCHeaderContextUnavailable
			}
		})
		require.True(t, skip)
		require.ErrorIs(t, err, vm.ErrBTCHeaderContextUnavailable)
		require.Nil(t, got)
	})
}

func TestBtcEnforceableSuffix(t *testing.T) {
	t.Run("empty input", func(t *testing.T) {
		suffix, deferred := btcEnforceableSuffix(nil, 100, 200)
		require.Nil(t, suffix)
		require.Equal(t, 0, deferred)
	})

	t.Run("entire chain at or above floor is fully enforced (firstHeight == enforceFloor)", func(t *testing.T) {
		in := mkHeaders(10)
		suffix, deferred := btcEnforceableSuffix(in, 1000, 1000)
		require.Len(t, suffix, 10)
		require.Equal(t, 0, deferred)
		require.Same(t, in[0], suffix[0])
	})

	t.Run("firstHeight STRICTLY above enforceFloor enforces all (underflow guard)", func(t *testing.T) {
		// firstHeight > enforceFloor exercises the `firstHeight >= enforceFloor` guard's strictly-greater
		// case. Without it (e.g. a `>=`->`==` mutant), c = enforceFloor-firstHeight underflows in uint64 to
		// a huge value -> c >= len -> the whole chain is WRONGLY deferred instead of fully enforced.
		in := mkHeaders(10) // heights 2000..2009, enforceFloor 1000 => all strictly above
		suffix, deferred := btcEnforceableSuffix(in, 2000, 1000)
		require.Len(t, suffix, 10, "a chain wholly above the enforce floor must be fully enforced, not deferred")
		require.Equal(t, 0, deferred)
		require.Same(t, in[0], suffix[0])
	})

	t.Run("entire chain below floor is fully deferred", func(t *testing.T) {
		in := mkHeaders(10) // heights 100..109, enforceFloor 200 => all deferred
		suffix, deferred := btcEnforceableSuffix(in, 100, 200)
		require.Nil(t, suffix)
		require.Equal(t, 10, deferred)
	})

	t.Run("split in the middle defers the prefix, enforces the suffix", func(t *testing.T) {
		in := mkHeaders(10) // heights 100..109
		// enforceFloor 105 => indices 0..4 (heights 100..104) deferred, indices 5..9 enforced.
		suffix, deferred := btcEnforceableSuffix(in, 100, 105)
		require.Equal(t, 5, deferred)
		require.Len(t, suffix, 5)
		require.Same(t, in[5], suffix[0])
		require.Same(t, in[9], suffix[4])
	})

	t.Run("first enforceable height exactly at the boundary", func(t *testing.T) {
		in := mkHeaders(4) // heights 50..53
		// enforceFloor 53 => only the last header (height 53) enforced.
		suffix, deferred := btcEnforceableSuffix(in, 50, 53)
		require.Equal(t, 3, deferred)
		require.Len(t, suffix, 1)
		require.Same(t, in[3], suffix[0])
	})

	t.Run("c exactly equals len defers the whole chain", func(t *testing.T) {
		in := mkHeaders(10) // heights 100..109; enforceFloor 110 => c = 10 == len => all deferred
		suffix, deferred := btcEnforceableSuffix(in, 100, 110)
		require.Nil(t, suffix)
		require.Equal(t, 10, deferred)
	})

	t.Run("c just below len enforces exactly the last header", func(t *testing.T) {
		in := mkHeaders(10) // heights 100..109; enforceFloor 109 => c = 9 => enforce only index 9
		suffix, deferred := btcEnforceableSuffix(in, 100, 109)
		require.Equal(t, 9, deferred)
		require.Len(t, suffix, 1)
		require.Same(t, in[9], suffix[0])
	})
}

// TestSnapEnforceFloorAboveValidatorGate pins the snap-sync alignment invariant. Snap-sync is
// observe-only for contextual-difficulty (never halts — see SnapSyncHvm), so this keeps the snap-base alert meaningful
// and low-noise: the snap enforce floor (GenesisHeightOffset + clearance + (MaximumBtcHeadersInTx-1))
// must sit above the validator's own defer gate (GenesisHeightOffset + clearance) and above the highest
// header any forward batch could defer, so the observed band is exactly the band the forward apply path
// enforces. If a future change lowered the floor below the gate, btcEnforceableSuffix would hand the
// validator a suffix it reports ErrBTCBatchBelowFloor for, and the observation would go quiet. Cheap
// structural guard; real-node enforce/defer behavior at the gate is covered by
// TestHvmBtcDiffFloorAwareAgainstRealLightweightNode.
func TestSnapEnforceFloorAboveValidatorGate(t *testing.T) {
	const maxBatch = uint64(types.MaximumBtcHeadersInTx)
	require.Greater(t, maxBatch, uint64(1), "the (maxBatch-1) margin is only meaningful for batches > 1 header")

	for _, network := range []string{"mainnet", "testnet3", "upgradetest", "localnet"} {
		clearance, err := vm.BTCFloorClearanceForNetwork(network)
		require.NoError(t, err)
		const floor = uint64(3488421) // an arbitrary non-zero effective-genesis offset

		// Drive the production helper (not a re-derived copy), so a mutation in btcSnapEnforceFloor — the
		// single definition SnapSyncHvm uses — is caught here.
		enforceFloor := btcSnapEnforceFloor(floor, clearance)

		// (1) The lowest observed height must not fall in the validator's defer band [floor,
		// floor+clearance), else the suffix would be reported ErrBTCBatchBelowFloor and the alert would go
		// quiet. A mutant dropping the +clearance term (e.g. enforceFloor = floor + (maxBatch-1)) fails this
		// on every network whose clearance > (maxBatch-1) — true for all (clearance in the thousands >> 29).
		require.Greaterf(t, enforceFloor, floor+clearance,
			"network %q: enforce floor must be strictly above the validator defer gate, else the snap alert goes silent", network)
		// (2) It must be strictly above the highest header any forward-deferred batch can contain
		// (floor+clearance+(maxBatch-2)), so snap's enforce set is a strict subset of the forward path's. A
		// mutant that dropped or shrank the (maxBatch-1) split-safety margin fails this.
		require.Greaterf(t, enforceFloor, floor+clearance+(maxBatch-2),
			"network %q: enforce floor must clear the highest forward-deferrable header (split-safety)", network)
		// (3) And it must be EXACTLY one above that highest forward-deferred header — not needlessly higher
		// (which would deepen the unenforced band). Pins the precise constant.
		require.Equalf(t, floor+clearance+(maxBatch-1), enforceFloor,
			"network %q: enforce floor must be exactly floor+clearance+(maxBatch-1)", network)
	}
}

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

// applyForkBtcAttr applies a BtcAttr block carrying `headers` with the claimed canonical tip, via the genesis-
// reset first-update branch (no parent-state check), at the given enforce setting. Returns the apply error.
func applyForkBtcAttr(t *testing.T, chain *BlockChain, num int64, claim wire.BlockHeader, headers []wire.BlockHeader, enforce bool) error {
	t.Helper()
	c := claim.BlockHash()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&c, headers)
	require.NoError(t, err)
	blk := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(num), Time: btcDiffTestHvm0Time}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blk.Hash().String()] = blk
	chain.tempHeaders[blk.Hash().String()] = blk.Header()
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))
	return chain.applyHvmHeaderConsensusUpdate(blk.Header(), false, enforce)
}

// TestHvmApplyPathCanonicalTipReorgsToHeavierBranch exercises the cumulative-work CanonicalTip SELECTION arm the
// committed (linear) differential-replay fixture never reaches: a competing HEAVIER branch must win fork-choice and the honest
// CanonicalTip claim naming the heavier tip must be accepted. Corpus-free (regtest).
func TestHvmApplyPathCanonicalTipReorgsToHeavierBranch(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis) // incumbent above-floor tip P

	// Commit a single child A off P (live tip = A, height P+1).
	a := *mineRegtestChild(t, p, 100)
	require.NoError(t, applyForkBtcAttr(t, chain, 11, a, []wire.BlockHeader{a}, true))
	_, tipA, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, a.BlockHash(), tipA.BlockHash(), "after committing A the tip is A (P+1)")

	// Competing HEAVIER branch B1->B2 off the SAME parent P (height P+2). Honest claim = B2 (the new winner).
	b1 := *mineRegtestChild(t, p, 200)
	b2 := *mineRegtestChild(t, &b1, 300)
	require.NoError(t, applyForkBtcAttr(t, chain, 12, b2, []wire.BlockHeader{b1, b2}, true),
		"the heavier competing branch with an honest CanonicalTip=B2 claim must be accepted")
	_, tipB, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, b2.BlockHash(), tipB.BlockHash(), "fork-choice must reorg to the heavier branch tip B2")
}

// TestHvmApplyPathCanonicalTipKeepsHeavierOnLighterSideBranch: a LIGHTER side-branch added off a non-tip ancestor
// must NOT displace the heavier incumbent tip; an honest CanonicalTip claim naming the still-heavier incumbent is
// accepted (the header is stored but fork-choice does not move). Corpus-free.
func TestHvmApplyPathCanonicalTipKeepsHeavierOnLighterSideBranch(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)

	// Heavier incumbent A1->A2 off P (tip = A2, height P+2).
	a1 := *mineRegtestChild(t, p, 100)
	a2 := *mineRegtestChild(t, &a1, 110)
	require.NoError(t, applyForkBtcAttr(t, chain, 11, a2, []wire.BlockHeader{a1, a2}, true))
	_, tipA, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, a2.BlockHash(), tipA.BlockHash())

	// Lighter side-branch B1 off P (height P+1) — honestly claim the still-heavier incumbent A2.
	b1 := *mineRegtestChild(t, p, 200)
	require.NoError(t, applyForkBtcAttr(t, chain, 12, a2, []wire.BlockHeader{b1}, true),
		"a lighter side-branch with an honest CanonicalTip=A2 (incumbent) claim must be accepted without reorg")
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, a2.BlockHash(), tipAfter.BlockHash(), "a lighter side-branch must NOT displace the heavier incumbent tip")
}

// TestHvmApplyPathCanonicalTipRejectsLoserClaim: a dishonest CanonicalTip claim naming the LOSING (lighter)
// side-branch as winner must be rejected and BOTH side-branch headers rolled back. Extends the existing
// single-header wrong-tip rollback test to a multi-header competing branch. Corpus-free.
func TestHvmApplyPathCanonicalTipRejectsLoserClaim(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)

	// Heavier incumbent A1->A2->A3 off P (tip = A3, height P+3).
	a1 := *mineRegtestChild(t, p, 100)
	a2 := *mineRegtestChild(t, &a1, 110)
	a3 := *mineRegtestChild(t, &a2, 120)
	require.NoError(t, applyForkBtcAttr(t, chain, 11, a3, []wire.BlockHeader{a1, a2, a3}, true))
	_, tip0, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, a3.BlockHash(), tip0.BlockHash())

	// Lighter branch B1->B2 off P (height P+2) but DISHONESTLY claim CanonicalTip=B2 (the loser).
	b1 := *mineRegtestChild(t, p, 200)
	b2 := *mineRegtestChild(t, &b1, 210)
	require.NoError(t, vm.CheckBTCHeaderBatchPoWForNetwork("localnet", []*wire.BlockHeader{&b1, &b2}),
		"precondition: b1,b2 are PoW-valid, so the rollback below is caused by the dishonest CanonicalTip claim, not a PoW failure")
	require.ErrorIs(t, applyForkBtcAttr(t, chain, 12, b2, []wire.BlockHeader{b1, b2}, true), consensus.ErrInvalidHVMHeaders,
		"a CanonicalTip claim naming the LOSING branch must be rejected")
	// Both rolled-back headers must be absent, and the tip restored to A3.
	_, _, err = chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, b1.BlockHash())
	require.Error(t, err, "rolled-back B1 must be absent")
	_, _, err = chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, b2.BlockHash())
	require.Error(t, err, "rolled-back B2 must be absent")
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, a3.BlockHash(), tipAfter.BlockHash(), "rollback must restore the heavier incumbent tip A3")
}

// TestHvmApplyPathCanonicalTipEqualWorkKeepsIncumbent: an equal-cumulative-work sibling branch (same height, same
// work, different hash) must NOT displace the first-seen incumbent tip — the tie-break is first-seen-wins. An honest
// CanonicalTip claim naming the incumbent is accepted; the tip does not move. Corpus-free.
func TestHvmApplyPathCanonicalTipEqualWorkKeepsIncumbent(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)

	// Incumbent child A1 off P (tip = A1, height P+1).
	a1 := *mineRegtestChild(t, p, 100)
	require.NoError(t, applyForkBtcAttr(t, chain, 11, a1, []wire.BlockHeader{a1}, true))
	_, tipA, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, a1.BlockHash(), tipA.BlockHash())

	// Sibling B1 off the SAME parent P (height P+1, EQUAL cumulative work, different nonce → different hash).
	b1 := *mineRegtestChild(t, p, 999)
	require.NotEqual(t, a1.BlockHash(), b1.BlockHash(), "sibling must differ from the incumbent")
	require.NoError(t, applyForkBtcAttr(t, chain, 12, a1, []wire.BlockHeader{b1}, true),
		"an equal-work sibling with an honest CanonicalTip=A1 (incumbent) claim must be accepted without reorg")
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, a1.BlockHash(), tipAfter.BlockHash(), "equal-work tie must keep the first-seen incumbent A1")
}

// TestHvmApplyPathCanonicalTipEqualWorkRejectsDishonestSiblingClaim: an equal-cumulative-work sibling whose BtcAttr
// claims ITSELF as the canonical tip must be REJECTED. TBC's equal-work tie-break keeps the first-seen incumbent A1,
// so the claimed tip (B1) mismatches the TBC-computed tip (A1) and the cbHash==claim guard (blockchain.go ~2945)
// fires with ErrInvalidHVMHeaders. This is the cross-product the existing tests leave uncovered: the equal-work
// KeepsIncumbent test uses an HONEST claim (-> accept) and RejectsLoserClaim uses a strictly LIGHTER branch
// (-> reject); neither pins a DISHONEST claim in the EQUAL-work tie. The sibling header must roll back and the tip
// must be restored to A1. Corpus-free (regtest).
func TestHvmApplyPathCanonicalTipEqualWorkRejectsDishonestSiblingClaim(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)

	// Incumbent child A1 off P (tip = A1, height P+1).
	a1 := *mineRegtestChild(t, p, 100)
	require.NoError(t, applyForkBtcAttr(t, chain, 11, a1, []wire.BlockHeader{a1}, true))
	_, tipA, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, a1.BlockHash(), tipA.BlockHash())

	// Equal-work sibling B1 off the SAME parent P (height P+1, equal work, different nonce -> different hash),
	// DISHONESTLY claiming CanonicalTip=B1 (itself). The tie-break keeps A1, so the claim mismatches -> reject.
	b1 := *mineRegtestChild(t, p, 999)
	require.NotEqual(t, a1.BlockHash(), b1.BlockHash(), "sibling must differ from the incumbent")
	require.ErrorIs(t, applyForkBtcAttr(t, chain, 12, b1, []wire.BlockHeader{b1}, true), consensus.ErrInvalidHVMHeaders,
		"an equal-work sibling claiming ITSELF as canonical must be rejected (tie-break keeps the first-seen incumbent)")
	// The rejected sibling header must be rolled back and the tip restored to A1.
	_, _, err = chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, b1.BlockHash())
	require.Error(t, err, "the rejected equal-work sibling B1 must be rolled back")
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, a1.BlockHash(), tipAfter.BlockHash(), "rollback must restore the first-seen incumbent A1")
}

// TestHvmApplyPathDuplicateReapplyIsIdempotent drives the end-to-end addHeadersDuplicate arm against a REAL
// lightweight TBC node — the load-bearing claim in the AddExternalHeaders retry doc-comment ("a re-insert is
// duplicate-skipped, cumulative work never double-counted; the duplicate arm's SetUpstreamStateId advance is
// load-bearing"). The PURE classifier is covered on a synthetic DuplicateError elsewhere; this re-feeds the same
// real header batch end-to-end. Re-applying an identical batch (distinct EVM block) must: return nil (NOT
// ErrInvalidHVMHeaders — a duplicate batch must not be mistaken for an invalid one); leave the tip + height unchanged (no double-count);
// and advance the upstream-state-id via the duplicate arm (a dropped advance leaves it at the reset genesis value).
func TestHvmApplyPathDuplicateReapplyIsIdempotent(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers into a real lightweight TBC node")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	// 3 headers off genesis (below the floor clearance -> contextual defers -> the batch falls through to the real
	// AddExternalHeaders, exercising the duplicate arm on a re-apply).
	h1 := *mineRegtestChild(t, genesis, 100)
	h2 := *mineRegtestChild(t, &h1, 110)
	h3 := *mineRegtestChild(t, &h2, 120)
	batch := []wire.BlockHeader{h1, h2, h3}

	// First apply: adds the headers, advances the tip to h3.
	require.NoError(t, applyForkBtcAttr(t, chain, 11, h3, batch, true))
	height1, tip1, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, h3.BlockHash(), tip1.BlockHash())
	sid1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	// Pin sid1 ABSOLUTELY (symmetric to the sid2 pin below): the FIRST (header-bearing success) apply must advance the
	// state-id to its own EVM block 11. sid1 is otherwise only used relationally (!= sid2), so a mutant corrupting the
	// success-path state-id advance (a different branch from the duplicate arm the second apply exercises) would survive.
	c11 := h3.BlockHash()
	btc11, err := types.MakeBtcAttributesDepositedTx(&c11, batch)
	require.NoError(t, err)
	block11 := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc11)}})
	require.Equal(t, block11.Hash().Bytes(), sid1[:], "the first apply must advance the state-id to the re-applying EVM block 11")

	// Second apply: an IDENTICAL batch carried by a DISTINCT EVM block (num 12) -> AddExternalHeaders returns a real
	// DuplicateError -> the addHeadersDuplicate arm repairs idempotently and returns nil.
	require.NoError(t, applyForkBtcAttr(t, chain, 12, h3, batch, true),
		"a re-apply of an identical batch must be idempotent (duplicate arm), not a false reject")
	height2, tip2, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, tip1.BlockHash(), tip2.BlockHash(), "duplicate re-apply must NOT change the canonical tip (no double-insert)")
	require.Equal(t, height1, height2, "duplicate re-apply must NOT change the tip height (cumulative work not double-counted)")
	for _, h := range batch { // headers still present exactly once
		_, _, e := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, h.BlockHash())
		require.NoError(t, e, "the originally-committed header must still be present")
	}

	// The duplicate arm's load-bearing SetUpstreamStateId advance must have fired: the state-id is NOT left at the
	// reset genesis value (a dropped advance would leave genesis and crash the next steady-state forward block).
	sid2, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.NotEqual(t, hVMGenesisUpstreamId, sid2, "the duplicate arm must re-issue SetUpstreamStateId (not leave the reset genesis id)")
	require.NotEqual(t, sid1, sid2, "the duplicate arm must advance the state-id to the re-applying block")
	// Pin the EXACT advanced value (not just !=): the state-id must be the re-applying EVM block 12's hash (the same
	// recipe applyForkBtcAttr used for num 12). Kills a mutant advancing the state-id to an arbitrary wrong value.
	c12 := h3.BlockHash()
	btc12, err := types.MakeBtcAttributesDepositedTx(&c12, batch)
	require.NoError(t, err)
	block12 := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: btcDiffTestHvm0Time}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc12)}})
	require.Equal(t, block12.Hash().Bytes(), sid2[:], "the duplicate arm must advance the state-id to the re-applying EVM block 12")

	// Third re-apply of the SAME batch (EVM block 13): the duplicate arm must fire AGAIN and advance the state-id to
	// block 13, proving the advance is idempotent across REPEATED invocations (not first-duplicate-only), still with
	// no double-insert (tip/height unchanged).
	require.NoError(t, applyForkBtcAttr(t, chain, 13, h3, batch, true), "a third identical re-apply must also be idempotent")
	height3, tip3, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, tip2.BlockHash(), tip3.BlockHash(), "third re-apply must NOT change the tip")
	require.Equal(t, height2, height3, "third re-apply must NOT change the height")
	sid3, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	c13 := h3.BlockHash()
	btc13, err := types.MakeBtcAttributesDepositedTx(&c13, batch)
	require.NoError(t, err)
	block13 := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(13), Time: btcDiffTestHvm0Time}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc13)}})
	require.Equal(t, block13.Hash().Bytes(), sid3[:], "the duplicate arm must advance the state-id again to EVM block 13 (idempotent across re-applies)")
}

// The operator-facing canonical-tip-mismatch DIAGNOSTIC (blockchain.go ~2952). The dishonest-claim tests pin the
// returned error class (ErrInvalidHVMHeaders), but the descriptive log message — which reports the headers added and
// the divergence between the CLAIMED and the ACTUAL computed tip, and is the primary signal an operator/tooling sees
// when a BtcAttr tx commits the wrong tip — lives only in the log, untested. A refactor that drops or garbles it
// would leave the rejection silent-but-cryptic. Corpus-free (regtest); captures the root logger for the apply only.
func TestHvmCanonicalTipMismatchLogMessage(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)
	a1 := *mineRegtestChild(t, p, 100) // the header actually added -> becomes the real canonical tip
	d := *mineRegtestChild(t, p, 777)  // a distinct sibling; its hash is the WRONG claimed tip
	require.NotEqual(t, a1.BlockHash(), d.BlockHash(), "the claimed tip must differ from the produced tip")

	// Capture the root logger for the duration of the apply only (harness setup above logs to the real logger).
	var buf bytes.Buffer
	prev := log.Root()
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(&buf, slog.LevelDebug, false)))
	err := applyForkBtcAttr(t, chain, 11, d, []wire.BlockHeader{a1}, true)
	log.SetDefault(prev) // restore before asserting

	require.ErrorIs(t, err, consensus.ErrInvalidHVMHeaders,
		"a claim naming a tip other than the one produced by adding the headers must be rejected")
	out := buf.String()
	require.Contains(t, out, "claims that after adding",
		"the operator-facing canonical-tip-mismatch diagnostic must be emitted")
	require.Contains(t, out, "but after adding the headers to TBC the canonical tip is",
		"the diagnostic must report the actual computed tip vs the claimed one")
}

// Boot-time hVM difficulty-enforcement decision, exercised through the REAL initHvmHeaderNode path (a live
// lightweight TBC node), not just the isLegacyDeferredPairing predicate. This is the integration the apply-path
// gate tests and the pure-predicate test do not cover: that a node which boots in the legacy DEFER state
// (network="testnet3" over the Bitcoin-MAINNET genesis pair — the classifier accepts it via the testnet3 dual-pin)
// comes up UNENFORCED, while a genuine testnet3 node and a migrated mainnet node both come up ENFORCED. Corpus-free.
func TestHvmBootEnforcementDecision(t *testing.T) {
	if testing.Short() {
		t.Skip("builds real lightweight TBC nodes")
	}
	mainnetGen := decodeMainnetGenesisHeader(t)

	cases := []struct {
		name    string
		network string
		genesis *wire.BlockHeader
		height  uint64
		enforce bool
	}{
		{
			// DEFER state: testnet3 params over the Bitcoin-mainnet pair (the legacy mislabel / migration defer
			// fallback). Accepted by the pairing guard (testnet3 dual-pins {883092,…}), but must boot UNENFORCED —
			// enforcing real mainnet headers under TestNet3Params would split from a migrated fleet.
			name: "deferred-testnet3-over-mainnet-pair", network: "testnet3",
			genesis: mainnetGen, height: vm.MainnetHvmGenesisHeight, enforce: false,
		},
		{
			// Genuine testnet3 node (the shipped consensus network) at its own canonical pair -> ENFORCED.
			name: "genuine-testnet3", network: "testnet3",
			genesis: mustEffectiveGenesisHeader(t), height: canonicalHvmGenesisHeight, enforce: true,
		},
		{
			// Migrated mainnet node at the mainnet pair -> ENFORCED (keyed on the (network,height) pair, not the
			// word "migrated").
			name: "migrated-mainnet", network: "mainnet",
			genesis: mainnetGen, height: vm.MainnetHvmGenesisHeight, enforce: true,
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			chain := newHvmInitTestChain(t)
			cfg := hvmInitLightTBCConfig(t, tc.network, tc.genesis, tc.height)

			// Capture logs across initHvmHeaderNode to assert the DEFER-boot operator warning (the only split-
			// prevention signal). It fires ONLY on the unenforced (deferred) path; enforced boots must stay silent.
			var buf bytes.Buffer
			prev := log.Root()
			log.SetDefault(log.NewLogger(log.NewTerminalHandler(&buf, false)))
			chain.initHvmHeaderNode(cfg) // crits (os.Exit) if the pairing guard rejects -> reaching below proves it booted
			log.SetDefault(prev)
			t.Cleanup(func() {
				if chain.tbcHeaderNode != nil {
					_ = chain.tbcHeaderNode.ExternalHeaderTearDown()
				}
			})
			require.True(t, chain.hvmEnabled, "the node must have booted hVM (pairing guard accepted the pair)")
			require.Equal(t, tc.enforce, chain.hvmDiffEnforceable.Load(),
				"boot-time difficulty enforcement decision for %s", tc.name)
			require.NotNil(t, chain.tbcHeaderNodeConfig, "tbcHeaderNodeConfig must be initialized")
			require.Equal(t, tc.network, chain.tbcHeaderNodeConfig.Network, "config network must match input: %s vs %s", tc.network, chain.tbcHeaderNodeConfig.Network)
			require.Equal(t, tc.height, chain.tbcHeaderNodeConfig.GenesisHeightOffset, "config genesis height must match input: %d vs %d", tc.height, chain.tbcHeaderNodeConfig.GenesisHeightOffset)
			if tc.enforce {
				require.NotContains(t, buf.String(), "enforcement DISABLED", "an ENFORCED boot must NOT emit the defer warning")
			} else {
				require.Contains(t, buf.String(), "enforcement DISABLED", "a DEFER boot must warn the operator not to sequence on it")
			}
		})
	}
}

// TestSnapShouldObserveBtcDiff pins the snap observe-only gate predicate: the observe-only
// contextual-difficulty check runs ONLY when there is >=1 reconstructed header AND the node is
// difficulty-enforceable. A DEFER-state node (enforceable=false) must SKIP it. Pure predicate — no TBC node.
func TestSnapShouldObserveBtcDiff(t *testing.T) {
	cases := []struct {
		headers     int
		enforceable bool
		want        bool
	}{
		{5, true, true},   // headers present + enforceable -> observe
		{5, false, false}, // DEFER state: must SKIP even with headers (no spurious wrong-params alerts)
		{0, true, false},  // no headers -> nothing to observe
		{0, false, false},
	}
	for _, c := range cases {
		require.Equalf(t, c.want, snapShouldObserveBtcDiff(c.headers, c.enforceable),
			"snapShouldObserveBtcDiff(%d,%v)", c.headers, c.enforceable)
	}
}

// TestEnforceableBTCBatchGate exercises the build-path classifier (the truncation predicate
// longestEnforceableBTCHeaderPrefix calls) in BOTH gate states. For a wrong-difficulty but PoW-valid above-floor
// header: a DEFER-state node (hvmDiffEnforceable=false) must ACCEPT it (return nil — do NOT truncate, else it
// judges mainnet headers under testnet3 params and diverges from a migrated sequencer); an enforceable node must
// REJECT it (contextual RuleError -> truncate). Uses a regtest light node.
func TestEnforceableBTCBatchGate(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: seeds >floorClearance headers into a real lightweight TBC leveldb")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	tip := seedRegtestAboveFloor(t, chain, genesis)
	wrong := *mineRegtestChildBits(t, tip, 0x207ffffe, 1) // above-floor, PoW-valid, contextually-wrong difficulty
	require.NoError(t, vm.CheckBTCHeaderBatchPoWForNetwork("localnet", []*wire.BlockHeader{&wrong}),
		"precondition: the wrong-difficulty header PASSES PoW, so the CONTEXTUAL arm is what rejects")
	batch := []*wire.BlockHeader{&wrong}

	// DEFER state (hvmDiffEnforceable=false): accept the full prefix (no truncation) — must not judge under wrong params.
	chain.hvmDiffEnforceable.Store(false)
	require.NoError(t, chain.enforceableBTCBatch(batch),
		"a DEFER-state build path must accept the full prefix (the enforce gate, not the params, turns judgement off)")

	// Enforceable state: the contextually-wrong header is rejected (so the prefix truncates).
	chain.hvmDiffEnforceable.Store(true)
	require.Error(t, chain.enforceableBTCBatch(batch),
		"an enforceable build path must reject a contextually-wrong above-floor header")
}

// TestHvmApplyPathGateSuppressesEnforceWhenNotEnforceable pins the apply-path gate in the DEFER state: a
// deferred node (hvmDiffEnforceable=false) asked to ENFORCE (enforce param TRUE) must behave like restore/replay.
// The per-boot gate, not the enforce param, turns judgement off, so a deferred node never judges mainnet headers
// under testnet3 params and splits the fleet. Complements TestHvmApplyPathEnforcesAndReplaySuppresses, which
// covers enforceable+enforce=true -> reject and enforceable+enforce=false -> replay.
func TestHvmApplyPathGateSuppressesEnforceWhenNotEnforceable(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: seeds >floorClearance headers into a real lightweight TBC leveldb")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	tip := seedRegtestAboveFloor(t, chain, genesis)
	wrong := *mineRegtestChildBits(t, tip, 0x207ffffe, 1)
	require.NoError(t, vm.CheckBTCHeaderBatchPoWForNetwork("localnet", []*wire.BlockHeader{&wrong}),
		"precondition: the wrong-difficulty header must PASS PoW so only the CONTEXTUAL check could reject")
	canon := wrong.BlockHash()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, []wire.BlockHeader{wrong})
	require.NoError(t, err)
	blockN := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId)) // first-update branch

	// DEFER state + enforce param TRUE: the gate must SUPPRESS enforcement and COMMIT (identical to replay), NOT
	// reject. Keying enforcement on the enforce param alone (ignoring the gate) would ErrInvalidHVMHeaders here
	// and split a deferred node from the fleet.
	chain.hvmDiffEnforceable.Store(false)
	err = chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true)
	require.NoError(t, err, "a DEFER-state node (hvmDiffEnforceable=false) asked to enforce must SUPPRESS judgement and commit")
	require.NotErrorIs(t, err, consensus.ErrInvalidHVMHeaders)
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, wrong.BlockHash(), tipAfter.BlockHash(), "the suppressed-enforce commit must advance the BTC tip to the (un-judged) header")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sid[:], "the commit must advance the upstream-state-id to the block")
}

// Apply-path PRE-Hvm0-TIME enforce-flag truth-table cells. Enforcement is gated by enforceBTCDiff =
// enforce && hvmDiffEnforceable, and the whole BtcAttr handling is gated by IsHvm0(header.Time). The DEFER cell
// (hvmDiffEnforceable=false) is covered. The PRE-activation-TIME cells (IsHvm0(header.Time)==false) are not: every
// existing direct apply uses a Time at/after activation. These pin that a pre-activation block is handled by the
// FORMAT/no-op branches, never the difficulty/PoW gate, even with enforce=true && hvmDiffEnforceable=true.
// TestApplyPathPreHvm0HeaderBearingIsFormatReject: a header-bearing BtcAttr block whose timestamp is BEFORE
// activation must reject as ErrInvalidHVMBlockFormat (a permanently-invalid block), NOT ErrInvalidHVMHeaders, and
// must never reach the difficulty/PoW gate — independent of the enforce flags. A reorder running the difficulty gate
// before the format guard would mis-classify (or, if suppressed, silently accept) a pre-activation header batch.
func TestApplyPathPreHvm0HeaderBearingIsFormatReject(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	require.True(t, chain.hvmDiffEnforceable.Load(), "precondition: enforceable boot")

	h := *mineRegtestChild(t, genesis, 1) // a PoW-valid header (so only the format/difficulty path could reject)
	c := h.BlockHash()
	btc, err := types.MakeBtcAttributesDepositedTx(&c, []wire.BlockHeader{h})
	require.NoError(t, err)
	// PRE-activation timestamp.
	blk := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time - 1}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc)}})
	require.False(t, chain.chainConfig.IsHvm0(blk.Time()), "precondition: the block is pre-activation")
	chain.tempHeaders[blk.Hash().String()] = blk.Header()
	chain.tempBlocks[blk.Hash().String()] = blk
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))

	err = chain.applyHvmHeaderConsensusUpdate(blk.Header(), false, true) // enforce=true + enforceable
	require.ErrorIs(t, err, consensus.ErrInvalidHVMBlockFormat, "a pre-activation header-bearing block is a format reject")
	require.NotErrorIs(t, err, consensus.ErrInvalidHVMHeaders, "the difficulty arm must NOT be the one that fires")
	// The difficulty/PoW gate and AddExternalHeaders were skipped: tip + state-id unchanged.
	_, tip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, genesis.BlockHash(), tip.BlockHash(), "no commit: tip stays at genesis")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId, *sid, "no state-id advance on a format reject")
}

// TestApplyPathPreHvm0HeaderlessDoesNotAdvanceStateId: a headerless (no-BtcAttr) block BEFORE activation must
// return nil WITHOUT advancing the upstream-state-id (the IsHvm0(time) guard around SetUpstreamStateId is false),
// whereas the SAME shape at/after activation MUST advance it. A mutant making that SetUpstreamStateId unconditional
// would corrupt the genesis-upstream-id invariant for a pre-activation block and survive every existing test.
func TestApplyPathPreHvm0HeaderlessDoesNotAdvanceStateId(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	chain, _ := newHvmTestChainWithLightTBC(t, btcDiffTestHvm0Time)
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))

	// PRE-activation headerless block: must be a no-op that does NOT advance the state-id.
	pre := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time - 1})
	require.False(t, chain.chainConfig.IsHvm0(pre.Time()))
	chain.tempHeaders[pre.Hash().String()] = pre.Header()
	chain.tempBlocks[pre.Hash().String()] = pre
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(pre.Header(), false, true), "pre-activation headerless block is a clean no-op")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId, *sid, "a pre-activation headerless block must NOT advance the upstream-state-id")

	// Differential: the SAME headerless shape AT activation DOES advance the state-id (the IsHvm0 gate is the diff).
	active := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: btcDiffTestHvm0Time})
	require.True(t, chain.chainConfig.IsHvm0(active.Time()))
	chain.tempHeaders[active.Hash().String()] = active.Header()
	chain.tempBlocks[active.Hash().String()] = active
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(active.Header(), false, true))
	sid, err = chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, active.Hash().Bytes(), sid[:], "an Hvm0-active headerless block MUST advance the upstream-state-id")
}
