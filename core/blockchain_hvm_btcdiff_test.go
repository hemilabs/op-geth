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

// Contextual-difficulty integration tests against a real lightweight TBC node, seeded with a contiguous testnet3
// min-difficulty chain past the floor clearance. These exercise the floor-aware validator and the
// consensus apply-path enforcement at above-floor heights — coverage the in-memory fakeHeaderStore unit
// tests cannot reach. The harness uses GenesisHeightOffset = hvmSyntheticGenesisHeight = 3488421
// (min-difficulty), so the floor and retarget boundaries sit at real, non-zero-residue Bitcoin heights.

import (
	"bytes"
	"encoding/hex"
	"math/big"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/stretchr/testify/require"
)

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
