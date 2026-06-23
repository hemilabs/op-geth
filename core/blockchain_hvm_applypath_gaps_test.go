// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Apply-path + snap/build observe gaps the regtest harness did not yet reach:
//   - the apply path validates the ENTIRE batch and must reject the whole block atomically (no partial prefix
//     commit) when a trailing header is contextually wrong;
//   - the apply-path PoW gate must fail CLOSED to recoverable-corrupt (not silent-accept / not bad-block) on an
//     unknown network;
//   - observeSnapBtcDiff must route an unconnected (incomplete) verdict with contextualRan set;
//   - enforceableBTCBatch must reject on the PoW-first arm (hash above target), and the gate must suppress it
//     when not enforceable;
//   - a PoW-failing header must NOT short-circuit the contextual stage of observeSnapBtcDiff.

import (
	"context"
	"fmt"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/hemilabs/heminetwork/database"
	"github.com/stretchr/testify/require"
)

// notFoundParentLookup resolves exactly one candidate header and returns a genuine (wrapped) database.NotFoundError
// for every other hash — so the batch validator classifies the candidate's absent parent as NOT-FOUND (unconnected),
// distinct from an IO error (which the generic-error fakeBtcLookup would produce -> unavailable).
type notFoundParentLookup struct {
	candidate  *wire.BlockHeader
	candHeight uint64
}

func (l *notFoundParentLookup) BlockHeaderByHash(_ context.Context, h chainhash.Hash) (*wire.BlockHeader, uint64, error) {
	if h == l.candidate.BlockHash() {
		return l.candidate, l.candHeight, nil
	}
	return nil, 0, fmt.Errorf("db block header by hash: %w", database.NotFoundError("block header not found"))
}

// forgePoWFailingChild builds a child of prev with the regtest Bits but a nonce whose hash EXCEEDS the regtest
// target (no real work). The mining oracle (HashToBig/CompactToBig) is independent of the production PoW check.
func forgePoWFailingChild(t *testing.T, prev *wire.BlockHeader, nonceBase uint32) *wire.BlockHeader {
	t.Helper()
	target := blockchain.CompactToBig(regtestPowBits)
	h := &wire.BlockHeader{Version: 4, PrevBlock: prev.BlockHash(), Timestamp: prev.Timestamp.Add(60 * time.Second), Bits: regtestPowBits}
	for i := uint32(0); i < 1<<22; i++ {
		h.Nonce = nonceBase + i
		hash := h.BlockHash()
		if blockchain.HashToBig(&hash).Cmp(target) > 0 {
			return h
		}
	}
	t.Fatal("failed to forge a PoW-failing regtest child within 2^22 nonces")
	return nil
}

// TestHvmApplyPathRejectsWholeBatchOnWrongTrailingHeader: the apply path validates the ENTIRE batch and must
// reject the block atomically when a trailing header is contextually wrong — it must NOT commit the valid leading
// headers and drop only the bad one (the build path truncates; the apply path is all-or-nothing). The tip-unchanged
// + leading-headers-absent oracle is what kills a partial-commit mutant; ErrInvalidHVMHeaders alone would not.
func TestHvmApplyPathRejectsWholeBatchOnWrongTrailingHeader(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)

	h1 := *mineRegtestChild(t, p, 100)
	h2 := *mineRegtestChild(t, &h1, 110)
	h3 := *mineRegtestChildBits(t, &h2, 0x207ffffe, 120) // PoW-valid but contextually-wrong difficulty

	// Precondition: the leading headers h1,h2 pass PoW, so the whole-batch rejection below is caused by the
	// CONTEXTUAL (difficulty) arm on h3 — not a PoW failure on h1/h2 (which would make the not-committed asserts vacuous).
	require.NoError(t, vm.CheckBTCHeaderBatchPoWForNetwork("localnet", []*wire.BlockHeader{&h1, &h2}),
		"precondition: the leading headers must pass PoW so only the contextual arm rejects the batch")

	err := applyForkBtcAttr(t, chain, 11, h3, []wire.BlockHeader{h1, h2, h3}, true)
	require.ErrorIs(t, err, consensus.ErrInvalidHVMHeaders, "a batch with a contextually-wrong trailing header must reject the whole block")

	_, tip, berr := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, berr)
	require.Equal(t, p.BlockHash(), tip.BlockHash(), "no partial commit: the tip must still be the pre-apply seeded tip")
	_, _, e1 := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, h1.BlockHash())
	require.Error(t, e1, "the valid leading header h1 must NOT be committed (whole-batch atomic reject)")
	_, _, e2 := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, h2.BlockHash())
	require.Error(t, e2, "the valid leading header h2 must NOT be committed")
}

// TestHvmApplyPathPoWGateUnknownNetworkIsCorrupt: the apply-path PoW gate must fail CLOSED to recoverable corrupt
// state (never silent-accept, never bad-block) when the network has no chaincfg params — the PoW-gate twin of the
// contextual-validator unavailable->corrupt arm. The only unknown-network coverage is the snap-observe path, which
// has the OPPOSITE (skip-and-proceed) semantics.
func TestHvmApplyPathPoWGateUnknownNetworkIsCorrupt(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	chain.tbcHeaderNodeConfig.Network = "zzz-no-chaincfg-params" // SupportsBTCNetwork == false
	require.True(t, chain.hvmDiffEnforceable.Load(), "precondition: the regtest boot is enforceable, so the gate runs")

	h := *mineRegtestChild(t, genesis, 1) // PoW-valid; the gate fails on the network, not the work
	require.ErrorIs(t, vm.CheckBTCHeaderBatchPoWForNetwork("zzz-no-chaincfg-params", []*wire.BlockHeader{&h}),
		vm.ErrBTCHeaderContextUnavailable, "precondition: the PoW gate yields the skip sentinel for an unknown network")

	err := applyForkBtcAttr(t, chain, 11, h, []wire.BlockHeader{h}, true)
	require.ErrorIs(t, err, consensus.ErrCorruptHVMHeaderOnlyModeState, "an unknown-network PoW gate must fail closed to recoverable corrupt")
	require.NotErrorIs(t, err, consensus.ErrInvalidHVMHeaders, "it must NOT be classified a bad block")

	_, tip, berr := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, berr)
	require.Equal(t, genesis.BlockHash(), tip.BlockHash(), "no commit on the corrupt arm: tip stays at genesis")
}

// TestObserveSnapBtcDiffIncompleteOnUnconnected: an above-floor header whose parent is absent must flow through
// observeSnapBtcDiff to the snapObsIncomplete arm WITH contextualRan set (ErrBTCBatchUnconnected). This is the
// exact result shape the snap + migration callers route to a distinct INCOMPLETE warn; the regtest harness always
// has fully-seeded ancestry, so it never produces this.
func TestObserveSnapBtcDiffIncompleteOnUnconnected(t *testing.T) {
	const genesisOffset = uint64(883092)
	var absentParent chainhash.Hash
	absentParent[0] = 0xde
	hdr := &wire.BlockHeader{Version: 1, PrevBlock: absentParent, Bits: 0x1d00ffff, Timestamp: time.Unix(1_600_000_000, 0), Nonce: 1}
	// The candidate resolves (above the enforce floor) but its parent is genuinely NotFound -> unconnected.
	f := &notFoundParentLookup{candidate: hdr, candHeight: 887040}

	obs := observeSnapBtcDiff(context.Background(), f, "mainnet", genesisOffset, []*wire.BlockHeader{hdr})
	require.True(t, obs.contextualRan, "the above-floor header must be contextually validated")
	require.Equal(t, 1, obs.enforcedCount)
	require.Equal(t, snapObsIncomplete, obs.ctxObservation, "an unconnected above-floor header must classify INCOMPLETE")
	require.ErrorIs(t, obs.ctxErr, vm.ErrBTCBatchUnconnected)
}

// TestEnforceableBTCBatchPoWArm: enforceableBTCBatch checks PoW BEFORE contextual difficulty, so a header whose
// hash misses its target must be rejected on the PoW arm — the build path must never package it. The existing gate
// test only feeds a PoW-VALID header (it asserts PoW passes as a precondition), leaving the PoW-first arm unrun.
func TestEnforceableBTCBatchPoWArm(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)
	forged := forgePoWFailingChild(t, p, 1)
	batch := []*wire.BlockHeader{forged}

	require.Error(t, vm.CheckBTCHeaderBatchPoWForNetwork("localnet", batch), "precondition: the forged header fails PoW")
	require.True(t, chain.hvmDiffEnforceable.Load())
	require.Error(t, chain.enforceableBTCBatch(batch), "enforceable: a hash-above-target header must be rejected on the PoW arm")

	chain.hvmDiffEnforceable.Store(false)
	require.NoError(t, chain.enforceableBTCBatch(batch), "not enforceable: the gate suppresses even the PoW judgement")
}

// TestObserveSnapBtcDiffPoWFailDoesNotShortCircuitContextual: observeSnapBtcDiff runs the PoW check over ALL
// headers but must still run the contextual stage afterward. A base containing BOTH a PoW-failing header AND a
// resolvable above-floor enforceable suffix must set powFailed AND contextualRan — a `return r` after powFailed
// would silence the contextual observation.
func TestObserveSnapBtcDiffPoWFailDoesNotShortCircuitContextual(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	clearance, err := vm.BTCFloorClearanceForNetwork("localnet")
	require.NoError(t, err)
	enforceFloor := btcSnapEnforceFloor(0, clearance)
	total := int(enforceFloor) + 16
	hdrs := buildAndSeedRegtestChain(t, chain, genesis, total, -1, 0) // clean, fully-mined above-floor base

	// Append a PoW-failing child (correct difficulty, hash above target) as the LAST element so firstHeight still
	// resolves on headers[0] and the clean above-floor prefix is still contextually validated.
	forged := forgePoWFailingChild(t, hdrs[len(hdrs)-1], 1)
	allHdrs := append(append([]*wire.BlockHeader{}, hdrs...), forged)

	obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, allHdrs)
	require.True(t, obs.powFailed, "the appended forged header must flag the PoW observation")
	require.True(t, obs.contextualRan, "PoW failure must NOT short-circuit the contextual stage")
}
