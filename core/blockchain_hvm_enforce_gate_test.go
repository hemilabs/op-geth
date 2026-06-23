// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/stretchr/testify/require"
)

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
