// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Rollback RESIDUE fidelity for the apply-path CanonicalTip-mismatch reject arm (RemoveExternalHeaders). Existing
// reject tests assert the tip is restored and the bad headers absent; these pin the residual properties they miss:
// (1) the upstream-state-id is restored BYTE-EXACTLY to the prior value (not the rejected block's hash), and (2) a
// rejected apply leaves ZERO residue so a SUBSEQUENT honest apply lands identically to one on a never-touched store.

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

// TestHvmRejectRestoresStateIdExactly drives the STEADY-STATE reject arm (prev state-id is a real prior BtcAttr
// block A, not genesis) and asserts RemoveExternalHeaders restores the upstream-state-id byte-exactly to A's hash —
// NOT the rejected block B's hash. A mutant passing the rejected block's hash (stateTransitionTargetHash) instead of
// previousStateTransitionHash restores the TIP correctly yet leaves a wrong state-id that trips the next apply's
// parent-mismatch check — invisible to every tip-only reject assertion.
func TestHvmRejectRestoresStateIdExactly(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers into a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)
	mineHeaders := func(prev *wire.BlockHeader, n int, nonceBase uint32) ([]wire.BlockHeader, *wire.BlockHeader) {
		hs := make([]wire.BlockHeader, 0, n)
		p := prev
		for i := 0; i < n; i++ {
			h := mineRegtestChildBits(t, p, regtestPowBits, nonceBase+uint32(i))
			hs = append(hs, *h)
			p = h
		}
		return hs, p
	}

	// Activation block A (2 headers, parent pre-activation) -> steady state with upstream-state-id == A.
	aHeaders, aTip := mineHeaders(genesis, 2, 100)
	aCanon := aTip.BlockHash()
	aBtc, err := types.MakeBtcAttributesDepositedTx(&aCanon, aHeaders)
	require.NoError(t, err)
	aParent := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	aHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: aParent.Hash()}
	blockA := types.NewBlockWithHeader(aHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(aBtc)}})
	chain.tempHeaders[aParent.Hash().String()] = aParent
	chain.tempBlocks[aParent.Hash().String()] = types.NewBlockWithHeader(aParent)
	chain.tempHeaders[blockA.Hash().String()] = blockA.Header()
	chain.tempBlocks[blockA.Hash().String()] = blockA
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))

	_, tipAHeader, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	sidA, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockA.Hash().Bytes(), sidA[:], "precondition: post-A state-id is A")

	// Steady-state block B (parent A) carrying c1->c2 off the A-tip but DISHONESTLY claiming c1 (interior, not the
	// cumulative-work tip c2) -> cbh(c2) != claim(c1) -> reject via RemoveExternalHeaders.
	cHeaders, _ := mineHeaders(tipAHeader, 2, 5000)
	dishonest := cHeaders[0].BlockHash() // claim c1, not c2
	cBtc, err := types.MakeBtcAttributesDepositedTx(&dishonest, cHeaders)
	require.NoError(t, err)
	bHeader := &types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: blockA.Hash()}
	blockB := types.NewBlockWithHeader(bHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(cBtc)}})
	chain.tempHeaders[blockB.Hash().String()] = blockB.Header()
	chain.tempBlocks[blockB.Hash().String()] = blockB
	require.ErrorIs(t, chain.applyHvmHeaderConsensusUpdate(blockB.Header(), false, true), consensus.ErrInvalidHVMHeaders)

	// ORACLE: the state-id is restored byte-exactly to A, NOT left at the rejected block B's hash.
	sidPost, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, sidA[:], sidPost[:], "reject must restore the upstream-state-id to the prior value (A)")
	require.NotEqual(t, blockB.Hash().Bytes(), sidPost[:], "the state-id must NOT be left at the rejected block's own hash")
	_, tipPost, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, tipAHeader.BlockHash(), tipPost.BlockHash(), "tip restored to A")
	for _, c := range cHeaders {
		_, _, e := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, c.BlockHash())
		require.Error(t, e, "rolled-back header must be absent")
	}
}

// TestHvmRejectLeavesZeroResidueForLaterHonestApply is a two-store differential: a clean store does an honest apply;
// a dirty store does a REJECTED apply first, then the SAME honest apply. Both must end byte-identically (tip AND
// upstream-state-id) — proving the rejected apply's RemoveExternalHeaders left zero residue (no half-written header
// that could perturb a later fork-choice, no stale state-id).
func TestHvmRejectLeavesZeroResidueForLaterHonestApply(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: seeds two >floorClearance regtest chains")
	}
	build := func() (*BlockChain, *wire.BlockHeader) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		return chain, seedRegtestAboveFloor(t, chain, genesis)
	}
	honest := func(chain *BlockChain, p *wire.BlockHeader) (a1, a2, a3 wire.BlockHeader) {
		a1 = *mineRegtestChild(t, p, 100)
		a2 = *mineRegtestChild(t, &a1, 110)
		a3 = *mineRegtestChild(t, &a2, 120)
		return
	}

	// CLEAN baseline: honest apply only.
	chainC, pC := build()
	a1, a2, a3 := honest(chainC, pC)
	require.NoError(t, applyForkBtcAttr(t, chainC, 11, a3, []wire.BlockHeader{a1, a2, a3}, true))
	_, cleanTip, err := chainC.tbcHeaderNode.BlockHeaderBest(chainC.ctx)
	require.NoError(t, err)
	cleanSid, err := chainC.tbcHeaderNode.UpstreamStateId(chainC.ctx)
	require.NoError(t, err)

	// DIRTY: a REJECTED apply (dishonest interior claim) THEN the identical honest apply.
	chainD, pD := build()
	require.Equal(t, pC.BlockHash(), pD.BlockHash(), "the deterministic seed yields the same incumbent tip on both chains")
	b1 := *mineRegtestChild(t, pD, 200)
	b2 := *mineRegtestChild(t, &b1, 210)
	require.ErrorIs(t, applyForkBtcAttr(t, chainD, 12, b1, []wire.BlockHeader{b1, b2}, true), consensus.ErrInvalidHVMHeaders,
		"dishonest interior CanonicalTip claim must reject")
	for _, b := range []wire.BlockHeader{b1, b2} { // probe: no header residue before the honest apply
		_, _, e := chainD.tbcHeaderNode.BlockHeaderByHash(chainD.ctx, b.BlockHash())
		require.Error(t, e, "rejected-branch header must be absent after rollback")
	}
	d1, d2, d3 := honest(chainD, pD)
	require.NoError(t, applyForkBtcAttr(t, chainD, 11, d3, []wire.BlockHeader{d1, d2, d3}, true))
	_, dirtyTip, err := chainD.tbcHeaderNode.BlockHeaderBest(chainD.ctx)
	require.NoError(t, err)
	dirtySid, err := chainD.tbcHeaderNode.UpstreamStateId(chainD.ctx)
	require.NoError(t, err)

	require.Equal(t, cleanTip.BlockHash(), dirtyTip.BlockHash(), "a rejected apply must leave NO tip residue for a later honest apply")
	require.Equal(t, cleanSid[:], dirtySid[:], "a rejected apply must leave NO upstream-state-id residue")
}
