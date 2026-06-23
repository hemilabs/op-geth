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
