package core

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

// TestApplyUnapplyHeaderBearingRoundTrip is a property test for hVM apply/unapply symmetry — the invariant a
// reorg depends on: applying a header-bearing BtcAttr block then unapplying it must leave the lightweight TBC
// view (tip hash, tip height, upstream-state-id) BYTE-IDENTICAL to before, for any header count. The existing
// empty-but-present tests cover the no-header case and a single header-bearing apply; this exercises the
// steady-state unapply (parent is itself an hVM block, so the rollback target is a real prior BtcAttr tip,
// not the activation special-case) across several header counts. A regression where unapply removes too few
// or too many headers, or restores the wrong upstream-state-id, fails the round-trip assertion.
func TestApplyUnapplyHeaderBearingRoundTrip(t *testing.T) {
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

	// Activation block A: 2 mined headers off the genesis checkpoint, parent pre-activation. After this, the
	// lightweight node is in a steady (post-activation) state whose upstream-state-id is A.
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
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true), "apply activation block A")

	// Snapshot the post-A steady state — the round-trip target.
	heightA, tipAHeader, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	sidA, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockA.Hash().Bytes(), sidA[:], "post-A upstream-state-id must be A")
	tipAHash := tipAHeader.BlockHash()

	for _, n := range []int{1, 2, 3, 5} {
		// Steady-state block B (parent A) carrying n real headers off the post-A tip.
		bHeaders, _ := mineHeaders(tipAHeader, n, 1000+uint32(n)*37)
		bTip := bHeaders[len(bHeaders)-1].BlockHash()
		bBtc, err := types.MakeBtcAttributesDepositedTx(&bTip, bHeaders)
		require.NoError(t, err)
		bHeader := &types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: blockA.Hash()}
		blockB := types.NewBlockWithHeader(bHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(bBtc)}})
		chain.tempHeaders[blockB.Hash().String()] = blockB.Header()
		chain.tempBlocks[blockB.Hash().String()] = blockB

		require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockB.Header(), false, true), "apply B with %d headers", n)
		_, tipB, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
		require.NoError(t, err)
		tipBHash := tipB.BlockHash()
		require.Equal(t, bTip[:], tipBHash[:], "apply of B (%d headers) must advance the tip to B's chain tip", n)

		require.NoError(t, chain.unapplyHvmHeaderConsensusUpdate(blockB.Header()), "unapply B with %d headers", n)

		// Round-trip property: post-unapply view must equal the post-A view exactly.
		heightBack, tipBack, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
		require.NoError(t, err)
		sidBack, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		tipBackHash := tipBack.BlockHash()
		require.Equal(t, heightA, heightBack, "unapply of B (%d headers) must restore the tip height", n)
		require.Equal(t, tipAHash[:], tipBackHash[:], "unapply of B (%d headers) must restore the exact tip", n)
		require.Equal(t, sidA[:], sidBack[:], "unapply of B (%d headers) must restore the exact upstream-state-id", n)

		delete(chain.tempHeaders, blockB.Hash().String())
		delete(chain.tempBlocks, blockB.Hash().String())
	}
}

// TestUnapplyHvmHeaderConsensusUpdateOrphanedParentBlockRecoverable pins the BLOCK-store half of the unapply
// orphaned-parent guard. unapplyHvmHeaderConsensusUpdate guards the parent-HEADER lookup (prevBlock==nil), but
// for a header-bearing block it then walks back to the previous BtcAttr tip via the separate BLOCK store
// (getBlockFromDiskOrHoldingPen) and dereferences cursor.Time(). The two stores differ: a parent's header can
// resolve while its full block is absent (a deep reorg/rewind orphaned the body). That cursor.Time() must not
// nil-panic — the function returns the recoverable consensus.ErrCorruptHVMHeaderOnlyModeState sentinel (which
// the walkHvmHeaderConsensusBack caller routes through recovery, not crit). A mutation removing the cursor==nil
// guard panics here; without the guard a header-resolves/block-absent parent crashes the process on reorg.
func TestUnapplyHvmHeaderConsensusUpdateOrphanedParentBlockRecoverable(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)

	mine := func(prev *wire.BlockHeader, n int, nonceBase uint32) ([]wire.BlockHeader, *wire.BlockHeader) {
		hs := make([]wire.BlockHeader, 0, n)
		p := prev
		for i := 0; i < n; i++ {
			h := mineRegtestChildBits(t, p, regtestPowBits, nonceBase+uint32(i))
			hs = append(hs, *h)
			p = h
		}
		return hs, p
	}

	// Activation block A (header-bearing, parent pre-activation), then steady-state block B (parent A).
	aHeaders, aTip := mine(genesis, 2, 100)
	aCanon := aTip.BlockHash()
	aBtc, err := types.MakeBtcAttributesDepositedTx(&aCanon, aHeaders)
	require.NoError(t, err)
	aParent := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	blockA := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: aParent.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(aBtc)}})
	chain.tempHeaders[aParent.Hash().String()] = aParent
	chain.tempBlocks[aParent.Hash().String()] = types.NewBlockWithHeader(aParent)
	chain.tempHeaders[blockA.Hash().String()] = blockA.Header()
	chain.tempBlocks[blockA.Hash().String()] = blockA
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true), "apply activation block A")

	_, tipA, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	bHeaders, _ := mine(tipA, 1, 5000)
	bTip := bHeaders[len(bHeaders)-1].BlockHash()
	bBtc, err := types.MakeBtcAttributesDepositedTx(&bTip, bHeaders)
	require.NoError(t, err)
	blockB := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: blockA.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(bBtc)}})
	chain.tempHeaders[blockB.Hash().String()] = blockB.Header()
	chain.tempBlocks[blockB.Hash().String()] = blockB
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockB.Header(), false, true), "apply steady-state block B")

	// Orphan A's BLOCK but keep its HEADER: the prevBlock (header) guard passes, but the walk-back's
	// getBlockFromDiskOrHoldingPen(A) returns nil → cursor.Time() would nil-panic without the nil-cursor guard.
	delete(chain.tempBlocks, blockA.Hash().String())
	require.NotNil(t, chain.getHeaderFromDiskOrHoldingPen(blockA.Hash()),
		"A's header must still resolve (only the block is orphaned, so the prevBlock guard does not fire first)")

	var got error
	require.NotPanics(t, func() { got = chain.unapplyHvmHeaderConsensusUpdate(blockB.Header()) },
		"an orphaned parent BLOCK on the unapply walk-back must not nil-deref")
	require.ErrorIs(t, got, consensus.ErrCorruptHVMHeaderOnlyModeState,
		"unapply with an unresolvable parent block must return the recoverable corrupt-state sentinel")

	// The recoverable corrupt return must NOT have mutated the consensus view: B stays applied (tip + state-id
	// unchanged) and all of B's headers remain present. Kills a mutant that removes headers or rolls the state-id
	// back BEFORE returning the sentinel (such a side-effect would pass the error-class check above but silently
	// diverge the lightweight TBC view).
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, bTip, tipAfter.BlockHash(), "a corrupt-return unapply must leave the BTC tip at B unchanged")
	sidAfter, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockB.Hash().Bytes(), sidAfter[:], "a corrupt-return unapply must leave the upstream-state-id at B")
	for _, h := range bHeaders {
		_, _, e := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, h.BlockHash())
		require.NoError(t, e, "B's headers must remain present after a corrupt-return unapply")
	}
}
