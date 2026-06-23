// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// The 3-way FORK arm of updateHvmHeaderConsensus and its findCommonAncestor geometry router. Every existing reorg
// test (TestHvmReorgForkConvergesToCompetingBranch) deliberately BYPASSES the dispatcher — it calls
// walkHvmHeaderConsensusBack + a direct applyHvmHeaderConsensusUpdate, because the dispatcher's forward walk forces a
// block-availability prefetch that needs a real FULL TBC node. The revert test drives updateHvmHeaderConsensus but
// only its LINEAR-back arm and explicitly documents findCommonAncestor fork-routing as uncovered. So neither
// findCommonAncestor (blockchain.go ~1649) nor the final fork arm (~4518: walkBack(currentHead,ancestor) then
// walkForward(ancestor,newHead)) is ever exercised by test code; a mutant corrupting the height-equality routing
// would survive the whole suite.
//
// Corpus-free: the competing branch C is HEADERLESS (empty-present BtcAttr). The forward walk's prefetch is gated on
// headersToAdd>0, so a zero-header apply never touches the (absent) full node. findCommonAncestor resolves the
// ancestor via bc.GetHeader (rawdb only, NOT the holding pen), so the ancestor block is written to rawdb.

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

func TestUpdateHvmHeaderConsensusForkArmFindsCommonAncestor(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers into a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	node, genesis := newRegtestChainWithLightTBC(t, hvm0Time)
	ref, _ := newRegtestChainWithLightTBC(t, hvm0Time)
	checkpoint := genesis.BlockHash() // the lightweight TBC genesis-checkpoint tip (no headers applied)

	// Common ancestor A: a no-BtcAttr activation block (parent pre-activation). Applying it sets state-id=A with the
	// BTC tip still at the genesis checkpoint, so both competing siblings build off the same checkpoint.
	preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	blockA := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})

	// Orphan branch B (#12, parent A): header-bearing, so the unwind genuinely UN-applies real BTC headers.
	xHeaders := make([]wire.BlockHeader, 0, 3)
	prev := genesis
	for i := 0; i < 3; i++ {
		h := mineRegtestChild(t, prev, 2000+uint32(i))
		xHeaders = append(xHeaders, *h)
		prev = h
	}
	xTip := xHeaders[len(xHeaders)-1].BlockHash()
	bBtc, err := types.MakeBtcAttributesDepositedTx(&xTip, xHeaders)
	require.NoError(t, err)
	blockB := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: blockA.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(bBtc)}})

	// Competing branch C (#12, parent A, same height as B, distinct body): HEADERLESS, claiming the genesis
	// checkpoint as its canonical tip (the tip the node sits at after the unwind back to A).
	cBtc, err := types.MakeBtcAttributesDepositedTx(&checkpoint, nil)
	require.NoError(t, err)
	blockC := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 2, ParentHash: blockA.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(cBtc)}})
	require.NotEqual(t, blockB.Hash(), blockC.Hash(), "competing siblings must differ")

	seed := func(c *BlockChain) {
		c.tempHeaders[preAct.Hash().String()] = preAct
		c.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
		for _, b := range []*types.Block{blockA, blockB, blockC} {
			c.tempBlocks[b.Hash().String()] = b
			c.tempHeaders[b.Hash().String()] = b.Header()
		}
		// findCommonAncestor reads the ancestor via bc.GetHeader (rawdb only). Persist A to disk so the fork
		// router can resolve it (the holding pen alone would make GetHeader return nil and nil-panic the walk).
		rawdb.WriteBlock(c.db, blockA)
	}
	seed(node)
	seed(ref)

	// REFERENCE: only ever sees A then the competing branch C (linear single-block applies).
	require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockC.Header(), false, true))
	refSid, err := ref.tbcHeaderNode.UpstreamStateId(ref.ctx)
	require.NoError(t, err)
	require.Equal(t, blockC.Hash().Bytes(), refSid[:], "reference converges to C")
	_, refTip, err := ref.tbcHeaderNode.BlockHeaderBest(ref.ctx)
	require.NoError(t, err)

	// NODE under test: apply A then the ORPHAN branch B (state-id=B, tip=xTip).
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockB.Header(), false, true))
	_, orphTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
	require.NoError(t, err)
	require.Equal(t, xTip, orphTip.BlockHash(), "node is on the orphan branch tip before the reorg")

	// THE TARGET: drive the REAL dispatcher. state-id=B, newHead=C, neither is the ancestor A -> the final fork arm
	// runs findCommonAncestor(C,B)=A, then walkBack(B,A) (unwinds the orphan X headers) and walkForward(A,C).
	require.NoError(t, node.updateHvmHeaderConsensus(blockC.Header(), false),
		"the 3-way fork dispatch (findCommonAncestor + walkBack + walkForward) must converge to C")

	// CONVERGENCE with the competing-branch-only reference, and the orphan headers fully unwound.
	nodeSid, err := node.tbcHeaderNode.UpstreamStateId(node.ctx)
	require.NoError(t, err)
	require.Equal(t, refSid[:], nodeSid[:], "post-fork state-id must converge to C (the reference view)")
	require.Equal(t, blockC.Hash().Bytes(), nodeSid[:], "the fork walk must land the state-id exactly on newHead C")
	_, nodeTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
	require.NoError(t, err)
	require.Equal(t, refTip.BlockHash(), nodeTip.BlockHash(), "post-fork tip must converge")
	require.Equal(t, checkpoint, nodeTip.BlockHash(), "headerless C leaves the tip at the genesis checkpoint")
	for _, h := range xHeaders {
		_, _, e := node.tbcHeaderNode.BlockHeaderByHash(node.ctx, h.BlockHash())
		require.Error(t, e, "the orphan-branch header must be fully removed by the fork unwind")
	}
}

// TestUpdateHvmHeaderConsensusForkArmDepthMultiBlock extends the depth-1 fork test to a DEEPER, unequal-depth fork
// so findCommonAncestor's two loops actually iterate: the first walk-down loop (skipped entirely at depth-1 because
// both heads start at the same height) AND the joint walk-back loop iterating more than once. Geometry: ancestor
// A@11; orphan branch B1@12->B2@13->B3@14 (each adds one mined BTC header); competing branch C1@12->C2@13 (both
// HEADERLESS, so the forward walk dodges the full-node prefetch). updateHvmHeaderConsensus(C2) -> findCommonAncestor
// (C2@13,B3@14): first loop walks B3 14->13, joint loop walks 13->12->11 to A. Then walkBack(B3,A) unwinds three
// real header blocks and walkForward(A,C2) applies two headerless blocks. An off-by-one in either loop survives the
// depth-1 test but diverges here. Corpus-free (regtest); intermediates are written to rawdb because findCommonAncestor
// resolves via bc.GetHeader (rawdb only, not the holding pen).
func TestUpdateHvmHeaderConsensusForkArmDepthMultiBlock(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers into a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	node, genesis := newRegtestChainWithLightTBC(t, hvm0Time)
	ref, _ := newRegtestChainWithLightTBC(t, hvm0Time)
	checkpoint := genesis.BlockHash()

	preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	blockA := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})

	// Orphan branch: three header-bearing blocks, each adding one mined BTC header chained off the previous.
	x1 := mineRegtestChild(t, genesis, 3000)
	x2 := mineRegtestChild(t, x1, 3100)
	x3 := mineRegtestChild(t, x2, 3200)
	mkHdrBlock := func(num int64, toff uint64, parent *types.Block, claim *wire.BlockHeader, hdrs []wire.BlockHeader) *types.Block {
		tip := claim.BlockHash()
		btc, err := types.MakeBtcAttributesDepositedTx(&tip, hdrs)
		require.NoError(t, err)
		return types.NewBlockWithHeader(&types.Header{Number: big.NewInt(num), Time: hvm0Time + toff, ParentHash: parent.Hash()}).
			WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc)}})
	}
	blockB1 := mkHdrBlock(12, 1, blockA, x1, []wire.BlockHeader{*x1})
	blockB2 := mkHdrBlock(13, 1, blockB1, x2, []wire.BlockHeader{*x2})
	blockB3 := mkHdrBlock(14, 1, blockB2, x3, []wire.BlockHeader{*x3})

	// Competing branch: two HEADERLESS blocks claiming the genesis checkpoint (the tip after the unwind back to A).
	mkHeaderless := func(num int64, toff uint64, parent *types.Block) *types.Block {
		btc, err := types.MakeBtcAttributesDepositedTx(&checkpoint, nil)
		require.NoError(t, err)
		return types.NewBlockWithHeader(&types.Header{Number: big.NewInt(num), Time: hvm0Time + toff, ParentHash: parent.Hash()}).
			WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc)}})
	}
	blockC1 := mkHeaderless(12, 2, blockA)
	blockC2 := mkHeaderless(13, 2, blockC1)

	all := []*types.Block{blockA, blockB1, blockB2, blockB3, blockC1, blockC2}
	seed := func(c *BlockChain) {
		c.tempHeaders[preAct.Hash().String()] = preAct
		c.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
		for _, b := range all {
			c.tempBlocks[b.Hash().String()] = b
			c.tempHeaders[b.Hash().String()] = b.Header()
			rawdb.WriteBlock(c.db, b) // findCommonAncestor resolves intermediates via bc.GetHeader (rawdb only)
		}
	}
	seed(node)
	seed(ref)

	// Reference: A then the competing branch C1, C2 (linear headerless applies).
	require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockC1.Header(), false, true))
	require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockC2.Header(), false, true))
	refSid, err := ref.tbcHeaderNode.UpstreamStateId(ref.ctx)
	require.NoError(t, err)
	require.Equal(t, blockC2.Hash().Bytes(), refSid[:], "reference converges to C2")

	// Node: A, then the orphan branch B1->B2->B3 (state-id=B3@14, tip=x3).
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockB1.Header(), false, true))
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockB2.Header(), false, true))
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockB3.Header(), false, true))
	_, orphTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
	require.NoError(t, err)
	require.Equal(t, x3.BlockHash(), orphTip.BlockHash(), "node is on the orphan-branch tip x3 before the reorg")

	// THE TARGET: the DEPTH>1 fork dispatch.
	require.NoError(t, node.updateHvmHeaderConsensus(blockC2.Header(), false),
		"the depth>1 fork dispatch must converge to C2")

	nodeSid, err := node.tbcHeaderNode.UpstreamStateId(node.ctx)
	require.NoError(t, err)
	require.Equal(t, refSid[:], nodeSid[:], "depth>1 fork must converge to the competing-branch reference (C2)")
	require.Equal(t, blockC2.Hash().Bytes(), nodeSid[:], "the fork walk must land the state-id on newHead C2")
	_, nodeTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
	require.NoError(t, err)
	require.Equal(t, checkpoint, nodeTip.BlockHash(), "headerless competing branch leaves the tip at the genesis checkpoint")
	for _, h := range []*wire.BlockHeader{x1, x2, x3} {
		_, _, e := node.tbcHeaderNode.BlockHeaderByHash(node.ctx, h.BlockHash())
		require.Error(t, e, "every orphan-branch header must be unwound by the multi-step fork back-walk")
	}
}

// TestUpdateHvmHeaderConsensusSingleApplyBansBadBlock pins the DISPATCH-level single-block-apply ban arm of
// updateHvmHeaderConsensus (~4471): when newHead is a direct child of currentHead and its apply fails with
// ErrInvalidHVMHeaders, the dispatcher reportBlocks it (rawdb.WriteBadBlock). The existing bad-block-routing test
// drives the FORWARD-WALK reportBlock path (via walkHvmHeaderConsensusForward directly); this drives the distinct
// single-apply arm via the dispatcher. Deleting the dispatch-level reportBlock would survive every test that calls
// applyHvmHeaderConsensusUpdate or walkHvmHeaderConsensusForward directly. Corpus-free (headerless wrong-tip block).
func TestUpdateHvmHeaderConsensusSingleApplyBansBadBlock(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)
	var wrongTip chainhash.Hash
	for i := range wrongTip {
		wrongTip[i] = 0x42
	}

	preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	currentHead := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})
	// newHead is a DIRECT CHILD of currentHead, headerless with a WRONG canonical tip -> apply -> ErrInvalidHVMHeaders.
	newHead := emptyPresentBtcAttrBlock(t, 12, hvm0Time+1, currentHead.Header(), wrongTip)

	chain.tempHeaders[preAct.Hash().String()] = preAct
	chain.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
	for _, b := range []*types.Block{currentHead, newHead} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
	}
	// findCommonAncestor resolves currentHead via bc.GetHeader (rawdb only).
	rawdb.WriteBlock(chain.db, currentHead)

	// Establish state-id = currentHead so the dispatcher takes the single-block-apply arm for the direct child.
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(currentHead.Header(), false, true))
	require.Nil(t, rawdb.ReadBadBlock(chain.db, newHead.Hash()), "precondition: newHead is not yet banned")

	err := chain.updateHvmHeaderConsensus(newHead.Header(), false)
	require.ErrorIs(t, err, consensus.ErrInvalidHVMHeaders, "a wrong-tip direct child must be rejected via the single-apply arm")
	require.NotNil(t, rawdb.ReadBadBlock(chain.db, newHead.Hash()),
		"the dispatch-level single-apply arm must reportBlock (ban) the invalid direct-child block")
}
