// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// L2 reorg onto a COMPETING branch: the only updateHvmHeaderConsensus arm that composes
// walkHvmHeaderConsensusBack (unwind the orphaned branch) THEN walkHvmHeaderConsensusForward (apply the competing
// branch). Every existing apply/unapply test is single-branch (apply-then-unapply the SAME branch, or back-only, or
// forward-only) — none unwinds one branch's REAL BTC headers and re-applies a DIFFERENT branch's headers. A same-
// branch round-trip cannot catch a cross-branch residue because the re-applied headers are identical to the
// unapplied ones. Oracle: a node that reorgs from the orphaned branch onto the competing branch must reach a view
// (tip hash + height + upstream-state-id) byte-IDENTICAL to a reference node that only ever saw the competing branch.
import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

func TestHvmReorgForkConvergesToCompetingBranch(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers into real lightweight TBC nodes")
	}
	const hvm0Time = uint64(1000)

	for _, tc := range []struct {
		name           string
		orphanN, compN int
	}{
		{"orphan-deeper", 3, 1}, // unwind 3, re-apply 1
		{"competing-deeper", 1, 3},
	} {
		t.Run(tc.name, func(t *testing.T) {
			node, genesis := newRegtestChainWithLightTBC(t, hvm0Time)
			ref, _ := newRegtestChainWithLightTBC(t, hvm0Time)

			mineN := func(n int, nonceBase uint32) ([]wire.BlockHeader, chainhash.Hash) {
				hs := make([]wire.BlockHeader, 0, n)
				prev := genesis
				for i := 0; i < n; i++ {
					h := mineRegtestChild(t, prev, nonceBase+uint32(i))
					hs = append(hs, *h)
					prev = h
				}
				return hs, hs[len(hs)-1].BlockHash()
			}
			// timeOff distinguishes the two competing blocks: block.Hash() is header-only (WithBody does not recompute
			// the TxHash), so same-header competing blocks would otherwise collide.
			branchBlock := func(num int64, timeOff uint64, parent *types.Block, headers []wire.BlockHeader, tip chainhash.Hash) *types.Block {
				btc, err := types.MakeBtcAttributesDepositedTx(&tip, headers)
				require.NoError(t, err)
				return types.NewBlockWithHeader(&types.Header{Number: big.NewInt(num), Time: hvm0Time + timeOff, ParentHash: parent.Hash()}).
					WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc)}})
			}

			// Common ancestor: a no-BtcAttr activation block A (parent pre-activation). Applying it sets state-id=A
			// with the tip still at the genesis checkpoint, so both competing branches build off the same checkpoint.
			preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
			blockA := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})

			xHeaders, xTip := mineN(tc.orphanN, 2000) // orphaned branch X
			yHeaders, yTip := mineN(tc.compN, 9000)   // competing branch Y (distinct nonce base -> distinct hashes)
			require.NotEqual(t, xTip, yTip, "the two branches must have distinct tips")
			blockB := branchBlock(12, 1, blockA, xHeaders, xTip) // orphan branch block (parent A)
			blockC := branchBlock(12, 2, blockA, yHeaders, yTip) // competing branch block (parent A, same height, diff body)
			require.NotEqual(t, blockB.Hash(), blockC.Hash(), "competing blocks must differ")

			seed := func(c *BlockChain) {
				c.tempHeaders[preAct.Hash().String()] = preAct
				c.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
				for _, b := range []*types.Block{blockA, blockB, blockC} {
					c.tempBlocks[b.Hash().String()] = b
					c.tempHeaders[b.Hash().String()] = b.Header()
				}
			}
			seed(node)
			seed(ref)

			// REFERENCE: only ever sees A then the competing branch C.
			require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
			require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockC.Header(), false, true))
			refHeight, refTip, err := ref.tbcHeaderNode.BlockHeaderBest(ref.ctx)
			require.NoError(t, err)
			refSid, err := ref.tbcHeaderNode.UpstreamStateId(ref.ctx)
			require.NoError(t, err)
			require.Equal(t, blockC.Hash().Bytes(), refSid[:])
			refTipHash := refTip.BlockHash()
			require.Equal(t, yTip[:], refTipHash[:])

			// NODE under test: apply A then the ORPHAN branch B, then reorg (unwind B, re-apply C).
			require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
			require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockB.Header(), false, true))
			_, orphTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
			require.NoError(t, err)
			orphTipHash := orphTip.BlockHash()
			require.Equal(t, xTip[:], orphTipHash[:], "node is on the orphan branch tip before the reorg")

			// The fork: unwind the orphan branch back to the common ancestor A (the production walk that genuinely
			// UN-applies committed real BTC headers), then re-apply the competing branch C. (The re-apply uses the
			// direct apply with attemptPrefetch=false rather than walkHvmHeaderConsensusForward, because the forward
			// walk forces a block-availability prefetch that requires a real FULL TBC node — out of corpus-free
			// scope; it is a best-effort fetch optimization that logs-and-continues and does not affect the committed
			// consensus view this test asserts.)
			require.NoError(t, node.walkHvmHeaderConsensusBack(blockB.Header(), blockA.Header()))
			// Intermediate: back at the common ancestor (state-id A, tip at the genesis checkpoint, X removed).
			midSid, err := node.tbcHeaderNode.UpstreamStateId(node.ctx)
			require.NoError(t, err)
			require.Equal(t, blockA.Hash().Bytes(), midSid[:], "after unwind the state-id is the common ancestor A")
			for _, h := range xHeaders {
				_, _, e := node.tbcHeaderNode.BlockHeaderByHash(node.ctx, h.BlockHash())
				require.Error(t, e, "orphan-branch header must be fully removed by the unwind")
			}
			require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockC.Header(), false, true))

			// CONVERGENCE: byte-exact with the reference node that only ever saw the competing branch.
			nodeHeight, nodeTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
			require.NoError(t, err)
			nodeSid, err := node.tbcHeaderNode.UpstreamStateId(node.ctx)
			require.NoError(t, err)
			nodeTipHash := nodeTip.BlockHash()
			require.Equal(t, refTipHash[:], nodeTipHash[:], "post-reorg tip must equal the competing-branch-only reference")
			require.Equal(t, refHeight, nodeHeight, "post-reorg height must converge")
			require.Equal(t, refSid[:], nodeSid[:], "post-reorg upstream-state-id must converge (no orphan residue)")
		})
	}
}
