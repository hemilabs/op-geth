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
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
)

// emptyPresentBtcAttrBlock builds a block carrying an "empty-but-present" Bitcoin Attributes Deposited tx
// (present, zero headers) claiming canonicalTip, on the given parent/number/time. The empty-present
// apply/unapply paths make no TBC header change (no AddExternalHeaders, hence no full-TBC-node prefetch) —
// they only move the upstream-state-id — which lets this test drive walkHvmHeaderConsensusForward (which
// hardcodes attemptPrefetch=true) without a vm.TBCFullNode.
func emptyPresentBtcAttrBlock(t *testing.T, num int64, time uint64, parent *types.Header, canonicalTip chainhash.Hash) *types.Block {
	t.Helper()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canonicalTip, nil)
	require.NoError(t, err)
	h := &types.Header{Number: big.NewInt(num), Time: time, ParentHash: parent.Hash()}
	return types.NewBlockWithHeader(h).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
}

// TestHvmForwardWalkRollbackUnwindsPredecessors covers the error-recovery loop in
// walkHvmHeaderConsensusForward. It drives a multi-block forward walk that applies two predecessors
// (block1, block2) and then fails on block3 with ErrInvalidHVMHeaders, and asserts the loop rolls the live TBC
// upstream-state-id back exactly to currentHead — i.e. it unwinds the genuinely-applied predecessors
// headers[index-1..1], not the failing block headers[index].
//
// The recovery loop must unapply headers[backIndex] (the applied predecessors, backIndex varying 2 then 1), NOT the
// constant failing block headers[index]. Unapplying the constant index — with the btcAttrDepIsHeaderless guard in
// place — would no-op-unapply block3 twice (rolling the state-id to block3's parent, block2) and leave block1/block2
// applied, so the state-id would end at block2, not currentHead. This test fails deterministically under the
// constant-index form and passes only when the loop walks back the predecessors via backIndex.
//
// Two predecessors (failure at slice index 3) are used so the recovery loop iterates twice with distinct
// backIndex values (2 then 1), exercising the varying-vs-constant index distinction at the core of correct recovery.
// Empty-but-present blocks keep the walk on the no-AddExternalHeaders path so no full TBC node is required;
// header-removal mechanics on unapply are covered by the empty-but-present round-trip tests.
func TestHvmForwardWalkRollbackUnwindsPredecessors(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)

	// canonTip = the lightweight tip (genesis checkpoint). The successful predecessors claim this
	// (it matches the tip, which empty-present blocks never move), so they apply cleanly.
	canonTip := lightTip.BlockHash()

	// A deliberately wrong canonical-tip claim for the failing block: any hash != the live tip. This makes
	// block3's empty-present CanonicalTip check fail -> ErrInvalidHVMHeaders, returned before it advances the
	// state-id (so block3 itself commits no state — why it must not be unwound).
	var wrongTip chainhash.Hash
	for i := range wrongTip {
		wrongTip[i] = 0x42
	}
	require.NotEqual(t, canonTip[:], wrongTip[:])

	// Geometry: pre-activation parent -> currentHead (activation, no BtcAttr) -> block1 -> block2
	// (both empty-present, valid) -> block3 (empty-present, invalid canonical claim).
	preActivation := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	currentHead := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preActivation.Hash()})
	block1 := emptyPresentBtcAttrBlock(t, 12, hvm0Time+1, currentHead.Header(), canonTip)
	block2 := emptyPresentBtcAttrBlock(t, 13, hvm0Time+2, block1.Header(), canonTip)
	block3 := emptyPresentBtcAttrBlock(t, 14, hvm0Time+3, block2.Header(), wrongTip)

	// Seed every block+header into the holding pen: headersBetweenBlocks walks newHead->currentHead
	// via parent headers, and apply/unapply resolve blocks and the descend-target parent header.
	for _, b := range []*types.Block{currentHead, block1, block2, block3} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
	}
	chain.tempHeaders[preActivation.Hash().String()] = preActivation
	chain.tempBlocks[preActivation.Hash().String()] = types.NewBlockWithHeader(preActivation)

	// Establish the starting state the walk assumes: currentHead already applied -> state-id == currentHead.
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(currentHead.Header(), false, true))
	sidStart, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, currentHead.Hash().Bytes(), sidStart[:], "precondition: state-id starts at currentHead")

	_, tipStart, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipStartHash := tipStart.BlockHash()
	require.Equal(t, canonTip[:], tipStartHash[:], "precondition: tip starts at the genesis checkpoint")

	// Drive the forward walk currentHead -> block3. block1/block2 apply (advancing state-id to block2),
	// then block3 fails; the recovery loop must unwind block2 then block1 back to currentHead.
	err = chain.walkHvmHeaderConsensusForward(currentHead.Header(), block3.Header())
	require.Error(t, err, "the walk must surface the invalid block3's error")
	require.ErrorIs(t, err, consensus.ErrInvalidHVMHeaders,
		"block3's wrong canonical-tip claim must fail as ErrInvalidHVMHeaders")

	// The recovery loop must unwind the applied predecessors (block1, block2) and restore the state-id exactly to
	// currentHead. A constant-headers[index] unapply would instead leave it at block2 (predecessors left applied,
	// block3 no-op-unapplied to its parent).
	sidEnd, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, currentHead.Hash().Bytes(), sidEnd[:],
		"error-recovery must unwind the applied predecessors back to currentHead, not the failing block")
	require.NotEqual(t, block2.Hash().Bytes(), sidEnd[:],
		"a state-id left at block2 means the predecessors were not unwound (constant-index unapply)")

	// The lightweight tip never moved (empty-present blocks add no headers); it must still be the checkpoint.
	_, tipEnd, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipEndHash := tipEnd.BlockHash()
	require.Equal(t, canonTip[:], tipEndHash[:], "tip must be unchanged after the rolled-back walk")
}

// TestWalkHvmHeaderConsensusForwardBadGeometry pins the operator-facing "bad geometry" diagnostic emitted by
// walkHvmHeaderConsensusForward when currentHead is at or above newHead (blockchain.go ~3919). This guard is the
// first line of the function — reached before any TBC interaction — so it is trivially corpus-free. The string is a
// stable diagnostic external tooling may match; no test pinned it (existing walkForward tests pass valid geometry).
func TestWalkHvmHeaderConsensusForwardBadGeometry(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	higher := &types.Header{Number: big.NewInt(20), Time: hvm0Time}
	lower := &types.Header{Number: big.NewInt(15), Time: hvm0Time}
	sidBefore, sErr := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, sErr)
	err := chain.walkHvmHeaderConsensusForward(higher, lower)
	require.Error(t, err)
	sidAfter, sErr := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, sErr)
	require.Equal(t, sidBefore[:], sidAfter[:], "the bad-geometry guard returns BEFORE any work; it must not mutate the state-id")
	require.Contains(t, err.Error(), "Cannot walk hVM consensus forewards", "the bad-geometry diagnostic must be emitted")
	require.Contains(t, err.Error(), "bad geometry")

	// Equal height is also bad geometry (the guard is >=, not >).
	require.ErrorContains(t, chain.walkHvmHeaderConsensusForward(lower, lower), "bad geometry",
		"equal-height currentHead/newHead must also be rejected as bad geometry")
}

// TestWalkHvmHeaderConsensusForwardPathNotFound pins the "unable to find a path" diagnostic emitted when
// headersBetweenBlocks cannot connect currentHead to newHead (a missing intermediate header; blockchain.go ~3936).
// Corpus-free: newHead's parent hash resolves to nothing in disk + holding pen, so headersBetweenBlocks fails on the
// first walk-back step.
func TestWalkHvmHeaderConsensusForwardPathNotFound(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	currentHead := &types.Header{Number: big.NewInt(10), Time: hvm0Time}
	// newHead is 2 above currentHead, but its parent (the intermediate at #11) is absent from disk + holding pen.
	newHead := &types.Header{Number: big.NewInt(12), Time: hvm0Time + 2, ParentHash: common.HexToHash("0xdeadbeefdeadbeef")}
	err := chain.walkHvmHeaderConsensusForward(currentHead, newHead)
	require.Error(t, err)
	require.Contains(t, err.Error(), "unable to find a path", "the path-not-found diagnostic must be emitted")
}
