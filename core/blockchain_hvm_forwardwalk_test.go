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

// TestHvmForwardWalkRollbackUnwindsPredecessors is the regression for the wrong-index unapply in
// walkHvmHeaderConsensusForward's error-recovery loop. It drives a multi-block forward walk that applies
// two predecessors (block1, block2) and then fails on block3 with ErrInvalidHVMHeaders, and asserts the
// loop rolls the live TBC upstream-state-id back exactly to currentHead — i.e. it unwinds the
// genuinely-applied predecessors headers[index-1..1], not the failing block headers[index].
//
// Pre-fix the loop called unapplyHvmHeaderConsensusUpdate(headers[index]) — the constant failing block —
// on every iteration instead of headers[backIndex]. With the btcAttrDepIsHeaderless guard also in place,
// that loop would no-op-unapply block3 twice (rolling the state-id to block3's parent, block2) and leave
// block1/block2 applied — so the state-id would end at block2, not currentHead. This test therefore fails
// deterministically on the pre-fix (constant index) code and passes only once the loop walks back the
// predecessors via backIndex.
//
// Two predecessors (failure at slice index 3) are used so the recovery loop iterates twice with distinct
// backIndex values (2 then 1), exercising the varying-vs-constant index that is the heart of the fix.
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

	// The wrong-index unapply assertion: the recovery loop unwound the applied predecessors (block1, block2)
	// and the state-id is restored exactly to currentHead. Pre-fix (constant headers[index]) this would be
	// block2 (predecessors left applied, block3 no-op-unapplied to its parent) -> assertion fails.
	sidEnd, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, currentHead.Hash().Bytes(), sidEnd[:],
		"wrong-index unapply fix: error-recovery must unwind the applied predecessors back to currentHead, not the failing block")
	require.NotEqual(t, block2.Hash().Bytes(), sidEnd[:],
		"wrong-index unapply fix: a state-id left at block2 is the pre-fix signature (predecessors not unwound)")

	// The lightweight tip never moved (empty-present blocks add no headers); it must still be the checkpoint.
	_, tipEnd, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipEndHash := tipEnd.BlockHash()
	require.Equal(t, canonTip[:], tipEndHash[:], "tip must be unchanged after the rolled-back walk")
}
