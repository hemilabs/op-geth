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

	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/core/types"
)

// TestHvmRevertUndoesHeaderBearingBlockAdvance is the consensus-critical regression for the revert path:
// when a block advances the TBC consensus state (upstream-state-id + BTC headers) but is then rejected by
// EVM Process/ValidateState, the revert must roll the lightweight TBC node fully back to the pre-insert EVM
// tip (tbcHeader) — restoring the upstream-state-id and removing every BTC header the rejected block added.
//
// Reproduces the insert sequence the revert path handles, at the lightweight (consensus) seam:
//  1. apply currentHead (activation block) -> state-id = currentHead   (this is "tbcHeader", the EVM tip
//     the TBC represents at insert entry, captured in production via getHeaderModeTBCEVMHeader).
//  2. apply a header-bearing block N -> AddExternalHeaders advances the tip and state-id to N (mirrors the
//     insert's forward updateHvmHeaderConsensus(block) advance).
//  3. "EVM rejects N" -> revert via walkHvmHeaderConsensusBack(N, tbcHeader).
//
// Step 3 is the unwind the revert helper drives: revertHvmStateAfterInvalidBlock calls
// updateHvmHeaderConsensus(tbcHeader, true), which for a linear rejected block (tbcHeader is N's ancestor,
// the common case) dispatches to walkHvmHeaderConsensusBack to remove N's headers and roll the state-id
// back. Two parts of updateHvmHeaderConsensus are not exercised: findCommonAncestor (pure geometry routing,
// and it reads headers via GetHeader from disk — in production it walks persisted canonical headers, not
// this test's holding-pen-only blocks), and the trailing full-node indexer sync
// (updateFullTBCToLightweight, gated by bool=true) which needs a live vm.TBCFullNode — out of scope, the
// same reason related tests use attemptPrefetch=false. Full-node-lag is covered by TestIsHvmFullNodeBehind.
//
// Scope: this locks in the revert unwind, not the wiring. The novel surface is the two
// revertHvmStateAfterInvalidBlock call sites in insertChain's EVM-failure paths (after processor.Process
// and validator.ValidateState, under the isHvmActivated guard); deleting both would leave this green. That
// wiring cannot run in a unit test (needs the full insert path -> a live vm.TBCFullNode, plus
// findCommonAncestor's disk reads); this test guards the behavior the wiring invokes — that the revert
// fully undoes a rejected block's TBC advance (state-id + headers).
//
// The assertion that the added BTC headers are removed (tip restored to the checkpoint), not just the
// state-id rolled back, is what makes this a revert regression rather than a generic state-id check: a
// refactor that left the rejected block's headers in the lightweight leveldb would leave the consensus view
// diverged, and this would catch it.
func TestHvmRevertUndoesHeaderBearingBlockAdvance(t *testing.T) {
	const hvm0Time = uint64(1000)
	// Regtest harness: the apply path enforces PoW, so the header-bearing block's headers must be really
	// mined (regtest PoW is mineable in ~2 nonces). Near-genesis => contextual defers; PoW passes.
	chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)

	// Pre-insert state: currentHead is the activation block (no BtcAttr). Applying it sets the
	// upstream-state-id to currentHead — this is the "tbcHeader" the revert must restore to.
	preActivation := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	currentHead := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preActivation.Hash()})

	// Block N: a header-bearing BtcAttr block built on currentHead, carrying 3 mined contiguous regtest
	// headers chained off the lightweight checkpoint. Near-genesis => the contextual validator defers; the
	// apply-path PoW gate requires real work, so they are really mined (cheap on regtest).
	headers := make([]wire.BlockHeader, 0, 3)
	prev := genesis
	for i := 0; i < 3; i++ {
		h := mineRegtestChild(t, prev, uint32(2000+i)*101+1)
		headers = append(headers, *h)
		prev = h
	}
	newTip := headers[len(headers)-1].BlockHash()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&newTip, headers)
	require.NoError(t, err)
	blockN := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: currentHead.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})

	// Seed the holding pen so the revert walk (updateHvmHeaderConsensus -> findCommonAncestor ->
	// walkHvmHeaderConsensusBack -> unapply) can resolve every block/header it traverses.
	chain.tempHeaders[preActivation.Hash().String()] = preActivation
	chain.tempBlocks[preActivation.Hash().String()] = types.NewBlockWithHeader(preActivation)
	for _, b := range []*types.Block{currentHead, blockN} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
	}

	checkpoint := genesis.BlockHash()

	// Step 1: establish the pre-insert state (tbcHeader == currentHead).
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(currentHead.Header(), false, true))
	sidPre, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, currentHead.Hash().Bytes(), sidPre[:], "pre-insert state-id must be currentHead (tbcHeader)")
	_, tipPre, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipPreHash := tipPre.BlockHash()
	require.Equal(t, checkpoint[:], tipPreHash[:], "pre-insert tip must be the genesis checkpoint")

	// Step 2: forward advance for block N (state-id -> N, tip -> newTip, 3 headers added).
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true))
	sidAdvanced, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sidAdvanced[:], "after forward-apply the state-id must point at block N")
	_, tipAdvanced, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipAdvancedHash := tipAdvanced.BlockHash()
	require.Equal(t, newTip[:], tipAdvancedHash[:], "after forward-apply the tip must be N's claimed canonical tip")

	// Step 3: "EVM rejects N" -> revert to tbcHeader (the unwind the revert helper drives for a linear block).
	require.NoError(t, chain.walkHvmHeaderConsensusBack(blockN.Header(), currentHead.Header()),
		"revert to the pre-insert tip must succeed")

	// ASSERTIONS: both the state-id and the added BTC headers are fully undone.
	sidReverted, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, currentHead.Hash().Bytes(), sidReverted[:],
		"revert must restore the upstream-state-id to the pre-insert tip (not leave it at the rejected block)")
	require.NotEqual(t, blockN.Hash().Bytes(), sidReverted[:],
		"a state-id left at block N means the rejected block's advance was not undone")
	_, tipReverted, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipRevertedHash := tipReverted.BlockHash()
	require.Equal(t, checkpoint[:], tipRevertedHash[:],
		"revert must REMOVE the BTC headers the rejected block added (tip back to the checkpoint)")
	for _, h := range headers {
		_, _, err := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, h.BlockHash())
		require.Error(t, err, "revert must remove header %s from the store", h.BlockHash())
	}
}

// TestHvmRevertFirstHvmBlockNilGuard exercises revertHvmStateAfterInvalidBlock on its tbcHeader==nil branch
// (the first-hVM/activation block case): the pre-state is TBC genesis, which cannot be expressed as an
// EVM-header revert target, so the helper must safely no-op (log + return) and rely on restart recovery —
// not panic and not mutate the consensus state. This branch takes no full-TBC-node path, so it runs
// directly. Guards against a change that dereferences a nil tbcHeader or reverts the activation block in
// place.
func TestHvmRevertFirstHvmBlockNilGuard(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	sidBefore, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)

	block := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time})
	require.NotPanics(t, func() { chain.revertHvmStateAfterInvalidBlock(nil, block) },
		"the first-hVM-block (nil tbcHeader) branch must be a safe no-op, never a nil deref")

	sidAfter, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, sidBefore[:], sidAfter[:], "the nil-tbcHeader branch must not mutate the upstream-state-id")
}
