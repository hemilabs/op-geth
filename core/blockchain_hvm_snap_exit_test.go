// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Snap-sync EXIT/resumption invariant. The ENTRY gate (updateHvmHeaderConsensus short-circuits while
// isAwaitingHvmSnapSync) is covered, and the latch lifecycle is unit-tested on a bare &BlockChain{}. But no test
// drives updateHvmHeaderConsensus AFTER hvmSnapMarkFinished — the documented behavior (blockchain.go ~4364) that
// "blocks deferred during the window are caught up by the first updateHvmHeaderConsensus after the snap completes
// (it walks the gap)". A mutant that fails to clear the latch, or breaks the gap walk, would silently wedge the
// lightweight TBC view after snap yet pass every current test. Corpus-free: the deferred gap blocks are HEADERLESS
// (empty-present), so the forward walk never reaches the full-node prefetch.

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

func TestHvmSnapExitResumesDeferredGapForwardWalk(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)
	checkpoint := lightTip.BlockHash()

	preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	blockM := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})
	// Deferred gap M+1, M+2, N: headerless empty-present blocks (so walkForward dodges the full-node prefetch).
	blockM1 := emptyPresentBtcAttrBlock(t, 12, hvm0Time+1, blockM.Header(), checkpoint)
	blockM2 := emptyPresentBtcAttrBlock(t, 13, hvm0Time+2, blockM1.Header(), checkpoint)
	blockN := emptyPresentBtcAttrBlock(t, 14, hvm0Time+3, blockM2.Header(), checkpoint)

	chain.tempHeaders[preAct.Hash().String()] = preAct
	chain.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
	for _, b := range []*types.Block{blockM, blockM1, blockM2, blockN} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
		rawdb.WriteBlock(chain.db, b) // findCommonAncestor resolves the gap via bc.GetHeader (rawdb only)
	}

	// Establish state-id = M (the snap-pinned base the lightweight TBC is reconstructed to).
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockM.Header(), false, true))
	sidM, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockM.Hash().Bytes(), sidM[:])

	// ENTER snap-await: a head move to N must short-circuit (deferred), leaving the state-id at M.
	chain.SetAwaitingHvmSnapSync()
	require.True(t, chain.isAwaitingHvmSnapSync())
	require.NoError(t, chain.updateHvmHeaderConsensus(blockN.Header(), false), "while awaiting snap, the head move is a deferred no-op")
	sidAwait, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockM.Hash().Bytes(), sidAwait[:], "the awaiting gate must NOT advance the state-id")

	// EXIT snap: the first updateHvmHeaderConsensus after finish must walk the deferred gap M+1..N forward to N.
	chain.hvmSnapMarkFinished()
	require.False(t, chain.isAwaitingHvmSnapSync())
	require.NoError(t, chain.updateHvmHeaderConsensus(blockN.Header(), false), "after snap finish the deferred gap must be walked forward")
	sidN, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sidN[:], "post-snap resumption must land the state-id on N (gap M+1..N caught up)")
}
