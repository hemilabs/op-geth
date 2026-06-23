// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Operator-facing diagnostics on the walkHvmHeaderConsensusBack entry/loop guards. Both return the bare sentinel
// consensus.ErrBadTraversalGeometry (whose .Error() is "bad traversal geometry", NOT the diagnostic string), so the
// descriptive message lives only in log.Error — pinned here via log capture, alongside the sentinel. Existing walkBack
// callers (reorg_fork, revert) pass only valid geometry, so neither guard was covered.

import (
	"bytes"
	"log/slog"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/stretchr/testify/require"
)

func TestWalkHvmHeaderConsensusBackBadGeometry(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)
	lower := &types.Header{Number: big.NewInt(15), Time: hvm0Time}
	higher := &types.Header{Number: big.NewInt(20), Time: hvm0Time}

	var buf bytes.Buffer
	prev := log.Root()
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(&buf, slog.LevelDebug, false)))
	err := chain.walkHvmHeaderConsensusBack(lower, higher) // currentHead(15) <= newHead(20) -> bad geometry
	log.SetDefault(prev)

	require.ErrorIs(t, err, consensus.ErrBadTraversalGeometry, "walking back to a higher target is bad geometry")
	require.Contains(t, buf.String(), "Cannot walk hVM consensus backwards", "the backwards bad-geometry diagnostic must be logged")
	require.Contains(t, buf.String(), "bad geometry")
	// Equal height is also bad geometry (the guard is <=).
	require.ErrorIs(t, chain.walkHvmHeaderConsensusBack(lower, lower), consensus.ErrBadTraversalGeometry,
		"equal-height currentHead/newHead is also bad geometry")
}

func TestWalkHvmHeaderConsensusBackBadAncestor(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)
	checkpoint := lightTip.BlockHash()

	preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	blockA := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})
	// currentHead: a headerless empty-present block @12 whose real parent is blockA @11 (so its unwind is corpus-free).
	currentHead := emptyPresentBtcAttrBlock(t, 12, hvm0Time+1, blockA.Header(), checkpoint)
	chain.tempHeaders[preAct.Hash().String()] = preAct
	chain.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
	for _, b := range []*types.Block{blockA, currentHead} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
	}
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(currentHead.Header(), false, true))

	// A WRONG ancestor at height 11, distinct from blockA: walking back from currentHead@12 unapplies it, reaches
	// blockA@11 (currentHead's real parent) whose height collides with wrongAncestor@11 but whose hash differs ->
	// the "impossible" broken-ancestry branch fires (bad ancestor), not a real unwind to a wrong target.
	wrongAncestor := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: common.HexToHash("0xfeedface")}
	require.NotEqual(t, blockA.Hash(), wrongAncestor.Hash(), "anti-vacuity: the wrong ancestor must differ from the real one")

	var buf bytes.Buffer
	prev := log.Root()
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(&buf, slog.LevelDebug, false)))
	err := chain.walkHvmHeaderConsensusBack(currentHead.Header(), wrongAncestor)
	log.SetDefault(prev)

	require.ErrorIs(t, err, consensus.ErrBadTraversalGeometry, "a height-collision with a hash mismatch is a broken ancestry (bad traversal geometry)")
	require.Contains(t, buf.String(), "was expecting", "the bad-ancestor diagnostic must be logged")
}
