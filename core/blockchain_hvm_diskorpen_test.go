// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// getBlockFromDiskOrHoldingPen / getHeaderFromDiskOrHoldingPen: disk-first (GetBlockByHash/GetHeaderByHash), then the
// tempBlocks/tempHeaders holding pen, nil if absent in both. Dozens of hVM tests USE these helpers but none pins the
// precedence/fallback contract directly; a pen-first reversal (or a dropped pen fallback) would silently change which
// header/block the apply/walk paths read. Corpus-free.

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

func TestGetFromDiskOrHoldingPenPrecedence(t *testing.T) {
	chain, _ := newHvmTestChainWithLightTBC(t, uint64(1000))

	// Disk-only: a block written to rawdb resolves via the disk path.
	onDisk := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(5), Time: 1})
	rawdb.WriteBlock(chain.db, onDisk)
	require.NotNil(t, chain.getBlockFromDiskOrHoldingPen(onDisk.Hash()), "a disk-only block must resolve")
	require.NotNil(t, chain.getHeaderFromDiskOrHoldingPen(onDisk.Hash()), "a disk-only header must resolve")

	// Pen-only: a block only in tempBlocks/tempHeaders resolves via the fallback.
	inPen := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(6), Time: 2})
	chain.tempBlocks[inPen.Hash().String()] = inPen
	chain.tempHeaders[inPen.Hash().String()] = inPen.Header()
	require.NotNil(t, chain.getBlockFromDiskOrHoldingPen(inPen.Hash()), "a holding-pen-only block must resolve")
	require.NotNil(t, chain.getHeaderFromDiskOrHoldingPen(inPen.Hash()), "a holding-pen-only header must resolve")

	// Pen-only source check: the header helper must read tempHeaders, NOT tempBlocks[hash].Header().
	// Store a DIFFERENT header in tempHeaders than the block's own header under the same key.
	inPen2 := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(8), Time: 5})
	differentHdr := &types.Header{Number: big.NewInt(7), Time: 3}
	require.NotEqual(t, inPen2.Header().Hash(), differentHdr.Hash(), "anti-vacuity: pen header must differ from block header")
	chain.tempBlocks[inPen2.Hash().String()] = inPen2
	chain.tempHeaders[inPen2.Hash().String()] = differentHdr
	gotPenHdr := chain.getHeaderFromDiskOrHoldingPen(inPen2.Hash())
	require.NotNil(t, gotPenHdr)
	require.Equal(t, differentHdr.Hash(), gotPenHdr.Hash(), "pen header helper must read tempHeaders, not tempBlocks[hash].Header()")

	// Absent in both -> nil (callers must nil-check).
	require.Nil(t, chain.getBlockFromDiskOrHoldingPen(common.Hash{0xab}), "an absent block must resolve to nil")
	require.Nil(t, chain.getHeaderFromDiskOrHoldingPen(common.Hash{0xab}), "an absent header must resolve to nil")

	// Precedence: DISK wins. Force a mismatched pen entry (a DIFFERENT block stored under onDisk's hash key) and
	// assert the DISK block is returned — a pen-first reversal would return the decoy.
	decoy := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(99), Time: 3})
	require.NotEqual(t, onDisk.Hash(), decoy.Hash(), "anti-vacuity: the decoy must differ from the disk block")
	chain.tempBlocks[onDisk.Hash().String()] = decoy
	got := chain.getBlockFromDiskOrHoldingPen(onDisk.Hash())
	require.NotNil(t, got)
	require.Equal(t, onDisk.Hash(), got.Hash(), "disk must take precedence over the holding pen (kills a pen-first mutant)")

	// Same precedence for the HEADER helper: a decoy header under onDisk's hash key must not shadow the disk header.
	decoyHdr := &types.Header{Number: big.NewInt(98), Time: 4}
	require.NotEqual(t, onDisk.Hash(), decoyHdr.Hash())
	chain.tempHeaders[onDisk.Hash().String()] = decoyHdr
	gotHdr := chain.getHeaderFromDiskOrHoldingPen(onDisk.Hash())
	require.NotNil(t, gotHdr)
	require.Equal(t, onDisk.Hash(), gotHdr.Hash(), "disk must take precedence over the holding pen for headers too")
}
