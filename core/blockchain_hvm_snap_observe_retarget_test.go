// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// observeSnapBtcDiff (the snap-sync AND migration bulk-load observe-only difficulty check) routed through a REAL
// retarget-boundary computation. The regtest harness that covers observeSnapBtcDiff (TestObserveSnapBtcDiffDispatch)
// is PoWNoRetargeting, so it structurally cannot exercise a retarget-difficulty rejection — the one place the
// migration/snap observe surface computes a 2016-block retarget. This pins that a wrong difficulty AT a real
// mainnet retarget boundary, fed through observeSnapBtcDiff, classifies as the alertable snapObsReject (never a
// skip/incomplete). Corpus-free: synthetic headers spanning only the boundary's 2016 ancestors (no real chaindata).

import (
	"context"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"
)

func TestObserveSnapBtcDiffRejectsRetargetBoundaryViolation(t *testing.T) {
	if testing.Short() {
		t.Skip("builds the boundary's 2016-header ancestry")
	}
	const mainBits = uint32(0x1d00ffff)  // mainnet PowLimitBits; the boundary retarget recomputes a different value
	const genesisOffset = uint64(883092) // mainnet hVM genesis height -> positions the enforce floor (~885119)
	const boundary = uint64(887040)      // 440*2016, the first retarget boundary above the enforce floor
	const startH = boundary - 2016       // 885024: contiguous ancestors for the 2015-hop retarget walk + MTP

	// A contiguous synthetic chain [startH .. boundary] at 10-min spacing. The boundary header carries the
	// inherited mainBits, but a retarget at 887040 recomputes a (harder) expected difficulty -> mismatch.
	f := &fakeBtcLookup{byHash: map[chainhash.Hash]*wire.BlockHeader{}, height: map[chainhash.Hash]uint64{}}
	base := int64(1_600_000_000)
	var prev chainhash.Hash
	var boundaryHdr *wire.BlockHeader
	for h := startH; h <= boundary; h++ {
		hdr := &wire.BlockHeader{
			Version:   1,
			PrevBlock: prev,
			Bits:      mainBits,
			Timestamp: time.Unix(base+int64(h-startH)*600, 0),
			Nonce:     uint32(h),
		}
		hh := hdr.BlockHash()
		f.byHash[hh] = hdr
		f.height[hh] = h
		if h == boundary {
			boundaryHdr = hdr
		}
		prev = hh
	}

	obs := observeSnapBtcDiff(context.Background(), f, "mainnet", genesisOffset, []*wire.BlockHeader{boundaryHdr})

	require.True(t, obs.contextualRan, "the above-floor boundary header must be contextually validated (not deferred)")
	require.Equal(t, 1, obs.enforcedCount, "the boundary header is above the enforce floor -> enforced")
	require.Equal(t, 1, obs.enforcedCount+obs.deferredCount, "every header is either enforced or deferred; a single above-floor header must leave 0 deferred")
	require.Equal(t, snapObsReject, obs.ctxObservation,
		"a wrong difficulty at a real retarget boundary must classify as the alertable reject verdict")
	// Specifically a difficulty rejection (the retarget computation ran), not a timestamp/version or skip verdict.
	var re blockchain.RuleError
	require.ErrorAs(t, obs.ctxErr, &re, "the rejection must be a btcd RuleError")
	require.Equal(t, blockchain.ErrUnexpectedDifficulty, re.ErrorCode,
		"the retarget recomputation must produce ErrUnexpectedDifficulty (proving the boundary math ran)")
}
