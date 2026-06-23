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

package vm

// Adapter-fidelity differential for (*tbcHeaderCtx).RelativeAncestorCtx. Its load-bearing claim (tbc_difficulty.go
// lines 207-216) is that the retarget window-start MUST be resolved by walking the candidate's OWN PrevBlock chain,
// NOT a height index — because under a same-height fork in the store a height index would return the wrong fork's
// header (which would still pass the height-contiguity check) and corrupt the retarget timespan. Every existing
// retarget test uses a SINGLE linear chain (one header per height), so a height-indexed resolution and an
// ancestry-exact PrevBlock walk are observationally identical. The fakeHeaderStore is hash-keyed, so it can hold TWO
// distinct full windows at the same heights — this is the only test that makes the anchor selection discriminating.

import (
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"
)

// putWindowInto builds a full retarget window (heights 0..2015) into a SHARED store: ts[0]=base,
// ts[2015]=base+actualTimespan (so the boundary recompute sees exactly actualTimespan), monotone between. The
// base offset + nonceOff keep two branches' headers distinct (different hashes) so they coexist at the same heights.
func putWindowInto(store *fakeHeaderStore, bits uint32, actualTimespan, base int64, nonceOff uint32) []*wire.BlockHeader {
	step := actualTimespan / 2016
	hdrs := make([]*wire.BlockHeader, 2016)
	var prev chainhash.Hash
	for i := 0; i < 2016; i++ {
		ts := base + int64(i)*step
		if i == 0 {
			ts = base
		} else if i == 2015 {
			ts = base + actualTimespan
		}
		h := &wire.BlockHeader{Version: 1, PrevBlock: prev, Bits: bits, Timestamp: time.Unix(ts, 0), Nonce: nonceOff + uint32(i)}
		store.put(h, uint64(i))
		hdrs[i] = h
		prev = h.BlockHash()
	}
	return hdrs
}

func TestRelativeAncestorCtxForkAnchorDifferential(t *testing.T) {
	const baseA, baseB = int64(1_600_000_000), int64(1_600_000_001) // +1s so branch B headers never collide with A
	const actualA = int64(1_209_600)                                // == TargetTimespan -> no adjustment -> expected_A == mainBits
	const actualB = int64(100_000)                                  // << MinRetargetTimespan -> clamp -> expected_B harder

	// Both full windows coexist in ONE hash-keyed store; each height 0..2015 holds two distinct headers.
	store := newFakeStore()
	hA := putWindowInto(store, mainBits, actualA, baseA, 0)
	hB := putWindowInto(store, mainBits, actualB, baseB, 2_000_000)
	require.NotEqual(t, hA[0].BlockHash(), hB[0].BlockHash(), "the two branches must not share the height-0 header")

	expA := mainnetRetargetExpected(mainBits, actualA)
	expB := mainnetRetargetExpected(mainBits, actualB)
	require.NotEqual(t, expA, expB, "anti-vacuity: the two branches' boundary difficulties must diverge")

	// Candidate on branch A's parent: the walk must resolve A's height-0 anchor (timespan actualA) -> expA, NOT B's
	// (same height, different timestamp). A height-indexed resolution returning B's height-0 would pass the
	// height-contiguity check yet compute expB, flipping the verdict.
	candA := childOf(hA[2015], expA, hA[2015].Timestamp.Unix()+600)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, candA),
		"on branch A the boundary difficulty must be A's own window (expA); the anchor is ancestry-exact")
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
		childOf(hA[2015], expB, hA[2015].Timestamp.Unix()+600)), blockchain.ErrUnexpectedDifficulty)

	// Symmetric twin on branch B's parent -> expB accepted, expA rejected.
	candB := childOf(hB[2015], expB, hB[2015].Timestamp.Unix()+600)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, candB),
		"on branch B the boundary difficulty must be B's own window (expB)")
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
		childOf(hB[2015], expA, hB[2015].Timestamp.Unix()+600)), blockchain.ErrUnexpectedDifficulty)
}
