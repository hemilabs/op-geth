// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package vm

// Build-path prefetch decision: vm.TBCBlocksAvailableToHeader is the consensus build/apply path's gate for
// deciding whether the full node already holds every full block needed to index up to a target header, or whether
// blocks must be prefetched first (core/blockchain.go:1969, :3098 feed its result into TBCAttemptBlockRefetch). It was
// only ever reachable with a live indexed full node, so prior tests skipped it (see blockchain_hvm_corrupt_test.go:656
// "that needs a live vm.TBCFullNode"). With the synthetic full node we can drive its three outcomes directly:
//   - every full block present                  -> (true,  nil,            nil,        nil)
//   - headers present but full blocks missing    -> (false, &missingList,   nil,        nil)
//   - a target header the node never saw         -> (false, nil,            &hash,      nil)
//
// (TBCAttemptBlockRefetch itself is NOT covered here: it calls DownloadBlockFromRandomPeers, a P2P operation with no
// peers in this harness, which belongs to live-network testing.)

import (
	"testing"

	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/hemilabs/heminetwork/database"
	"github.com/stretchr/testify/require"
)

func TestSyntheticFullNodeBlocksAvailableToHeader(t *testing.T) {
	setupSyntheticFullNode(t)

	script, _ := regtestP2PKH(t, 0x42)
	const val = int64(50 * 1e8)
	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header

	// Build a 3-block chain h1->h2->h3 over genesis. The index stays at genesis (we never SyncIndexersToHash), so the
	// availability walk runs from the target header all the way back to genesis.
	h1 := mineRegtestBlockWithTxs(t, genesis, []*wire.MsgTx{buildRegtestCoinbase(t, 1, script, val, 31)}, 31_001)
	h2 := mineRegtestBlockWithTxs(t, &h1.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 2, script, val, 32)}, 32_001)
	h3 := mineRegtestBlockWithTxs(t, &h2.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 3, script, val, 33)}, 33_001)
	hashesOf := func(blks ...*wire.MsgBlock) map[chainhash.Hash]bool {
		m := make(map[chainhash.Hash]bool)
		for _, b := range blks {
			m[b.Header.BlockHash()] = true
		}
		return m
	}

	hh1, hh2, hh3 := h1.Header, h2.Header, h3.Header

	// The several not-found paths exercised below must NOT mutate the shared heminetwork database.ErrNotFound sentinel:
	// they must match with errors.Is, never errors.As(err, &database.ErrNotFound) — which would overwrite this global
	// with the specific error instance on every match. Snapshot its value now; assert it is unchanged at the end.
	errNotFoundBefore := database.ErrNotFound.Error()

	// (0) Unknown header: before inserting any headers, the node has never seen h3 -> not-found hash returned.
	avail, missing, missingHash, err := TBCBlocksAvailableToHeader(MainCtx, &hh3)
	require.NoError(t, err)
	require.False(t, avail)
	require.Nil(t, missing)
	require.NotNil(t, missingHash, "an unknown target header must surface its hash as not-found")
	require.Equal(t, hh3.BlockHash(), *missingHash)

	// Insert all three HEADERS but no full blocks yet.
	_, _, _, _, err = TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&hh1, &hh2, &hh3}})
	require.NoError(t, err)

	// (1) Headers known, zero full blocks present -> all three are missing.
	avail, missing, missingHash, err = TBCBlocksAvailableToHeader(MainCtx, &hh3)
	require.NoError(t, err)
	require.False(t, avail, "no full blocks inserted -> not available")
	require.Nil(t, missingHash, "headers exist, so this is a missing-full-block case, not a missing-header case")
	require.NotNil(t, missing)
	require.Len(t, *missing, 3, "all three full blocks are missing")
	got := make(map[chainhash.Hash]bool)
	for _, m := range *missing {
		got[m.BlockHash()] = true
	}
	require.Equal(t, hashesOf(h1, h2, h3), got, "the missing set must be exactly {h1,h2,h3}")

	// (2) Insert only h1's full block -> h2,h3 still missing.
	_, err = TBCFullNode.BlockInsert(MainCtx, h1)
	require.NoError(t, err)
	avail, missing, _, err = TBCBlocksAvailableToHeader(MainCtx, &hh3)
	require.NoError(t, err)
	require.False(t, avail)
	require.NotNil(t, missing)
	got = make(map[chainhash.Hash]bool)
	for _, m := range *missing {
		got[m.BlockHash()] = true
	}
	require.Equal(t, hashesOf(h2, h3), got, "with h1 present, only h2,h3 are missing")

	// (2b) NON-CONTIGUOUS availability: insert the TIP h3 but leave the middle h2 absent (h1,h3 present, h2 missing).
	// The backward walk from h3 must NOT early-terminate on the first available block (the tip h3) — it must keep
	// walking and report ONLY h2 missing. An "available -> stop" mutation in the walk would return avail=true (since
	// h3 is present) and never discover the h2 gap.
	_, err = TBCFullNode.BlockInsert(MainCtx, h3)
	require.NoError(t, err)
	avail, missing, _, err = TBCBlocksAvailableToHeader(MainCtx, &hh3)
	require.NoError(t, err)
	require.False(t, avail, "the middle block h2 is still missing -> not available even though the tip h3 is present")
	require.NotNil(t, missing)
	got = make(map[chainhash.Hash]bool)
	for _, m := range *missing {
		got[m.BlockHash()] = true
	}
	require.Equal(t, hashesOf(h2), got, "exactly h2 missing: the walk continued past the available tip h3 to the gap")

	// (3) Insert the remaining middle block -> everything available.
	_, err = TBCFullNode.BlockInsert(MainCtx, h2)
	require.NoError(t, err)
	avail, missing, missingHash, err = TBCBlocksAvailableToHeader(MainCtx, &hh3)
	require.NoError(t, err)
	require.True(t, avail, "all full blocks present -> available")
	require.Nil(t, missing)
	require.Nil(t, missingHash)

	// (4) A header that is an ancestor of / equal to the indexed view is trivially available. Genesis is the indexed
	// tip; asking for genesis must report available with nothing missing.
	avail, missing, missingHash, err = TBCBlocksAvailableToHeader(MainCtx, genesis)
	require.NoError(t, err)
	require.True(t, avail, "the indexed tip (genesis) is trivially available")
	require.Nil(t, missing)
	require.Nil(t, missingHash)

	// (5) OFF-GENESIS indexed tip + FORKED target: advance the indexers to h2 (non-genesis), then query availability
	// for a fork f2->f3 built on h1. This drives the path where the indexed tip and target diverge ABOVE genesis, so
	// the second FindCommonAncestor must return h1 (not genesis) and the backward walk must terminate at h1 — code
	// that every prior scenario left dead because the index never left genesis.
	require.NoError(t, TBCFullNode.SyncIndexersToHash(MainCtx, h2.Header.BlockHash()), "advance the indexers to h2")
	f2 := mineRegtestBlockWithTxs(t, &h1.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 2, script, val, 41)}, 41_001)
	f3 := mineRegtestBlockWithTxs(t, &f2.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 3, script, val, 42)}, 42_001)
	hf2, hf3 := f2.Header, f3.Header
	_, _, _, _, err = TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&hf2, &hf3}})
	require.NoError(t, err)

	// f2,f3 headers known but blocks absent -> missing == {f2,f3}; the walk stops at the common ancestor h1.
	avail, missing, missingHash, err = TBCBlocksAvailableToHeader(MainCtx, &hf3)
	require.NoError(t, err)
	require.False(t, avail, "the fork's full blocks are absent")
	require.Nil(t, missingHash, "the fork headers exist, so this is a missing-block case")
	require.NotNil(t, missing)
	got = make(map[chainhash.Hash]bool)
	for _, m := range *missing {
		got[m.BlockHash()] = true
	}
	require.Equal(t, hashesOf(f2, f3), got, "only the post-(h1)-ancestor fork blocks are missing (walk terminated at h1)")

	// Insert the fork blocks -> the fork is now fully available from the h2-indexed tip across the h1 fork point.
	_, err = TBCFullNode.BlockInsert(MainCtx, f2)
	require.NoError(t, err)
	_, err = TBCFullNode.BlockInsert(MainCtx, f3)
	require.NoError(t, err)
	avail, missing, missingHash, err = TBCBlocksAvailableToHeader(MainCtx, &hf3)
	require.NoError(t, err)
	require.True(t, avail, "with the fork blocks present, the forked target is available across the non-genesis ancestor")
	require.Nil(t, missing)
	require.Nil(t, missingHash)

	// The shared heminetwork NotFound sentinel must be byte-identical to its initial value (errors.As-mutation guard).
	require.Equal(t, errNotFoundBefore, database.ErrNotFound.Error(),
		"the not-found paths must use errors.Is and must NOT mutate the shared database.ErrNotFound global")
}
