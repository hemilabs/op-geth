// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Cross-path DIFFERENTIAL coverage: the sequencer BUILD path (longestEnforceableBTCHeaderPrefix +
// bc.enforceableBTCBatch, which TRUNCATES to the honest prefix) and the consensus APPLY path
// (applyHvmHeaderConsensusUpdate, which REJECTS the whole block) must AGREE on the same crafted batch against the
// SAME seeded node — the closure that justifies both paths existing. Each path is also tested in isolation on its own
// chain elsewhere; these feed ONE batch to BOTH and assert: apply rejects the full batch (no partial commit) AND
// apply accepts-and-commits exactly the build path's truncated prefix.

import (
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/stretchr/testify/require"
)

// TestHvmBuildPrefixIsExactlyWhatApplyCommits: build truncates a mid-batch contextually-wrong header to the honest
// prefix; the apply path rejects the full batch atomically (tip unchanged) and then accepts+commits exactly that
// prefix. A drift between the two enforcement points (floor clearance, PoW-vs-context order, acceptable-verdict set)
// would make build truncate to a length apply rejects (sequencer stall) or keep a header apply rejects.
func TestHvmBuildPrefixIsExactlyWhatApplyCommits(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)
	pHeight, _, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)

	h1 := *mineRegtestChild(t, p, 100)
	h2 := *mineRegtestChild(t, &h1, 110)
	h3 := *mineRegtestChildBits(t, &h2, 0x207ffffe, 120) // PoW-valid, contextually-wrong difficulty
	h4 := *mineRegtestChild(t, &h3, 130)

	// BUILD: the real production classifier (with its PoW arm) truncates before the bad header -> prefix [h1,h2].
	prefix, skip, err := longestEnforceableBTCHeaderPrefix([]*wire.BlockHeader{&h1, &h2, &h3, &h4}, chain.enforceableBTCBatch)
	require.NoError(t, err)
	require.False(t, skip)
	require.Len(t, prefix, 2, "build must truncate before the contextually-wrong h3")
	require.Equal(t, h2.BlockHash(), prefix[1].BlockHash(), "the build prefix ends at h2")

	// APPLY the FULL batch: atomic reject, no partial commit (tip still p).
	require.ErrorIs(t, applyForkBtcAttr(t, chain, 11, h4, []wire.BlockHeader{h1, h2, h3, h4}, true), consensus.ErrInvalidHVMHeaders)
	hReject, tip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, p.BlockHash(), tip.BlockHash(), "apply must NOT partially commit the honest prefix")
	require.Equal(t, pHeight, hReject, "an atomic reject must not advance the tip HEIGHT either")

	// APPLY the build's truncated prefix on the SAME node: accepted and committed (tip -> h2). This closes the
	// round-trip — the prefix the sequencer would package is exactly what every validator's apply path commits.
	require.NoError(t, applyForkBtcAttr(t, chain, 12, h2, []wire.BlockHeader{h1, h2}, true),
		"apply must ACCEPT exactly the build path's truncated prefix")
	h2Height, tip2, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, h2.BlockHash(), tip2.BlockHash(), "apply must commit the build prefix to its tip h2")
	require.Equal(t, pHeight+2, h2Height, "committing the 2-header prefix must advance the tip height by exactly 2")
}

// TestHvmBuildApplyAgreeOnMixedFaultBoundary: a batch with BOTH a contextual fault and a PoW fault at different
// indices. The build path converges on the FIRST fault of either kind; the apply path rejects the whole block.
// Pins that the two gates (PoW-then-context in both paths) pick the same first-bad boundary regardless of which
// fault class comes first.
func TestHvmBuildApplyAgreeOnMixedFaultBoundary(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	for _, tc := range []struct {
		name    string
		mkBatch func(t *testing.T, p *wire.BlockHeader) []wire.BlockHeader
	}{
		{
			// contextual fault at idx1, PoW fault at idx3 -> first fault is the contextual one -> prefix len 1.
			name: "ctx-before-pow",
			mkBatch: func(t *testing.T, p *wire.BlockHeader) []wire.BlockHeader {
				h1 := *mineRegtestChild(t, p, 100)
				h2 := *mineRegtestChildBits(t, &h1, 0x207ffffe, 110) // ctx-wrong
				h3 := *mineRegtestChild(t, &h2, 120)
				h4 := *forgePoWFailingChild(t, &h3, 1) // PoW-bad
				return []wire.BlockHeader{h1, h2, h3, h4}
			},
		},
		{
			// PoW fault at idx1, contextual fault at idx3 -> first fault is the PoW one -> prefix len 1.
			name: "pow-before-ctx",
			mkBatch: func(t *testing.T, p *wire.BlockHeader) []wire.BlockHeader {
				h1 := *mineRegtestChild(t, p, 100)
				h2 := *forgePoWFailingChild(t, &h1, 1) // PoW-bad
				h3 := *mineRegtestChild(t, &h2, 120)
				h4 := *mineRegtestChildBits(t, &h3, 0x207ffffe, 130) // ctx-wrong
				return []wire.BlockHeader{h1, h2, h3, h4}
			},
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
			p := seedRegtestAboveFloor(t, chain, genesis)
			batch := tc.mkBatch(t, p)
			ptrs := make([]*wire.BlockHeader, len(batch))
			for i := range batch {
				ptrs[i] = &batch[i]
			}

			prefix, skip, err := longestEnforceableBTCHeaderPrefix(ptrs, chain.enforceableBTCBatch)
			require.NoError(t, err)
			require.False(t, skip)
			require.Len(t, prefix, 1, "build converges on the FIRST fault of either kind (index 1)")

			require.ErrorIs(t, applyForkBtcAttr(t, chain, 11, batch[len(batch)-1], batch, true), consensus.ErrInvalidHVMHeaders,
				"apply rejects the whole mixed-fault batch")
			_, tip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
			require.NoError(t, err)
			require.Equal(t, p.BlockHash(), tip.BlockHash(), "no partial commit on a mixed-fault batch")

			// The build prefix {h1} re-applies cleanly on the same node.
			require.NoError(t, applyForkBtcAttr(t, chain, 12, batch[0], []wire.BlockHeader{batch[0]}, true))
			_, tip2, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
			require.NoError(t, err)
			require.Equal(t, batch[0].BlockHash(), tip2.BlockHash())
		})
	}
}
