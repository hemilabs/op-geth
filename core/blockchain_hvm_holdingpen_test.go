package core

import (
	"testing"

	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

// TestInsertChainEvictsHoldingPenButKeepsDiskFallback is the regression test from the
// holding-pen-eviction safety review. It drives real InsertChain across multiple calls on a
// production-wired (hVM-enabled) BlockChain and asserts the two load-bearing properties of the fix in
// insertChain (core/blockchain.go — the `defer { clear(bc.tempBlocks); clear(bc.tempHeaders) }`):
//
//	(1) Leak fixed: tempBlocks/tempHeaders are emptied after every insertChain return. Pre-fix these maps
//	    grew unbounded for the node's lifetime (a *types.Block + *types.Header per distinct hash ever
//	    imported, including every block during initial sync) -> heap exhaustion / OOM. The per-block store
//	    at the top of the insertChain loop is hVM-independent, so plain blocks exercise the pen write + the
//	    new clear exactly as BtcAttr-bearing blocks do.
//
//	(2) Disk fallback preserved: a block imported in an earlier InsertChain call (whose pen entry was
//	    therefore already cleared on that call's return) remains resolvable via
//	    getBlockFromDiskOrHoldingPen / getHeaderFromDiskOrHoldingPen — the disk-first accessors the hVM
//	    consensus-update machinery (updateHvmHeaderConsensus and its apply/unapply/walk helpers) uses to
//	    walk ancestry. Guards the cross-call dependency: a change that widened the clear to drop a
//	    not-yet-flushed entry, or regressed the writeBlockWithState-before-updateHvmHeaderConsensus ordering
//	    (invariant I4, so a block were not durably on disk at return), would make these accessors return nil.
//
// hVM activation is set far in the future so the generated plain blocks import without a seeded Bitcoin
// view; the pen write + clear and the accessors are hVM-independent, so the fix is still exercised end to
// end on a real, production-wired chain.
func TestInsertChainEvictsHoldingPenButKeepsDiskFallback(t *testing.T) {
	const farFutureHvm0 = uint64(1) << 62 // no generated block reaches hVM activation
	chain, _ := newRegtestChainWithLightTBC(t, farFutureHvm0)

	const total = 8
	parent := chain.GetBlockByHash(chain.CurrentBlock().Hash()) // genesis
	require.NotNil(t, parent, "genesis must be present")
	blocks, _ := GenerateChain(chain.chainConfig, parent, ethash.NewFaker(), chain.db, total, func(i int, b *BlockGen) {})
	require.Len(t, blocks, total)

	penEmpty := func(label string) {
		require.Lenf(t, chain.tempBlocks, 0, "tempBlocks must be empty after insertChain (%s) — the eviction fix", label)
		require.Lenf(t, chain.tempHeaders, 0, "tempHeaders must be empty after insertChain (%s) — the eviction fix", label)
	}
	resolvableFromDisk := func(blks []*types.Block, label string) {
		for _, blk := range blks {
			h := blk.Hash()
			// The pen is empty here, so these must resolve from disk — the disk-first path the hVM consensus
			// ancestry walk depends on after the pen has been evicted.
			require.NotNilf(t, chain.getBlockFromDiskOrHoldingPen(h), "%s: block #%d must resolve from disk after pen eviction", label, blk.NumberU64())
			require.NotNilf(t, chain.getHeaderFromDiskOrHoldingPen(h), "%s: header #%d must resolve from disk after pen eviction", label, blk.NumberU64())
			require.NotNilf(t, chain.GetBlockByHash(h), "%s: block #%d must be durably on disk", label, blk.NumberU64())
		}
	}

	// Call #1 — import the first half in one InsertChain call.
	n, err := chain.InsertChain(blocks[:total/2])
	require.NoError(t, err, "first InsertChain call")
	require.Equal(t, total/2, n)
	penEmpty("after call #1")
	resolvableFromDisk(blocks[:total/2], "after call #1")

	// Call #2 — import the second half in a separate InsertChain call. The first half's pen entries were
	// already evicted when call #1 returned, so the cross-call lookups below are served from disk.
	n, err = chain.InsertChain(blocks[total/2:])
	require.NoError(t, err, "second InsertChain call")
	require.Equal(t, total-total/2, n)
	penEmpty("after call #2")
	// All blocks — including the first half whose pen entries were cleared after call #1 — must still
	// resolve via the hVM accessors (from disk). The cross-call dependency the fix must preserve.
	resolvableFromDisk(blocks, "after call #2 (cross-call)")
	require.Equal(t, blocks[total-1].Hash(), chain.CurrentBlock().Hash(), "the full chain must be canonical")
}
