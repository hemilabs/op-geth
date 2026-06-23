// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package vm

// Reorg / unwind: this covers the indexer unwind path (utxoIndexerUnwind / txIndexerUnwind) — exercised whenever
// Bitcoin reorgs and the hVM view must roll its UTXO/Tx state back to a common ancestor and re-apply the new branch.
// The forward-only synthetic chains in the sibling tests wind the indexers forward and do not exercise this path.
//
// This builds a shared NON-genesis prefix block c1 (coinbase to C), then chain A (c1->a2->a3, coinbases to A) and
// indexes to a3, then a heavier chain B (c1->b2->b3->b4, coinbases to B) that wins the canonical race on cumulative
// work (regtest has PoWNoRetargeting, so c1+3 blocks outweigh c1+2). The common ancestor is therefore c1, NOT genesis,
// which is asserted directly via FindCommonAncestor. The reorg is driven through the PRODUCTION entry point
// vm.TBCIndexToHashHeight (which finds the common ancestor and orchestrates the unwind-to-ancestor + wind-to-target; a
// single raw cross-branch SyncIndexersToHash is rejected as non-linear). It then asserts via the precompiles that
// chain A's UTXOs/txs are gone, chain B's are present, the ANCESTOR c1's UTXO survives (the unwind stopped at c1), and
// the reported tip moved a3 -> b4.

import (
	"encoding/binary"
	"testing"

	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/hemilabs/heminetwork/database/tbcd"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

func TestSyntheticFullNodeReorgUnwind(t *testing.T) {
	setupSyntheticFullNode(t)

	scriptA, addrA := regtestP2PKH(t, 0x42)
	scriptB, addrB := regtestP2PKH(t, 0x33)
	scriptC, addrC := regtestP2PKH(t, 0x55) // funded ONLY in the shared prefix block c1 (the common ancestor)
	const vc = int64(10 * 1e8)
	const va = int64(50 * 1e8)
	const vb = int64(30 * 1e8)

	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header

	balance := func(addr string) uint64 {
		t.Helper()
		out, err := (&btcBalAddr{}).Run([]byte(addr), common.Hash{})
		require.NoError(t, err)
		return binary.BigEndian.Uint64(out)
	}
	tipHeight := func() uint32 {
		t.Helper()
		out, err := (&btcLastHeader{}).Run(nil, common.Hash{})
		require.NoError(t, err)
		return binary.BigEndian.Uint32(out[0:4])
	}
	tipHash := func() []byte {
		t.Helper()
		out, err := (&btcLastHeader{}).Run(nil, common.Hash{})
		require.NoError(t, err)
		return reverseBytes(out[4:36])
	}
	insert := func(blocks ...*wire.MsgBlock) tbcd.InsertType {
		t.Helper()
		hdrs := make([]*wire.BlockHeader, len(blocks))
		for i, b := range blocks {
			h := b.Header
			hdrs[i] = &h
		}
		it, _, _, _, err := TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: hdrs})
		require.NoError(t, err)
		for _, b := range blocks {
			_, err = TBCFullNode.BlockInsert(MainCtx, b)
			require.NoError(t, err)
		}
		return it
	}

	// --- Shared prefix c1 (the NON-genesis common ancestor), then chain A (a2,a3) off c1. Index chain A to a3. ---
	c1 := mineRegtestBlockWithTxs(t, genesis, []*wire.MsgTx{buildRegtestCoinbase(t, 1, scriptC, vc, 5_001)}, 5_011)
	a2 := mineRegtestBlockWithTxs(t, &c1.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 2, scriptA, va, 11_001)}, 11_011)
	a3 := mineRegtestBlockWithTxs(t, &a2.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 3, scriptA, va, 12_001)}, 12_011)
	insert(c1, a2, a3)
	a3Hash := a3.Header.BlockHash()
	require.NoError(t, TBCFullNode.SyncIndexersToHash(MainCtx, a3Hash))

	require.Equal(t, uint64(vc), balance(addrC), "ancestor c1 credits C")
	require.Equal(t, uint64(2*va), balance(addrA), "chain A credits A twice")
	require.Equal(t, uint64(0), balance(addrB), "B has nothing yet")
	require.Equal(t, uint32(3), tipHeight(), "indexed tip is a3 (height 3)")

	// --- Chain B (b2,b3,b4) off the SAME c1. Heavier (c1+3 > c1+2) -> wins canonical. ---
	b2 := mineRegtestBlockWithTxs(t, &c1.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 2, scriptB, vb, 21_001)}, 21_011)
	b3 := mineRegtestBlockWithTxs(t, &b2.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 3, scriptB, vb, 22_001)}, 22_011)
	b4 := mineRegtestBlockWithTxs(t, &b3.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 4, scriptB, vb, 23_001)}, 23_011)
	require.Equal(t, tbcd.ITChainFork, insert(b2, b3, b4), "the heavier chain B (4 blocks > 3) must win the canonical race")
	b4Hash := b4.Header.BlockHash()

	// The canonical HEADER tip is now b4, but the indexers are still at a3. btcLastHeader must report the INDEXED tip
	// (a3), NOT the header-best tip (b4) — pinning that its height/hash come from the UTXO index, not BlockHeaderBest.
	require.Equal(t, uint32(3), tipHeight(), "btcLastHeader reports the indexed tip height (a3=3), not header-best (b4=4)")
	require.Equal(t, a3Hash[:], tipHash(), "btcLastHeader reports the indexed tip hash (a3), not header-best (b4)")

	// Pin the marquee precondition DIRECTLY: the common ancestor of a3 and b4 is the NON-genesis prefix c1 (height 1),
	// with isFork=true. The post-reorg balance asserts alone cannot prove this — c1's coinbase is re-applied on the
	// wind-forward regardless of how deep the unwind went, so an unwind-to-genesis regression yields identical final
	// balances. This assertion is what actually makes "the unwind stopped at c1, not genesis" falsifiable.
	anc, _, _, isFork, err := FindCommonAncestor(&tbc.HashHeight{Hash: a3Hash, Height: 3}, &tbc.HashHeight{Hash: b4Hash, Height: 4})
	require.NoError(t, err)
	require.True(t, isFork, "a3 and b4 are on different branches -> isFork")
	require.Equal(t, c1.Header.BlockHash(), anc.BlockHash(), "the common ancestor must be the non-genesis prefix c1")
	require.NotEqual(t, genesis.BlockHash(), anc.BlockHash(), "the common ancestor must NOT be genesis")

	// FindCommonAncestor must order the cursors by the FETCHED header heights, NOT the caller-supplied Height. Pass
	// deliberately INVERTED supplied heights (b4 tagged 0, a3 tagged 4) and assert it STILL finds c1 with no spurious
	// missing-header. If it ordered the cursors by the caller-supplied Height instead, it would mis-assign higher/lower
	// and the both-cursor walk-back would run off the bottom of the chain.
	ancBad, _, missBad, _, err := FindCommonAncestor(&tbc.HashHeight{Hash: b4Hash, Height: 0}, &tbc.HashHeight{Hash: a3Hash, Height: 4})
	require.NoError(t, err, "an inconsistent (hash,height) input must not error")
	require.Nil(t, missBad, "an inconsistent (hash,height) input must not spuriously report a missing header")
	require.NotNil(t, ancBad)
	require.Equal(t, c1.Header.BlockHash(), ancBad.BlockHash(), "FindCommonAncestor orders by fetched heights -> still c1 despite inverted supplied heights")

	// A single cross-branch sync is rejected as non-linear (the fork can't be walked in one direction)...
	require.ErrorIs(t, TBCFullNode.SyncIndexersToHash(MainCtx, b4Hash), tbc.ErrNotLinear,
		"a direct a3->b4 sync crosses a fork and must be rejected as non-linear")

	// ...so drive the reorg through the PRODUCTION entry point, which finds the common ancestor (c1, NOT genesis) and
	// orchestrates the unwind-to-ancestor + wind-to-target itself.
	require.NoError(t, TBCIndexToHashHeight(&tbc.HashHeight{Hash: b4Hash, Height: 4}), "production reorg to b4 over the c1 fork")

	// --- Post-reorg: chain A gone, chain B present, tip at b4, and crucially the ANCESTOR block c1's UTXO SURVIVES
	//     (the unwind stopped at c1, not at genesis). ---
	require.Equal(t, uint64(0), balance(addrA), "chain A's coinbases are unwound")
	require.Equal(t, uint64(3*vb), balance(addrB), "all three chain B coinbases are credited to B")
	require.Equal(t, uint64(vc), balance(addrC), "the common-ancestor block c1 stays indexed: C's balance is unchanged across the reorg")
	require.Equal(t, uint32(4), tipHeight(), "indexed tip is now b4 (height 4)")
	require.Equal(t, b4Hash[:], tipHash(), "indexed tip hash is now b4")

	// The reorg must unwind+rewind the TX index too (not just the UTXO index, which the balances above cover): a
	// chain-B coinbase now resolves through the tx index to its block, while a chain-A coinbase (a3) is GONE from the
	// tx index (TxById not-found -> nil). This is what exercises txIndexerUnwind/Wind, distinct from the UTXO path.
	outB2, err := (&btcTxByTxid{}).Run(append(reversedHash(b2.Transactions[0].TxHash()), 0x40, 0x00, 0x00, 0x00), common.Hash{})
	require.NoError(t, err)
	b2Hash := b2.Header.BlockHash()
	require.Equal(t, b2Hash[:], reverseBytes(outB2), "chain B tx resolves to its block post-reorg (tx index rewound)")
	outA3, err := (&btcTxByTxid{}).Run(append(reversedHash(a3.Transactions[0].TxHash()), 0x40, 0x00, 0x00, 0x00), common.Hash{})
	require.NoError(t, err)
	require.Nil(t, outA3, "chain A tx is gone from the tx index post-reorg (tx index unwound)")

	// The common-ancestor c1's coinbase must SURVIVE in the tx index across the reorg (txIndexerUnwind stopped at c1) —
	// the tx-index twin of the addrC UTXO-balance ancestor check above.
	outC, err := (&btcTxByTxid{}).Run(append(reversedHash(c1.Transactions[0].TxHash()), 0x40, 0x00, 0x00, 0x00), common.Hash{})
	require.NoError(t, err)
	c1Hash := c1.Header.BlockHash()
	require.Equal(t, c1Hash[:], reverseBytes(outC), "ancestor c1's coinbase stays in the tx index post-reorg")
}
