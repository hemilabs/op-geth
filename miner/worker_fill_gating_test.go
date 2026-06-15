package miner

import (
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/beacon"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/consensus/misc/eip1559"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

// TestShouldFillFromMempool pins the mempool-fill gating invariant that generateWork's single, consolidated
// fillTransactions call hinges on: a block is filled from the mempool ONLY when it is neither a no-tx block
// nor a block carrying a Bitcoin Attributes Deposited tx. The BtcAttr-true row is the case that was
// previously untested — a block carrying a BtcAttr dep tx must exclude mempool txs. Driving the worker to
// GENERATE a real BtcAttr (so containsBtcAttrDepTx becomes true end-to-end) needs a live vm.TBCFullNode,
// which the codebase treats as out of unit-test scope (see core/blockchain_hvm_btcattr_cache_test.go), so
// the exclusion decision is pinned directly here.
func TestShouldFillFromMempool(t *testing.T) {
	cases := []struct {
		noTxs, containsBtcAttr, want bool
	}{
		{noTxs: false, containsBtcAttr: false, want: true}, // normal block: fill from mempool
		{noTxs: false, containsBtcAttr: true, want: false}, // BtcAttr block: exclude mempool (the invariant)
		{noTxs: true, containsBtcAttr: false, want: false}, // no-tx (derived) block: exclude mempool
		{noTxs: true, containsBtcAttr: true, want: false},  // no-tx AND BtcAttr: exclude
	}
	for _, c := range cases {
		if got := shouldFillFromMempool(c.noTxs, c.containsBtcAttr); got != c.want {
			t.Errorf("shouldFillFromMempool(noTxs=%v, containsBtcAttr=%v) = %v, want %v",
				c.noTxs, c.containsBtcAttr, got, c.want)
		}
	}
}

// TestGenerateWorkMempoolFillGate proves the consolidated fillTransactions in generateWork actually consults
// shouldFillFromMempool, by building the same block both ways and observing the gate flip: with noTxs=true
// the seeded mempool is excluded, with noTxs=false it is filled. This exercises the exact exclusion code
// path that a BtcAttr block also takes (the shouldFillFromMempool gate); the BtcAttr arm is structurally
// identical and only differs in which input flips the predicate to false, but additionally needs a live TBC
// node to drive end-to-end. Together with TestShouldFillFromMempool this closes the fill-consolidation gap.
func TestGenerateWorkMempoolFillGate(t *testing.T) {
	cfg := jovianConfig()
	db := rawdb.NewMemoryDatabase()
	w, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)
	require.False(t, b.chain.IsHvmEnabled(), "harness has no live TBC; hVM must be off so only the noTxs arm gates the fill")

	// Seed the mempool with user txs that WOULD be filled (newTestWorker also preloads a nonce-0 pending tx).
	if errs := b.txPool.Add(genTxs(1, 3), true); len(errs) > 0 {
		for _, err := range errs {
			require.NoError(t, err, "failed adding tx to pool")
		}
	}

	parent := b.chain.CurrentBlock()
	// tx[0] is the Jovian-format L1-attributes deposit (carries the DA scalar); len(txs)==1 (<2) so
	// generateWork enters the BtcAttr-generation branch (skipped here since hVM is off) and then reaches the
	// shared shouldFillFromMempool gate.
	l1Info := types.NewTx(jovianDepositTx(testDAFootprintGasScalar))
	mk := func(noTxs bool) *generateParams {
		return &generateParams{
			parentHash:    parent.Hash(),
			timestamp:     parent.Time + 12,
			withdrawals:   types.Withdrawals{},
			beaconRoot:    new(common.Hash),
			gasLimit:      ptr(uint64(15_000_000)),
			txs:           types.Transactions{l1Info},
			eip1559Params: eip1559.EncodeHolocene1559Params(250, 6),
			minBaseFee:    new(uint64),
			noTxs:         noTxs,
		}
	}
	countUser := func(blk *types.Block) int {
		n := 0
		for _, tx := range blk.Transactions() {
			if !tx.IsDepositTx() && !tx.IsBtcAttributesDepositedTx() && !tx.IsPopPayoutTx() {
				n++
			}
		}
		return n
	}

	// noTxs=true: the gate returns false -> mempool excluded. This is the same exclusion a BtcAttr block gets.
	excl := w.generateWork(mk(true), false)
	require.NoError(t, excl.err, "no-tx block must build")
	require.NotNil(t, excl.block)
	require.Zero(t, countUser(excl.block),
		"noTxs=true must exclude every mempool user tx via the shouldFillFromMempool gate (the same gate BtcAttr blocks use)")

	// noTxs=false: the gate returns true -> mempool filled. Proves the exclusion above is real (the gate flips,
	// it is not a vacuous always-empty block), so a mutant that always-excluded or always-filled fails here.
	fill := w.generateWork(mk(false), false)
	require.NoError(t, fill.err, "normal block must build")
	require.NotNil(t, fill.block)
	require.Positive(t, countUser(fill.block),
		"noTxs=false must fill user txs from the mempool (gate returns true) — confirms the exclusion is meaningful")
}
