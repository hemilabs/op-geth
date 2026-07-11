// Copyright 2026 The go-ethereum Authors
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

package miner

import (
	"crypto/ecdsa"
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/beacon"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/consensus/misc/eip1559"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/tracing"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/params"
	"github.com/holiman/uint256"
	"github.com/stretchr/testify/require"
)

// TestDAFootprintForceIncludedPopPayoutTx is the end-to-end build-vs-import test for the Jovian
// DA-footprint seam: it builds a post-Jovian block force-including a PoP payout (0x7D) alongside mempool
// txs, then re-imports it. The miner accumulates header.BlobGasUsed only over mempool txs, so the 0x7D
// contributes nothing at build; import's CalcDAFootprint must skip it too, else the recomputed footprint
// exceeds the builder's and every node rejects the block (a liveness stall). Before the fix (deposits-only
// skip) InsertChain fails with "invalid DA footprint in blobGasUsed field".
func TestDAFootprintForceIncludedPopPayoutTx(t *testing.T) {
	cfg := jovianConfig()
	db := rawdb.NewMemoryDatabase()
	w, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)

	// Mempool txs (nonce 1+) with a real DA footprint, so BlobGasUsed is non-zero and build==import is
	// genuinely exercised (not a trivial 0==0).
	const numMempoolTxs = 3
	mempoolTxs := genTxs(1, numMempoolTxs)
	if errs := b.txPool.Add(mempoolTxs, true); len(errs) > 0 {
		for _, err := range errs {
			require.NoError(t, err, "failed adding tx to pool")
		}
	}

	parent := b.chain.CurrentBlock()
	ts := parent.Time + 12

	// Force-include the L1-attributes deposit (tx[0], carrying the DA scalar) and a PoP payout (0x7D).
	popTo := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := types.NewTx(&types.PopPayoutTx{To: &popTo, Gas: 50000, Data: []byte("popPayout")})

	genParams := &generateParams{
		parentHash:    parent.Hash(),
		timestamp:     ts,
		withdrawals:   types.Withdrawals{},
		beaconRoot:    new(common.Hash),
		gasLimit:      ptr(uint64(1e6)),
		txs:           types.Transactions{types.NewTx(jovianDepositTx(testDAFootprintGasScalar)), popTx},
		eip1559Params: eip1559.EncodeHolocene1559Params(250, 6),
		minBaseFee:    new(uint64),
	}

	r := w.generateWork(genParams, false)
	require.NoError(t, r.err, "block generation failed")
	require.NotNil(t, r.block, "no block generated")
	block := r.block

	// The force-included PoP payout and the mempool txs must be in the built block.
	var sawPop bool
	var nUser int
	for _, tx := range block.Transactions() {
		switch {
		case tx.IsPopPayoutTx():
			sawPop = true
		case !tx.IsDepositTx():
			nUser++
		}
	}
	require.True(t, sawPop, "the force-included PoP payout tx must be present in the block")
	// newTestWorker preloads one nonce-0 pending tx, so the block carries our numMempoolTxs plus it.
	require.GreaterOrEqual(t, nUser, numMempoolTxs, "the mempool txs must be included alongside the system tx")

	// Builder's header.BlobGasUsed (accumulated only over mempool txs) must equal the footprint
	// recomputed over the full tx set on import: the 0x7D contributes 0 on both sides.
	require.NotNil(t, block.Header().BlobGasUsed)
	recomputed, err := types.CalcDAFootprint(block.Transactions())
	require.NoError(t, err)
	require.Positive(t, recomputed, "mempool txs must contribute a non-zero footprint")
	require.Equal(t, *block.Header().BlobGasUsed, recomputed,
		"builder BlobGasUsed must equal CalcDAFootprint over the full block (the 0x7D is excluded on both sides)")

	// Decisive check: the self-built block must import (build==import); a mismatch here is the stall.
	_, err = b.chain.InsertChain(types.Blocks{block})
	require.NoError(t, err, "self-built block must import (build==import); a mismatch here is the bug")
}

// TestDAFootprintWrongBlobGasUsedRejectedOnImport is the negative counterpart to the build==import tests:
// it builds a valid post-Jovian block, then imports a copy whose header.BlobGasUsed is corrupted to a value
// != CalcDAFootprint(txs). The Jovian DA-footprint enforcement (core/block_validator.go) must REJECT it,
// proving that check is load-bearing — the acceptance-path tests alone would still pass even if the validator
// never compared the stored footprint to the recomputed one. Mutation: removing the
// `blobGasUsed != daFootprint` reject branch makes this import succeed and fails the test.
func TestDAFootprintWrongBlobGasUsedRejectedOnImport(t *testing.T) {
	cfg := jovianConfig()
	db := rawdb.NewMemoryDatabase()
	w, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)

	const numMempoolTxs = 3
	mempoolTxs := genTxs(1, numMempoolTxs)
	if errs := b.txPool.Add(mempoolTxs, true); len(errs) > 0 {
		for _, err := range errs {
			require.NoError(t, err, "failed adding tx to pool")
		}
	}

	parent := b.chain.CurrentBlock()
	genParams := &generateParams{
		parentHash:    parent.Hash(),
		timestamp:     parent.Time + 12,
		withdrawals:   types.Withdrawals{},
		beaconRoot:    new(common.Hash),
		gasLimit:      ptr(uint64(1e6)),
		txs:           types.Transactions{types.NewTx(jovianDepositTx(testDAFootprintGasScalar))},
		eip1559Params: eip1559.EncodeHolocene1559Params(250, 6),
		minBaseFee:    new(uint64),
	}
	r := w.generateWork(genParams, false)
	require.NoError(t, r.err, "block generation failed")
	require.NotNil(t, r.block, "no block generated")
	block := r.block
	require.NotNil(t, block.Header().BlobGasUsed, "post-Jovian block must store a DA footprint in BlobGasUsed")

	// Corrupt only BlobGasUsed (footprint+1), keeping the same txs/withdrawals so TxHash/WithdrawalsHash still
	// match — the block reaches ValidateBody and is rejected specifically by the DA-footprint comparison.
	hdr := types.CopyHeader(block.Header())
	bad := *hdr.BlobGasUsed + 1
	hdr.BlobGasUsed = &bad
	badBlock := types.NewBlockWithHeader(hdr).WithBody(types.Body{
		Transactions: block.Transactions(),
		Withdrawals:  block.Withdrawals(),
	})

	_, err := b.chain.InsertChain(types.Blocks{badBlock})
	require.Error(t, err, "a block whose header.BlobGasUsed != CalcDAFootprint(txs) must be REJECTED on import")
	require.ErrorContains(t, err, "DA footprint",
		"the rejection must come from the Jovian DA-footprint validator, not an unrelated check")
}

// TestDAFootprintForceIncludedBtcAttrAndPop is the production-dominant build==import variant: it
// force-includes both a BTC Attributes Deposited (0x7C, present in nearly every hVM block) and a PoP
// payout (0x7D) alongside mempool txs. It also adds an independent oracle: builder's header.BlobGasUsed
// is checked against a footprint summed by hand (not via CalcDAFootprint), so a shared bug in
// CalcDAFootprint's loop cannot make both sides agree spuriously.
func TestDAFootprintForceIncludedBtcAttrAndPop(t *testing.T) {
	cfg := jovianConfig()
	db := rawdb.NewMemoryDatabase()
	w, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)

	const numMempoolTxs = 3
	mempoolTxs := genTxs(1, numMempoolTxs)
	if errs := b.txPool.Add(mempoolTxs, true); len(errs) > 0 {
		for _, err := range errs {
			require.NoError(t, err, "failed adding tx to pool")
		}
	}

	parent := b.chain.CurrentBlock()
	ts := parent.Time + 12

	popTo := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := types.NewTx(&types.PopPayoutTx{To: &popTo, Gas: 50000, Data: []byte("popPayout")})
	btcHash := chainhash.Hash{0x09, 0x08, 0x07}
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&btcHash, nil)
	require.NoError(t, err)

	genParams := &generateParams{
		parentHash:    parent.Hash(),
		timestamp:     ts,
		withdrawals:   types.Withdrawals{},
		beaconRoot:    new(common.Hash),
		gasLimit:      ptr(uint64(15_000_000)), // room for the 1M-gas 0x7C plus the mempool txs
		txs:           types.Transactions{types.NewTx(jovianDepositTx(testDAFootprintGasScalar)), types.NewTx(btcAttr), popTx},
		eip1559Params: eip1559.EncodeHolocene1559Params(250, 6),
		minBaseFee:    new(uint64),
	}

	r := w.generateWork(genParams, false)
	require.NoError(t, r.err, "block generation failed")
	require.NotNil(t, r.block, "no block generated")
	block := r.block

	// Independent oracle: sum user-tx footprints by hand from the built block (not via CalcDAFootprint).
	var sawPop, sawBtc bool
	var nUser int
	var handOracle uint64
	for _, tx := range block.Transactions() {
		switch {
		case tx.IsPopPayoutTx():
			sawPop = true
		case tx.IsBtcAttributesDepositedTx():
			sawBtc = true
		case tx.IsDepositTx():
			// L1-info deposit contributes nothing.
		default:
			nUser++
			handOracle += tx.RollupCostData().EstimatedDASize().Uint64() * testDAFootprintGasScalar
		}
	}
	require.True(t, sawPop, "the force-included PoP payout (0x7D) must be present")
	require.True(t, sawBtc, "the force-included BTC Attributes Deposited (0x7C) must be present")
	require.GreaterOrEqual(t, nUser, numMempoolTxs, "mempool txs must be included alongside the system txs")

	require.NotNil(t, block.Header().BlobGasUsed)
	require.Positive(t, handOracle)
	// Build side: header.BlobGasUsed equals the hand-summed user footprint (0x7C/0x7D contribute nothing).
	require.Equal(t, handOracle, *block.Header().BlobGasUsed,
		"builder BlobGasUsed must equal the independent hand-summed user-tx footprint")
	// Import side: CalcDAFootprint over the full block must match (0x7C/0x7D excluded on both sides).
	recomputed, err := types.CalcDAFootprint(block.Transactions())
	require.NoError(t, err)
	require.Equal(t, *block.Header().BlobGasUsed, recomputed, "build==import with both 0x7C and 0x7D force-included")

	_, err = b.chain.InsertChain(types.Blocks{block})
	require.NoError(t, err, "self-built block with force-included 0x7C+0x7D must import")
}

// TestDAFootprintSystemOnlyBlockGateZero exercises the consensus.go FinalizeAndAssemble ==0 recompute
// gate: a block with no user txs (only the L1-info deposit plus a force-included 0x7C and 0x7D)
// accumulates header.BlobGasUsed=0 at build, tripping the recompute. CalcDAFootprint must also yield 0
// (system txs skipped) so the block imports. noTxs=true skips the mempool fill (the validator/non-
// sequencer build path).
func TestDAFootprintSystemOnlyBlockGateZero(t *testing.T) {
	cfg := jovianConfig()
	db := rawdb.NewMemoryDatabase()
	w, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)

	parent := b.chain.CurrentBlock()
	ts := parent.Time + 12

	popTo := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := types.NewTx(&types.PopPayoutTx{To: &popTo, Gas: 50000, Data: []byte("popPayout")})
	btcHash := chainhash.Hash{0x01, 0x02, 0x03}
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&btcHash, nil)
	require.NoError(t, err)

	genParams := &generateParams{
		parentHash:    parent.Hash(),
		timestamp:     ts,
		withdrawals:   types.Withdrawals{},
		beaconRoot:    new(common.Hash),
		gasLimit:      ptr(uint64(15_000_000)),
		txs:           types.Transactions{types.NewTx(jovianDepositTx(testDAFootprintGasScalar)), types.NewTx(btcAttr), popTx},
		eip1559Params: eip1559.EncodeHolocene1559Params(250, 6),
		minBaseFee:    new(uint64),
		noTxs:         true, // skip the mempool fill -> no user txs in the block
	}

	r := w.generateWork(genParams, false)
	require.NoError(t, r.err, "block generation failed")
	require.NotNil(t, r.block, "no block generated")
	block := r.block

	var sawPop, sawBtc bool
	var nUser int
	for _, tx := range block.Transactions() {
		switch {
		case tx.IsPopPayoutTx():
			sawPop = true
		case tx.IsBtcAttributesDepositedTx():
			sawBtc = true
		case tx.IsDepositTx():
		default:
			nUser++
		}
	}
	require.True(t, sawPop, "the force-included PoP payout must be present")
	require.True(t, sawBtc, "the force-included BTC Attributes Deposited must be present")
	require.Zero(t, nUser, "a noTxs build must contain no user txs")

	require.NotNil(t, block.Header().BlobGasUsed)
	require.Zero(t, *block.Header().BlobGasUsed, "a system-only block must have a zero DA footprint at build")
	recomputed, err := types.CalcDAFootprint(block.Transactions())
	require.NoError(t, err)
	require.Zero(t, recomputed, "CalcDAFootprint over a system-only block must be 0")

	_, err = b.chain.InsertChain(types.Blocks{block})
	require.NoError(t, err, "system-only block must import via the ==0 recompute-gate path")
}

// TestDAFootprintNotComputedPreJovian pins pre-Jovian dormancy of the DA-footprint seam: with Jovian in
// the future, the builder must not store a footprint in header.BlobGasUsed and import must not run the
// footprint check — a plain pre-Jovian block (tx[0] deposit carries no DA scalar) builds and imports
// normally. CalcDAFootprint would error on the scalar extraction pre-Jovian, so a clean build+import is
// the dormancy proof.
func TestDAFootprintNotComputedPreJovian(t *testing.T) {
	cfg := jovianConfig()
	future := uint64(1) << 62
	cfg.JovianTime = &future
	require.False(t, cfg.IsJovian(0), "config must be pre-Jovian for this test")

	// Makes the dormancy proof load-bearing: CalcDAFootprint on this tx set (tx[0] a plain deposit, no DA
	// scalar) errors, so a clean build+import below proves the DA path was never invoked. If a refactor
	// made this return nil, the test would weaken silently.
	_, calcErr := types.CalcDAFootprint(types.Transactions{types.NewTx(new(types.DepositTx))})
	require.Error(t, calcErr, "dormancy proof requires CalcDAFootprint to error on a plain pre-Jovian deposit block")

	db := rawdb.NewMemoryDatabase()
	w, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)

	const numMempoolTxs = 3
	mempoolTxs := genTxs(1, numMempoolTxs)
	if errs := b.txPool.Add(mempoolTxs, true); len(errs) > 0 {
		for _, err := range errs {
			require.NoError(t, err, "failed adding tx to pool")
		}
	}

	parent := b.chain.CurrentBlock()
	ts := parent.Time + 12
	require.False(t, cfg.IsJovian(ts), "block timestamp must be pre-Jovian")

	// Pre-Jovian: tx[0] is a plain deposit (no DA scalar), as the miner builds it pre-fork.
	genParams := &generateParams{
		parentHash:    parent.Hash(),
		timestamp:     ts,
		withdrawals:   types.Withdrawals{},
		beaconRoot:    new(common.Hash),
		gasLimit:      ptr(uint64(10_000_000)),
		txs:           types.Transactions{types.NewTx(new(types.DepositTx))},
		eip1559Params: eip1559.EncodeHolocene1559Params(250, 6),
	}
	r := w.generateWork(genParams, false)
	require.NoError(t, r.err, "pre-Jovian block generation failed")
	require.NotNil(t, r.block, "no block generated")
	block := r.block

	// Pre-Jovian, BlobGasUsed must not carry a DA footprint: for a non-blob block it is 0 (Cancun blob
	// accounting), never a CalcDAFootprint value.
	if block.Header().BlobGasUsed != nil {
		require.Zero(t, *block.Header().BlobGasUsed, "pre-Jovian block must not store a DA footprint in BlobGasUsed")
	}

	// And it must import on the pre-Jovian chain (ValidateBody must not run the Jovian footprint check).
	_, err := b.chain.InsertChain(types.Blocks{block})
	require.NoError(t, err, "pre-Jovian block must import without invoking the DA-footprint path")
}

// TestDAFootprintForceIncludedSystemTxDoesNotConsumeDABudget proves a force-included 0x7C/0x7D does not
// consume the Jovian DA-footprint budget (gasLimit - BlobGasUsed). It builds two blocks from the same
// deterministic mempool under a tight gas limit so the DA budget (not gas) throttles the fill: block A
// force-includes only the L1-info deposit, block B also a 0x7C and a 0x7D. Admitted user-tx count and
// accumulated BlobGasUsed must be identical. A regression letting a system tx add to env.header.BlobGasUsed
// would shrink B's budget and admit fewer mempool txs — invisible to the build==import oracle (both sides
// shrink together), caught only here.
func TestDAFootprintForceIncludedSystemTxDoesNotConsumeDABudget(t *testing.T) {
	// Generate the mempool txs once so both builds see byte-identical pending txs (genTxs uses rand).
	mempoolTxs := genTxs(1, 20)

	build := func(forceTxs types.Transactions) (*types.Block, int) {
		cfg := jovianConfig()
		db := rawdb.NewMemoryDatabase()
		w, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)
		if errs := b.txPool.Add(mempoolTxs, true); len(errs) > 0 {
			for _, err := range errs {
				require.NoError(t, err, "failed adding tx to pool")
			}
		}
		parent := b.chain.CurrentBlock()
		txs := append(types.Transactions{types.NewTx(jovianDepositTx(testDAFootprintGasScalar))}, forceTxs...)
		genParams := &generateParams{
			parentHash:    parent.Hash(),
			timestamp:     parent.Time + 12,
			withdrawals:   types.Withdrawals{},
			beaconRoot:    new(common.Hash),
			gasLimit:      ptr(uint64(500_000)), // tight: the DA-footprint budget binds before gas
			txs:           txs,
			eip1559Params: eip1559.EncodeHolocene1559Params(250, 6),
			minBaseFee:    new(uint64),
		}
		r := w.generateWork(genParams, false)
		require.NoError(t, r.err, "block generation failed")
		nUser := 0
		for _, tx := range r.block.Transactions() {
			if !tx.IsDepositTx() && !tx.IsPopPayoutTx() && !tx.IsBtcAttributesDepositedTx() {
				nUser++
			}
		}
		return r.block, nUser
	}

	// Build the system txs with small gas limits so they fit the tight gas pool (the 1M-gas
	// MakeBtcAttributesDepositedTx would not). System txs report zero actual gas used, so they consume
	// neither the gas budget nor — the property under test — the DA-footprint budget.
	popTo := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := types.NewTx(&types.PopPayoutTx{To: &popTo, Gas: 30_000, Data: []byte("pop")})
	btcTo := common.HexToAddress("0x4200000000000000000000000000000000000016")
	btcTx := types.NewTx(&types.BtcAttributesDepositedTx{To: &btcTo, Gas: 30_000, Data: []byte("btc")})

	blockA, nA := build(nil)                              // L1-info deposit only
	blockB, nB := build(types.Transactions{btcTx, popTx}) // + force-included 0x7C and 0x7D

	require.Positive(t, nA)
	require.Less(t, nA, 20, "the DA-footprint budget must actually throttle the mempool fill (else the test is vacuous)")
	require.Equal(t, nA, nB, "force-included 0x7C/0x7D must NOT consume DA budget — same admitted user-tx count")
	require.Equal(t, *blockA.Header().BlobGasUsed, *blockB.Header().BlobGasUsed, "same accumulated footprint regardless of force-included system txs")
}

// TestDAFootprintBtcAttrAndPopValidatesOnFreshChain is the highest-fidelity build==import proof: it
// builds a post-Jovian block with force-included 0x7C+0x7D + mempool txs on one node, then imports it
// into an independent cold-DB chain that never saw the build. That chain re-executes from scratch
// (ProcessBlock + ValidateState + the Jovian ValidateBody footprint check) and must accept it with an
// identical block hash and state root — catching divergence a warm same-DB self import could mask by
// reusing builder-side in-memory state.
func TestDAFootprintBtcAttrAndPopValidatesOnFreshChain(t *testing.T) {
	cfg := jovianConfig()
	db := rawdb.NewMemoryDatabase()
	w, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)

	mempoolTxs := genTxs(1, 3)
	if errs := b.txPool.Add(mempoolTxs, true); len(errs) > 0 {
		for _, err := range errs {
			require.NoError(t, err, "failed adding tx to pool")
		}
	}
	parent := b.chain.CurrentBlock()
	popTo := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := types.NewTx(&types.PopPayoutTx{To: &popTo, Gas: 50_000, Data: []byte("popPayout")})
	btcHash := chainhash.Hash{0x21, 0x22, 0x23}
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&btcHash, nil)
	require.NoError(t, err)

	genParams := &generateParams{
		parentHash:    parent.Hash(),
		timestamp:     parent.Time + 12,
		withdrawals:   types.Withdrawals{},
		beaconRoot:    new(common.Hash),
		gasLimit:      ptr(uint64(15_000_000)),
		txs:           types.Transactions{types.NewTx(jovianDepositTx(testDAFootprintGasScalar)), types.NewTx(btcAttr), popTx},
		eip1559Params: eip1559.EncodeHolocene1559Params(250, 6),
		minBaseFee:    new(uint64),
	}
	r := w.generateWork(genParams, false)
	require.NoError(t, r.err, "block generation failed")
	block := r.block
	require.Positive(t, *block.Header().BlobGasUsed)

	// Independent validator: fresh DB and chain from the same genesis, never saw the build.
	vdb := rawdb.NewMemoryDatabase()
	vchain, err := core.NewBlockChain(vdb, b.genesis, nil, beacon.New(ethash.NewFaker()), nil, nil, nil, t.Context())
	require.NoError(t, err)
	defer vchain.Stop()

	n, err := vchain.InsertChain(types.Blocks{block})
	require.NoError(t, err, "an independent validator must accept the 0x7C+0x7D footprint block")
	require.Equal(t, 1, n)
	require.Equal(t, block.Hash(), vchain.CurrentBlock().Hash(), "independent re-execution must yield the same block hash")
	require.Equal(t, block.Root(), vchain.CurrentBlock().Root, "independent re-execution must yield the same state root")
}

// TestDAFootprintBlobTxRejectedFromMempool documents the guard keeping the DA-footprint fill loop's
// unconditional ltx.DABytes.Uint64() deref (in worker.go) unreachable for blob txs: on an OP-Stack
// chain the blobpool is gated out, so a blob tx (EIP-4844, type 0x03) is rejected at pool admission and
// never enters the pending set. The blobpool would not populate DABytes, so a blob tx reaching that loop
// would nil-panic. If a change ever admitted blob txs to L2 blocks, this test fails, flagging that the
// DABytes deref must be guarded first.
func TestDAFootprintBlobTxRejectedFromMempool(t *testing.T) {
	cfg := jovianConfig()
	db := rawdb.NewMemoryDatabase()
	_, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)

	signer := types.NewCancunSigner(cfg.ChainID) // blob-capable; rejection is type-based, pre-sender-recovery
	blobTx, err := types.SignTx(types.NewTx(&types.BlobTx{
		ChainID:    uint256.MustFromBig(cfg.ChainID),
		Nonce:      0,
		GasTipCap:  uint256.NewInt(1),
		GasFeeCap:  uint256.NewInt(1_000_000_000),
		Gas:        100_000,
		To:         testUserAddress,
		BlobFeeCap: uint256.NewInt(1_000_000_000),
		BlobHashes: []common.Hash{{0x01}},
		Value:      new(uint256.Int),
	}), signer, testBankKey)
	require.NoError(t, err)
	require.Equal(t, uint8(types.BlobTxType), blobTx.Type())

	errs := b.txPool.Add(types.Transactions{blobTx}, true)
	require.Len(t, errs, 1)
	require.ErrorIs(t, errs[0], core.ErrTxTypeNotSupported, "blob txs must be rejected from the mempool on an OP-Stack chain (blobpool is gated out)")
}

// TestDAFootprintMaxDABlockSizeThrottle exercises the sequencer DA-size throttle (in worker.go),
// otherwise uncovered: with a small miner.config.MaxDABlockSize the mempool fill caps at a few txs and
// hits the early-break (remaining < MinTransactionSize), yet the block must still build cleanly.
// Force-included 0x7C/0x7D confirm they do not perturb this mempool-only path.
func TestDAFootprintMaxDABlockSizeThrottle(t *testing.T) {
	cfg := jovianConfig()
	db := rawdb.NewMemoryDatabase()
	w, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)
	// Each genTxs tx occupies ~100 DA bytes (floored EstimatedDASize). Cap the block DA so only a few
	// fit; after ~3 the remaining budget (<100) trips the early-break. config is passed by value to New(),
	// so this does not mutate the shared testConfig.
	w.config.MaxDABlockSize = big.NewInt(350)

	if errs := b.txPool.Add(genTxs(1, 20), true); len(errs) > 0 {
		for _, err := range errs {
			require.NoError(t, err, "failed adding tx to pool")
		}
	}

	parent := b.chain.CurrentBlock()
	popTo := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := types.NewTx(&types.PopPayoutTx{To: &popTo, Gas: 30_000, Data: []byte("pop")})
	btcTo := common.HexToAddress("0x4200000000000000000000000000000000000016")
	btcTx := types.NewTx(&types.BtcAttributesDepositedTx{To: &btcTo, Gas: 30_000, Data: []byte("btc")})

	genParams := &generateParams{
		parentHash:    parent.Hash(),
		timestamp:     parent.Time + 12,
		withdrawals:   types.Withdrawals{},
		beaconRoot:    new(common.Hash),
		gasLimit:      ptr(uint64(15_000_000)), // generous gas: the DA-size cap (not gas) is the binding limit
		txs:           types.Transactions{types.NewTx(jovianDepositTx(testDAFootprintGasScalar)), btcTx, popTx},
		eip1559Params: eip1559.EncodeHolocene1559Params(250, 6),
		minBaseFee:    new(uint64),
	}
	r := w.generateWork(genParams, false)
	require.NoError(t, r.err, "block must build cleanly with the DA-size throttle active (incl. the early-break path)")

	nUser := 0
	for _, tx := range r.block.Transactions() {
		if !tx.IsDepositTx() && !tx.IsPopPayoutTx() && !tx.IsBtcAttributesDepositedTx() {
			nUser++
		}
	}
	require.Positive(t, nUser, "some mempool txs must be admitted")
	require.Less(t, nUser, 10, "MaxDABlockSize must throttle the mempool fill well below the 20 available txs")
}

// TestDAFootprintActivationBlockBuildEqualsImport is the fork-boundary tripwire: it builds the Jovian
// activation block (parent pre-Jovian, header post-Jovian) through the miner. Here build and import gate
// on different time references — worker.go extracts the DA scalar only when IsJovian(parent.Time)
// (false at activation, so the scalar stays 0 and header.BlobGasUsed accumulates 0), while import's
// CalcDAFootprint keys on tx[0]'s length (the 176-byte Isthmus old-format L1-info op-node emits at
// activation) and takes the activation branch. The block must build (BlobGasUsed==0) and import. Asserting
// tx[0] is 176 bytes pins the op-node old-format contract: refactoring that gate from parent.Time to header.Time, or
// op-node emitting a 178-byte tx[0] a block early, would diverge the build-side 0 footprint from a nonzero
// import recompute — the fork-boundary fleet stall.
func TestDAFootprintActivationBlockBuildEqualsImport(t *testing.T) {
	cfg := jovianConfig()
	activation := uint64(12)
	cfg.JovianTime = &activation // genesis is at time 0 (pre-Jovian); the child header at t=12 is the activation block

	db := rawdb.NewMemoryDatabase()
	w, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)

	parent := b.chain.CurrentBlock()
	require.False(t, cfg.IsJovian(parent.Time), "parent (genesis) must be pre-Jovian")
	ts := parent.Time + 12
	require.True(t, cfg.IsJovian(ts), "the child header must be at/after the Jovian activation time")

	// op-node emits the old 176-byte Isthmus-format L1-info deposit at the activation block (no DA scalar
	// yet) and sets NoTxPool so the block carries no trailing user tx. Model both.
	l1Info := types.NewTx(&types.DepositTx{Data: make([]byte, types.IsthmusL1AttributesLen)})
	popTo := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := types.NewTx(&types.PopPayoutTx{To: &popTo, Gas: 30_000, Data: []byte("pop")})
	btcTo := common.HexToAddress("0x4200000000000000000000000000000000000016")
	btcTx := types.NewTx(&types.BtcAttributesDepositedTx{To: &btcTo, Gas: 30_000, Data: []byte("btc")})

	genParams := &generateParams{
		parentHash:    parent.Hash(),
		timestamp:     ts,
		withdrawals:   types.Withdrawals{},
		beaconRoot:    new(common.Hash),
		gasLimit:      ptr(uint64(15_000_000)),
		txs:           types.Transactions{l1Info, btcTx, popTx},
		eip1559Params: eip1559.EncodeHolocene1559Params(250, 6),
		minBaseFee:    new(uint64),
		noTxs:         true, // op-node sets NoTxPool at the activation block
	}
	r := w.generateWork(genParams, false)
	require.NoError(t, r.err, "the Jovian activation block must build")
	block := r.block

	// Build side: the DA scalar is not extracted (gated on the pre-Jovian parent), so no footprint; tx[0]
	// is the 176-byte old-format L1-info (pins the op-node activation contract).
	require.Len(t, block.Transactions()[0].Data(), types.IsthmusL1AttributesLen, "activation tx[0] must be the 176-byte old-format L1-info")
	require.NotNil(t, block.Header().BlobGasUsed)
	require.Zero(t, *block.Header().BlobGasUsed, "the activation block sets no DA footprint")

	// Import side: CalcDAFootprint takes the activation branch (tx[0] len==176) and returns 0; build==import.
	fp, err := types.CalcDAFootprint(block.Transactions())
	require.NoError(t, err)
	require.Zero(t, fp)
	_, err = b.chain.InsertChain(types.Blocks{block})
	require.NoError(t, err, "the Jovian activation block must import (build==import at the fork boundary)")
}

// TestDAFootprintActivationBlockRejectsTrailingUserTx is the end-to-end negative of the activation
// tripwire. op-node sets NoTxPool at the Jovian activation block so it carries no user tx; this test
// violates that by enabling the mempool fill, so the miner appends a user tx after the forced
// deposit/system txs, leaving a trailing user tx. Since the activation block accumulates
// header.BlobGasUsed==0 (no DA scalar for a pre-Jovian parent), the consensus.go ==0 recompute gate fires
// during FinalizeAndAssemble and CalcDAFootprint's activation branch rejects the trailing user tx — so the
// build itself fails. The sequencer self-rejects (a missed slot) rather than producing a block that would
// be rejected fleet-wide on import.
func TestDAFootprintActivationBlockRejectsTrailingUserTx(t *testing.T) {
	cfg := jovianConfig()
	activation := uint64(12)
	cfg.JovianTime = &activation // genesis at t=0 is pre-Jovian; the child header at t=12 is the activation block

	db := rawdb.NewMemoryDatabase()
	w, b := newTestWorker(t, cfg, beacon.New(ethash.NewFaker()), db, 0)

	parent := b.chain.CurrentBlock()
	require.False(t, cfg.IsJovian(parent.Time), "parent (genesis) must be pre-Jovian")
	ts := parent.Time + 12
	require.True(t, cfg.IsJovian(ts), "the child header must be at/after the Jovian activation time")

	// Seed the mempool and do not set NoTxPool: the miner appends user txs after the forced txs, leaving a
	// trailing user tx in the activation block (the contract violation under test).
	if errs := b.txPool.Add(genTxs(1, 3), true); len(errs) > 0 {
		for _, err := range errs {
			require.NoError(t, err, "failed adding tx to pool")
		}
	}

	l1Info := types.NewTx(&types.DepositTx{Data: make([]byte, types.IsthmusL1AttributesLen)})
	popTo := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := types.NewTx(&types.PopPayoutTx{To: &popTo, Gas: 30_000, Data: []byte("pop")})
	btcTo := common.HexToAddress("0x4200000000000000000000000000000000000016")
	btcTx := types.NewTx(&types.BtcAttributesDepositedTx{To: &btcTo, Gas: 30_000, Data: []byte("btc")})

	genParams := &generateParams{
		parentHash:    parent.Hash(),
		timestamp:     ts,
		withdrawals:   types.Withdrawals{},
		beaconRoot:    new(common.Hash),
		gasLimit:      ptr(uint64(15_000_000)),
		txs:           types.Transactions{l1Info, btcTx, popTx},
		eip1559Params: eip1559.EncodeHolocene1559Params(250, 6),
		minBaseFee:    new(uint64),
		// noTxs deliberately false: NoTxPool contract violated so a user tx trails.
	}
	r := w.generateWork(genParams, false)
	require.Error(t, r.err, "a trailing user tx in the Jovian activation block must be rejected")
	require.ErrorContains(t, r.err, "unexpected non-deposit transactions in Jovian activation block")
}

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

// Regression tests for applyTransaction's gas/state accounting around hVM precompiles.
//
// A regular tx that invokes an hVM precompile with invalid input must be handled identically by the
// builder and validators: EVM.runPrecompile normalizes the invalid-input sentinel to an empty successful
// return, so the tx is included as a no-op, not dropped at build time. A previous build-time rejection was
// removed because it (a) called state.RevertToSnapshot after core.ApplyTransaction had Finalised the state
// — which panics, since Finalise invalidates the snapshot — and (b) left header.GasUsed inflated by the
// rejected tx's gas, producing blocks that fail validation. These tests lock in the no-panic,
// no-rejection, correctly-accounted behavior.

// btcTxConfirmationsAddr is the hVM precompile at 0x43; it returns the invalid-input sentinel for any
// input whose length != 32 bytes, before touching any external (TBC) state.
var btcTxConfirmationsAddr = common.BytesToAddress([]byte{0x43})

// btcUtxosAddrListAddr is the hVM precompile at 0x41; its RequiredGas is the high
// params.BtcUtxosAddrList (100000), charged before Run() executes. Used to exercise the under-funded path
// where the precompile call runs out of gas before it can return the invalid-input sentinel.
var btcUtxosAddrListAddr = common.BytesToAddress([]byte{0x41})

func newGasUsedTestEnv(t *testing.T) (*environment, *params.ChainConfig, *ecdsa.PrivateKey, common.Address) {
	t.Helper()

	cfg := *params.MergedTestChainConfig // post-merge, all forks active
	zero := uint64(0)
	cfg.Hvm0Time = &zero // activate the hVM precompiles (0x40-0x49)

	statedb, err := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
	require.NoError(t, err)

	key, err := crypto.GenerateKey()
	require.NoError(t, err)
	sender := crypto.PubkeyToAddress(key.PublicKey)
	statedb.AddBalance(sender, uint256.NewInt(1_000_000_000_000_000_000), tracing.BalanceChangeUnspecified)

	header := &types.Header{
		Number:     big.NewInt(1),
		Time:       1,
		GasLimit:   30_000_000,
		BaseFee:    big.NewInt(0),
		Difficulty: big.NewInt(0),
	}
	random := common.Hash{}
	blockCtx := vm.BlockContext{
		CanTransfer: core.CanTransfer,
		Transfer:    core.Transfer,
		GetHash:     func(uint64) common.Hash { return common.Hash{} },
		BlockNumber: header.Number,
		Time:        header.Time,
		Difficulty:  big.NewInt(0),
		GasLimit:    header.GasLimit,
		BaseFee:     header.BaseFee,
		Random:      &random, // post-merge
	}
	env := &environment{
		signer:  types.MakeSigner(&cfg, header.Number, header.Time),
		state:   statedb,
		gasPool: new(core.GasPool).AddGas(header.GasLimit),
		header:  header,
		evm:     vm.NewEVM(blockCtx, statedb, &cfg, vm.Config{}),
	}
	return env, &cfg, key, sender
}

func signTestTx(t *testing.T, cfg *params.ChainConfig, header *types.Header, key *ecdsa.PrivateKey, nonce uint64, to common.Address, data []byte) *types.Transaction {
	t.Helper()
	tx, err := types.SignNewTx(key, types.MakeSigner(cfg, header.Number, header.Time), &types.LegacyTx{
		Nonce:    nonce,
		GasPrice: big.NewInt(1),
		Gas:      100_000,
		To:       &to,
		Value:    big.NewInt(0),
		Data:     data,
	})
	require.NoError(t, err)
	return tx
}

// A regular tx invoking an hVM precompile with invalid input must be included as a no-op (empty successful
// return), not rejected, and must never panic. Guards both the RevertToSnapshot panic and the GasUsed
// desync the removed build-time rejection caused.
func TestApplyTransactionIncludesInvalidHVMInputTx(t *testing.T) {
	env, cfg, key, sender := newGasUsedTestEnv(t)

	// 4-byte input to btcTxConfirmations (0x43) is the wrong length -> the precompile returns the
	// invalid-input sentinel, which runPrecompile normalizes to an empty successful return.
	tx := signTestTx(t, cfg, env.header, key, 0, btcTxConfirmationsAddr, []byte{0x00, 0x00, 0x00, 0x00})
	env.state.SetTxContext(tx.Hash(), 0)

	var (
		receipt *types.Receipt
		err     error
	)
	require.NotPanics(t, func() { receipt, err = (&Miner{}).applyTransaction(env, tx) },
		"applyTransaction must not panic on an invalid-hVM-input tx")
	require.NoError(t, err, "invalid hVM input must be included as a no-op, not rejected")
	require.NotNil(t, receipt)
	require.Equal(t, types.ReceiptStatusSuccessful, receipt.Status, "the invalid-hVM call is a successful empty no-op, not a revert")
	// Anchor the exact gas so the test cannot silently go vacuous: 21000 intrinsic + 4 zero calldata bytes
	// * 4 + the precompile's RequiredGas (BtcTxConf=5000). If 0x43 stopped resolving to the hVM precompile
	// this would collapse to a plain 21016-gas EOA transfer and the assertion below would fail — proving
	// the precompile was actually invoked, not merely that some gas was charged.
	const wantGas = params.TxGas + 4*params.TxDataZeroGas + params.BtcTxConf // 26016
	require.Equal(t, uint64(wantGas), env.header.GasUsed, "exact gas must include the precompile's RequiredGas (proves 0x43 was invoked as an hVM precompile)")
	require.Equal(t, env.header.GasUsed, receipt.CumulativeGasUsed, "header GasUsed must equal the receipt's cumulative gas")
	require.Equal(t, uint64(1), env.state.GetNonce(sender), "sender nonce must advance for the included tx")
}

// Under-funded path: a tx invoking an hVM precompile with would-be-invalid input but too little gas to
// cover the precompile's RequiredGas OOGs at the gas-charge step in RunPrecompiledContract, before Run()
// returns the sentinel. ErrOutOfGas is not normalized (only the sentinel is), so this is an ordinary
// revert, not a success no-op. It is still included (no panic, applyTransaction returns a nil error) with a
// failed receipt consuming all supplied gas — byte-for-byte identical to the prior behavior, since the
// sentinel is never emitted here so the removed build-time rejection never engaged. Pins that the two
// implementations cannot diverge on under-funded invalid-input calls.
func TestApplyTransactionUnderfundedInvalidHVMInputReverts(t *testing.T) {
	env, cfg, key, sender := newGasUsedTestEnv(t)

	// 0x41 (btcUtxosAddrList) needs 100000 gas for the precompile alone; fund only 90000 so that, after
	// ~21016 intrinsic, the precompile call is starved and OOGs before Run() (and the sentinel) is reached.
	const gasLimit = uint64(90_000)
	tx, err := types.SignNewTx(key, types.MakeSigner(cfg, env.header.Number, env.header.Time), &types.LegacyTx{
		Nonce:    0,
		GasPrice: big.NewInt(1),
		Gas:      gasLimit,
		To:       &btcUtxosAddrListAddr,
		Value:    big.NewInt(0),
		Data:     []byte{0x00, 0x00, 0x00, 0x00}, // would be invalid-length input if Run() were reached
	})
	require.NoError(t, err)
	env.state.SetTxContext(tx.Hash(), 0)

	var receipt *types.Receipt
	require.NotPanics(t, func() { receipt, err = (&Miner{}).applyTransaction(env, tx) },
		"an under-funded invalid-hVM-input tx must not panic")
	require.NoError(t, err, "under-funded invalid-hVM input is included (reverted), not rejected at build time")
	require.NotNil(t, receipt)
	require.Equal(t, types.ReceiptStatusFailed, receipt.Status,
		"under-funded call OOGs before the sentinel -> ordinary revert, NOT a success no-op")
	require.Equal(t, gasLimit, env.header.GasUsed, "a top-level out-of-gas revert consumes the entire supplied gas")
	require.Equal(t, env.header.GasUsed, receipt.CumulativeGasUsed, "header GasUsed must equal the receipt's cumulative gas")
	require.Equal(t, uint64(1), env.state.GetNonce(sender), "the reverted-but-included tx still advances the sender nonce")
}

// Guard: a successful ordinary tx still counts its gas into the header.
func TestApplyTransactionSuccessCountsGasUsed(t *testing.T) {
	env, cfg, key, _ := newGasUsedTestEnv(t)

	to := common.HexToAddress("0x000000000000000000000000000000000000c0fe") // plain EOA, no code
	tx := signTestTx(t, cfg, env.header, key, 0, to, nil)
	env.state.SetTxContext(tx.Hash(), 0)

	_, err := (&Miner{}).applyTransaction(env, tx)
	require.NoError(t, err)
	require.Equal(t, uint64(params.TxGas), env.header.GasUsed, "successful transfer must count 21000 gas")
}

// Guard: a normal apply error (here, nonce too high) reverts cleanly — state, gas pool and GasUsed are
// untouched, no panic (the snapshot is still valid because core.ApplyTransaction errors before Finalise).
func TestApplyTransactionNormalErrorRevertsCleanly(t *testing.T) {
	env, cfg, key, sender := newGasUsedTestEnv(t)

	to := common.HexToAddress("0x000000000000000000000000000000000000c0fe")
	tx := signTestTx(t, cfg, env.header, key, 7, to, nil) // state nonce is 0 -> ErrNonceTooHigh
	env.state.SetTxContext(tx.Hash(), 0)

	gasBefore := env.header.GasUsed
	gpBefore := env.gasPool.Gas()
	nonceBefore := env.state.GetNonce(sender)

	var err error
	require.NotPanics(t, func() { _, err = (&Miner{}).applyTransaction(env, tx) })
	require.Error(t, err)
	require.Equal(t, gasBefore, env.header.GasUsed, "normal apply error must not change GasUsed")
	require.Equal(t, gpBefore, env.gasPool.Gas(), "gas pool must be restored")
	require.Equal(t, nonceBefore, env.state.GetNonce(sender), "state must be reverted")
}

// Regression for the cumulative dimension bug #1 lived in: the removed reject path left header.GasUsed
// inflated, corrupting the CumulativeGasUsed of every tx mined after the rejected one. The other tests
// mine a single invalid-hVM tx in isolation, where a single-tx total can land correctly by accident; this
// places a normal transfer immediately after the no-op tx in the same block and pins both the per-tx
// cumulative values and the block total, catching a re-introduced over-count on the 2nd+ tx.
func TestApplyTransactionCumulativeGasAcrossNoOp(t *testing.T) {
	env, cfg, key, sender := newGasUsedTestEnv(t)

	// Tx 0: invalid-hVM-input no-op to 0x43 (4 zero bytes of calldata).
	tx0 := signTestTx(t, cfg, env.header, key, 0, btcTxConfirmationsAddr, []byte{0x00, 0x00, 0x00, 0x00})
	env.state.SetTxContext(tx0.Hash(), 0)
	r0, err := (&Miner{}).applyTransaction(env, tx0)
	require.NoError(t, err)
	require.Equal(t, types.ReceiptStatusSuccessful, r0.Status)

	const wantGas0 = params.TxGas + 4*params.TxDataZeroGas + params.BtcTxConf // 26016
	require.Equal(t, uint64(wantGas0), r0.CumulativeGasUsed, "first receipt cumulative gas")
	require.Equal(t, uint64(wantGas0), env.header.GasUsed, "header after tx0")

	// Tx 1: a plain value transfer to an EOA, mined directly after the no-op.
	to := common.HexToAddress("0x000000000000000000000000000000000000c0fe")
	tx1 := signTestTx(t, cfg, env.header, key, 1, to, nil)
	env.state.SetTxContext(tx1.Hash(), 1)
	r1, err := (&Miner{}).applyTransaction(env, tx1)
	require.NoError(t, err)
	require.Equal(t, types.ReceiptStatusSuccessful, r1.Status)

	// The no-op tx must not corrupt the running total: tx1's cumulative gas and the block total must both
	// be exactly tx0 + 21000.
	const wantGas1 = wantGas0 + params.TxGas // 47016
	require.Equal(t, uint64(wantGas1), r1.CumulativeGasUsed, "second receipt cumulative gas must be tx0 + 21000")
	require.Equal(t, uint64(wantGas1), env.header.GasUsed, "block total must be tx0 + tx1, with no inflation from the no-op")
	require.Equal(t, uint64(2), env.state.GetNonce(sender), "both txs included -> nonce advanced twice")
}

// TestHVMInvalidInputTxBuildsAndValidatesAcrossNodes is the end-to-end two-node regression:
// a sequencer must be able to build a block containing a tx that invokes an hVM precompile with invalid
// input (now an empty-success no-op, not a build-time rejection), and an independent validator must
// re-execute and accept it with a byte-identical state root and GasUsed. Before this fix this tx would (a)
// crash the builder at RevertToSnapshot (Finalise had invalidated the snapshot) and (b) inflate
// header.GasUsed so the block fails validation. Exercises the real miner build path (buildPayload ->
// generateWork -> commitTransactions -> applyTransaction) and a real core.BlockChain.InsertChain.
func TestHVMInvalidInputTxBuildsAndValidatesAcrossNodes(t *testing.T) {
	// Non-OP chain with the hVM precompiles (0x40-0x49) activated at genesis. hVM activation depends only
	// on IsHvm0 (a timestamp fork), not on Optimism or a configured TBC node, and an invalid-length input
	// returns the sentinel before any TBC access — so no external state is needed.
	cfg := *params.TestChainConfig
	z := uint64(0)
	cfg.Hvm0Time = &z

	engine := ethash.NewFaker()
	db := rawdb.NewMemoryDatabase()
	backend := newTestWorkerBackend(t, &cfg, engine, db, 0)
	defer backend.chain.Stop()
	w := New(backend, testConfig, engine)

	// A regular signed tx (from the funded test bank) to btcTxConfirmations (0x43) with a 4-byte
	// (invalid-length) payload.
	to := common.BytesToAddress([]byte{0x43})
	badTx := types.MustSignNewTx(testBankKey, types.LatestSigner(&cfg), &types.LegacyTx{
		Nonce:    0,
		To:       &to,
		Value:    big.NewInt(0),
		Gas:      100_000,
		GasPrice: big.NewInt(params.InitialBaseFee),
		Data:     []byte{0x00, 0x00, 0x00, 0x00},
	})
	if errs := backend.txPool.Add([]*types.Transaction{badTx}, true); errs[0] != nil {
		t.Fatalf("txpool rejected the tx: %v", errs[0])
	}

	// --- Node A (sequencer): build a block via the real miner. ---
	args := newPayloadArgs(backend.chain.CurrentBlock().Hash(), &cfg)
	args.NoTxPool = false  // run fillTransactions so the pooled tx is selected
	args.Withdrawals = nil // TestChainConfig is pre-Shanghai at this timestamp; no withdrawals
	payload, err := w.buildPayload(args, false)
	require.NoError(t, err, "buildPayload")
	payload.WaitFull() // let fillTransactions finish so the pooled tx is committed before we resolve
	require.NotNil(t, payload.ResolveFull(), "full payload must resolve (build must not panic/abort)")

	block := payload.full
	require.NotNil(t, block, "built block")

	// The invalid-hVM-input tx must be included (as a no-op), not dropped.
	included := false
	for _, tx := range block.Transactions() {
		if tx.Hash() == badTx.Hash() {
			included = true
		}
	}
	require.True(t, included, "the invalid-hVM-input tx must be included as a no-op, not rejected at build time")
	require.Greater(t, block.GasUsed(), uint64(0), "block must account the no-op tx's gas")

	// --- Node B (independent validator): re-execute & validate the built block. ---
	// A fresh chain from the same genesis. InsertChain runs Process + ValidateState (state root, GasUsed,
	// receipt root); no error proves the block re-executes byte-identically (builder and validator agree).
	vdb := rawdb.NewMemoryDatabase()
	vchain, err := core.NewBlockChain(vdb, backend.genesis, nil, ethash.NewFaker(), nil, nil, nil, t.Context())
	require.NoError(t, err, "validator NewBlockChain")
	defer vchain.Stop()

	n, err := vchain.InsertChain(types.Blocks{block})
	require.NoError(t, err, "independent validator must import the built block without error")
	require.Equal(t, 1, n, "exactly one block inserted")

	head := vchain.CurrentBlock()
	require.Equal(t, block.Hash(), head.Hash(), "validator head must equal the built block")
	require.Equal(t, block.GasUsed(), head.GasUsed, "GasUsed must match builder vs validator")
	require.Equal(t, block.Root(), head.Root, "state root must match builder vs validator")
}

// TestHVMUnderfundedInvalidInputBuildsAndValidatesAcrossNodes is the two-node regression for the
// under-funded path. A tx invokes an hVM precompile with would-be-invalid input but too little gas for the
// precompile's RequiredGas, so the call OOGs before Run() emits the sentinel. ErrOutOfGas is not
// normalized, so the tx is included with a failed receipt consuming all its gas — and builder and
// independent validator must agree byte-for-byte (equal block hash, GasUsed, state root; the equal hash
// also proves the failed-receipt root matches). Identical to the prior behavior (the
// sentinel is never emitted, so neither the old build-time rejection nor the new no-op normalization is involved),
// guarding any gas-accounting divergence on under-funding.
func TestHVMUnderfundedInvalidInputBuildsAndValidatesAcrossNodes(t *testing.T) {
	cfg := *params.TestChainConfig
	z := uint64(0)
	cfg.Hvm0Time = &z

	engine := ethash.NewFaker()
	db := rawdb.NewMemoryDatabase()
	backend := newTestWorkerBackend(t, &cfg, engine, db, 0)
	defer backend.chain.Stop()
	w := New(backend, testConfig, engine)

	// 0x41 (btcUtxosAddrList) needs 100000 gas for the precompile alone; fund only 90000 so the call is
	// starved after intrinsic gas and OOGs before Run().
	const gasLimit = uint64(90_000)
	to := common.BytesToAddress([]byte{0x41})
	badTx := types.MustSignNewTx(testBankKey, types.LatestSigner(&cfg), &types.LegacyTx{
		Nonce:    0,
		To:       &to,
		Value:    big.NewInt(0),
		Gas:      gasLimit,
		GasPrice: big.NewInt(params.InitialBaseFee),
		Data:     []byte{0x00, 0x00, 0x00, 0x00},
	})
	if errs := backend.txPool.Add([]*types.Transaction{badTx}, true); errs[0] != nil {
		t.Fatalf("txpool rejected the tx: %v", errs[0])
	}

	// --- Node A (sequencer): build. ---
	args := newPayloadArgs(backend.chain.CurrentBlock().Hash(), &cfg)
	args.NoTxPool = false
	args.Withdrawals = nil
	payload, err := w.buildPayload(args, false)
	require.NoError(t, err, "buildPayload")
	payload.WaitFull()
	require.NotNil(t, payload.ResolveFull(), "full payload must resolve (build must not panic/abort)")

	block := payload.full
	require.NotNil(t, block, "built block")

	included := false
	for _, tx := range block.Transactions() {
		if tx.Hash() == badTx.Hash() {
			included = true
		}
	}
	require.True(t, included, "the under-funded invalid-hVM-input tx must be included (as a revert), not rejected at build time")
	require.Equal(t, gasLimit, block.GasUsed(), "a top-level OOG revert consumes the full supplied gas")

	// --- Node B (independent validator): re-execute & validate. ---
	vdb := rawdb.NewMemoryDatabase()
	vchain, err := core.NewBlockChain(vdb, backend.genesis, nil, ethash.NewFaker(), nil, nil, nil, t.Context())
	require.NoError(t, err, "validator NewBlockChain")
	defer vchain.Stop()

	n, err := vchain.InsertChain(types.Blocks{block})
	require.NoError(t, err, "independent validator must import the built block without error")
	require.Equal(t, 1, n, "exactly one block inserted")

	head := vchain.CurrentBlock()
	require.Equal(t, block.Hash(), head.Hash(), "validator head must equal the built block")
	require.Equal(t, block.GasUsed(), head.GasUsed, "GasUsed must match builder vs validator")
	require.Equal(t, block.Root(), head.Root, "state root must match builder vs validator")

	// The included tx must have a failed receipt on the validator (OOG revert, not a success no-op). The
	// equal block hash above proves the builder's receipt root matches, so this status is shared by both.
	receipts := vchain.GetReceiptsByHash(block.Hash())
	require.Len(t, receipts, 1, "exactly one receipt")
	require.Equal(t, types.ReceiptStatusFailed, receipts[0].Status,
		"under-funded invalid-hVM-input tx must revert (OOG), not be a success no-op")
}
