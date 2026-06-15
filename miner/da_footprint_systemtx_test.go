package miner

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/beacon"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/consensus/misc/eip1559"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
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
