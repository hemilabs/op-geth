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

package miner

import (
	"math/big"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
)

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
