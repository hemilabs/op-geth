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
	"crypto/ecdsa"
	"math/big"
	"testing"

	"github.com/holiman/uint256"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/tracing"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/params"
)

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
