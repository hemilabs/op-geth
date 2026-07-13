// Copyright 2024 The go-ethereum Authors
// Copyright 2026 Hemi Labs, Inc.
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

package ethapi

// newRPCTransaction representation (the live eth_getTransactionByHash path) for the hVM system txs. The 0x7C/0x7D
// arms pull the per-tx nonce from the receipt (BtcAttributesDepositedNonce / PoPPayoutNonce), and the From resolves
// to the hardcoded 0x8888 consensus sender via the modern (Isthmus) signer. Only the 0x7E deposit arm was tested;
// a mutant dropping the 0x7C/0x7D receipt-nonce arm or the sender special-case would survive. OptimismTestConfig
// has Isthmus active, so MakeSigner selects the modernSigner that resolves the hardcoded sender.

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
	"github.com/stretchr/testify/require"
)

func TestNewRPCTransactionBtcAttributesDeposited(t *testing.T) {
	inner, err := types.MakeBtcAttributesDepositedTx(&chainhash.Hash{0x01, 0x02}, nil)
	require.NoError(t, err)
	tx := types.NewTx(inner)
	nonce := uint64(9)
	receipt := &types.Receipt{BtcAttributesDepositedNonce: &nonce}

	got := newRPCTransaction(tx, common.Hash{}, 12, 0, 1, big.NewInt(0), params.OptimismTestConfig, receipt)
	require.Equal(t, hexutil.Uint64(types.BtcAttributesDepositedTxType), got.Type)
	require.Equal(t, types.BtcAttributesDepositedSenderAddress, got.From, "From must be the hardcoded 0x7C consensus sender")
	require.Equal(t, hexutil.Uint64(nonce), got.Nonce, "Nonce must come from the receipt's BtcAttributesDepositedNonce")
	require.Equal(t, (*hexutil.Big)(big.NewInt(0)), got.GasPrice)
	require.Equal(t, (*hexutil.Big)(big.NewInt(0)), got.V)
	require.Equal(t, (*hexutil.Big)(big.NewInt(0)), got.R)
	require.Equal(t, (*hexutil.Big)(big.NewInt(0)), got.S)
	require.Equal(t, hexutil.Uint64(tx.Gas()), got.Gas)
	require.Equal(t, tx.To(), got.To)

	// Negative control: a LEGACY tx carrying the same receipt must use its OWN nonce, not the receipt's BtcAttr
	// nonce (the receipt-nonce arm is gated on tx type 0x7C). Kills a mutant dropping that tx-type guard.
	legacyTo := common.HexToAddress("0x00000000000000000000000000000000000000aa")
	legacy := types.NewTx(&types.LegacyTx{Nonce: 3, GasPrice: big.NewInt(1), Gas: 21000, To: &legacyTo, Value: big.NewInt(0)})
	gotLegacy := newRPCTransaction(legacy, common.Hash{}, 12, 0, 1, big.NewInt(0), params.OptimismTestConfig, receipt)
	require.Equal(t, hexutil.Uint64(3), gotLegacy.Nonce, "a legacy tx must use its own nonce, not the receipt's BtcAttr nonce")

	// nil-safety: the 0x7C arm is guarded on receipt != nil && BtcAttributesDepositedNonce != nil; both fall back to
	// the tx's own nonce (0). These prove the guards are load-bearing.
	gotNilReceipt := newRPCTransaction(tx, common.Hash{}, 12, 0, 1, big.NewInt(0), params.OptimismTestConfig, nil)
	require.Equal(t, hexutil.Uint64(0), gotNilReceipt.Nonce, "nil receipt -> fall back to tx nonce")
	gotNilNonce := newRPCTransaction(tx, common.Hash{}, 12, 0, 1, big.NewInt(0), params.OptimismTestConfig, &types.Receipt{})
	require.Equal(t, hexutil.Uint64(0), gotNilNonce.Nonce, "nil BtcAttributesDepositedNonce -> fall back to tx nonce")
}

func TestNewRPCTransactionPopPayout(t *testing.T) {
	gov := common.HexToAddress("0x4200000000000000000000000000000000000042")
	tx := types.NewTx(&types.PopPayoutTx{To: &gov, Gas: 50_000, Data: []byte("pop")})
	nonce := uint64(13)
	receipt := &types.Receipt{PoPPayoutNonce: &nonce}

	got := newRPCTransaction(tx, common.Hash{}, 12, 0, 1, big.NewInt(0), params.OptimismTestConfig, receipt)
	require.Equal(t, hexutil.Uint64(types.PopPayoutTxType), got.Type)
	require.Equal(t, types.PoPPayoutSenderAddress, got.From, "From must be the hardcoded 0x7D consensus sender")
	require.Equal(t, hexutil.Uint64(nonce), got.Nonce, "Nonce must come from the receipt's PoPPayoutNonce")
	require.Equal(t, (*hexutil.Big)(big.NewInt(0)), got.GasPrice)
	require.Equal(t, (*hexutil.Big)(big.NewInt(0)), got.V)
	require.Equal(t, gov, *got.To)
	require.Equal(t, hexutil.Uint64(tx.Gas()), got.Gas)

	// Negative control: a LEGACY tx carrying the same receipt must use its OWN nonce, not the receipt's PoP nonce.
	legacyTo := common.HexToAddress("0x00000000000000000000000000000000000000aa")
	legacy := types.NewTx(&types.LegacyTx{Nonce: 3, GasPrice: big.NewInt(1), Gas: 21000, To: &legacyTo, Value: big.NewInt(0)})
	gotLegacy := newRPCTransaction(legacy, common.Hash{}, 12, 0, 1, big.NewInt(0), params.OptimismTestConfig, receipt)
	require.Equal(t, hexutil.Uint64(3), gotLegacy.Nonce, "a legacy tx must use its own nonce, not the receipt's PoP nonce")

	// nil-safety: the 0x7D arm is guarded on receipt != nil && PoPPayoutNonce != nil; both fall back to tx nonce (0).
	gotNilReceipt := newRPCTransaction(tx, common.Hash{}, 12, 0, 1, big.NewInt(0), params.OptimismTestConfig, nil)
	require.Equal(t, hexutil.Uint64(0), gotNilReceipt.Nonce, "nil receipt -> fall back to tx nonce")
	gotNilNonce := newRPCTransaction(tx, common.Hash{}, 12, 0, 1, big.NewInt(0), params.OptimismTestConfig, &types.Receipt{})
	require.Equal(t, hexutil.Uint64(0), gotNilNonce.Nonce, "nil PoPPayoutNonce -> fall back to tx nonce")
}

// TestMarshalReceiptSystemTxNonce pins the eth_getTransactionReceipt marshalling of the per-type nonce fields for
// system txs (api.go MarshalReceipt ~1788): popPayoutNonce for 0x7D, btcAttributesDepositedNonce for 0x7C, gated on
// chainConfig.Optimism != nil + the tx-type predicate + a non-nil receipt nonce. This is a SEPARATE map-builder path
// from the core/types Receipt JSON round-trip and from newRPCTransaction (eth_getTransactionByHash); a mutant dropping
// either field assignment survives all of those. Corpus-free (in-memory tx + receipt + OptimismTestConfig).
func TestMarshalReceiptSystemTxNonce(t *testing.T) {
	signer := types.LatestSignerForChainID(big.NewInt(1))
	gov := common.HexToAddress("0x4200000000000000000000000000000000000042")
	btcInner, err := types.MakeBtcAttributesDepositedTx(&chainhash.Hash{0x01}, nil)
	require.NoError(t, err)
	nPop, nBtc := uint64(13), uint64(9)

	for _, tc := range []struct {
		name    string
		tx      *types.Transaction
		receipt *types.Receipt
		field   string
		nonce   uint64
	}{
		{"pop-0x7D", types.NewTx(&types.PopPayoutTx{To: &gov, Gas: 50_000, Data: []byte("pop")}),
			&types.Receipt{Status: types.ReceiptStatusSuccessful, CumulativeGasUsed: 1, PoPPayoutNonce: &nPop}, "popPayoutNonce", 13},
		{"btcattr-0x7C", types.NewTx(btcInner),
			&types.Receipt{Status: types.ReceiptStatusSuccessful, CumulativeGasUsed: 1, BtcAttributesDepositedNonce: &nBtc}, "btcAttributesDepositedNonce", 9},
	} {
		t.Run(tc.name, func(t *testing.T) {
			tc.receipt.TxHash = tc.tx.Hash()
			fields := MarshalReceipt(tc.receipt, common.Hash{}, 12, signer, tc.tx, 0, params.OptimismTestConfig)
			v, ok := fields[tc.field]
			require.True(t, ok, "MarshalReceipt must surface %s for the system tx", tc.field)
			require.Equal(t, hexutil.Uint64(tc.nonce), v, "%s must equal the receipt's per-type nonce", tc.field)
		})
	}

	// Negative control: a LEGACY tx whose receipt carries BOTH system nonces must surface NEITHER field — each is
	// gated on the tx-type predicate. Kills a mutant dropping the IsPopPayoutTx/IsBtcAttributesDepositedTx guard.
	legacy := types.NewTx(&types.LegacyTx{Nonce: 1, GasPrice: big.NewInt(1), Gas: 21000, To: &gov, Value: big.NewInt(0)})
	legacyReceipt := &types.Receipt{Status: types.ReceiptStatusSuccessful, CumulativeGasUsed: 1, PoPPayoutNonce: &nPop, BtcAttributesDepositedNonce: &nBtc, TxHash: legacy.Hash()}
	lf := MarshalReceipt(legacyReceipt, common.Hash{}, 12, signer, legacy, 0, params.OptimismTestConfig)
	require.NotContains(t, lf, "popPayoutNonce", "a legacy tx receipt must NOT surface popPayoutNonce")
	require.NotContains(t, lf, "btcAttributesDepositedNonce", "a legacy tx receipt must NOT surface btcAttributesDepositedNonce")

	// nil-nonce control: a 0x7D tx whose receipt has a NIL PoPPayoutNonce must NOT surface the field — the != nil
	// guard in MarshalReceipt is load-bearing (without it the field would leak or nil-deref).
	popNoNonce := types.NewTx(&types.PopPayoutTx{To: &gov, Gas: 50_000, Data: []byte("pop")})
	nf := MarshalReceipt(&types.Receipt{Status: types.ReceiptStatusSuccessful, CumulativeGasUsed: 1, TxHash: popNoNonce.Hash()},
		common.Hash{}, 12, signer, popNoNonce, 0, params.OptimismTestConfig)
	require.NotContains(t, nf, "popPayoutNonce", "a system tx with a nil per-type nonce must NOT surface the field")
}
