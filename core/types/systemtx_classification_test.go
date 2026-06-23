// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

// The complete (IsSystemTx, IsZeroDAFootprintTx) classification matrix across every tx type. Individual spot-checks
// pin 0x7C/0x7D; this table pins the FULL cross-type contract so a per-type mis-classification — a standard tx wrongly
// flagged system or zero-DA (mis-billing L1 fees / skipping gas metering), or a system tx losing its flag — is caught.
// IsZeroDAFootprintTx = IsDepositTx||IsPopPayoutTx||IsBtcAttributesDepositedTx; IsSystemTx = deposit-with-system-flag.

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/holiman/uint256"
	"github.com/stretchr/testify/require"
)

func TestTransactionTypeClassificationMatrix(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	btcInner, err := MakeBtcAttributesDepositedTx(&chainhash.Hash{0x01}, nil)
	require.NoError(t, err)

	for _, tc := range []struct {
		name       string
		inner      TxData
		wantSystem bool
		wantZeroDA bool
	}{
		{"legacy", &LegacyTx{Nonce: 1, GasPrice: big.NewInt(1), Gas: 21000, To: &to, Value: big.NewInt(0)}, false, false},
		{"accesslist", &AccessListTx{ChainID: big.NewInt(1), Gas: 21000, GasPrice: big.NewInt(1), To: &to, Value: big.NewInt(0)}, false, false},
		{"dynamicfee", &DynamicFeeTx{ChainID: big.NewInt(1), Gas: 21000, GasFeeCap: big.NewInt(1), GasTipCap: big.NewInt(1), To: &to, Value: big.NewInt(0)}, false, false},
		{"blob", &BlobTx{ChainID: uint256.NewInt(1), Gas: 21000, GasFeeCap: uint256.NewInt(1), GasTipCap: uint256.NewInt(1), Value: uint256.NewInt(0), To: to, BlobFeeCap: uint256.NewInt(1)}, false, false},
		{"setcode", &SetCodeTx{ChainID: uint256.NewInt(1), Gas: 21000, GasFeeCap: uint256.NewInt(1), GasTipCap: uint256.NewInt(1), Value: uint256.NewInt(0), To: to}, false, false},
		{"pop-0x7D", &PopPayoutTx{To: &to, Gas: 50000, Data: []byte("p")}, false, true},
		{"btcattr-0x7C", btcInner, false, true},
		{"deposit-nonsys-0x7E", &DepositTx{From: common.HexToAddress("0xde"), To: &to, Value: big.NewInt(0), Gas: 21000, IsSystemTransaction: false}, false, true},
		{"deposit-sys-0x7E", &DepositTx{From: common.HexToAddress("0xde"), To: &to, Value: big.NewInt(0), Gas: 21000, IsSystemTransaction: true}, true, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			tx := NewTx(tc.inner)
			require.Equal(t, tc.wantSystem, tx.IsSystemTx(), "%s IsSystemTx", tc.name)
			require.Equal(t, tc.wantZeroDA, tx.IsZeroDAFootprintTx(), "%s IsZeroDAFootprintTx", tc.name)
		})
	}
}
