// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

// Transaction.Size() for the three force-included system txs (0x7C/0x7D/0x7E). Size() adds 1 for the type byte gated
// on `tx.Type() != LegacyTxType`; TestTransactionSizes only covers 0x00-0x02, so a mutant narrowing that gate to the
// standard EIP-2718 range (<= 0x04) would drop the +1 for system types (all > 0x04) yet survive the suite. Size()
// feeds mempool admission / DA accounting and these txs appear in every hVM block.

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

func TestSystemTxSizes(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	btcInner, err := MakeBtcAttributesDepositedTx(&chainhash.Hash{0x01, 0x02}, nil)
	require.NoError(t, err)

	for _, tc := range []struct {
		name  string
		inner TxData
	}{
		{"btcattr-0x7C", btcInner},
		{"pop-0x7D", &PopPayoutTx{To: &to, Gas: 50_000, Data: []byte{0xc9, 0x4f}}},
		{"deposit-0x7E", &DepositTx{From: common.HexToAddress("0xde"), To: &to, Mint: big.NewInt(7), Value: big.NewInt(0), Gas: 21_000, Data: []byte{0x01}}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			tx := NewTx(tc.inner)
			bin, err := tx.MarshalBinary()
			require.NoError(t, err)
			require.Greater(t, len(bin), 1, "anti-vacuity: a typed envelope is more than its 1-byte prefix")
			require.Equal(t, len(bin), int(tx.Size()), "Size must match the typed-envelope wire length (incl. the +1 type byte)")
			require.Equal(t, len(bin), int(tx.Size()), "cached Size must match")

			utx := new(Transaction)
			require.NoError(t, utx.UnmarshalBinary(bin))
			require.Equal(t, len(bin), int(utx.Size()), "unmarshalled Size must match")
			require.Equal(t, len(bin), int(utx.Size()), "cached unmarshalled Size must match")
		})
	}
}
