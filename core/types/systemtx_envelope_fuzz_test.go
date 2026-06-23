// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

// Fuzz coverage for the hVM/op system-tx WIRE ENVELOPE (Transaction.MarshalBinary/UnmarshalBinary via decodeTyped)
// for 0x7C (BtcAttr), 0x7D (PoP) and 0x7E (deposit). The calldata layer (BtcAttributesDepositData) is fuzzed
// elsewhere; the envelope decode was only covered by hand-written round-trip/anti-case tests. Corpus-free, deterministic.

import (
	"bytes"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

// FuzzSystemTxEnvelopeRoundTrip: any system tx built from fuzzed fields must survive MarshalBinary -> UnmarshalBinary
// byte-for-byte (type/gas/data preserved) and re-marshal idempotently. Catches an asymmetric encode/decode change.
func FuzzSystemTxEnvelopeRoundTrip(f *testing.F) {
	f.Add(uint64(0), []byte(nil), uint8(0))
	f.Add(uint64(1_000_000), []byte{0x01, 0x02, 0x03}, uint8(1))
	f.Add(uint64(50_000), []byte{0xff}, uint8(2))
	f.Fuzz(func(t *testing.T, gas uint64, data []byte, sel uint8) {
		to := common.BytesToAddress([]byte{0x42})
		var inner TxData
		switch sel % 3 {
		case 0:
			inner = &BtcAttributesDepositedTx{To: &to, Gas: gas, Data: data}
		case 1:
			inner = &PopPayoutTx{To: &to, Gas: gas, Data: data}
		default:
			inner = &DepositTx{From: common.BytesToAddress([]byte{0xde}), To: &to, Value: big.NewInt(0), Gas: gas, Data: data}
		}
		tx := NewTx(inner)
		bin, err := tx.MarshalBinary()
		if err != nil {
			return
		}
		var got Transaction
		require.NoError(t, got.UnmarshalBinary(bin), "a freshly-marshaled system tx must decode")
		require.Equal(t, tx.Type(), got.Type())
		require.Equal(t, tx.Gas(), got.Gas())
		require.True(t, bytes.Equal(tx.Data(), got.Data()))
		again, err := got.MarshalBinary()
		require.NoError(t, err)
		require.True(t, bytes.Equal(bin, again), "re-marshal must be idempotent")
	})
}

// FuzzSystemTxEnvelopeDecode: UnmarshalBinary on ARBITRARY bytes (incl. system-tx type prefixes) must never panic —
// only return data or an error. Block import / p2p / freezer feed this path untrusted bytes.
func FuzzSystemTxEnvelopeDecode(f *testing.F) {
	f.Add([]byte{BtcAttributesDepositedTxType})
	f.Add([]byte{PopPayoutTxType, 0x01})
	f.Add([]byte{DepositTxType, 0xc0})
	f.Add([]byte{0x7c, 0xc4, 0x80, 0x80, 0x80})
	f.Fuzz(func(t *testing.T, raw []byte) {
		var tx Transaction
		_ = tx.UnmarshalBinary(raw) // property: never panics on arbitrary input
	})
}
