// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

import (
	"bytes"
	"encoding/json"
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/holiman/uint256"
	"github.com/stretchr/testify/require"
)

// The complete (IsSystemTx, IsZeroDAFootprintTx) classification matrix across every tx type. Individual spot-checks
// pin 0x7C/0x7D; this table pins the FULL cross-type contract so a per-type mis-classification — a standard tx wrongly
// flagged system or zero-DA (mis-billing L1 fees / skipping gas metering), or a system tx losing its flag — is caught.
// IsZeroDAFootprintTx = IsDepositTx||IsPopPayoutTx||IsBtcAttributesDepositedTx; IsSystemTx = deposit-with-system-flag.
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

// Fuzz coverage for the hVM/op system-tx WIRE ENVELOPE (Transaction.MarshalBinary/UnmarshalBinary via decodeTyped)
// for 0x7C (BtcAttr), 0x7D (PoP) and 0x7E (deposit). The calldata layer (BtcAttributesDepositData) is fuzzed
// elsewhere; the envelope decode was only covered by hand-written round-trip/anti-case tests. Corpus-free, deterministic.
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

// System txs (0x7C BtcAttr, 0x7D PoP) are force-included and NEVER signed. The signer special-cases Sender() to
// return their hardcoded identity, but SignatureValues must still REFUSE them (ErrTxTypeNotSupported via the
// supportsType gate at transaction_signing.go ~298). No test pinned this rejection — a mutant adding 0x7C/0x7D to
// supportsType would let a caller "sign" a system tx and would survive the suite.
func TestSignatureValuesRejectsSystemTxs(t *testing.T) {
	signer := LatestSignerForChainID(big.NewInt(1))
	sig := make([]byte, 65) // a well-formed-length signature; rejection happens before it is decoded

	btcInner, err := MakeBtcAttributesDepositedTx(&chainhash.Hash{0x01}, nil)
	require.NoError(t, err)
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := NewTx(&PopPayoutTx{To: &to, Gas: 50_000, Data: []byte("pop")})

	for _, tc := range []struct {
		name string
		tx   *Transaction
	}{
		{"btcattr-0x7C", NewTx(btcInner)},
		{"pop-0x7D", popTx},
	} {
		_, _, _, err := signer.SignatureValues(tc.tx, sig)
		require.ErrorIs(t, err, ErrTxTypeNotSupported, "%s must be unsignable (SignatureValues rejects it)", tc.name)
	}
}

// Transaction.Size() for the three force-included system txs (0x7C/0x7D/0x7E). Size() adds 1 for the type byte gated
// on `tx.Type() != LegacyTxType`; TestTransactionSizes only covers 0x00-0x02, so a mutant narrowing that gate to the
// standard EIP-2718 range (<= 0x04) would drop the +1 for system types (all > 0x04) yet survive the suite. Size()
// feeds mempool admission / DA accounting and these txs appear in every hVM block.
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

// The 0x7C (BtcAttributesDeposited) and 0x7D (PoPPayout) UnmarshalJSON arms dereference *dec.Input, so a missing
// "input" field must be rejected with a clean "missing required field 'input'" error (as every other tx type does)
// rather than nil-deref panicking. Block import / RPC decode must never panic on malformed JSON.
func TestSystemTxUnmarshalJSONMissingInput(t *testing.T) {
	for _, tc := range []struct {
		name string
		json string
	}{
		{"btcattr-0x7c", `{"type":"0x7c","to":"0x8888888888888888888888888888888888888888","gas":"0xf4240","gasPrice":"0x0"}`},
		{"poppayout-0x7d", `{"type":"0x7d","to":"0x4200000000000000000000000000000000000042","gas":"0xc350","gasPrice":"0x0"}`},
	} {
		t.Run(tc.name, func(t *testing.T) {
			var tx Transaction
			var err error
			require.NotPanics(t, func() { err = json.Unmarshal([]byte(tc.json), &tx) },
				"a %s tx JSON without 'input' must not panic", tc.name)
			require.Error(t, err, "missing 'input' must be a decode error")
			require.Contains(t, err.Error(), "input", "the error must name the missing 'input' field")
		})
	}
}

// A forced system tx (0x7C BtcAttr, 0x7D PoP) carries NO access list and a ZERO signature — these txs are never
// signed and their sender is the hardcoded identity. This pins the zero-contract of the inner
// accessList()/rawSignatureValues() stubs via the Transaction accessors.
func TestSystemTxZeroSignatureAndAccessList(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	btcInner, err := MakeBtcAttributesDepositedTx(&chainhash.Hash{0x01}, nil)
	require.NoError(t, err)
	for _, tx := range []*Transaction{
		NewTx(btcInner),
		NewTx(&PopPayoutTx{To: &to, Gas: 50_000, Data: []byte("pop")}),
	} {
		require.Nil(t, tx.AccessList(), "a system tx must carry no access list")
		v, r, s := tx.RawSignatureValues()
		require.Zero(t, v.Sign(), "system-tx signature V must be zero")
		require.Zero(t, r.Sign(), "system-tx signature R must be zero")
		require.Zero(t, s.Sign(), "system-tx signature S must be zero")
	}
}
