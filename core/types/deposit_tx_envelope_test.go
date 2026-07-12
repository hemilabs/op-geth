// Copyright 2024 The go-ethereum Authors
// Copyright 2026 Hemi Labs, Inc.
// This file is part of the go-ethereum library.

package types

// Transaction-level wire envelope for the deposit (0x7E) system tx — the decodeTyped/MarshalBinary path used by
// block import, p2p relay, and freezer storage. DepositTx has TWO rlp:"nil" fields (To and Mint); no test pinned
// the wrapper-level round-trip, the nil-To/nil-Mint behavior, or trailing-byte rejection. Mirrors the 0x7C/0x7D
// envelope tests for the third system-tx sibling.

import (
	"bytes"
	"encoding/hex"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

func TestDepositTxEnvelopeRoundTrip(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	tx := NewTx(&DepositTx{
		SourceHash: common.HexToHash("0xabc"), From: common.HexToAddress("0xde"),
		To: &to, Mint: big.NewInt(12345), Value: big.NewInt(7), Gas: 50_000, Data: []byte{0x01, 0x02},
	})
	bin, err := tx.MarshalBinary()
	require.NoError(t, err)
	require.Equal(t, byte(DepositTxType), bin[0], "the typed envelope must carry the 0x7E prefix byte")

	utx := new(Transaction)
	require.NoError(t, utx.UnmarshalBinary(bin), "the 0x7E typed envelope must decode (decodeTyped case)")
	require.Equal(t, uint8(DepositTxType), utx.Type())
	require.Equal(t, tx.Gas(), utx.Gas())
	require.Equal(t, tx.To(), utx.To())
	require.True(t, bytes.Equal(tx.Data(), utx.Data()))
	require.Equal(t, 0, tx.Value().Cmp(utx.Value()), "Value must round-trip")
	require.Equal(t, 0, tx.Mint().Cmp(utx.Mint()), "Mint must round-trip")

	again, err := utx.MarshalBinary()
	require.NoError(t, err)
	require.True(t, bytes.Equal(bin, again), "re-marshaling a decoded 0x7E tx must reproduce the wire bytes")
}

// TestDepositTxEnvelopeNilToAndMint pins the two rlp:"nil" fields of DepositTx. A nil To round-trips as nil. A nil
// Mint, however, is NOT nil-preserving: the rlp:"nil" empty decodes to a zero-valued (non-nil) big.Int. Pin that
// deterministic behavior (the contract downstream Mint() consumers see), not an assumed nil round-trip.
func TestDepositTxEnvelopeNilToAndMint(t *testing.T) {
	tx := NewTx(&DepositTx{From: common.HexToAddress("0xde"), To: nil, Mint: nil, Value: big.NewInt(0), Gas: 50_000})
	bin, err := tx.MarshalBinary()
	require.NoError(t, err)
	utx := new(Transaction)
	require.NoError(t, utx.UnmarshalBinary(bin))
	require.Nil(t, utx.To(), "a nil To must round-trip as nil (rlp:\"nil\")")
	require.NotNil(t, utx.Mint(), "a nil Mint decodes to a non-nil zero big.Int")
	require.Zero(t, utx.Mint().Sign(), "a nil Mint round-trips as a zero-valued Mint (deterministic)")
}

func TestDepositTxEnvelopeTruncatedDecodeErrors(t *testing.T) {
	var err error
	require.NotPanics(t, func() { err = new(Transaction).UnmarshalBinary([]byte{byte(DepositTxType), 0x01, 0x02}) },
		"a truncated 0x7E envelope must not panic")
	require.Error(t, err, "a truncated 0x7E envelope must decode-error")
	require.Contains(t, err.Error(), "rlp:", "the decode error must originate from the RLP decoder")
}

func TestDepositTxEnvelopeRejectTrailingBytes(t *testing.T) {
	to := common.HexToAddress("0x42")
	bin, err := NewTx(&DepositTx{From: common.HexToAddress("0xde"), To: &to, Value: big.NewInt(0), Gas: 50_000}).MarshalBinary()
	require.NoError(t, err)
	require.NoError(t, new(Transaction).UnmarshalBinary(bin))
	malformed := append(append([]byte{}, bin...), 0x01, 0x02, 0x03, 0x04)
	var derr error
	require.NotPanics(t, func() { derr = new(Transaction).UnmarshalBinary(malformed) })
	require.Error(t, derr, "a 0x7E envelope with trailing bytes must be rejected")
}

// TestDepositTxEnvelopeGolden freezes the EXACT 0x7E wire layout — the sibling golden that the 0x7C/0x7D envelope
// tests have but this file omitted. The round-trip above is symmetric (encode->decode->compare) and survives a field
// reorder of the 8-field {SourceHash,From,To,Mint,Value,Gas,IsSystemTransaction,Data} RLP struct; this golden does
// not. The nil-To/nil-Mint case exercises both rlp:"nil" fields, and the full case pins IsSystemTransaction=true
// (which the round-trip never asserts).
func TestDepositTxEnvelopeGolden(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	full, err := NewTx(&DepositTx{
		SourceHash: common.HexToHash("0xabc"), From: common.HexToAddress("0xde"),
		To: &to, Mint: big.NewInt(12345), Value: big.NewInt(7), Gas: 50000, IsSystemTransaction: true, Data: []byte{0x01},
	}).MarshalBinary()
	require.NoError(t, err)
	require.Equal(t, "7ef854a00000000000000000000000000000000000000000000000000000000000000abc9400000000000000000000000000000000000000de9442000000000000000000000000000000000000428230390782c3500101",
		hex.EncodeToString(full), "the 0x7E typed-envelope wire layout must be stable (a {SourceHash..Data} field reorder is caught here)")

	nilToMint, err := NewTx(&DepositTx{
		SourceHash: common.HexToHash("0xabc"), From: common.HexToAddress("0xde"),
		To: nil, Mint: nil, Value: big.NewInt(7), Gas: 50000, Data: []byte{0x01},
	}).MarshalBinary()
	require.NoError(t, err)
	require.Equal(t, "7ef83ea00000000000000000000000000000000000000000000000000000000000000abc9400000000000000000000000000000000000000de80800782c3508001",
		hex.EncodeToString(nilToMint), "nil To and nil Mint must each encode the 0x80 empty item (rlp:\"nil\")")
}
