// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

// Transaction-level wire envelope for the PoP payout (0x7D) typed tx — the decodeTyped/MarshalBinary path that
// block import, p2p relay, and freezer storage use. The existing pop_payout_tx_test.go exercises ONLY the inner
// tx.encode()/tx.decode(); a field reorder of {To,Gas,Data} or a broken rlp:"nil" tag re-encodes/re-decodes
// self-consistently at the inner level and survives it, but breaks the wrapper round-trip and the golden wire bytes.
// Mirrors btc_attributes_envelope_test.go for 0x7C.

import (
	"bytes"
	"encoding/hex"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/stretchr/testify/require"
)

func TestPopPayoutTxEnvelopeRoundTrip(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	tx := NewTx(&PopPayoutTx{To: &to, Gas: 1_000_000, Data: []byte{0xc9, 0x4f}})

	bin, err := tx.MarshalBinary()
	require.NoError(t, err)
	require.NotEmpty(t, bin)
	require.Equal(t, byte(PopPayoutTxType), bin[0], "the typed envelope must carry the 0x7D prefix byte")

	utx := new(Transaction)
	require.NoError(t, utx.UnmarshalBinary(bin), "the 0x7D typed envelope must decode (decodeTyped case)")
	require.Equal(t, uint8(PopPayoutTxType), utx.Type())
	require.Equal(t, tx.Gas(), utx.Gas())
	require.Equal(t, tx.To(), utx.To(), "the To pointer must round-trip")
	require.True(t, bytes.Equal(tx.Data(), utx.Data()), "the data must round-trip byte-for-byte")

	// Idempotence: re-encoding the decoded tx reproduces the exact wire bytes.
	again, err := utx.MarshalBinary()
	require.NoError(t, err)
	require.True(t, bytes.Equal(bin, again), "re-marshaling a decoded 0x7D tx must reproduce the wire bytes")
}

// TestPopPayoutTxEnvelopeNilTo pins the rlp:"nil" tag on To: a nil To round-trips as nil (encoded as the 0x80 empty
// item), not a zero address.
func TestPopPayoutTxEnvelopeNilTo(t *testing.T) {
	tx := NewTx(&PopPayoutTx{To: nil, Gas: 1_000_000, Data: []byte{0xc9, 0x4f}})
	bin, err := tx.MarshalBinary()
	require.NoError(t, err)
	utx := new(Transaction)
	require.NoError(t, utx.UnmarshalBinary(bin))
	require.Nil(t, utx.To(), "a nil To must round-trip as nil (rlp:\"nil\" tag)")
	require.True(t, bytes.Equal([]byte{0xc9, 0x4f}, utx.Data()))
}

// TestPopPayoutTxEnvelopeTruncatedDecodeErrors: a malformed 0x7D envelope is REJECTED with an error, never a panic.
func TestPopPayoutTxEnvelopeTruncatedDecodeErrors(t *testing.T) {
	var err error
	require.NotPanics(t, func() {
		err = new(Transaction).UnmarshalBinary([]byte{byte(PopPayoutTxType), 0x01, 0x02, 0x03})
	}, "a truncated 0x7D envelope must not panic")
	require.Error(t, err, "a truncated 0x7D envelope must decode-error, not silently succeed")
	require.Contains(t, err.Error(), "rlp:", "the decode error must originate from the RLP decoder, not a higher-level path")
}

// TestPopPayoutTxEnvelopeRejectTrailingBytes: a well-formed 0x7D envelope with trailing bytes is rejected
// (canonical-encoding invariant; rlp.DecodeBytes rejects more-than-one-value).
func TestPopPayoutTxEnvelopeRejectTrailingBytes(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	bin, err := NewTx(&PopPayoutTx{To: &to, Gas: 1_000_000, Data: []byte{0xc9, 0x4f}}).MarshalBinary()
	require.NoError(t, err)
	require.NoError(t, new(Transaction).UnmarshalBinary(bin))

	malformed := append(append([]byte{}, bin...), 0x01, 0x02, 0x03, 0x04)
	var derr error
	require.NotPanics(t, func() { derr = new(Transaction).UnmarshalBinary(malformed) })
	require.ErrorIs(t, derr, rlp.ErrMoreThanOneValue, "a 0x7D envelope with trailing bytes must be rejected by the canonical-encoding guard")
}

// TestPopPayoutTxEnvelopeGolden freezes the EXACT wire bytes of the 0x7D envelope (Data is arbitrary bytes, so the
// golden is unconditionally stable). A field reorder in the {To,Gas,Data} RLP struct silently changes the layout and
// survives the symmetric round-trip tests; this golden catches it.
func TestPopPayoutTxEnvelopeGolden(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	bin, err := NewTx(&PopPayoutTx{To: &to, Gas: 1_000_000, Data: []byte{0xc9, 0x4f}}).MarshalBinary()
	require.NoError(t, err)
	require.Equal(t, "7ddc944200000000000000000000000000000000000042830f424082c94f", hex.EncodeToString(bin),
		"the 0x7D typed-envelope wire layout (type || rlp[To,Gas,Data]) must be stable")

	nilBin, err := NewTx(&PopPayoutTx{To: nil, Gas: 1_000_000, Data: []byte{0xc9, 0x4f}}).MarshalBinary()
	require.NoError(t, err)
	require.Equal(t, "7dc880830f424082c94f", hex.EncodeToString(nilBin),
		"nil-To must encode the 0x80 empty item (rlp:\"nil\")")
}
