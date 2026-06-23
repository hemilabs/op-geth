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

package types

// Transaction-level typed-envelope RLP round-trip for the BtcAttributesDeposited (0x7C) tx type — the WIRE/DB form
// for these force-included consensus txs in every hVM block body (block import, freezer storage, p2p relay all
// RLP-decode the body and dispatch to decodeTyped case 0x7C). All existing BtcAttr tests exercise only the CALLDATA
// layer (BtcAttributesDepositData marshal) or Sender identity, building the tx via NewTx on in-memory objects that
// never traverse RLP; the generic coding suites structurally exclude 0x7C (its sigHash panics). So the inner
// encode/decode (the {To rlp:"nil", Gas, Data} struct) and the decodeTyped 0x7C dispatch have NO coverage — a field
// reorder, a broken rlp:"nil" tag, or a wrong/deleted decode case would corrupt the consensus tx while staying green.

import (
	"bytes"
	"encoding/hex"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

func TestBtcAttrTxEnvelopeRoundTrip(t *testing.T) {
	tip := chainhash.Hash{0x01, 0x02, 0x03}
	hdrs := []wire.BlockHeader{
		{Version: 1, Bits: 0x207fffff, Nonce: 11},
		{Version: 1, Bits: 0x207fffff, Nonce: 22},
	}
	inner, err := MakeBtcAttributesDepositedTx(&tip, hdrs)
	require.NoError(t, err)
	tx := NewTx(inner)

	bin, err := tx.MarshalBinary()
	require.NoError(t, err)
	require.NotEmpty(t, bin)
	require.Equal(t, byte(BtcAttributesDepositedTxType), bin[0], "the typed-envelope must carry the 0x7C prefix byte")

	// Decode the wire form back into a Transaction and assert every field survived the inner RLP round-trip.
	utx := new(Transaction)
	require.NoError(t, utx.UnmarshalBinary(bin), "the 0x7C typed envelope must decode (decodeTyped case)")
	require.Equal(t, uint8(BtcAttributesDepositedTxType), utx.Type())
	require.Equal(t, tx.Gas(), utx.Gas())
	require.Equal(t, tx.To(), utx.To(), "the To pointer must round-trip")
	require.True(t, bytes.Equal(tx.Data(), utx.Data()), "the calldata must round-trip byte-for-byte")

	// The full nest survives: re-parse the decoded tx's calldata and confirm the canonical tip + headers.
	var bad BtcAttributesDepositData
	require.NoError(t, bad.UnmarshalBinary(utx.Data()))
	require.Equal(t, [BitcoinHashLengthBytes]byte(tip), bad.CanonicalTip)
	require.Len(t, bad.Headers, 2)

	// Idempotence: re-encoding the decoded tx reproduces the exact wire bytes.
	again, err := utx.MarshalBinary()
	require.NoError(t, err)
	require.True(t, bytes.Equal(bin, again), "re-marshaling a decoded 0x7C tx must reproduce the wire bytes")
}

// TestBtcAttrTxEnvelopeNilTo pins the `rlp:"nil"` tag on the To pointer: a nil To must round-trip as nil (not a
// zero address), exercising the encode/decode path the canonical (non-nil To) case does not.
func TestBtcAttrTxEnvelopeNilTo(t *testing.T) {
	data, err := (&BtcAttributesDepositData{CanonicalTip: chainhash.Hash{0xAA}}).MarshalBinary()
	require.NoError(t, err)
	tx := NewTx(&BtcAttributesDepositedTx{To: nil, Gas: 1_000_000, Data: data})

	bin, err := tx.MarshalBinary()
	require.NoError(t, err)
	utx := new(Transaction)
	require.NoError(t, utx.UnmarshalBinary(bin))
	require.Nil(t, utx.To(), "a nil To must round-trip as nil (rlp:\"nil\" tag)")
	require.True(t, bytes.Equal(data, utx.Data()))
}

// TestBtcAttrTxEnvelopeTruncatedDecodeErrors pins that a malformed 0x7C envelope is REJECTED with an error, never a
// panic — block import must not crash on a corrupt force-included tx on the wire.
func TestBtcAttrTxEnvelopeTruncatedDecodeErrors(t *testing.T) {
	var err error
	require.NotPanics(t, func() {
		err = new(Transaction).UnmarshalBinary([]byte{byte(BtcAttributesDepositedTxType), 0x01, 0x02, 0x03})
	}, "a truncated 0x7C envelope must not panic")
	require.Error(t, err, "a truncated 0x7C envelope must decode-error, not silently succeed")
	require.Contains(t, err.Error(), "rlp:", "the decode error must originate from the RLP decoder")
}

// TestBtcAttrTxEnvelopeRejectTrailingBytes pins the CANONICAL-encoding invariant for the 0x7C envelope: a
// well-formed envelope with EXTRA trailing bytes appended must be rejected, not silently accepted (which would let
// two distinct wire sequences decode to the same tx). The inner decode delegates to rlp.DecodeBytes, which rejects
// trailing data with ErrMoreThanOneValue. The existing truncated-envelope test hits a DIFFERENT branch (malformed
// list shape, "expected input list"); the trailing-data strict-decode guard was unpinned for the tx envelope (the
// receipt path pins the equivalent at receipt_test.go). Block import / freezer / p2p body decode all reach this path.
func TestBtcAttrTxEnvelopeRejectTrailingBytes(t *testing.T) {
	tip := chainhash.Hash{0x01, 0x02, 0x03}
	inner, err := MakeBtcAttributesDepositedTx(&tip, []wire.BlockHeader{{Version: 1, Bits: 0x207fffff, Nonce: 11}})
	require.NoError(t, err)
	bin, err := NewTx(inner).MarshalBinary()
	require.NoError(t, err)

	// Precondition: the unmodified envelope decodes cleanly.
	require.NoError(t, new(Transaction).UnmarshalBinary(bin))

	malformed := append(append([]byte{}, bin...), 0x01, 0x02, 0x03, 0x04)
	var derr error
	require.NotPanics(t, func() {
		derr = new(Transaction).UnmarshalBinary(malformed)
	}, "trailing bytes on a 0x7C envelope must not panic")
	require.Error(t, derr, "a 0x7C envelope with trailing bytes must be rejected (canonical-encoding invariant)")
}

// TestBtcAttrTxTypeConstantPinned is a cross-repo coordination tripwire. BtcAttributesDepositedTxType == 0x7C is a
// WIRE constant the op-stack fork and op-geth must agree on, and decodeTyped/receipt/marshalling/signing all branch
// on it. Every other test references the constant SYMBOLICALLY, so a silent value change (e.g. to 0x7B) or a future
// rebase relocating another typed tx into 0x7C would survive them. Pin the LITERAL value and registry non-collision.
func TestBtcAttrTxTypeConstantPinned(t *testing.T) {
	require.Equal(t, byte(0x7C), byte(BtcAttributesDepositedTxType), "the BtcAttr consensus tx wire prefix must be exactly 0x7C")

	// Every registered typed-tx prefix must be distinct — a collision would route the consensus tx to the wrong
	// decoder or shadow it.
	all := []byte{
		LegacyTxType, AccessListTxType, DynamicFeeTxType, BlobTxType, SetCodeTxType,
		BtcAttributesDepositedTxType, PopPayoutTxType, DepositTxType,
	}
	seen := map[byte]bool{}
	for _, ty := range all {
		require.Falsef(t, seen[ty], "tx type prefix 0x%02x collides with another registered type", ty)
		seen[ty] = true
	}
	require.Len(t, seen, len(all), "all registered tx type prefixes must be distinct")
}

// TestBtcAttrTxEnvelopeGolden freezes the EXACT wire bytes of the 0x7C typed envelope. TestBtcAttrTxEnvelopeRoundTrip
// and TestBtcAttrTxEnvelopeNilTo are SYMMETRIC checks (decode==original, idempotent re-marshal) — a field reorder in
// the RLP struct {To, Gas, Data} re-encodes/re-decodes self-consistently and survives them, silently changing the
// on-the-wire layout. The BtcAttr CALLDATA layer is golden-pinned (TestBtcAttributesDepositData*); the tx envelope
// was not. Uses a raw fixed Data literal (no btcd-version-dependent serialized headers) so the golden is stable.
func TestBtcAttrTxEnvelopeGolden(t *testing.T) {
	addr := common.HexToAddress("0x8888888888888888888888888888888888888888")
	data := []byte{0xc9, 0x4f, 0x1c, 0xca, 0xde, 0xad, 0xbe, 0xef}

	withTo, err := NewTx(&BtcAttributesDepositedTx{To: &addr, Gas: 1000000, Data: data}).MarshalBinary()
	require.NoError(t, err)
	require.Equal(t, "7ce2948888888888888888888888888888888888888888830f424088c94f1ccadeadbeef",
		hex.EncodeToString(withTo), "the 0x7C envelope wire layout (prefix + RLP {To,Gas,Data}) must be byte-frozen")

	// nil-To must encode as the empty RLP string item (0x80), NOT a 20-byte zero address — the rlp:"nil" contract.
	nilTo, err := NewTx(&BtcAttributesDepositedTx{To: nil, Gas: 1000000, Data: data}).MarshalBinary()
	require.NoError(t, err)
	require.Equal(t, "7cce80830f424088c94f1ccadeadbeef", hex.EncodeToString(nilTo),
		"a nil To must serialize as the empty RLP item (rlp:\"nil\"), not a zero address")
}
