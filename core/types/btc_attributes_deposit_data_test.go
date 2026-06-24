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

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"errors"
	"io"
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/accounts/abi"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/stretchr/testify/require"
)

// Dual-commit consistency: processing an hVM block mutates BOTH the EVM state (the updateHvmState(bytes32,bytes[])
// call to the 0x8400 predeploy, decoded with the canonical Solidity/accounts/abi decoder, its state root part of the
// L2 block hash) AND the BTC view (BtcAttributesDepositData.UnmarshalBinary of the SAME tx.Data()). The two are
// independent parsers. Existing tests prove only MarshalBinary matches a hand-asserted golden and round-trips with
// its own UnmarshalBinary — nothing machine-checks the emitted bytes against the ABI decoder the EVM actually uses.
// A format change that kept the bespoke round-trip green but broke ABI-equivalence would make the predeploy and the
// view extract DIFFERENT (tip, headers), silently diverging EVM-recorded hVM state from the consensus BTC view.
func TestBtcAttrCalldataAbiEquivalence(t *testing.T) {
	bytes32T, err := abi.NewType("bytes32", "", nil)
	require.NoError(t, err)
	bytesArrT, err := abi.NewType("bytes[]", "", nil)
	require.NoError(t, err)
	args := abi.Arguments{{Type: bytes32T}, {Type: bytesArrT}}

	mkHdr := func(seed byte) [BitcoinHeaderLengthBytes]byte {
		var h [BitcoinHeaderLengthBytes]byte
		for i := range h {
			h[i] = seed + byte(i)
		}
		return h
	}

	for _, n := range []int{0, 1, 2, MaximumBtcHeadersInTx} {
		hdrs := make([][BitcoinHeaderLengthBytes]byte, n)
		for i := range hdrs {
			hdrs[i] = mkHdr(byte(i + 1))
		}
		tip := tipOf(byte(0x40 + n))
		data, err := (&BtcAttributesDepositData{CanonicalTip: tip, Headers: hdrs}).MarshalBinary()
		require.NoError(t, err)
		require.Equal(t, UpdateHvmStateFuncBytes4[:], data[:4], "selector prefix (%d headers)", n)

		// Decode the calldata with the SAME ABI decoder the 0x8400 predeploy uses.
		vals, err := args.UnpackValues(data[4:])
		require.NoErrorf(t, err, "the EVM ABI decoder must accept the emitted calldata (%d headers)", n)
		abiTip := vals[0].([32]byte)
		abiHdrs := vals[1].([][]byte)
		require.Equalf(t, [32]byte(tip), abiTip, "ABI-decoded canonical tip must equal the source (%d headers)", n)
		require.Lenf(t, abiHdrs, n, "ABI-decoded header count (%d headers)", n)
		for i := range hdrs {
			require.Equalf(t, hdrs[i][:], abiHdrs[i], "ABI-decoded header %d must be the exact 80 bytes the predeploy sees (%d headers)", i, n)
		}

		// And the view's bespoke parser must agree on the same bytes.
		var view BtcAttributesDepositData
		require.NoError(t, view.UnmarshalBinary(data))
		require.Equal(t, tip, view.CanonicalTip)
		require.Equal(t, hdrs, view.Headers)
	}

	// The view must be STRICTLY stronger than the ABI decoder: a bytes[] element of length != 80 is valid ABI (the
	// predeploy would decode a wrong-length header) but UnmarshalBinary must REJECT it — so the view can never apply
	// something the predeploy would silently accept as a header.
	shortPacked, err := args.Pack([32]byte(tipOf(0x99)), [][]byte{make([]byte, 79)})
	require.NoError(t, err)
	roundtrip, err := args.UnpackValues(shortPacked)
	require.NoError(t, err, "the ABI decoder accepts a 79-byte bytes[] element")
	require.Len(t, roundtrip[1].([][]byte)[0], 79)
	bad := append(append([]byte{}, UpdateHvmStateFuncBytes4[:]...), shortPacked...)
	require.Error(t, new(BtcAttributesDepositData).UnmarshalBinary(bad),
		"the view must REJECT a non-80-byte header the ABI decoder accepts (view is stricter than ABI)")
}

// The 0x7C BtcAttributesDeposited TX-LEVEL accessor contract the apply/fee/mempool paths rely on: zero
// gas/value/nonce/effective-price, fixed To, defensive-copied big.Int getters, and the unsupported sign operation
// PANICS (not silently zero). None of these were pinned at the Transaction level.
func TestBtcAttrTxAccessorContract(t *testing.T) {
	tip := chainhash.Hash{0x01, 0x02, 0x03}
	inner, err := MakeBtcAttributesDepositedTx(&tip, []wire.BlockHeader{{Version: 1, Bits: 0x207fffff, Nonce: 7}})
	require.NoError(t, err)
	tx := NewTx(inner)

	// Zero economic fields.
	require.Zero(t, tx.Value().Sign(), "Value is zero")
	require.Zero(t, tx.GasPrice().Sign(), "GasPrice is zero")
	require.Zero(t, tx.GasTipCap().Sign(), "GasTipCap is zero")
	require.Zero(t, tx.GasFeeCap().Sign(), "GasFeeCap is zero")
	require.Equal(t, uint64(0), tx.Nonce(), "Nonce is zero (set during execution)")

	// Structural fields pass through. Pin Gas to the hardcoded constructor constant (1M) rather than to inner.Gas
	// (a self-comparison: both sides resolve to the same field, so a constructor gas-value mutant would survive).
	require.Equal(t, uint64(1_000_000), tx.Gas(), "BtcAttributesDeposited must use the hardcoded 1M system-tx gas")
	require.Equal(t, inner.To, tx.To())
	require.True(t, bytes.Equal(inner.Data, tx.Data()))
	// Data must be DEFENSIVELY COPIED by the constructor's copy(): mutating the wrapped tx's Data must not affect the
	// original inner.Data. bytes.Equal alone passes even if both share one backing array, so mutate-and-recheck.
	d := tx.Data()
	require.NotEmpty(t, d, "anti-vacuity: Data must be non-empty for the mutation to be observable")
	innerSnapshot := append([]byte{}, inner.Data...)
	for i := range d {
		d[i] ^= 0xFF
	}
	require.Equal(t, innerSnapshot, inner.Data, "the constructor must defensively copy Data (no shared backing array)")

	// Defensive copy: the big.Int getters must not alias internal state.
	a, b := tx.GasPrice(), tx.GasPrice()
	a.SetInt64(99)
	require.Zero(t, b.Sign(), "GasPrice must return a fresh copy each call (no alias leak)")

	// Cost is zero (zero value + zero gas price) regardless of the large 1M gas limit.
	require.Greater(t, tx.Gas(), uint64(0), "anti-vacuity: a nonzero gas-price mutant would surface in Cost")
	require.Zero(t, tx.Cost().Sign(), "Cost is zero for a fee-free system tx")

	// EffectiveGasTip: zero with no base fee; below-base-fee with a positive base fee (gasFeeCap 0 < baseFee).
	gt, err := tx.EffectiveGasTip(nil)
	require.NoError(t, err)
	require.Zero(t, gt.Sign())
	_, err = tx.EffectiveGasTip(big.NewInt(1000))
	require.ErrorIs(t, err, ErrGasFeeCapTooLow, "a zero fee cap is below any positive base fee")

	// The unsupported sign operation must PANIC (reachable via Signer.Hash -> inner.sigHash), not silently return zero.
	require.Panics(t, func() { _ = LatestSignerForChainID(big.NewInt(1)).Hash(tx) },
		"signing a BtcAttr tx must panic (it is force-included, never signed)")
}

// TestMakeBtcAttributesDepositedTxToField pins that the CONSTRUCTOR MakeBtcAttributesDepositedTx sets To to the
// hardcoded consensus sender (BtcAttributesDepositedSenderAddress, 0x8888...). The accessor-contract test compares
// the constructor's output To against ITSELF (a wrapper pass-through), so a mutant changing the constructor's To
// assignment (e.g. to HvmStateAddress) survives it; the sender-identity tests build To manually. This pins the
// actual assignment line. Value comparison (Transaction.To() returns a fresh copy, so pointer-eq would not hold).
func TestMakeBtcAttributesDepositedTxToField(t *testing.T) {
	inner, err := MakeBtcAttributesDepositedTx(&chainhash.Hash{0x01}, nil)
	require.NoError(t, err)
	tx := NewTx(inner)
	require.NotNil(t, tx.To(), "the constructor must set a non-nil To")
	require.Equal(t, BtcAttributesDepositedSenderAddress, *tx.To(),
		"MakeBtcAttributesDepositedTx must set To = the hardcoded consensus sender (kills a constructor To-reassignment mutant)")
}

// Deterministic anti-cases for the BtcAttributesDeposited parser. The fuzz test only asserts "rejected OR
// canonical round-trip" — it never pins WHICH validation branch fires, and several branches (offset/length/
// padding guards) are unlikely to be hit reliably by random mutation. These pin each guard with an exact error
// oracle, plus the header-count cap boundary (30 accepted / 31 rejected).
func zeroHeaders(n int) [][BitcoinHeaderLengthBytes]byte {
	h := make([][BitcoinHeaderLengthBytes]byte, n)
	return h
}

// TestBtcAttributesDepositDataHeaderCountBoundary pins the consensus DoS/size cap: exactly MaximumBtcHeadersInTx
// (30) is accepted; one more is rejected. The fuzz oracle only checks accepted inputs honor the cap — it never
// proves 30 is legal or that 31 is refused, so a '>' -> '>=' or wrong-constant mutant survives it.
func TestBtcAttributesDepositDataHeaderCountBoundary(t *testing.T) {
	at, err := (&BtcAttributesDepositData{CanonicalTip: tipOf(1), Headers: zeroHeaders(MaximumBtcHeadersInTx)}).MarshalBinary()
	require.NoError(t, err)
	var ok BtcAttributesDepositData
	require.NoError(t, ok.UnmarshalBinary(at), "exactly %d headers must be accepted", MaximumBtcHeadersInTx)
	require.Len(t, ok.Headers, MaximumBtcHeadersInTx)

	// MarshalBinary has no cap, so it produces a 31-header blob; UnmarshalBinary must reject it.
	over, err := (&BtcAttributesDepositData{CanonicalTip: tipOf(1), Headers: zeroHeaders(MaximumBtcHeadersInTx + 1)}).MarshalBinary()
	require.NoError(t, err)
	var bad BtcAttributesDepositData
	err = bad.UnmarshalBinary(over)
	require.Error(t, err, "%d headers must be rejected", MaximumBtcHeadersInTx+1)
	require.Contains(t, err.Error(), "maximum of 30 BTC headers, but got 31")
}

// TestBtcAttributesDepositDataParserAntiCases mutates one field of a known-good 2-header blob per row and asserts
// the specific guard fires. Offsets are computed from the wire layout: sig(4) tip(32) initialOffset(32)
// numHeaders(32) then per-header offset words (32 each) then per-header [len(32)+header(96)] blocks.
func TestBtcAttributesDepositDataParserAntiCases(t *testing.T) {
	good, err := (&BtcAttributesDepositData{CanonicalTip: tipOf(7), Headers: zeroHeaders(2)}).MarshalBinary()
	require.NoError(t, err)

	const word = SmartContractArgumentByteLen  // 32
	initialOffsetWord := 4 + 32                // 36..67; value last byte 67
	numHeadersWord := initialOffsetWord + word // 68..99; padding 68..91, value 92..99
	offset0 := numHeadersWord + word           // 100..131
	offset1 := offset0 + word                  // 132..163; value last byte 163
	hdr0Len := offset1 + word                  // 164..195; value last byte 195
	hdr0Data := hdr0Len + word                 // 196..291; 80-byte header then 16-byte pad (276..291)

	// Sanity: the good blob is exactly the computed length and parses cleanly.
	require.Equal(t, hdr0Data+96+word+96, len(good), "wire layout offsets must match the serializer")
	var ctrl BtcAttributesDepositData
	require.NoError(t, ctrl.UnmarshalBinary(good), "control: the unmutated blob must parse")

	mutate := func(idx int, xor byte) []byte {
		b := make([]byte, len(good))
		copy(b, good)
		b[idx] ^= xor
		return b
	}

	cases := []struct {
		name    string
		data    []byte
		wantSub string
	}{
		{"wrong-initial-offset", mutate(initialOffsetWord+word-1, 0x01), "initial offset for the header array of 64"},
		{"numHeaders-padding-nonzero", mutate(numHeadersWord, 0x01), "number padding was not empty"},
		{"offset-mismatch-index-1", mutate(offset1+word-1, 0x01), "offset of 192 for the array at index 1, but got 193"},
		{"wrong-header-length", mutate(hdr0Len+word-1, 0x01), "exactly 80 bytes long"},
		{"header-padding-nonzero", mutate(hdr0Data+80, 0x01), "header padding was not empty"},
		{"trailing-extra-byte", append(append([]byte{}, good...), 0x00), "more data than expected"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			var d BtcAttributesDepositData
			err := d.UnmarshalBinary(tc.data)
			require.Error(t, err)
			require.Contains(t, err.Error(), tc.wantSub)
		})
	}

	// Truncation by one byte: a positive control proves the unmutated blob PARSES, then truncation must surface an
	// EOF-class error (io.EOF / io.ErrUnexpectedEOF via ReadBitcoinHeader/ReadUint64) — not a validation error. This
	// catches a mutant that rejects the full blob, or that rejects the truncation for an unrelated (wrong) reason.
	t.Run("truncated-by-one", func(t *testing.T) {
		var okParse BtcAttributesDepositData
		require.NoError(t, okParse.UnmarshalBinary(good), "positive control: the unmutated blob must parse")
		var d BtcAttributesDepositData
		err := d.UnmarshalBinary(good[:len(good)-1])
		require.Error(t, err)
		require.True(t, errors.Is(err, io.EOF) || errors.Is(err, io.ErrUnexpectedEOF),
			"truncation must surface an EOF-class error, got %v", err)
	})
}

// TestBtcAttributesDepositDataWrongSelector pins the 4-byte function-selector guard (the first branch of
// UnmarshalBinary). The round-trip/golden/fuzz tests always feed the correct selector, so a mutant that drops or
// inverts the selector check would survive them. A valid encoding with its leading selector byte flipped must be
// rejected with the "function signature" error.
func TestBtcAttributesDepositDataWrongSelector(t *testing.T) {
	valid, err := (&BtcAttributesDepositData{CanonicalTip: tipOf(1), Headers: zeroHeaders(0)}).MarshalBinary()
	require.NoError(t, err)
	require.Equal(t, UpdateHvmStateFuncBytes4[:], valid[:4], "precondition: a valid encoding begins with the selector")

	corrupt := append([]byte{}, valid...)
	corrupt[0] ^= 0xFF // flip the leading selector byte
	var d BtcAttributesDepositData
	err = d.UnmarshalBinary(corrupt)
	require.Error(t, err)
	require.Contains(t, err.Error(), "function signature", "a wrong 4-byte selector must be rejected by the selector guard")
}

// FuzzBtcAttributesDepositDataUnmarshal fuzzes the BtcAttributesDeposited data parser against arbitrary bytes.
// UnmarshalBinary runs on attacker-influenceable transaction calldata (Transactions.ExtractBtcAttrData feeds it
// tx.Data() on the consensus apply path), so it must:
//   - NEVER panic on any input (a panic in block processing would halt the node);
//   - on success, honor the header-count cap; and
//   - on success, be CANONICAL — it rejects trailing/short/mis-offset bytes, so any accepted encoding must
//     re-marshal byte-for-byte to itself (a strong differential oracle that catches a parser/serializer drift).
func FuzzBtcAttributesDepositDataUnmarshal(f *testing.F) {
	// Seeds: a valid 0-header encoding, a valid multi-header encoding, and a few degenerate shapes.
	var tip [BitcoinHashLengthBytes]byte
	for i := range tip {
		tip[i] = byte(i + 1)
	}
	mk := func(n int) []byte {
		hdrs := make([][BitcoinHeaderLengthBytes]byte, n)
		for i := range hdrs {
			for j := range hdrs[i] {
				hdrs[i][j] = byte(i*7 + j)
			}
		}
		b, err := (&BtcAttributesDepositData{CanonicalTip: tip, Headers: hdrs}).MarshalBinary()
		if err != nil {
			f.Fatalf("seed marshal (%d headers): %v", n, err)
		}
		return b
	}
	f.Add(mk(0))
	f.Add(mk(1))
	f.Add(mk(3))
	f.Add(append(mk(1), 0x00))                                      // valid prefix + trailing byte -> must be rejected, never panic
	f.Add(UpdateHvmStateFuncBytes4[:])                              // just the selector, too short
	f.Add([]byte{})                                                 // empty
	f.Add(make([]byte, MinimumSerializedBtcAttributesDepositedLen)) // min length, wrong selector

	f.Fuzz(func(t *testing.T, data []byte) {
		var d BtcAttributesDepositData
		if err := d.UnmarshalBinary(data); err != nil {
			return // a rejection is fine; the only hard requirement on rejection is "did not panic"
		}

		// Accepted: the header-count cap must hold.
		if uint64(len(d.Headers)) > MaximumBtcHeadersInTx {
			t.Fatalf("accepted %d headers, exceeding the cap of %d", len(d.Headers), MaximumBtcHeadersInTx)
		}

		// Accepted inputs are canonical (the parser rejects trailing/short/mis-offset data), so re-marshaling
		// must reproduce the exact input bytes.
		re, err := d.MarshalBinary()
		if err != nil {
			t.Fatalf("re-marshal of an accepted value failed: %v", err)
		}
		if !bytes.Equal(data, re) {
			t.Fatalf("accepted input is not canonical: re-marshal differs\n in: %x\nout: %x", data, re)
		}

		// And the re-encoding must parse back to an equal value (idempotent round-trip).
		var d2 BtcAttributesDepositData
		if err := d2.UnmarshalBinary(re); err != nil {
			t.Fatalf("re-marshaled bytes failed to parse: %v", err)
		}
		if d2.CanonicalTip != d.CanonicalTip || len(d2.Headers) != len(d.Headers) {
			t.Fatalf("round-trip mismatch: %+v vs %+v", d, d2)
		}
		for i := range d.Headers {
			if d2.Headers[i] != d.Headers[i] {
				t.Fatalf("round-trip header %d mismatch", i)
			}
		}
	})
}

// Transaction-level typed-envelope RLP round-trip for the BtcAttributesDeposited (0x7C) tx type — the WIRE/DB form
// for these force-included consensus txs in every hVM block body (block import, freezer storage, p2p relay all
// RLP-decode the body and dispatch to decodeTyped case 0x7C). All existing BtcAttr tests exercise only the CALLDATA
// layer (BtcAttributesDepositData marshal) or Sender identity, building the tx via NewTx on in-memory objects that
// never traverse RLP; the generic coding suites structurally exclude 0x7C (its sigHash panics). So the inner
// encode/decode (the {To rlp:"nil", Gas, Data} struct) and the decodeTyped 0x7C dispatch have NO coverage — a field
// reorder, a broken rlp:"nil" tag, or a wrong/deleted decode case would corrupt the consensus tx while staying green.
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

// Direct unit tests for Transactions.ExtractBtcAttrData — the consensus entry that feeds attacker-influenceable
// calldata into UnmarshalBinary. All prior coverage was indirect (a single BtcAttr tx at a fixed index, always
// valid). These pin: the not-found path, position-independence (found at any index), the empty set, the
// multi-tx dedup error, and that a parse error from the FIRST BtcAttr tx propagates (dedup never reached).
func tipOf(b byte) [BitcoinHashLengthBytes]byte {
	var t [BitcoinHashLengthBytes]byte
	for i := range t {
		t[i] = b
	}
	return t
}

// validBtcAttrTxWithTip builds a well-formed BtcAttributesDeposited tx carrying the given canonical tip and no
// headers (a valid shape; ExtractBtcAttrData only parses, it does not validate the BTC chain).
func validBtcAttrTxWithTip(t *testing.T, tip byte) *Transaction {
	t.Helper()
	data, err := (&BtcAttributesDepositData{CanonicalTip: tipOf(tip)}).MarshalBinary()
	require.NoError(t, err)
	return NewTx(&BtcAttributesDepositedTx{To: &BtcAttributesDepositedSenderAddress, Gas: 1_000_000, Data: data})
}

// invalidBtcAttrTx builds a tx of the BtcAttr TYPE but with calldata too short to parse (under the minimum) so
// UnmarshalBinary fails — exercising the parse-error propagation path.
func invalidBtcAttrTx() *Transaction {
	return NewTx(&BtcAttributesDepositedTx{To: &BtcAttributesDepositedSenderAddress, Gas: 1_000_000, Data: UpdateHvmStateFuncBytes4[:]})
}

func nonBtcAttrTx() *Transaction { return NewTx(&LegacyTx{}) }

func TestExtractBtcAttrData_NotPresentAndEmpty(t *testing.T) {
	// No BtcAttr tx among non-BtcAttr txs -> (nil, nil), no error.
	got, err := Transactions{nonBtcAttrTx(), nonBtcAttrTx()}.ExtractBtcAttrData()
	require.NoError(t, err)
	require.Nil(t, got, "no BtcAttr tx present -> nil result")

	// Empty tx set -> (nil, nil).
	got, err = Transactions{}.ExtractBtcAttrData()
	require.NoError(t, err)
	require.Nil(t, got, "empty tx set -> nil result")
}

func TestExtractBtcAttrData_FoundAtAnyIndex(t *testing.T) {
	// The BtcAttr tx is the THIRD entry (not index 0/1) — pins the "allow it anywhere" contract; a mutant that
	// only inspects index 0 or 1, or returns early, would miss it.
	txs := Transactions{nonBtcAttrTx(), nonBtcAttrTx(), validBtcAttrTxWithTip(t, 0xAB)}
	got, err := txs.ExtractBtcAttrData()
	require.NoError(t, err)
	require.NotNil(t, got, "a BtcAttr tx at index 2 must be found")
	require.Equal(t, tipOf(0xAB), got.CanonicalTip, "the parsed canonical tip must match the found tx")
}

func TestExtractBtcAttrData_ParseErrorPropagates(t *testing.T) {
	// A BtcAttr tx whose calldata cannot be parsed must surface the UnmarshalBinary error, not be swallowed.
	got, err := Transactions{invalidBtcAttrTx()}.ExtractBtcAttrData()
	require.Error(t, err, "an unparseable BtcAttr tx must propagate the parse error")
	require.Nil(t, got)
	require.Contains(t, err.Error(), "at least", "the error must be the UnmarshalBinary length-floor error")
}

func TestExtractBtcAttrData_MultipleBtcAttrTxsRejected(t *testing.T) {
	// Two VALID BtcAttr txs -> the dedup error (first parsed, second triggers the "more than one" rejection).
	got, err := Transactions{validBtcAttrTxWithTip(t, 0x11), validBtcAttrTxWithTip(t, 0x22)}.ExtractBtcAttrData()
	require.Error(t, err)
	require.Nil(t, got)
	require.Contains(t, err.Error(), "more than one Bitcoin Attributes Deposited transaction",
		"two BtcAttr txs must be rejected by the dedup guard")
}

func TestExtractBtcAttrData_FirstInvalidWinsOverDedup(t *testing.T) {
	// When the FIRST BtcAttr tx is invalid and a valid one follows, the FIRST tx's parse error surfaces — the
	// dedup branch is never reached (first-match-then-parse ordering). Kills a mutant that parses the last tx or
	// moves the dedup check before the parse.
	got, err := Transactions{invalidBtcAttrTx(), validBtcAttrTxWithTip(t, 0x33)}.ExtractBtcAttrData()
	require.Error(t, err)
	require.Nil(t, got)
	require.Contains(t, err.Error(), "at least", "the FIRST (invalid) tx's parse error must surface")
	require.NotContains(t, err.Error(), "more than one", "the dedup guard must NOT be reached when the first tx fails to parse")
}

// TestExtractBtcAttrData_RealisticSystemTxComposition drives ExtractBtcAttrData over the PRODUCTION body shape: a
// deposit/l1-info tx (0x7E) at index 0, a PoP-payout (0x7D) at index 1, and the BtcAttr (0x7C) at index 2 — the
// exact {index 2 with PoP present} layout ExtractBtcAttrData's comment reserves. The type bytes are ADJACENT
// (0x7E/0x7D/0x7C) and detection is an exact Type()==0x7C compare, so a degraded compare (>=, off-by-one, switch
// fall-through) would misread the 0x7D PoP at the reserved slot as the BtcAttr. The existing extract tests use only
// LegacyTx (0x00) decoys, nowhere near the boundary; this is the realistic system-tx mix.
func TestExtractBtcAttrData_RealisticSystemTxComposition(t *testing.T) {
	deposit := NewTx(&DepositTx{Value: big.NewInt(0), Gas: 21000, Data: []byte{0x01}}) // 0x7E
	popTo := PoPPayoutSenderAddress
	pop := NewTx(&PopPayoutTx{To: &popTo, Gas: 21000, Data: []byte{0x11, 0x22, 0x33}}) // 0x7D
	require.Equal(t, uint8(DepositTxType), deposit.Type())
	require.Equal(t, uint8(PopPayoutTxType), pop.Type())

	// (A) realistic {deposit, PoP, BtcAttr}: the BtcAttr at index 2 is found; the adjacent 0x7D PoP is NOT mistaken.
	got, err := Transactions{deposit, pop, validBtcAttrTxWithTip(t, 0xCD)}.ExtractBtcAttrData()
	require.NoError(t, err)
	require.NotNil(t, got)
	require.Equal(t, tipOf(0xCD), got.CanonicalTip, "the BtcAttr (0x7C) must be found among adjacent system-tx types, with the right tip")

	// (B) {deposit, PoP} with NO BtcAttr (the real shape of a non-BtcAttr hVM block): a stray 0x7D must NOT produce
	// a phantom BtcAttr result.
	got, err = Transactions{deposit, pop}.ExtractBtcAttrData()
	require.NoError(t, err)
	require.Nil(t, got, "a PoP-payout (0x7D) must never be misread as a BtcAttr (0x7C)")

	// (C) PoP AFTER the BtcAttr — still exactly one 0x7C, found regardless of the 0x7D's position.
	got, err = Transactions{deposit, validBtcAttrTxWithTip(t, 0xEF), pop}.ExtractBtcAttrData()
	require.NoError(t, err)
	require.NotNil(t, got)
	require.Equal(t, tipOf(0xEF), got.CanonicalTip)
}

// The 0x7C receipt JSON (eth_getTransactionReceipt) contract: btcAttributesDepositedNonce is surfaced exactly when
// set (omitempty), and round-trips through MarshalJSON/UnmarshalJSON. The receipt RLP + per-receipt DeriveFields are
// covered; the JSON path for the 0x7C nonce field was not (the existing TestReceiptJSON bundle has no 0x7C fixtures).
func TestBtcAttrReceiptJSONNonce(t *testing.T) {
	// With a nonce: the field is present and round-trips.
	b, err := json.Marshal(btcAttributesDepositedWithNonce)
	require.NoError(t, err)
	require.Contains(t, string(b), "btcAttributesDepositedNonce", "a set nonce must appear in the receipt JSON")
	var got Receipt
	require.NoError(t, json.Unmarshal(b, &got))
	require.NotNil(t, got.BtcAttributesDepositedNonce)
	require.Equal(t, *btcAttributesDepositedWithNonce.BtcAttributesDepositedNonce, *got.BtcAttributesDepositedNonce)

	// Without a nonce: omitempty drops the field and it round-trips as nil.
	b2, err := json.Marshal(btcAttributesDepositedWithNoNonce)
	require.NoError(t, err)
	require.NotContains(t, string(b2), "btcAttributesDepositedNonce", "an unset nonce must be omitted (omitempty)")
	var got2 Receipt
	require.NoError(t, json.Unmarshal(b2, &got2))
	require.Nil(t, got2.BtcAttributesDepositedNonce)
}

// TestSystemTxMarshalJSONRoundTrip pins that the Hemi-added system tx types (BtcAttributesDeposited 0x7C and
// PopPayout 0x7D) round-trip through the GENERIC Transaction.MarshalJSON/UnmarshalJSON.
//
// Both types define an UnmarshalJSON arm; without a matching MarshalJSON arm a generic marshal emits
// to/gas/input/gasPrice as null and the symmetric unmarshal then fails ("missing required field 'to'") — the same
// oversight a MarshalJSON arm on depositTxWithNonce exists to avoid. The live RPC path (newRPCTransaction) is
// unaffected (it populates fields directly), but the generic path (signer/rules.go, t8n tooling) would break.
// This test locks the symmetric behavior and would catch a regression that drops the MarshalJSON arms.
func TestSystemTxMarshalJSONRoundTrip(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000015")
	data := []byte{0x01, 0x02, 0x03, 0x04}

	cases := []struct {
		name  string
		inner TxData
		typ   byte
		nonce uint64 // expected effective nonce (0 when unset)
	}{
		{"btcattr", &BtcAttributesDepositedTx{To: &to, Gas: 1_000_000, Data: data}, BtcAttributesDepositedTxType, 0},
		{"btcattr-nonce", &btcAttributesDepositedTxWithNonce{BtcAttributesDepositedTx: BtcAttributesDepositedTx{To: &to, Gas: 1_000_000, Data: data}, EffectiveNonce: 42}, BtcAttributesDepositedTxType, 42},
		{"pop", &PopPayoutTx{To: &to, Gas: 500_000, Data: data}, PopPayoutTxType, 0},
		{"pop-nonce", &popPayoutTxWithNonce{PopPayoutTx: PopPayoutTx{To: &to, Gas: 500_000, Data: data}, EffectiveNonce: 7}, PopPayoutTxType, 7},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			// setDecoded (not NewTx) mirrors how UnmarshalJSON installs the inner: the *WithNonce wrappers define no
			// copy(), so NewTx().copy() would fall through to the embedded type and silently drop the nonce. A
			// re-marshal in production always operates on a setDecoded-installed inner.
			tx := new(Transaction)
			tx.setDecoded(tc.inner, 0)

			b, err := json.Marshal(tx)
			require.NoError(t, err)

			// The fields UnmarshalJSON requires non-nil must be populated (not the null output a missing MarshalJSON arm would produce).
			var raw map[string]json.RawMessage
			require.NoError(t, json.Unmarshal(b, &raw))
			for _, f := range []string{"to", "gas", "input", "gasPrice"} {
				require.NotEqual(t, "null", string(raw[f]), "field %q must not marshal to null", f)
			}
			require.Equal(t, `"0x0"`, string(raw["gasPrice"]), "system tx gasPrice must serialize as 0")

			// Round-trip back through the generic path.
			var got Transaction
			require.NoError(t, json.Unmarshal(b, &got), "the symmetric unmarshal must succeed")
			require.Equal(t, tc.typ, got.Type())
			require.Equal(t, to, *got.To())
			require.Equal(t, tx.Gas(), got.Gas())
			require.Equal(t, data, got.Data())
			// The nonce surfaces via EffectiveNonce() (the inner nonce() is always 0 for these system txs).
			require.Equal(t, tc.nonce, *got.EffectiveNonce(), "effective nonce must round-trip (0 when unset)")
		})
	}
}

// TestBtcAttrTxUnmarshalJSONWithNonce pins the 0x7C UnmarshalJSON nonce arm directly from a hand-written JSON
// literal (independent of MarshalJSON): when "nonce" is present, the decoder wraps the inner in
// btcAttributesDepositedTxWithNonce and preserves it via EffectiveNonce(). When absent, EffectiveNonce reports 0.
// A mutant deleting the wrapper construction (transaction_marshalling.go ~654) or corrupting the stored nonce
// would survive every other test (no test decoded a 0x7C JSON object). The decode dereferences "input" with no
// nil-guard, so the literal includes it (along with the required to/gas).
func TestBtcAttrTxUnmarshalJSONWithNonce(t *testing.T) {
	withNonce := `{"type":"0x7c","nonce":"0x2a","to":"0x4200000000000000000000000000000000000015",` +
		`"gas":"0xf4240","gasPrice":"0x0","input":"0x01020304"}`
	var tx Transaction
	require.NoError(t, json.Unmarshal([]byte(withNonce), &tx))
	require.Equal(t, byte(BtcAttributesDepositedTxType), tx.Type())
	_, ok := tx.inner.(*btcAttributesDepositedTxWithNonce)
	require.True(t, ok, "a 0x7C JSON carrying a nonce must decode into the *WithNonce wrapper")
	require.Equal(t, uint64(0x2a), *tx.EffectiveNonce(), "the decoded nonce must be preserved")

	noNonce := `{"type":"0x7c","to":"0x4200000000000000000000000000000000000015",` +
		`"gas":"0xf4240","gasPrice":"0x0","input":"0x01020304"}`
	var tx2 Transaction
	require.NoError(t, json.Unmarshal([]byte(noNonce), &tx2))
	_, ok = tx2.inner.(*BtcAttributesDepositedTx)
	require.True(t, ok, "a 0x7C JSON without a nonce must decode into the bare type")
	require.Equal(t, uint64(0), *tx2.EffectiveNonce())
}

// The PER-RECEIPT step of the public read path Receipts.DeriveFields for a 0x7C BtcAttr receipt. The DA/L1-fee
// (deriveOPStackFields) half is covered by TestCalcDAFootprintEqualsReceiptBlobGasSum (which calls
// deriveOPStackFields directly). NOT covered: the FIRST step — (*Receipt).DeriveFields — which sets Type, GasUsed
// (position math), EffectiveGasPrice (zero for BtcAttr), sets BlobGasUsed only for BlobTxType, and must preserve the
// BtcAttributesDepositedNonce. Every existing Receipts.DeriveFields test uses bundles without a 0x7C.
func TestDeriveFieldsBtcAttrReceiptPerReceiptStep(t *testing.T) {
	config := jovianTestChainConfig()
	config.ChainID = big.NewInt(1) // the per-receipt sender derivation builds a signer from ChainID
	// l1-info (0x7E) + BtcAttr (0x7C): both fixed-sender system txs, so the per-receipt sender derivation needs no
	// signature recovery (an unsigned user LegacyTx would panic on chainID). The per-receipt step still runs for
	// every receipt regardless of the deriveOPStackFields skip.
	txs := []*Transaction{jovianL1InfoTx(400), systemTxBtcAttrTx(t)}
	nonce := uint64(7)
	rs := Receipts{
		{Status: ReceiptStatusSuccessful, CumulativeGasUsed: 5},
		{Status: ReceiptStatusSuccessful, CumulativeGasUsed: 12, BtcAttributesDepositedNonce: &nonce},
	}
	require.NoError(t, rs.DeriveFields(config, common.HexToHash("0xb10c"), 1, 0, big.NewInt(1000), big.NewInt(920), txs))

	btc := rs[1] // the 0x7C receipt
	require.Equal(t, uint8(BtcAttributesDepositedTxType), btc.Type, "Type must be derived to 0x7C")
	require.Equal(t, uint64(12-5), btc.GasUsed, "GasUsed must be the per-position cumulative delta")
	require.NotNil(t, btc.EffectiveGasPrice)
	require.Zero(t, btc.EffectiveGasPrice.Sign(), "a BtcAttr tx has zero effective gas price")
	require.Zero(t, btc.BlobGasUsed, "a non-blob system tx must have zero BlobGasUsed")
	require.NotNil(t, btc.BtcAttributesDepositedNonce, "the BtcAttributesDepositedNonce must be preserved through derivation")
	require.Equal(t, nonce, *btc.BtcAttributesDepositedNonce)
	require.Nil(t, btc.L1Fee, "a zero-DA BtcAttr tx must carry no L1Fee")
	// The l1-info deposit receipt confirms the per-receipt step ran across the bundle (Type derived to 0x7E).
	require.Equal(t, uint8(DepositTxType), rs[0].Type)
}

// TestDeriveFieldsPopPayoutReceiptPerReceiptStep mirrors the 0x7C DeriveFields test for the 0x7D (PoP) sibling: a
// PopPayout receipt's Type derives to 0x7D, GasUsed is the per-position cumulative delta, effective gas price + blob
// gas are zero, and CRITICALLY the PoPPayoutNonce SURVIVES DeriveFields (the per-receipt step must not clobber it).
// The existing PoPPayoutNonce coverage is RLP/JSON round-trips only — none drives DeriveFields, so a type-specific
// nil-out mutant in DeriveFields would escape.
func TestDeriveFieldsPopPayoutReceiptPerReceiptStep(t *testing.T) {
	config := jovianTestChainConfig()
	config.ChainID = big.NewInt(1)
	txs := []*Transaction{jovianL1InfoTx(400), systemTxPopTx()}
	nonce := uint64(7)
	rs := Receipts{
		{Status: ReceiptStatusSuccessful, CumulativeGasUsed: 5},
		{Status: ReceiptStatusSuccessful, CumulativeGasUsed: 12, PoPPayoutNonce: &nonce},
	}
	require.NoError(t, rs.DeriveFields(config, common.HexToHash("0xb10c"), 1, 0, big.NewInt(1000), big.NewInt(920), txs))

	pop := rs[1] // the 0x7D receipt
	require.Equal(t, uint8(PopPayoutTxType), pop.Type, "Type must be derived to 0x7D")
	require.Equal(t, uint64(12-5), pop.GasUsed, "GasUsed must be the per-position cumulative delta")
	require.NotNil(t, pop.EffectiveGasPrice)
	require.Zero(t, pop.EffectiveGasPrice.Sign(), "a PoP tx has zero effective gas price")
	require.Zero(t, pop.BlobGasUsed, "a non-blob system tx must have zero BlobGasUsed")
	require.NotNil(t, pop.PoPPayoutNonce, "the PoPPayoutNonce must be preserved through derivation")
	require.Equal(t, nonce, *pop.PoPPayoutNonce)
	require.Equal(t, uint8(DepositTxType), rs[0].Type, "the l1-info deposit receipt confirms the per-receipt step ran across the bundle")
}

// Sender() identity for the BtcAttributesDeposited (0x7C) tx type. The signer returns the hardcoded
// BtcAttributesDepositedSenderAddress unconditionally for this type — this is the consensus "from" identity for
// the force-included BtcAttr tx in essentially every hVM block (it drives msg.From / the nonce account on the
// apply path). No test asserted this derivation.
// TestBtcAttrSenderAddressConstantPinned pins the LITERAL value of the hardcoded BtcAttr (0x7C) consensus sender.
// Every existing test references BtcAttributesDepositedSenderAddress SYMBOLICALLY, so a silent edit of the constant
// (0x8888...->0x8887...) would propagate through them and still pass. This address is the consensus "from" identity
// for the force-included BtcAttr tx in essentially every hVM block; a wrong byte is a wire/consensus breach. Mirrors
// the TestBtcAttrTxTypeConstantPinned literal-tripwire for the 0x7C wire prefix.
func TestBtcAttrSenderAddressConstantPinned(t *testing.T) {
	const want = "0x8888888888888888888888888888888888888888"
	require.Equal(t, want, BtcAttributesDepositedSender, "the BtcAttr consensus sender string constant must not drift")
	require.Equal(t, common.HexToAddress(want), BtcAttributesDepositedSenderAddress, "the derived sender address bytes must match the literal")
}

func TestBtcAttrTxSenderIdentity(t *testing.T) {
	data, err := (&BtcAttributesDepositData{CanonicalTip: tipOf(1)}).MarshalBinary()
	require.NoError(t, err)
	signer := LatestSignerForChainID(big.NewInt(1))

	// Canonical construction: To == the sender address (as MakeBtcAttributesDepositedTx builds it).
	tx := NewTx(&BtcAttributesDepositedTx{To: &BtcAttributesDepositedSenderAddress, Gas: 1_000_000, Data: data})
	addr, err := Sender(signer, tx)
	require.NoError(t, err)
	require.Equal(t, BtcAttributesDepositedSenderAddress, addr, "the BtcAttr tx sender must be the hardcoded consensus identity")

	// To-INDEPENDENCE: with a DISTINCT inner To, Sender must still resolve to the type's hardcoded address — it
	// derives from the tx TYPE (0x7C), not the To field. Kills a mutant that returned tx.To().
	require.NotEqual(t, BtcAttributesDepositedSenderAddress, HvmStateAddress, "anti-vacuity: the distinct To must differ from the sender")
	tx2 := NewTx(&BtcAttributesDepositedTx{To: &HvmStateAddress, Gas: 1_000_000, Data: data})
	addr2, err := Sender(signer, tx2)
	require.NoError(t, err)
	require.Equal(t, BtcAttributesDepositedSenderAddress, addr2, "Sender must ignore To and use the type's hardcoded identity")

	// The top-level Sender caches the resolved address; a second call returns the same value.
	again, err := Sender(signer, tx)
	require.NoError(t, err)
	require.Equal(t, BtcAttributesDepositedSenderAddress, again)
}

func TestBtcAttributesDepositDataNoHeaders(t *testing.T) {
	hash, _ := hexutil.Decode("0x1122334455667788112233445566778811223344556677881122334455667788")

	headers := make([][80]byte, 0)

	btcDepData := BtcAttributesDepositData{
		CanonicalTip: [32]byte(hash),
		Headers:      headers,
	}

	serialized, err := btcDepData.MarshalBinary()
	if err != nil {
		t.Errorf("Error: unable to marshal binary: %v", err)
	}

	expected, _ := hexutil.Decode("0xc94f1cca112233445566778811223344556677881122334455667788112233445566778800000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000")
	if !bytes.Equal(serialized, expected) {
		t.Errorf("Error: expected serialized %x but got %x instead", expected, serialized)
	}

	var btcDepParsed BtcAttributesDepositData
	err = btcDepParsed.UnmarshalBinary(serialized)
	if err != nil {
		t.Errorf("Error: unable to unmarshal serialized data %x, err: %v", serialized[:], err)
	}

	if !bytes.Equal(hash[:], btcDepParsed.CanonicalTip[:]) {
		t.Errorf("Error: hash was not unserialized correctly, expected %x but got %x instead", hash[:], btcDepParsed.CanonicalTip[:])
	}
}

func TestBtcAttributesDepositDataOneHeader(t *testing.T) {
	hash, _ := hexutil.Decode("0x1122334455667788112233445566778811223344556677881122334455667788")

	headers := make([][80]byte, 1)
	h0, _ := hexutil.Decode("0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	headers[0] = [80]byte(h0)
	btcDepData := BtcAttributesDepositData{
		CanonicalTip: [32]byte(hash),
		Headers:      headers,
	}

	serialized, err := btcDepData.MarshalBinary()
	if err != nil {
		t.Errorf("Error: unable to marshal binary: %v", err)
	}

	expected, _ := hexutil.Decode("0xc94f1cca11223344556677881122334455667788112233445566778811223344556677880000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000050aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000")
	if !bytes.Equal(serialized, expected) {
		t.Errorf("Error: expected serialized %x but got %x instead", expected, serialized)
	}

	var btcDepParsed BtcAttributesDepositData
	err = btcDepParsed.UnmarshalBinary(serialized)
	if err != nil {
		t.Errorf("Error: unable to unmarshal serialized data %x, err: %v", serialized[:], err)
	}

	if !bytes.Equal(hash[:], btcDepParsed.CanonicalTip[:]) {
		t.Errorf("Error: hash was not unserialized correctly, expected %x but got %x instead", hash[:], btcDepParsed.CanonicalTip[:])
	}

	if !bytes.Equal(h0[:], btcDepParsed.Headers[0][:]) {
		t.Errorf("Error: header was not unserialized correctly, expected %x but got %x instead", h0[:], btcDepParsed.Headers[0][:])
	}
}

func TestBtcAttributesDepositDataSixHeaders(t *testing.T) {
	hash, _ := hexutil.Decode("0x1122334455667788112233445566778811223344556677881122334455667788")

	headers := make([][80]byte, 6)
	h0, _ := hexutil.Decode("0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	h1, _ := hexutil.Decode("0xbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	h2, _ := hexutil.Decode("0xcaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	h3, _ := hexutil.Decode("0xdaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	h4, _ := hexutil.Decode("0xeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	h5, _ := hexutil.Decode("0xfaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	headers[0] = [80]byte(h0)
	headers[1] = [80]byte(h1)
	headers[2] = [80]byte(h2)
	headers[3] = [80]byte(h3)
	headers[4] = [80]byte(h4)
	headers[5] = [80]byte(h5)
	btcDepData := BtcAttributesDepositData{
		CanonicalTip: [32]byte(hash),
		Headers:      headers,
	}

	serialized, err := btcDepData.MarshalBinary()
	if err != nil {
		t.Errorf("Error: unable to marshal binary: %v", err)
	}

	expected, _ := hexutil.Decode("0xc94f1cca11223344556677881122334455667788112233445566778811223344556677880000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000014000000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000024000000000000000000000000000000000000000000000000000000000000002c000000000000000000000000000000000000000000000000000000000000003400000000000000000000000000000000000000000000000000000000000000050aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050baaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050caaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050daaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050eaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050faaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000")
	if !bytes.Equal(serialized, expected) {
		t.Errorf("Error: expected serialized %x but got %x instead", expected, serialized)
	}

	var btcDepParsed BtcAttributesDepositData
	err = btcDepParsed.UnmarshalBinary(serialized)
	if err != nil {
		t.Errorf("Error: unable to unmarshal serialized data %x, err: %v", serialized[:], err)
	}

	if !bytes.Equal(hash[:], btcDepParsed.CanonicalTip[:]) {
		t.Errorf("Error: hash was not unserialized correctly, expected %x but got %x instead", hash[:], btcDepParsed.CanonicalTip[:])
	}

	if !bytes.Equal(h0[:], btcDepParsed.Headers[0][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h0[:], btcDepParsed.Headers[0][:])
	}
	if !bytes.Equal(h1[:], btcDepParsed.Headers[1][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h1[:], btcDepParsed.Headers[1][:])
	}
	if !bytes.Equal(h2[:], btcDepParsed.Headers[2][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h2[:], btcDepParsed.Headers[2][:])
	}
	if !bytes.Equal(h3[:], btcDepParsed.Headers[3][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h3[:], btcDepParsed.Headers[3][:])
	}
	if !bytes.Equal(h4[:], btcDepParsed.Headers[4][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h4[:], btcDepParsed.Headers[4][:])
	}
	if !bytes.Equal(h5[:], btcDepParsed.Headers[5][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h5[:], btcDepParsed.Headers[5][:])
	}
}
