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

// Deterministic anti-cases for the BtcAttributesDeposited parser. The fuzz test only asserts "rejected OR
// canonical round-trip" — it never pins WHICH validation branch fires, and several branches (offset/length/
// padding guards) are unlikely to be hit reliably by random mutation. These pin each guard with an exact error
// oracle, plus the header-count cap boundary (30 accepted / 31 rejected).

import (
	"errors"
	"io"
	"testing"

	"github.com/stretchr/testify/require"
)

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
