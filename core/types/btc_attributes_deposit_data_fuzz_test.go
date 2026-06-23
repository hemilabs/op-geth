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
	"testing"
)

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
