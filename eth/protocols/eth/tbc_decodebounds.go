// Copyright 2026 The go-ethereum Authors
// Copyright 2026 Hemi Labs, Inc.
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

// Bounds on peer-supplied Bitcoin block payloads, applied before wire.MsgBlock.Deserialize.

package eth

import (
	"bytes"
	"fmt"

	"github.com/btcsuite/btcd/wire"
)

// minBTCTxPayload mirrors btcd's unexported wire.minTxPayload: the smallest number of bytes a
// serialized Bitcoin transaction can occupy (4-byte version + 1-byte input count + 1-byte output
// count + 4-byte locktime). btcd uses it to derive maxTxPerBlock; we use it for the inverse check --
// given a payload of N bytes, how many transactions could it possibly contain.
//
// Kept as a local constant with this note rather than a magic 10, because if btcd ever changes its
// value the two derivations must move together.
const minBTCTxPayload = 10

// The remaining per-element minimums, for the counts wire allocates on inside each transaction.
// Each is the smallest number of bytes that element can possibly serialize into, so a declared count
// of N requires at least N*minimum bytes to follow it.
const (
	// 32-byte prevout hash + 4-byte prevout index + 1-byte zero script-length varint + 4-byte
	// sequence. wire allocates both a []TxIn and a []*TxIn of this count.
	minBTCTxInPayload = 41
	// 8-byte value + 1-byte zero script-length varint. wire allocates both a []TxOut and a []*TxOut.
	//
	// This one is taken from btcd rather than hand-copied, because it is the only one of the four
	// that btcd exports.
	minBTCTxOutPayload = wire.MinTxOutPayload
	// A single length varint. A zero-length witness item is legal, so one byte really is the floor;
	// wire allocates a [][]byte of this count, i.e. 24 bytes of slice header per claimed item.
	minBTCWitnessItem = 1
)

// checkBTCBlockDecodeBounds rejects a gossiped block payload whose declared transaction count cannot
// fit in the bytes supplied, without decoding it.
//
// wire.MsgBlock.BtcDecode reads the transaction-count varint and immediately allocates a slice with
// that capacity, validating only that the count is below btcd's maxTxPerBlock. Nothing checks the
// count against the payload's actual length, so a tiny message can drive a large allocation that is
// then thrown away when the decode hits EOF.
//
// The check is deliberately cheap; it reads only varints and skips over the bytes between
// them, and it asserts only arithmetic that a genuine block satisfies by construction.
func checkBTCBlockDecodeBounds(payload []byte) error {
	// A block is at minimum an 80-byte header plus a 1-byte transaction count.
	const minBlockPayload = wire.MaxBlockHeaderPayload + 1
	if len(payload) < minBlockPayload {
		return fmt.Errorf("payload of %d bytes is shorter than the %d-byte minimum block",
			len(payload), minBlockPayload)
	}
	// Refusing here keeps the scan below bounded.
	//
	// wire borrows a single 4 MiB scriptSlab per transaction and hands each script a sub-slice of
	// what remains, advancing by the length actually read. readScriptBuf then does
	// io.ReadFull(r, s[:count]) -- so once earlier scripts have consumed most of the slab, a later
	// script whose declared length is legal on its own slices out of range. skipVarBytes cannot see
	// this: it bounds a script against the bytes *remaining in the payload*, not against the slab
	// remainder, and those two coincide only while the payload is smaller than the slab.
	if len(payload) > wire.MaxBlockPayload {
		return fmt.Errorf("payload of %d bytes exceeds the %d-byte maximum block",
			len(payload), wire.MaxBlockPayload)
	}

	txCount, err := wire.ReadVarInt(bytes.NewReader(payload[wire.MaxBlockHeaderPayload:]), 0)
	if err != nil {
		return fmt.Errorf("reading transaction count: %w", err)
	}
	// txCount == 0 is deliberately allowed. A zero-transaction MsgBlock is a header-only relay
	// (peer advertising a bare header) which this handler supports and handles explicitly further
	// down.

	if txCount > uint64(len(payload))/minBTCTxPayload {
		return fmt.Errorf("declares %d transactions, but a %d-byte payload can hold at most %d",
			txCount, len(payload), uint64(len(payload))/minBTCTxPayload)
	}

	// Now the precise bound: header + the count varint itself + the smallest possible encoding of
	// that many transactions.
	need := uint64(wire.MaxBlockHeaderPayload) + uint64(wire.VarIntSerializeSize(txCount)) + txCount*minBTCTxPayload
	if need > uint64(len(payload)) {
		return fmt.Errorf("declares %d transactions requiring at least %d bytes, but payload is %d bytes",
			txCount, need, len(payload))
	}

	// The transaction count is bounded. Now bound every count nested inside those transactions.
	return checkBTCNestedCounts(payload)
}

// btcScanner walks a peer-supplied Bitcoin block payload reading only varints and skipping the bytes
// between them. It allocates nothing and never retains a reference to the payload beyond the call.
type btcScanner struct {
	b   []byte
	off int
	// bailed records that the scan could not make sense of the structure and stopped early.
	bailed bool
}

func (s *btcScanner) remaining() int { return len(s.b) - s.off }

func (s *btcScanner) bail() { s.bailed = true }

// skip advances the cursor by n bytes, reporting whether that many were available.
func (s *btcScanner) skip(n int) bool {
	if n < 0 || n > s.remaining() {
		return false
	}
	s.off += n
	return true
}

func (s *btcScanner) byteAt() (byte, bool) {
	if s.remaining() < 1 {
		return 0, false
	}
	c := s.b[s.off]
	s.off++
	return c, true
}

// varint reads a Bitcoin variable-length integer.
//
// It is deliberately more permissive than wire.ReadVarInt, which rejects non-canonical (overlong)
// encodings. Accepting them here is safe in both directions: the encoded length is fixed by the
// prefix byte, so the cursor never diverges from wire's; and if we read a large count from a
// non-canonical encoding and reject the payload, wire would have rejected it too, just with a
// different error.
func (s *btcScanner) varint() (uint64, bool) {
	prefix, ok := s.byteAt()
	if !ok {
		return 0, false
	}
	var n int
	switch prefix {
	case 0xff:
		n = 8
	case 0xfe:
		n = 4
	case 0xfd:
		n = 2
	default:
		return uint64(prefix), true
	}
	if s.remaining() < n {
		return 0, false
	}
	var v uint64
	for i := 0; i < n; i++ { // little-endian
		v |= uint64(s.b[s.off+i]) << (8 * uint(i))
	}
	s.off += n
	return v, true
}

// skipVarBytes reads a length varint and skips that many bytes.
func (s *btcScanner) skipVarBytes(txIdx uint64, field string) error {
	n, ok := s.varint()
	if !ok {
		s.bail()
		return nil
	}
	if n > uint64(s.remaining()) {
		return fmt.Errorf("transaction %d declares a %d-byte %s, but only %d bytes remain",
			txIdx, n, field, s.remaining())
	}
	s.off += int(n) // safe: n <= remaining(), which is an int
	return nil
}

// checkBTCNestedCounts bounds every eagerly-allocated count inside the payload's transactions.
// This function can only ever reject a payload that declares more elements than it has room for.
func checkBTCNestedCounts(payload []byte) error {
	s := &btcScanner{b: payload}
	if !s.skip(wire.MaxBlockHeaderPayload) {
		return nil // caller already enforced the 81-byte minimum; unreachable, and accept if reached
	}
	txCount, ok := s.varint()
	if !ok {
		return nil
	}
	for i := uint64(0); i < txCount; i++ {
		if err := s.scanTx(i); err != nil {
			return err
		}
		if s.bailed {
			return nil
		}
	}
	return nil
}

// scanTx walks one transaction, bounding each of its counts. The field order mirrors
// wire.MsgTx.BtcDecode under WitnessEncoding exactly, which is the encoding Deserialize uses.
func (s *btcScanner) scanTx(idx uint64) error {
	if !s.skip(4) { // version
		s.bail()
		return nil
	}

	// A zero input count is wire's segwit marker, not an empty input list: it is followed by a flag
	// byte that must be 0x01, then the real input count.
	witness := false
	inCount, ok := s.varint()
	if !ok {
		s.bail()
		return nil
	}
	if inCount == 0 {
		flag, ok := s.byteAt()
		if !ok || flag != 0x01 {
			s.bail() // wire errors here too; let it produce the error
			return nil
		}
		witness = true
		if inCount, ok = s.varint(); !ok {
			s.bail()
			return nil
		}
	}

	if inCount > uint64(s.remaining())/minBTCTxInPayload {
		return fmt.Errorf("transaction %d declares %d inputs, but the %d bytes that remain can hold at most %d",
			idx, inCount, s.remaining(), uint64(s.remaining())/minBTCTxInPayload)
	}
	for j := uint64(0); j < inCount; j++ {
		if !s.skip(36) { // prevout hash + index
			s.bail()
			return nil
		}
		if err := s.skipVarBytes(idx, "signature script"); err != nil {
			return err
		}
		if s.bailed {
			return nil
		}
		if !s.skip(4) { // sequence
			s.bail()
			return nil
		}
	}

	outCount, ok := s.varint()
	if !ok {
		s.bail()
		return nil
	}
	if outCount > uint64(s.remaining())/minBTCTxOutPayload {
		return fmt.Errorf("transaction %d declares %d outputs, but the %d bytes that remain can hold at most %d",
			idx, outCount, s.remaining(), uint64(s.remaining())/minBTCTxOutPayload)
	}
	for j := uint64(0); j < outCount; j++ {
		if !s.skip(8) { // value
			s.bail()
			return nil
		}
		if err := s.skipVarBytes(idx, "pk script"); err != nil {
			return err
		}
		if s.bailed {
			return nil
		}
	}

	if witness {
		for j := uint64(0); j < inCount; j++ {
			witCount, ok := s.varint()
			if !ok {
				s.bail()
				return nil
			}
			if witCount > uint64(s.remaining())/minBTCWitnessItem {
				return fmt.Errorf("transaction %d input %d declares %d witness items, but only %d bytes remain",
					idx, j, witCount, s.remaining())
			}
			for k := uint64(0); k < witCount; k++ {
				if err := s.skipVarBytes(idx, "witness item"); err != nil {
					return err
				}
				if s.bailed {
					return nil
				}
			}
		}
	}

	if !s.skip(4) { // lock time
		s.bail()
	}
	return nil
}
