// Copyright 2017 The go-ethereum Authors
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

package vm

import (
	"math/bits"
	"testing"

	"github.com/ethereum/go-ethereum/crypto"
)

func TestJumpDestAnalysis(t *testing.T) {
	tests := []struct {
		code  []byte
		exp   byte
		which int
	}{
		{[]byte{byte(PUSH1), 0x01, 0x01, 0x01}, 0b0000_0010, 0},
		{[]byte{byte(PUSH1), byte(PUSH1), byte(PUSH1), byte(PUSH1)}, 0b0000_1010, 0},
		{[]byte{0x00, byte(PUSH1), 0x00, byte(PUSH1), 0x00, byte(PUSH1), 0x00, byte(PUSH1)}, 0b0101_0100, 0},
		{[]byte{byte(PUSH8), byte(PUSH8), byte(PUSH8), byte(PUSH8), byte(PUSH8), byte(PUSH8), byte(PUSH8), byte(PUSH8), 0x01, 0x01, 0x01}, bits.Reverse8(0x7F), 0},
		{[]byte{byte(PUSH8), 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01}, 0b0000_0001, 1},
		{[]byte{0x01, 0x01, 0x01, 0x01, 0x01, byte(PUSH2), byte(PUSH2), byte(PUSH2), 0x01, 0x01, 0x01}, 0b1100_0000, 0},
		{[]byte{0x01, 0x01, 0x01, 0x01, 0x01, byte(PUSH2), 0x01, 0x01, 0x01, 0x01, 0x01}, 0b0000_0000, 1},
		{[]byte{byte(PUSH3), 0x01, 0x01, 0x01, byte(PUSH1), 0x01, 0x01, 0x01, 0x01, 0x01, 0x01}, 0b0010_1110, 0},
		{[]byte{byte(PUSH3), 0x01, 0x01, 0x01, byte(PUSH1), 0x01, 0x01, 0x01, 0x01, 0x01, 0x01}, 0b0000_0000, 1},
		{[]byte{0x01, byte(PUSH8), 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01}, 0b1111_1100, 0},
		{[]byte{0x01, byte(PUSH8), 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01}, 0b0000_0011, 1},
		{[]byte{byte(PUSH16), 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01}, 0b1111_1110, 0},
		{[]byte{byte(PUSH16), 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01}, 0b1111_1111, 1},
		{[]byte{byte(PUSH16), 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01}, 0b0000_0001, 2},
		{[]byte{byte(PUSH8), 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, byte(PUSH1), 0x01}, 0b1111_1110, 0},
		{[]byte{byte(PUSH8), 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, byte(PUSH1), 0x01}, 0b0000_0101, 1},
		{[]byte{byte(PUSH32)}, 0b1111_1110, 0},
		{[]byte{byte(PUSH32)}, 0b1111_1111, 1},
		{[]byte{byte(PUSH32)}, 0b1111_1111, 2},
		{[]byte{byte(PUSH32)}, 0b1111_1111, 3},
		{[]byte{byte(PUSH32)}, 0b0000_0001, 4},
	}
	for i, test := range tests {
		ret := codeBitmap(test.code)
		if ret[test.which] != test.exp {
			t.Fatalf("test %d: expected %x, got %02x", i, test.exp, ret[test.which])
		}
	}
}

// TestEIP8024JumpDestAnalysis checks that the code bitmap treats the 1-byte
// immediates of DUPN/SWAPN/EXCHANGE (EIP-8024) as data, except when doing so
// would change JUMPDEST validity relative to pre-EIP-8024 analysis: an
// immediate equal to JUMPDEST (0x5b) or in the PUSH1-PUSH32 range (0x60-0x7f)
// must be left as its own code position instead.
func TestEIP8024JumpDestAnalysis(t *testing.T) {
	// Normal immediate: skipped as data, and the following JUMPDEST is a
	// valid, ordinary code position.
	code := []byte{byte(DUPN), 0x01, byte(JUMPDEST)}
	bv := codeBitmap(code)
	if bv.codeSegment(1) {
		t.Fatalf("normal DUPN immediate at pos 1 should be marked as data")
	}
	if !bv.codeSegment(2) {
		t.Fatalf("JUMPDEST at pos 2 should remain a valid code position")
	}

	// Immediate == JUMPDEST: must NOT be skipped, so it remains a valid jump
	// target, matching what analysis with no knowledge of DUPN would produce.
	code = []byte{byte(SWAPN), byte(JUMPDEST), 0x01}
	bv = codeBitmap(code)
	if !bv.codeSegment(1) {
		t.Fatalf("SWAPN immediate equal to JUMPDEST at pos 1 must not be marked as data")
	}

	// Immediate in PUSH1-PUSH32 range: must NOT be skipped as DUPN/SWAPN/
	// EXCHANGE's own data, so the PUSH opcode's own immediate skip logic still
	// applies to the bytes that follow it.
	code = []byte{byte(EXCHANGE), byte(PUSH1), 0x01, byte(JUMPDEST)}
	bv = codeBitmap(code)
	if !bv.codeSegment(1) {
		t.Fatalf("EXCHANGE immediate in PUSH1-PUSH32 range at pos 1 must not be marked as data")
	}
	if bv.codeSegment(2) {
		t.Fatalf("PUSH1's own immediate at pos 2 should be marked as data")
	}
	if !bv.codeSegment(3) {
		t.Fatalf("JUMPDEST at pos 3 should remain a valid code position")
	}

	// EXCHANGE has a narrower disallowed range than DUPN/SWAPN: 0x52 is
	// disallowed for EXCHANGE but allowed for DUPN/SWAPN.
	code = []byte{byte(DUPN), 0x52, byte(JUMPDEST)}
	bv = codeBitmap(code)
	if bv.codeSegment(1) {
		t.Fatalf("0x52 immediate after DUPN should be marked as data")
	}
	code = []byte{byte(EXCHANGE), 0x52, byte(JUMPDEST)}
	bv = codeBitmap(code)
	if !bv.codeSegment(1) {
		t.Fatalf("0x52 immediate after EXCHANGE should not be marked as data")
	}
}

const analysisCodeSize = 1200 * 1024

func BenchmarkJumpdestAnalysis_1200k(bench *testing.B) {
	// 1.4 ms
	code := make([]byte, analysisCodeSize)
	bench.SetBytes(analysisCodeSize)
	for bench.Loop() {
		codeBitmap(code)
	}
}
func BenchmarkJumpdestHashing_1200k(bench *testing.B) {
	// 4 ms
	code := make([]byte, analysisCodeSize)
	bench.SetBytes(analysisCodeSize)
	for bench.Loop() {
		crypto.Keccak256Hash(code)
	}
}

func BenchmarkJumpdestOpAnalysis(bench *testing.B) {
	var op OpCode
	bencher := func(b *testing.B) {
		code := make([]byte, analysisCodeSize)
		b.SetBytes(analysisCodeSize)
		for i := range code {
			code[i] = byte(op)
		}
		bits := make(BitVec, len(code)/8+1+4)
		for b.Loop() {
			clear(bits)
			codeBitmapInternal(code, bits)
		}
	}
	for op = PUSH1; op <= PUSH32; op++ {
		bench.Run(op.String(), bencher)
	}
	op = JUMPDEST
	bench.Run(op.String(), bencher)
	op = STOP
	bench.Run(op.String(), bencher)
}
