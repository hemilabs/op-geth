// Copyright 2024 The go-ethereum Authors
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

package vm

import (
	"encoding/hex"
	"testing"
)

// TestMainnetHvmGenesisHeaderLength pins the constant's encoding: a Bitcoin block header is exactly 80 bytes
// (160 hex chars). The Header->Hash weld below can pass on a wrong-length literal that still decodes
// (parseHeader80 tolerates trailing bytes on some paths), so length is guarded explicitly. Catches a
// truncated/overlong --hvm.genesisheader before it misaligns field parsing on a live boot.
func TestMainnetHvmGenesisHeaderLength(t *testing.T) {
	raw, err := hex.DecodeString(MainnetHvmGenesisHeader)
	if err != nil {
		t.Fatalf("MainnetHvmGenesisHeader is not valid hex: %v", err)
	}
	if len(raw) != 80 {
		t.Fatalf("MainnetHvmGenesisHeader decodes to %d bytes, want exactly 80 (a Bitcoin header)", len(raw))
	}
	if len(MainnetHvmGenesisHeader) != 160 {
		t.Fatalf("MainnetHvmGenesisHeader is %d hex chars, want exactly 160", len(MainnetHvmGenesisHeader))
	}
}

// TestMainnetHvmGenesisHeaderHashesToPin welds the two halves of the mainnet genesis constant: the 80-byte
// header bytes MUST hash to the pinned hash. Every other consumer (the checkpoint map, the apply-path replay,
// the difficulty gate) relies on this weld, so a typo in either literal fails here instead of silently
// re-rooting a downstream chain.
func TestMainnetHvmGenesisHeaderHashesToPin(t *testing.T) {
	gen, err := parseHeader80(MainnetHvmGenesisHeader)
	if err != nil {
		t.Fatalf("decode MainnetHvmGenesisHeader: %v", err)
	}
	if got := gen.BlockHash().String(); got != MainnetHvmGenesisHash {
		t.Fatalf("MainnetHvmGenesisHeader hashes to %s, but MainnetHvmGenesisHash pins %s — the shared mainnet genesis constant is internally inconsistent", got, MainnetHvmGenesisHash)
	}
}

// TestMainnetHvmGenesisIsRealChainBlock pins the constant to the genuine Bitcoin-mainnet block at height 883092
// by its decoded header fields. The weld test above only proves Header->Hash internal consistency and passes for
// any self-consistent (header,hash) pair; checking the field literals against the real h=883092 block here stops
// a re-pin to a different block, which would otherwise crash the mainnet fleet at the genesis weld on first
// --tbc.network=mainnet boot.
func TestMainnetHvmGenesisIsRealChainBlock(t *testing.T) {
	gen, err := parseHeader80(MainnetHvmGenesisHeader)
	if err != nil {
		t.Fatalf("decode MainnetHvmGenesisHeader: %v", err)
	}
	if MainnetHvmGenesisHeight != 883092 {
		t.Fatalf("MainnetHvmGenesisHeight = %d, want the real Bitcoin-mainnet height 883092", MainnetHvmGenesisHeight)
	}
	if got, want := gen.PrevBlock.String(), "000000000000000000026cb149cb6bd1d1985211ef67bb12c584e65da62baafa"; got != want {
		t.Fatalf("PrevBlock = %s, want the real h=883092 parent %s", got, want)
	}
	if got, want := gen.MerkleRoot.String(), "3fad6587065961defde069f005eab9ee6aad91079ee64efc8a48c48867a531ed"; got != want {
		t.Fatalf("MerkleRoot = %s, want the real h=883092 merkle root %s", got, want)
	}
	if got, want := gen.Timestamp.Unix(), int64(1739139137); got != want {
		t.Fatalf("Timestamp = %d, want the real h=883092 time %d", got, want)
	}
	if got, want := gen.Version, int32(0x3e000000); got != want {
		t.Fatalf("Version = 0x%08x, want 0x%08x", got, want)
	}
	if got, want := uint32(gen.Bits), uint32(0x17027726); got != want {
		t.Fatalf("Bits = 0x%08x, want the real h=883092 bits 0x%08x", got, want)
	}
	if got, want := gen.Nonce, uint32(2250044647); got != want {
		t.Fatalf("Nonce = %d, want the real h=883092 nonce %d", got, want)
	}
}

// TestTestnet3HvmGenesisHeaderLength pins the testnet3 (the shipped default network) genesis constant to exactly
// 80 bytes / 160 hex chars, mirroring TestMainnetHvmGenesisHeaderLength. Without this tripwire a truncated/overlong
// literal would only surface as a misaligned field parse on a live testnet3 boot.
func TestTestnet3HvmGenesisHeaderLength(t *testing.T) {
	raw, err := hex.DecodeString(Testnet3HvmGenesisHeader)
	if err != nil {
		t.Fatalf("Testnet3HvmGenesisHeader is not valid hex: %v", err)
	}
	if len(raw) != 80 {
		t.Fatalf("Testnet3HvmGenesisHeader decodes to %d bytes, want exactly 80 (a Bitcoin header)", len(raw))
	}
	if len(Testnet3HvmGenesisHeader) != 160 {
		t.Fatalf("Testnet3HvmGenesisHeader is %d hex chars, want exactly 160", len(Testnet3HvmGenesisHeader))
	}
}
