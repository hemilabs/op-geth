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

// Single source of truth for the canonical Bitcoin-mainnet hVM effective-genesis pair (height 883092).
//
// Referenced from three consensus-relevant places that must not drift apart: the genesis-pairing
// checkpoint map (core.hvmGenesisCheckpoints["mainnet"]), the apply-path replay gate
// (core/blockchain_hvm_*_replay_test.go), and the in-package differential-replay difficulty gate
// (core/vm/btcdiff_mainnet_history_verify_test.go). core imports core/vm but not vice-versa, so core/vm is
// the lowest package both layers can share, making it the home for the single constant.
// TestMainnetHvmGenesisHeaderHashesToPin welds the header bytes to the hash.
const (
	// MainnetHvmGenesisHeight is the true Bitcoin-mainnet height of the effective-genesis header. It is a
	// consensus parameter: it positions the contextual-difficulty retarget boundary (% BlocksPerRetarget).
	MainnetHvmGenesisHeight = uint64(883092)
	// MainnetHvmGenesisHeader is the 80-byte Bitcoin-mainnet effective-genesis header, hex-encoded.
	MainnetHvmGenesisHeader = "0000003efaaa2ba65de684c512bb67ef115298d1d16bcb49b16c02000000000000000000ed31a56788c4488afc4ee69e0791ad6aeeb9ea05f069e0fdde6159068765ad3f4128a96726770217e7f41c86"
	// MainnetHvmGenesisHash is MainnetHvmGenesisHeader's block hash (display hex) — the value pinned in
	// core.hvmGenesisCheckpoints["mainnet"].
	MainnetHvmGenesisHash = "000000000000000000006e4855d5adfaefb7611c9446eb41ceb8a9327188eda8"
)

// Single source of truth for the canonical Bitcoin-TESTNET3 hVM effective-genesis pair (height 3522419) — the
// default network. The differential-replay gate references this one symbol so it cannot diverge from production.
// eth/backend_hvm_genesis_test.go cross-checks these against ethconfig.Defaults (welded to
// core.hvmGenesisCheckpoints["testnet3"]), so a re-genesis that updates production but not these constants fails
// CI. TestTestnet3HvmGenesisIsRealChainBlock welds these to the genuine testnet3 block by field literals.
const (
	// Testnet3HvmGenesisHeight is the true testnet3 height of the effective-genesis header.
	Testnet3HvmGenesisHeight = uint64(3522419)
	// Testnet3HvmGenesisHeader is the 80-byte testnet3 effective-genesis header, hex-encoded.
	Testnet3HvmGenesisHeader = "00c05732cdc3e0d654efe86351f0cbfc6c79325e9f9fa7886a39b552f5c4d90700000000dae4079485e26f1f77425b84a13760038a352d07a0fef92b5188bd04c2999162afca58679121011962b9d0a5"
	// Testnet3HvmGenesisHash is Testnet3HvmGenesisHeader's block hash (display hex).
	Testnet3HvmGenesisHash = "000000000000000096c98151accc5ee217d7cc4ff1e59a3d91e4c9365c4ea144"
)
