// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Apply-path gate (mainnet): replay Bitcoin Attributes Deposited transactions committed on Hemi mainnet
// through the full hVM apply path applyHvmHeaderConsensusUpdate (enforce=true): the contextual-difficulty
// validator, AddExternalHeaders, the cumulative-work canonical-tip claim check, and upstream-state-id chaining.
// Unlike the validator-only check in core/vm/btcdiff_mainnet_history_verify_test.go, this exercises the entire
// hVM state transition against a real lightweight TBC node seeded at the mainnet hVM genesis. The shared body
// lives in blockchain_hvm_replay_common_test.go; see blockchain_hvm_testnet3_replay_test.go for the shipped
// network.
//
// By default replays the bounded fixture vm/testdata/btcattr_mainnet_history.ndjson (relative to ./core),
// FAILING (not skipping) if absent. HEMI_MAINNET_VERIFY overrides the path for the live-tip reconstruction lane
// (history rebuilt by cmd/hvm-btcattr-reconstruct from a node's real L2 chaindata).

import (
	"testing"

	"github.com/ethereum/go-ethereum/core/vm"
)

func TestHvmReplaysAllMainnetBtcAttrThroughApplyPath(t *testing.T) {
	replayBtcAttrThroughApplyPath(t, replayParams{
		envPrefix: "HEMI_MAINNET",
		// The only lane that runs real committed history through the canonical-tip computation
		// (AddExternalHeaders + cumulative-work CanonicalTip selection + per-block tip-claim). The
		// linear fixture exercises only the extend-the-tip case; the tie-break/reject side is covered
		// by synthetic regtest tests. Path is relative to the ./core package dir.
		defaultPath:      "vm/testdata/btcattr_mainnet_history.ndjson",
		defaultCommitted: true,                                                               // absence FAILS, never skips
		expectTipHash:    "00000000000000000002358da40837b121dbf6974a73980728781562258f40d3", // real mainnet block 887040
		network:          "mainnet",
		genesisHeight:    vm.MainnetHvmGenesisHeight, // shared source of truth (core/vm/hvm_genesis.go)
		genesisHeader:    vm.MainnetHvmGenesisHeader,
		genesisHash:      vm.MainnetHvmGenesisHash,
	})
}
