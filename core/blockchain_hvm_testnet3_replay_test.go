// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Testnet3 apply-path differential-replay gate. testnet3 is the shipped default network (eth/backend.go defaults
// the consensus node to it via config.TBCNetwork -> ethconfig.DefaultTBCNetwork). It replays every committed
// BtcAttr batch through the byte-identical apply path used by the mainnet replay (shared body in
// blockchain_hvm_replay_common_test.go), so the cumulative-work canonical-tip selection and the per-block
// cbh==CanonicalTip reject — neither of which the validator-only vm harness recomputes — are differentially
// re-validated on the network nodes actually run. testnet3 is the only network whose params enable
// ReduceMinDifficulty, so applying its committed history is the only apply-path run that exercises that rule
// end-to-end. The bounded fixture includes 116 diff-1 headers above the floor, pinned by the validator integrity
// guard TestTestnet3HistoryFixtureIsContiguousAndConnectsToGenesis (which asserts the count, not this gate).
//
// Orphans: early testnet3 history contains a few genuinely non-contiguous (orphaned-parent) committed headers
// (see core/vm/btcdiff_testnet3_history_verify_test.go). The apply path REJECTS an unconnected batch
// (ErrBTCBatchUnconnected -> ErrInvalidHVMHeaders), so a full-history replay fatals at the first such batch.
// That fatal is the authoritative signal (the validator-only gate only diagnoses it); resolving it means either
// adding the missing canonical link to the fixture (a benign reconstruction gap) or confirming a genuine orphan.
// Defaults to the committed bounded fixture vm/testdata/btcattr_testnet3_history.ndjson (contiguous, so no orphan
// fatal), FAILING if absent; HEMI_TESTNET3_VERIFY overrides for the live-tip lane.

import (
	"testing"

	"github.com/ethereum/go-ethereum/core/vm"
)

// Single-sourced from the shared vm.Testnet3HvmGenesis* symbols so every testnet3-genesis copy (this apply-path
// replay, the validator gate, and — transitively via TestDifferentialReplayGateTestnet3GenesisMatchesProductionDefault —
// ethconfig.Defaults/the checkpoint) tracks one constant. A re-genesis then fails with a clear compile/parity
// signal instead of a confusing "fixture unconnected" error.
const (
	testnet3HvmGenesisHeightReplay = vm.Testnet3HvmGenesisHeight
	testnet3HvmGenesisHeaderReplay = vm.Testnet3HvmGenesisHeader
	testnet3HvmGenesisHashReplay   = vm.Testnet3HvmGenesisHash
)

func TestHvmReplaysAllTestnet3BtcAttrThroughApplyPath(t *testing.T) {
	replayBtcAttrThroughApplyPath(t, replayParams{
		envPrefix: "HEMI_TESTNET3",
		// CI-resident: replay the committed testnet3 bounded fixture through the apply path. Path is
		// relative to the ./core package dir.
		defaultPath:      "vm/testdata/btcattr_testnet3_history.ndjson",
		defaultCommitted: true,                                                               // absence FAILS, never skips
		expectTipHash:    "0000000000003b8315976d4a9412a8bc6a3a2cbdb9e748d886987b82e89aa68f", // real testnet3 block 3525984
		network:          "testnet3",
		genesisHeight:    testnet3HvmGenesisHeightReplay,
		genesisHeader:    testnet3HvmGenesisHeaderReplay,
		genesisHash:      testnet3HvmGenesisHashReplay,
	})
}
