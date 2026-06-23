// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

import (
	"os"
	"testing"
)

// Integration matrix for the legacy "mainnet-as-testnet3" hVM migration. These exercise the I/O paths the unit
// tests cannot (the guard-free LevelDB read, the full-node canonical walk, the bulk fill, the rename retirement,
// the crash windows). They need real infrastructure — a mainnet TBC full node holding the committed Bitcoin chain,
// a populated legacy <home>/testnet3/ header store, and an EVM chain at a known tip — gated behind HVM_MIGRATION_IT=1
// plus the fixtures HVM_MIGRATION_FULLNODE_DATADIR and HVM_MIGRATION_LEGACY_HOME. The pure decision logic is
// covered by the unit tests in blockchain_hvm_migration_test.go.
//
// These bodies have no assertions yet, so requireMigrationInfra SKIPs unconditionally — even with HVM_MIGRATION_IT
// set — to prevent an empty body reporting a vacuous PASS that masks the missing end-to-end verification. Each test
// must replace this call with a real body (and its own infra checks) before it can run; the per-test comments state
// the convergence that body must assert.
func requireMigrationInfra(t *testing.T) {
	t.Helper()
	if os.Getenv("HVM_MIGRATION_IT") == "" {
		t.Skip("integration matrix opt-in: set HVM_MIGRATION_IT=1 (note: these tests have no body yet)")
	}
	t.Skip("this test has no body yet and must NOT report a vacuous PASS. " +
		"Implement the documented assertions (a seeded legacy leveldb store makes most of these buildable without a P2P full node) before relying on it.")
}

// Full-sync legacy node: testnet3/ store at the EVM tip, full node holds T's ancestry -> migrate.
// Assert: <home>/mainnet/ tip == T, upstream-state-id == S, hvmDiffEnforceable == true, and <home>/testnet3/
// renamed to <home>/testnet3.migrated-<S>/.
func TestHvmMigration_FullSyncLegacy_Migrates(t *testing.T) { requireMigrationInfra(t) }

// Snap-synced legacy node (no pre-pivot EVM history): migrate via the guard-free T read + full-node fill, then
// the S_old-anchored forward catch-up. Assert it does NOT call performFullHvmHeaderStateRestore (which would
// crit on the missing deep bodies) and converges to tip == T.
func TestHvmMigration_SnapLegacy_MigratesWithoutGenesisRestore(t *testing.T) {
	requireMigrationInfra(t)
}

// Lagged legacy store (S_old < EVM tip after an unclean shutdown): after the fill, the forward catch-up walks
// [S_old+1 .. tip]. Assert the migrated store's state-id == current EVM tip (not the stale S_old).
func TestHvmMigration_LaggedLegacyStore_CatchesUpToTip(t *testing.T) { requireMigrationInfra(t) }

// Full node behind (does not yet hold T or its ancestry): DEFER. Assert no dir is touched, the node boots on
// the legacy testnet3/ store with hvmDiffEnforceable == false, and a re-run migrates once the full node catches up.
func TestHvmMigration_FullNodeBehind_DefersThenMigrates(t *testing.T) { requireMigrationInfra(t) }

// Genuine testnet3 / upgradetest / localnet node: NOT migrated, no crit, normal boot.
func TestHvmMigration_GenuineNonMainnet_NotMigrated(t *testing.T) { requireMigrationInfra(t) }

// Crash-safety windows: kill after each of {mainnet/ removed; init-before-fill; mid-fill torn;
// fill+state-id committed before rename; after rename} and assert the per-window convergence direction
// (re-migrate vs idempotent-rename vs steady-state) via the upstream-state-id witness.
func TestHvmMigration_CrashWindows_Converge(t *testing.T) { requireMigrationInfra(t) }

// A deferred node must BOOT (not crit) despite the guard-free read having opened the legacy store: the read
// fully closes before init re-opens the same dir (LOCK SAFETY).
func TestHvmMigration_DeferredNode_BootsNoLockCrit(t *testing.T) { requireMigrationInfra(t) }
