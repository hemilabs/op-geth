// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// crash-window CONVERGENCE: a node that dies mid-migration must, on the next boot, classify the partial on-disk
// state correctly and RE-MIGRATE to convergence — never crit-loop, never silently keep a headerless store, never
// destroy the legacy fallback. The classification leaf (classifyMigratedMainnetStore, hvmMigrationNeeded torn-store
// case) and the single-shot SUCCESS are tested in isolation; this drives the full orchestration across each
// simulated crash window, proving the detection->rebuild loop converges and that a re-run is idempotent. Uses real
// mainnet genesis + synthetic children + a lightweight in-process tbc.Server + an in-memory EVM chain.

import (
	"context"
	"fmt"
	"path/filepath"
	"testing"
	"time"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

func TestMigrate_CrashWindowsConverge(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: builds real lightweight TBC nodes + EVM chains per crash window")
	}
	ctx := context.Background()
	mainnetGen := decodeMainnetGenesisHeader(t)

	const N = 4
	children := make([]*wire.BlockHeader, N)
	prev := mainnetGen
	for i := 0; i < N; i++ {
		h := &wire.BlockHeader{Version: prev.Version, PrevBlock: prev.BlockHash(), MerkleRoot: mainnetGen.MerkleRoot,
			Timestamp: prev.Timestamp.Add(time.Duration(i+1) * 10 * time.Minute), Bits: mainnetGen.Bits, Nonce: uint32(i + 1)}
		children[i] = h
		prev = h
	}
	tipHash := prev.BlockHash()

	newSrv := func(home, network string, stateId [32]byte) *tbc.Server {
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = mainnetGen
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight
		cfg.LevelDBHome = home
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
		cfg.Network = network
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		_, _, _, _, addErr := srv.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: children}, stateId[:])
		require.NoError(t, addErr)
		return srv
	}

	// stage builds the standard migrate inputs at a fresh home: an EVM chain whose canonical tip == S (catch-up
	// no-op), a mainnet full node holding genesis..T, and a torn-down legacy testnet3 store committed to T with S.
	// `crash` is invoked AFTER the legacy/full are in place but BEFORE maybeMigrate, to plant the partial on-disk
	// <home>/mainnet state of a crash window. Returns the chain, cfg, home, and S.
	stage := func(t *testing.T, crash func(home string, S [32]byte)) (*BlockChain, *tbc.Config, string, [32]byte) {
		_, _, bc, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
		require.NoError(t, err)
		t.Cleanup(bc.Stop)
		S := [32]byte(bc.CurrentBlock().Hash())

		home := t.TempDir()
		full := newSrv(t.TempDir(), "mainnet", [32]byte{0x01})
		t.Cleanup(func() { _ = full.ExternalHeaderTearDown() })
		prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
		vm.TBCFullNode, vm.TBCFullNodeConfig = full, &tbc.Config{Network: "mainnet"}
		t.Cleanup(func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg })

		legacy := newSrv(home, "testnet3", S)
		require.NoError(t, legacy.ExternalHeaderTearDown())
		if crash != nil {
			crash(home, S)
		}
		return bc, mainnetMigrateConfig(mainnetGen, home), home, S
	}

	assertConverged := func(t *testing.T, bc *BlockChain, home string, S [32]byte) {
		postH, postTip, err := bc.tbcHeaderNode.BlockHeaderBest(ctx)
		require.NoError(t, err)
		require.Equal(t, tipHash.String(), postTip.BlockHash().String(), "rebuilt tip must be the committed tip T")
		require.Equal(t, vm.MainnetHvmGenesisHeight+uint64(N), postH)
		postId, err := bc.tbcHeaderNode.UpstreamStateId(ctx)
		require.NoError(t, err)
		require.Equal(t, S, *postId, "rebuilt state-id must be S")
		require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "the mainnet store must exist")
		require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy store must be retired")
		require.DirExists(t, filepath.Join(home, fmt.Sprintf("testnet3.migrated-%x", S[:])), "legacy renamed to backup")
	}

	// (a) CRASH AFTER THE RESET, BEFORE FILL: a version-only (no best header) mainnet store -> torn -> ReMigrate.
	t.Run("crash-after-reset-torn-mainnet", func(t *testing.T) {
		bc, cfg, home, S := stage(t, func(home string, _ [32]byte) {
			require.NoError(t, openStoreGuardFree(t, ctx, home, "mainnet").Close()) // creates+version, no headers
		})
		require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "precondition: the torn store has entries")
		handled := bc.maybeMigrateHvmHeaderNode(cfg)
		t.Cleanup(func() {
			if bc.tbcHeaderNode != nil {
				_ = bc.tbcHeaderNode.ExternalHeaderTearDown()
			}
		})
		require.True(t, handled, "a torn (post-reset) mainnet store must RE-MIGRATE to convergence")
		assertConverged(t, bc, home, S)
	})

	// (b) CRASH MID FILL: headers committed but the state-id never written -> torn -> ReMigrate.
	t.Run("crash-mid-fill-no-stateid", func(t *testing.T) {
		bc, cfg, home, S := stage(t, func(home string, S [32]byte) {
			srv := newSrv(home, "mainnet", S) // headers + state-id...
			require.NoError(t, srv.ExternalHeaderTearDown())
			db := openStoreGuardFree(t, ctx, home, "mainnet")
			require.NoError(t, db.MetadataDel(ctx, upstreamStateIdMetaKey)) // ...then drop the state-id (torn)
			require.NoError(t, db.Close())
		})
		handled := bc.maybeMigrateHvmHeaderNode(cfg)
		t.Cleanup(func() {
			if bc.tbcHeaderNode != nil {
				_ = bc.tbcHeaderNode.ExternalHeaderTearDown()
			}
		})
		require.True(t, handled, "a mid-fill (no state-id) mainnet store must RE-MIGRATE")
		assertConverged(t, bc, home, S)
	})

	// (c) IDEMPOTENT RE-RUN: a second boot over an already-migrated store must NOT re-migrate or re-count completed.
	t.Run("idempotent-rerun", func(t *testing.T) {
		bc, cfg, home, S := stage(t, nil)
		require.True(t, bc.maybeMigrateHvmHeaderNode(cfg), "first run migrates")
		assertConverged(t, bc, home, S)
		// Release the migrated store's exclusive lock so the second boot can read it guard-free.
		require.NoError(t, bc.tbcHeaderNode.ExternalHeaderTearDown())

		_, _, bc2, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
		require.NoError(t, err)
		t.Cleanup(bc2.Stop)
		compBefore := hvmMigrationCompletedMeter.Snapshot().Count()
		handled2 := bc2.maybeMigrateHvmHeaderNode(mainnetMigrateConfig(mainnetGen, home))
		t.Cleanup(func() {
			if bc2.tbcHeaderNode != nil {
				_ = bc2.tbcHeaderNode.ExternalHeaderTearDown()
			}
		})
		require.False(t, handled2, "a re-run over a valid migrated store must be a no-op (ValidMigrated), not handled")
		require.Equal(t, compBefore, hvmMigrationCompletedMeter.Snapshot().Count(), "a no-op re-run must NOT re-count completed")
		require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "the migrated store must remain intact")
	})
}
