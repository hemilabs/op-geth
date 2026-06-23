// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// DEFER-branch coverage for migrateHvmHeaderNode. The routine has several "leave everything untouched and boot on
// the legacy store" exits not reached by the other migrate tests:
//
//   - the full-node identity guard (absent / wrong-network embedded full node);
//   - the legacy-store-at-genesis exit (the recorded EVM state-id is still the genesis marker);
//   - the gather-not-ready exit (the mainnet full node lacks the committed tip T or its ancestry).
//
// Each must report not-handled, flip config.Network back to testnet3 (so the caller boots on the legacy store
// unenforced), and touch NO dirs. A lightweight tbc.Server stands in for the full node — no real Bitcoin full node
// or chaindata involved.

import (
	"bytes"
	"context"
	"encoding/hex"
	"testing"
	"time"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

func decodeMainnetGenesisHeader(t *testing.T) *wire.BlockHeader {
	t.Helper()
	raw, err := hex.DecodeString(vm.MainnetHvmGenesisHeader)
	require.NoError(t, err)
	var h wire.BlockHeader
	require.NoError(t, h.Deserialize(bytes.NewReader(raw)))
	return &h
}

// mainnetMigrateConfig is the config a migrating mainnet node carries: the canonical mainnet effective-genesis pair
// (so the genesis weld passes) plus the legacy store's home.
func mainnetMigrateConfig(gen *wire.BlockHeader, home string) *tbc.Config {
	return &tbc.Config{
		Network: "mainnet", LevelDBHome: home,
		EffectiveGenesisBlock: gen, GenesisHeightOffset: vm.MainnetHvmGenesisHeight, ExternalHeaderMode: true,
	}
}

// TestMigrate_DefersWhenFullNodeAbsentOrWrongNetwork pins the full-node identity guard: the routine must DEFER
// (never walk the wrong index / nil-deref) when the embedded full node is absent, or present but configured for a
// non-mainnet network. Both arms defer BEFORE reading the legacy store, so no store or chain is needed.
func TestMigrate_DefersWhenFullNodeAbsentOrWrongNetwork(t *testing.T) {
	gen := decodeMainnetGenesisHeader(t)
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	t.Run("absent", func(t *testing.T) {
		vm.TBCFullNode, vm.TBCFullNodeConfig = nil, nil
		bc := &BlockChain{ctx: context.Background()}
		cfg := mainnetMigrateConfig(gen, t.TempDir())
		require.False(t, bc.migrateHvmHeaderNode(cfg), "an absent full node must DEFER, not migrate")
		require.Equal(t, "testnet3", cfg.Network, "defer flips Network back to testnet3")
	})

	t.Run("wrong-network", func(t *testing.T) {
		// A non-nil full node configured for testnet3 (not mainnet) must defer on the third guard clause; the
		// dummy server is never dereferenced — the routine returns at the guard before any gather.
		vm.TBCFullNode = &tbc.Server{}
		vm.TBCFullNodeConfig = &tbc.Config{Network: "testnet3"}
		bc := &BlockChain{ctx: context.Background()}
		cfg := mainnetMigrateConfig(gen, t.TempDir())
		require.False(t, bc.migrateHvmHeaderNode(cfg), "a non-mainnet full node must DEFER")
		require.Equal(t, "testnet3", cfg.Network, "defer flips Network back to testnet3")
	})
}

// TestMigrate_DefersWhenLegacyStoreAtGenesis pins the at-genesis exit: a legacy store whose recorded EVM
// upstream-state-id is still the genesis marker (atGenesis) has no committed state to migrate, so the routine must
// DEFER to a normal boot, leaving the legacy store untouched and creating no mainnet store.
func TestMigrate_DefersWhenLegacyStoreAtGenesis(t *testing.T) {
	if testing.Short() {
		t.Skip("seeds a real lightweight legacy store")
	}
	ctx := context.Background()
	gen := decodeMainnetGenesisHeader(t)
	home := t.TempDir()

	// A legacy testnet3-labeled store seated at the mainnet genesis with the DEFAULT (genesis) state-id -> atGenesis.
	seedTbcHeaderStore(t, ctx, home, "testnet3", vm.MainnetHvmGenesisHeader, vm.MainnetHvmGenesisHeight, false /* keep genesis state-id */)

	// Make the full-node guard PASS (so the routine reaches the atGenesis check); the atGenesis defer happens
	// before any gather, so the dummy server is never dereferenced.
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	vm.TBCFullNode, vm.TBCFullNodeConfig = &tbc.Server{}, &tbc.Config{Network: "mainnet"}
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	bc := &BlockChain{ctx: ctx}
	cfg := mainnetMigrateConfig(gen, home)
	require.False(t, bc.migrateHvmHeaderNode(cfg), "an at-genesis legacy store has nothing to migrate -> DEFER")
	require.Equal(t, "testnet3", cfg.Network, "the at-genesis defer must flip Network back to testnet3")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy store must be untouched on the at-genesis defer")
	require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "no mainnet store may be created on the at-genesis defer")

	// Lock release: the guard-free read must have closed the legacy store so the normal boot can re-open it.
	reopened := openStoreGuardFree(t, ctx, home, "testnet3")
	require.NoError(t, reopened.Close(), "the legacy store must be re-openable after the at-genesis defer (the read released its lock)")
}

// TestMigrate_DefersWhenFullNodeNotReady pins the gather-not-ready exit: a readable, progressed legacy store
// (committed tip T = a child header, canonical EVM state-id) but a mainnet full node that does NOT hold T's
// ancestry must DEFER without touching any dir. The pure gather geometry is covered by TestGatherHeadersBackToGenesis;
// this pins that the routine maps a gather miss to deferHvmMigration. The full node is a lightweight genesis-only
// store (no real chaindata).
func TestMigrate_DefersWhenFullNodeNotReady(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a chain + two real lightweight stores")
	}
	ctx := context.Background()
	gen := decodeMainnetGenesisHeader(t)
	child := &wire.BlockHeader{
		Version: gen.Version, PrevBlock: gen.BlockHash(), MerkleRoot: gen.MerkleRoot,
		Timestamp: gen.Timestamp.Add(10 * time.Minute), Bits: gen.Bits, Nonce: 1,
	}

	newSrv := func(home, network string, withChild bool, stateId [32]byte) *tbc.Server {
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = gen
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight
		cfg.LevelDBHome = home
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
		cfg.Network = network
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		if withChild {
			_, _, _, _, addErr := srv.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{child}}, stateId[:])
			require.NoError(t, addErr)
		} else {
			require.NoError(t, srv.SetUpstreamStateId(ctx, stateId))
		}
		return srv
	}

	_, _, bc, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
	require.NoError(t, err)
	defer bc.Stop()
	S := [32]byte(bc.CurrentBlock().Hash()) // canonical -> passes legacyStateIdIsCanonical, reaches the gather

	// The mainnet full node holds ONLY the genesis (no child) -> the gather from T (=child) misses -> not ready.
	full := newSrv(t.TempDir(), "mainnet", false, [32]byte{0x01})
	defer func() { _ = full.ExternalHeaderTearDown() }()
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	vm.TBCFullNode, vm.TBCFullNodeConfig = full, &tbc.Config{Network: "mainnet"}
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	// The legacy store HAS progressed to T=child with a canonical state-id S.
	home := t.TempDir()
	legacy := newSrv(home, "testnet3", true, S)
	require.NoError(t, legacy.ExternalHeaderTearDown())

	cfg := mainnetMigrateConfig(gen, home)
	require.False(t, bc.migrateHvmHeaderNode(cfg), "a full node missing T's ancestry must DEFER")
	require.Equal(t, "testnet3", cfg.Network, "the gather-not-ready defer must flip Network back to testnet3")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy store must be untouched on the gather-not-ready defer")
	require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "no mainnet store may be created on the gather-not-ready defer")

	reopened := openStoreGuardFree(t, ctx, home, "testnet3")
	require.NoError(t, reopened.Close(), "the legacy store must be re-openable after a gather-not-ready defer")
}
