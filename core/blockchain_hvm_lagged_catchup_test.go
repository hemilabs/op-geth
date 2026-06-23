// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

import (
	"bytes"
	"context"
	"fmt"
	"log/slog"
	"math/big"
	"path/filepath"
	"testing"
	"time"

	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

// TestHvmMigration_LaggedStore_CatchUpAdvancesToBodiedTip exercises the forward-catch-up apply loop of
// catchUpMigratedStoreToTip ([S+1 .. tip]) over a genuinely lagged lightweight store. The pre-loop guards
// (no-op-at-tip, unknown-id, from>tip, non-canonical-ancestor) are covered elsewhere; this drives the loop body.
// Needs no real full node or mainnet data.
//
// The seam: build the bodied EVM chain BEFORE attaching the light TBC node, so the node lags by construction.
// Plain Hvm0-active blocks (no BtcAttr tx) are inserted while hvmEnabled==false — the apply path is gated on
// bc.hvmEnabled, so InsertChain touches no TBC store. Then the light node is attached (initHvmHeaderNode does
// only ExternalHeaderSetup, no state restore), leaving the store at the genesis upstream-state-id while
// CurrentBlock() leads it. catchUpMigratedStoreToTip must then walk the store forward to the bodied tip via the
// no-BtcAttr Hvm0 apply branch, which only SetUpstreamStateId's (no full node needed).
func TestHvmMigration_LaggedStore_CatchUpAdvancesToBodiedTip(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	// Hvm0Time=0 so genesis AND every generated block is Hvm0-active (no activation-transition special case, and
	// every no-BtcAttr block takes the IsHvm0 SetUpstreamStateId branch, keeping the parent-chain check valid).
	cfg := *params.TestChainConfig
	hvm0 := uint64(0)
	cfg.Hvm0Time = &hvm0
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}

	// Plain bodied blocks (NO BtcAttr tx), generated + inserted BEFORE the hVM node is attached.
	db, blocks, _ := GenerateChainWithGenesis(gspec, ethash.NewFaker(), 8, func(i int, b *BlockGen) {})
	chain, err := NewBlockChain(db, gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)
	require.False(t, chain.hvmEnabled, "precondition: hVM node not yet attached, so InsertChain touches no TBC store")

	_, err = chain.InsertChain(blocks)
	require.NoError(t, err)
	require.Equal(t, uint64(8), chain.CurrentBlock().Number.Uint64(), "bodied tip lands on disk")

	// Attach the light TBC node LATE (same config as newRegtestChainWithLightTBC) — it does no state restore, so
	// it sits at the genesis upstream-state-id while CurrentBlock() leads it: a genuine lag.
	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header
	tbcCfg := tbc.NewDefaultConfig()
	tbcCfg.ExternalHeaderMode = true
	tbcCfg.EffectiveGenesisBlock = genesis
	tbcCfg.GenesisHeightOffset = 0
	tbcCfg.LevelDBHome = t.TempDir()
	tbcCfg.BlockheaderCacheSize, tbcCfg.BlockCacheSize = "0", "0"
	tbcCfg.AutoIndex, tbcCfg.BlockSanity, tbcCfg.MaxCachedTxs, tbcCfg.MempoolEnabled = false, true, 0, false
	tbcCfg.Network = "localnet"
	chain.initHvmHeaderNode(tbcCfg)
	t.Cleanup(func() { _ = chain.tbcHeaderNode.ExternalHeaderTearDown() })
	require.True(t, chain.hvmEnabled)

	// Set the store's upstream-state-id to an EARLY canonical block S (strictly below the bodied tip).
	s := chain.GetCanonicalHash(2)
	require.NotEqual(t, common.Hash{}, s)
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, [32]byte(s)))
	require.True(t, chain.legacyStateIdIsCanonical([32]byte(s)), "precondition: S is a canonical ancestor at/below the bodied tip")

	// Drive the catch-up apply loop n=3..8. Capture logs: applyHvmHeaderConsensusUpdate emits "Nothing to apply..."
	// per plain block, proving the loop actually walked and applied each [S+1..tip] block rather than jumping
	// straight to SetUpstreamStateId(tip) (which would land the same final state-id but emit none of these logs).
	var ccBuf bytes.Buffer
	ccPrev := log.Root()
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(&ccBuf, slog.LevelDebug, false)))
	require.NoError(t, chain.catchUpMigratedStoreToTip([32]byte(s)))
	log.SetDefault(ccPrev)
	require.Contains(t, ccBuf.String(), "Nothing to apply in hVM state for block",
		"the catch-up loop must apply each intermediate block (not jump straight to the tip state-id)")

	// The store's upstream-state-id must advance exactly to the bodied tip. An off-by-one in the n<=tipN loop bound
	// or a dropped SetUpstreamStateId in the no-BtcAttr branch would both leave it short of CurrentBlock.
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, chain.CurrentBlock().Hash(), common.Hash(*sid),
		"after catch-up the store upstream-state-id must equal the bodied tip")
}

// TestMigrate_LaggedStore_CatchUpThroughOrchestration drives a genuinely lagged store through the full migrate
// orchestration (maybeMigrateHvmHeaderNode), not the standalone catchUpMigratedStoreToTip. The other orchestration
// success tests set S = CurrentBlock().Hash(), making the catch-up a no-op (from==tip early return), so the
// catchUpMigratedStoreToTip call inside migrateHvmHeaderNode and the S->bodied-tip advance go unexercised at the
// orchestration level; dropping that call would still pass those tests yet brick a real lagged-store boot. Needs no
// corpus: real mainnet BTC genesis + synthetic children + an Hvm0 plain-block EVM chain.
func TestMigrate_LaggedStore_CatchUpThroughOrchestration(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node + migrate fixture")
	}
	ctx := context.Background()
	mainnetGen := decodeMainnetGenesisHeader(t)

	// Synthetic children hash-linked from the real mainnet genesis (observe-only never halts on their easy PoW).
	const N = 4
	children := make([]*wire.BlockHeader, N)
	prev := mainnetGen
	for i := 0; i < N; i++ {
		h := &wire.BlockHeader{Version: prev.Version, PrevBlock: prev.BlockHash(), MerkleRoot: mainnetGen.MerkleRoot,
			Timestamp: prev.Timestamp.Add(time.Duration(i+1) * 10 * time.Minute), Bits: mainnetGen.Bits, Nonce: uint32(i + 1)}
		children[i] = h
		prev = h
	}
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

	// An Hvm0-active (Hvm0Time=0) EVM chain of plain (no-BtcAttr) blocks, built BEFORE the hVM node attaches so it
	// lags by construction; the catch-up walks the no-BtcAttr SetUpstreamStateId branch (no full-node read).
	ecfg := *params.TestChainConfig
	hvm0 := uint64(0)
	ecfg.Hvm0Time = &hvm0
	gspec := &Genesis{Config: &ecfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}
	edb, blocks, _ := GenerateChainWithGenesis(gspec, ethash.NewFaker(), 8, func(i int, b *BlockGen) {})
	bc, err := NewBlockChain(edb, gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, ctx)
	require.NoError(t, err)
	defer bc.Stop()
	require.False(t, bc.hvmEnabled, "precondition: no hVM node yet, so InsertChain touches no TBC store")
	_, err = bc.InsertChain(blocks)
	require.NoError(t, err)
	require.Equal(t, uint64(8), bc.CurrentBlock().Number.Uint64())

	// The legacy store records an early canonical state-id S (strictly below the bodied tip) so the catch-up must run.
	S := [32]byte(bc.GetCanonicalHash(2))
	require.True(t, bc.legacyStateIdIsCanonical(S), "precondition: S is canonical and below the bodied tip")
	require.NotEqual(t, bc.CurrentBlock().Hash(), common.Hash(S), "precondition: S lags the bodied tip (catch-up is not a no-op)")

	home := t.TempDir()
	full := newSrv(t.TempDir(), "mainnet", [32]byte{0x01})
	defer func() { _ = full.ExternalHeaderTearDown() }()
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	vm.TBCFullNode, vm.TBCFullNodeConfig = full, &tbc.Config{Network: "mainnet"}
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	legacy := newSrv(home, "testnet3", S)
	require.NoError(t, legacy.ExternalHeaderTearDown())

	cfg := mainnetMigrateConfig(mainnetGen, home)
	handled := bc.maybeMigrateHvmHeaderNode(cfg)
	t.Cleanup(func() {
		if bc.tbcHeaderNode != nil {
			_ = bc.tbcHeaderNode.ExternalHeaderTearDown()
		}
	})
	require.True(t, handled, "a ready full node + a progressed lagged legacy store must MIGRATE")
	require.Equal(t, "mainnet", cfg.Network)

	// The catch-up ran through the orchestration and advanced the rebuilt store from S to the bodied tip.
	sid, err := bc.tbcHeaderNode.UpstreamStateId(ctx)
	require.NoError(t, err)
	require.Equal(t, bc.CurrentBlock().Hash(), common.Hash(*sid),
		"after migration the rebuilt store's upstream-state-id must equal the bodied tip (catch-up advanced S->tip)")

	// Retirement: the backup is named by the legacy (pre-catch-up) state-id S, not the advanced bodied tip.
	// Rollback expects the backup keyed by the pre-migration legacy S. This is the only orchestration success test
	// where S != tip, so naming the backup by the advanced tip would only be detectable here (every other test sets
	// S == CurrentBlock, making the two names identical).
	require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy store must be retired after a lagged migration")
	require.DirExists(t, filepath.Join(home, fmt.Sprintf("testnet3.migrated-%x", S[:])),
		"the backup must be named by the LEGACY state-id S (block-2 hash), not the post-catch-up tip")
	require.NoDirExists(t, filepath.Join(home, fmt.Sprintf("testnet3.migrated-%x", bc.CurrentBlock().Hash().Bytes())),
		"the backup must NOT be named by the post-catch-up bodied tip (S != tip here)")
}
