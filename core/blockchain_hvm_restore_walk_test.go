// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Boot-sequence coverage for performFullHvmHeaderStateRestore — the steady-state recovery path SetupHvmHeaderNode
// takes (after NewBlockChain) when the lightweight store sits at the genesis upstream-state-id while the persisted
// EVM tip is already Hvm0-active. It is a DISTINCT implementation from catchUpMigratedStoreToTip (which the lagged
// tests cover): restore (a) resets the node to genesis, then (b) forward-walks from the Phase-0 activation block to
// CurrentBlock() reading DISK blocks and applying each, crit-ing on any error. No test exercises this disk
// forward-walk over a real lightweight node with bodied blocks: the only restore test runs on a genesis-only chain
// (zero blocks replayed, only proving teardown ran). Corpus-free: plain (no-BtcAttr) Hvm0 blocks take the
// SetUpstreamStateId-only apply branch, so no full node / Bitcoin corpus is needed.

import (
	"context"
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

func TestPerformFullHvmHeaderStateRestoreWalksDiskToTip(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	// Hvm0Time=0 so genesis and every block are Hvm0-active and every (no-BtcAttr) block takes the
	// SetUpstreamStateId apply branch.
	cfg := *params.TestChainConfig
	hvm0 := uint64(0)
	cfg.Hvm0Time = &hvm0
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}

	db, blocks, _ := GenerateChainWithGenesis(gspec, ethash.NewFaker(), 8, func(i int, b *BlockGen) {})
	chain, err := NewBlockChain(db, gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)
	require.False(t, chain.hvmEnabled, "precondition: no hVM node yet, so InsertChain touches no TBC store")
	_, err = chain.InsertChain(blocks)
	require.NoError(t, err)
	require.Equal(t, uint64(8), chain.CurrentBlock().Number.Uint64())

	// Attach the light node LATE -> it sits at the genesis upstream-state-id while the EVM tip leads it (a genuine
	// lag, the exact boot state SetupHvmHeaderNode's restore branch handles).
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
	sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId, *sid0, "precondition: the freshly-attached store lags at the genesis upstream-state-id")

	// Drive the disk forward-walk (resets to genesis, replays activation..tip from disk).
	chain.performFullHvmHeaderStateRestore()

	// ORACLE: the forward-walk advanced the store's upstream-state-id exactly to the bodied disk tip (block 8).
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, chain.CurrentBlock().Hash(), common.Hash(*sid),
		"performFullHvmHeaderStateRestore must forward-walk the disk chain to CurrentBlock and set the state-id to the tip")
}
