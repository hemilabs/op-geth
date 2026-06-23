// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Build-path LIVENESS: the sequencer build path must always yield a PROPOSABLE result, never a halting error that
// would stall block production. GetBitcoinAttributesForNextBlock returns a clean (nil tx, nil err) on a degenerate
// full-node feed via two arms: (a) the light tip already equals the full tip (idle), and (b) the light view LEADS
// the full node on the same chain (the deliberately-deferred arm that returns nil only after both cursors walk down
// to the lower common height). This is the only end-to-end coverage of GetBitcoinAttributesForNextBlock; the
// decomposed pure helpers (recordHvmBtcAttrResult, btcAttrFutureSkewExceeded, the prefix arms) are covered separately. A
// regression returning an error or the pending sentinel on these arms would stall the sequencer whenever its own
// view briefly leads the full node, and pass every existing test.

import (
	"context"
	"testing"
	"time"

	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

func TestGetBitcoinAttributesForNextBlockNonStall(t *testing.T) {
	if testing.Short() {
		t.Skip("builds real lightweight TBC nodes")
	}
	ctx := context.Background()
	now := uint64(time.Now().Unix())
	hvm0Time := now - 10_000 // so IsHvm0(now) is true and now is not future-skewed

	// A second external-header tbc.Server stands in for vm.TBCFullNode (the "full-node feed"). Same regtest genesis.
	newFullNode := func() *tbc.Server {
		g := &chaincfg.RegressionNetParams.GenesisBlock.Header
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = g
		cfg.GenesisHeightOffset = 0
		cfg.LevelDBHome = t.TempDir()
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, true, 0, false
		cfg.Network = "localnet"
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		return srv
	}
	withFullNode := func(t *testing.T, full *tbc.Server) {
		prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
		vm.TBCFullNode, vm.TBCFullNodeConfig = full, &tbc.Config{Network: "localnet"}
		t.Cleanup(func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg })
	}

	// (a) IDLE: light and full both at the genesis checkpoint (equal tips) -> (nil, nil), no stall.
	t.Run("equal-tips-idle", func(t *testing.T) {
		chain, _ := newRegtestChainWithLightTBC(t, hvm0Time)
		full := newFullNode()
		t.Cleanup(func() { _ = full.ExternalHeaderTearDown() })
		withFullNode(t, full)

		tx, err := chain.GetBitcoinAttributesForNextBlock(now)
		require.NoError(t, err, "an idle (equal-tip) feed must not stall the build path")
		require.Nil(t, tx, "no BtcAttr tx is proposed when the BTC view is already caught up")
	})

	// (b) LIGHT-AHEAD on the same chain: the light node holds h1..h4, the full node only h1..h2 -> after walking
	// both cursors down to the common height the light view leads -> (nil, nil), no stall.
	t.Run("light-ahead-same-chain", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)
		full := newFullNode()
		t.Cleanup(func() { _ = full.ExternalHeaderTearDown() })
		withFullNode(t, full)

		// One shared chain h1..h4.
		hdrs := make([]*wire.BlockHeader, 0, 4)
		prev := genesis
		for i := 0; i < 4; i++ {
			h := mineRegtestChild(t, prev, uint32(i)*53+1)
			hdrs = append(hdrs, h)
			prev = h
		}
		// Light gets all four; full only the first two prefix. State-id kept at genesis on the light node so the
		// build path's getHeaderModeTBCEVMHeader stays on the clean (nil) arm.
		_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: hdrs}, hVMGenesisUpstreamId[:])
		require.NoError(t, err)
		_, _, _, _, err = full.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: hdrs[:2]}, hVMGenesisUpstreamId[:])
		require.NoError(t, err)

		_, lightTipBefore, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
		require.NoError(t, err)
		sidBefore, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		tx, err := chain.GetBitcoinAttributesForNextBlock(now)
		require.NoError(t, err, "a light-ahead same-chain feed must not stall the build path")
		require.Nil(t, tx, "no BtcAttr tx is proposed when the light view already leads the full node")
		// The build/query path is READ-ONLY w.r.t. the lightweight consensus view: deciding there is nothing to
		// propose must not move the tip or advance the upstream-state-id.
		_, lightTipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
		require.NoError(t, err)
		require.Equal(t, lightTipBefore.BlockHash(), lightTipAfter.BlockHash(), "the build path must not move the lightweight tip")
		sidAfter, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		require.Equal(t, sidBefore[:], sidAfter[:], "the build path must not advance the upstream-state-id")
	})
}
