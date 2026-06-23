// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Boot-time hVM difficulty-enforcement decision, exercised through the REAL initHvmHeaderNode path (a live
// lightweight TBC node), not just the isLegacyDeferredPairing predicate. This is the integration the apply-path
// gate tests and the pure-predicate test do not cover: that a node which boots in the legacy DEFER state
// (network="testnet3" over the Bitcoin-MAINNET genesis pair — the classifier accepts it via the testnet3 dual-pin)
// comes up UNENFORCED, while a genuine testnet3 node and a migrated mainnet node both come up ENFORCED. Corpus-free.

import (
	"testing"

	"bytes"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/log"
	"github.com/stretchr/testify/require"
)

func TestHvmBootEnforcementDecision(t *testing.T) {
	if testing.Short() {
		t.Skip("builds real lightweight TBC nodes")
	}
	mainnetGen := decodeMainnetGenesisHeader(t)

	cases := []struct {
		name    string
		network string
		genesis *wire.BlockHeader
		height  uint64
		enforce bool
	}{
		{
			// DEFER state: testnet3 params over the Bitcoin-mainnet pair (the legacy mislabel / migration defer
			// fallback). Accepted by the pairing guard (testnet3 dual-pins {883092,…}), but must boot UNENFORCED —
			// enforcing real mainnet headers under TestNet3Params would split from a migrated fleet.
			name: "deferred-testnet3-over-mainnet-pair", network: "testnet3",
			genesis: mainnetGen, height: vm.MainnetHvmGenesisHeight, enforce: false,
		},
		{
			// Genuine testnet3 node (the shipped consensus network) at its own canonical pair -> ENFORCED.
			name: "genuine-testnet3", network: "testnet3",
			genesis: mustEffectiveGenesisHeader(t), height: canonicalHvmGenesisHeight, enforce: true,
		},
		{
			// Migrated mainnet node at the mainnet pair -> ENFORCED (keyed on the (network,height) pair, not the
			// word "migrated").
			name: "migrated-mainnet", network: "mainnet",
			genesis: mainnetGen, height: vm.MainnetHvmGenesisHeight, enforce: true,
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			chain := newHvmInitTestChain(t)
			cfg := hvmInitLightTBCConfig(t, tc.network, tc.genesis, tc.height)

			// Capture logs across initHvmHeaderNode to assert the DEFER-boot operator warning (the only split-
			// prevention signal). It fires ONLY on the unenforced (deferred) path; enforced boots must stay silent.
			var buf bytes.Buffer
			prev := log.Root()
			log.SetDefault(log.NewLogger(log.NewTerminalHandler(&buf, false)))
			chain.initHvmHeaderNode(cfg) // crits (os.Exit) if the pairing guard rejects -> reaching below proves it booted
			log.SetDefault(prev)
			t.Cleanup(func() {
				if chain.tbcHeaderNode != nil {
					_ = chain.tbcHeaderNode.ExternalHeaderTearDown()
				}
			})
			require.True(t, chain.hvmEnabled, "the node must have booted hVM (pairing guard accepted the pair)")
			require.Equal(t, tc.enforce, chain.hvmDiffEnforceable.Load(),
				"boot-time difficulty enforcement decision for %s", tc.name)
			require.NotNil(t, chain.tbcHeaderNodeConfig, "tbcHeaderNodeConfig must be initialized")
			require.Equal(t, tc.network, chain.tbcHeaderNodeConfig.Network, "config network must match input: %s vs %s", tc.network, chain.tbcHeaderNodeConfig.Network)
			require.Equal(t, tc.height, chain.tbcHeaderNodeConfig.GenesisHeightOffset, "config genesis height must match input: %d vs %d", tc.height, chain.tbcHeaderNodeConfig.GenesisHeightOffset)
			if tc.enforce {
				require.NotContains(t, buf.String(), "enforcement DISABLED", "an ENFORCED boot must NOT emit the defer warning")
			} else {
				require.Contains(t, buf.String(), "enforcement DISABLED", "a DEFER boot must warn the operator not to sequence on it")
			}
		})
	}
}
