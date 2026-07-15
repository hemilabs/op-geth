// Copyright 2026 The go-ethereum Authors
// Copyright 2026 Hemi Labs, Inc.
// This file is part of go-ethereum.
//
// go-ethereum is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// go-ethereum is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with go-ethereum. If not, see <http://www.gnu.org/licenses/>.

package main

import (
	"testing"

	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/eth/ethconfig"
	"github.com/stretchr/testify/require"
)

// TestResolveTBCNetwork pins the flag>TOML>default precedence that drives BOTH the full node and the lightweight
// hVM header node from one value (so the v1 "lightweight testnet3 over a mainnet fleet" mislabel cannot recur).
// The key regression guard is the flagSet=false + TOML="mainnet" case: a mutant that reads the flag default
// blindly (dropping the TOML honor) would clobber a TOML-configured mainnet node back to testnet3 and silently
// run the wrong network. Pure logic — no node, no header corpus.
func TestResolveTBCNetwork(t *testing.T) {
	const dflt = ethconfig.DefaultTBCNetwork // the value ctx.String returns when the flag is unset
	cases := []struct {
		name      string
		flagValue string
		flagSet   bool
		tomlValue string
		want      string
	}{
		{"flag wins over TOML", "mainnet", true, "testnet3", "mainnet"},
		{"flag wins over empty TOML", "mainnet", true, "", "mainnet"},
		{"TOML honored when flag unset", dflt, false, "mainnet", "mainnet"}, // <- the critical regression guard
		{"default when flag unset and TOML empty", dflt, false, "", dflt},
		{"flag unset, TOML equals default", dflt, false, dflt, dflt},
		{"explicit flag equal to default still wins over TOML", dflt, true, "mainnet", dflt},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := resolveTBCNetwork(tc.flagValue, tc.flagSet, tc.tomlValue)
			if got != tc.want {
				t.Fatalf("resolveTBCNetwork(%q, %v, %q) = %q, want %q", tc.flagValue, tc.flagSet, tc.tomlValue, got, tc.want)
			}
		})
	}
}

// TestValidateFullNodeHvmGenesisPair covers the fail-fast wiring makeFullNode uses for the non-consensus full
// TBC node: the header hex is parsed, its BlockHash().String() + the height are classified for the given network,
// and a DESYNCED pair or a bad header is rejected while a canonical or fully-custom pair is accepted. This
// exercises the whole call path (network arg, hash-string format, the mismatch predicate, the parse-error guard)
// that only inspection covered otherwise. The mainnet effective-genesis pair is the canonical fixture.
func TestValidateFullNodeHvmGenesisPair(t *testing.T) {
	// Canonical: the pinned mainnet (height, header) pair is accepted and the parsed header returned.
	h, err := validateFullNodeHvmGenesisPair("mainnet", vm.MainnetHvmGenesisHeader, vm.MainnetHvmGenesisHeight)
	require.NoError(t, err, "the canonical mainnet pair must be accepted")
	require.NotNil(t, h)
	require.Equal(t, vm.MainnetHvmGenesisHash, h.BlockHash().String(), "returned header must be the parsed mainnet genesis header")

	// Mismatch: canonical header but the wrong height (desynced) is rejected — verifies the height and the
	// hash-string are both threaded into the predicate for the right network.
	_, err = validateFullNodeHvmGenesisPair("mainnet", vm.MainnetHvmGenesisHeader, vm.MainnetHvmGenesisHeight+1)
	require.Error(t, err, "a desynced (right header, wrong height) pair must be rejected")
	require.Contains(t, err.Error(), "DESYNCED")

	// Custom: an unpinned network (no checkpoint) makes any well-formed pair fully custom, which is LEGITIMATE
	// for the non-consensus full node and must be allowed through — the property AL-CT's request hinges on.
	_, err = validateFullNodeHvmGenesisPair("localnet", vm.MainnetHvmGenesisHeader, vm.MainnetHvmGenesisHeight)
	require.NoError(t, err, "a fully-custom pair on an unpinned network must be allowed (not a mismatch)")

	// Bad header hex is rejected up front (the parse-error guard that also prevents a nil-header deref).
	_, err = validateFullNodeHvmGenesisPair("mainnet", "not-valid-hex-zz", 0)
	require.Error(t, err, "an unparseable --hvm.genesisheader must be rejected before use")
	require.Contains(t, err.Error(), "parse hVM effective-genesis header")
}
