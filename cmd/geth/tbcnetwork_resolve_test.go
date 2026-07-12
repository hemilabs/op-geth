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

	"github.com/ethereum/go-ethereum/eth/ethconfig"
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
