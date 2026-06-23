// Copyright 2024 The go-ethereum Authors
// This file is part of go-ethereum.
//
// Licensed under the GNU GPL v3. See the go-ethereum LICENSE file.

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
