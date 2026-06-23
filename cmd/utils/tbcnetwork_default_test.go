// Copyright 2024 The go-ethereum Authors
// This file is part of go-ethereum.
//
// Licensed under the GNU GPL v3. See the go-ethereum LICENSE file.

package utils

import (
	"testing"

	"github.com/ethereum/go-ethereum/eth/ethconfig"
)

// TestTBCNetworkDefaultsAreBound pins the three independent TBC-network defaults to ONE shared constant so they
// cannot silently diverge: the --tbc.network flag Value (cmd/utils/flags.go), ethconfig.Defaults.TBCNetwork
// (the value loadBaseConfig seeds before flag resolution), and ethconfig.DefaultTBCNetwork (the eth/backend.go
// empty-config fallback also references it). If any drifts, a geth node could run the lightweight hVM header
// node on a different Bitcoin network than the full node — the exact mislabel the migration exists to kill.
// Node-free and corpus-free.
func TestTBCNetworkDefaultsAreBound(t *testing.T) {
	if TBCNetwork.Value != ethconfig.DefaultTBCNetwork {
		t.Fatalf("--tbc.network flag default %q != ethconfig.DefaultTBCNetwork %q (the flag default drifted)",
			TBCNetwork.Value, ethconfig.DefaultTBCNetwork)
	}
	if ethconfig.Defaults.TBCNetwork != ethconfig.DefaultTBCNetwork {
		t.Fatalf("ethconfig.Defaults.TBCNetwork %q != ethconfig.DefaultTBCNetwork %q (the ethconfig default drifted)",
			ethconfig.Defaults.TBCNetwork, ethconfig.DefaultTBCNetwork)
	}
}
