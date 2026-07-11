// Copyright 2024 The go-ethereum Authors
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
