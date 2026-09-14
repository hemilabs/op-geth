// Copyright 2026 Hemi Labs, Inc.
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package miner

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/params"
)

func osakaOnlyConfig() *params.ChainConfig {
	cfg := *params.TestChainConfig
	zero := uint64(0)
	cfg.OsakaTime = &zero
	return &cfg
}

func osakaAmsterdamConfig() *params.ChainConfig {
	cfg := *osakaOnlyConfig()
	zero := uint64(0)
	cfg.AmsterdamTime = &zero
	return &cfg
}

// TestPendingGasLimitCap checks that the miner's pending-transaction
// GasLimitCap filter enforces EIP-7825's MaxTxGas from Osaka onward, but does
// NOT apply it under Amsterdam - EIP-8037 redefines MaxTxGas to bound only a
// transaction's execution-gas portion there, so a transaction may legitimately
// declare more gas than that to fund its state-gas reservoir; filtering such
// transactions out of the pending set would make that mechanism unusable.
func TestPendingGasLimitCap(t *testing.T) {
	if got := pendingGasLimitCap(params.TestChainConfig, big.NewInt(0), 0); got != 0 {
		t.Fatalf("pre-Osaka cap = %d; want 0 (no cap)", got)
	}
	if got := pendingGasLimitCap(osakaOnlyConfig(), big.NewInt(0), 0); got != params.MaxTxGas {
		t.Fatalf("Osaka cap = %d; want %d", got, params.MaxTxGas)
	}
	if got := pendingGasLimitCap(osakaAmsterdamConfig(), big.NewInt(0), 0); got != 0 {
		t.Fatalf("Amsterdam cap = %d; want 0 (no cap - EIP-8037 reservoir funding needs tx.gas > MaxTxGas)", got)
	}
}

// TestMinPackableTxGas checks that the miner's "not enough gas left to pack
// another transaction" threshold uses EIP-2780's lower TX_BASE_COST under
// Amsterdam instead of the legacy flat TxGas, so the miner doesn't stop
// filling a block prematurely.
func TestMinPackableTxGas(t *testing.T) {
	if got := minPackableTxGas(params.TestChainConfig, big.NewInt(0), 0); got != params.TxGas {
		t.Fatalf("pre-Amsterdam minPackableTxGas = %d; want %d", got, params.TxGas)
	}
	if got := minPackableTxGas(osakaAmsterdamConfig(), big.NewInt(0), 0); got != params.TxBaseCostEIP2780 {
		t.Fatalf("Amsterdam minPackableTxGas = %d; want %d", got, params.TxBaseCostEIP2780)
	}
}
