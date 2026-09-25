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

package gasestimator

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/params"
)

// TestMaxTxGasCapApplies checks that the gas-estimation search ceiling is
// capped at EIP-7825's MaxTxGas from Osaka onward, but NOT under Amsterdam -
// EIP-8037 redefines MaxTxGas to bound only a transaction's execution-gas
// portion there, so a call needing to fund a state-gas reservoir (e.g. a
// large contract deployment) may legitimately need more than MaxTxGas.
func TestMaxTxGasCapApplies(t *testing.T) {
	if maxTxGasCapApplies(params.TestChainConfig, big.NewInt(0), 0) {
		t.Fatalf("pre-Osaka: cap should not apply")
	}

	zero := uint64(0)
	osaka := *params.TestChainConfig
	osaka.OsakaTime = &zero
	if !maxTxGasCapApplies(&osaka, big.NewInt(0), 0) {
		t.Fatalf("Osaka: cap should apply")
	}

	amsterdam := osaka
	amsterdam.AmsterdamTime = &zero
	if maxTxGasCapApplies(&amsterdam, big.NewInt(0), 0) {
		t.Fatalf("Amsterdam: cap should not apply (EIP-8037 reservoir funding needs tx.gas > MaxTxGas)")
	}
}
