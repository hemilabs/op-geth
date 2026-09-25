// Copyright 2015 The go-ethereum Authors
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

package core

import (
	"fmt"
	"math"
)

// GasPool tracks the amount of gas available during execution of the transactions
// in a block. The zero value is a pool with zero gas available.
type GasPool uint64

// AddGas makes gas available for execution.
func (gp *GasPool) AddGas(amount uint64) *GasPool {
	if uint64(*gp) > math.MaxUint64-amount {
		panic("gas pool pushed above uint64")
	}
	*(*uint64)(gp) += amount
	return gp
}

// SubGas deducts the given amount from the pool if enough gas is
// available and returns an error otherwise.
func (gp *GasPool) SubGas(amount uint64) error {
	if uint64(*gp) < amount {
		return ErrGasLimitReached
	}
	*(*uint64)(gp) -= amount
	return nil
}

// Gas returns the amount of gas remaining in the pool.
func (gp *GasPool) Gas() uint64 {
	return uint64(*gp)
}

// SetGas sets the amount of gas with the provided number.
func (gp *GasPool) SetGas(gas uint64) {
	*(*uint64)(gp) = gas
}

func (gp *GasPool) String() string {
	return fmt.Sprintf("%d", *gp)
}

// StateGasPool tracks the "state-gas" dimension introduced by EIP-8037
// (Amsterdam/Glamsterdam): a second, independently-tracked block-level gas
// pool that meters state growth, seeded from the same block gas limit as the
// execution GasPool rather than a distinct on-chain limit. Identical
// semantics to GasPool; kept as its own type (not an alias) so call sites
// can't accidentally mix the two pools up.
type StateGasPool uint64

// AddGas makes state-gas available.
func (gp *StateGasPool) AddGas(amount uint64) *StateGasPool {
	if uint64(*gp) > math.MaxUint64-amount {
		panic("state gas pool pushed above uint64")
	}
	*(*uint64)(gp) += amount
	return gp
}

// SubGas deducts the given amount from the state-gas pool if enough is
// available and returns an error otherwise.
func (gp *StateGasPool) SubGas(amount uint64) error {
	if uint64(*gp) < amount {
		return ErrGasLimitReached
	}
	*(*uint64)(gp) -= amount
	return nil
}

// Gas returns the amount of state-gas remaining in the pool.
func (gp *StateGasPool) Gas() uint64 {
	return uint64(*gp)
}

// SetGas sets the amount of state-gas with the provided number.
func (gp *StateGasPool) SetGas(gas uint64) {
	*(*uint64)(gp) = gas
}

func (gp *StateGasPool) String() string {
	return fmt.Sprintf("%d", *gp)
}
