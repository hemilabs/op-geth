// Copyright 2024 The go-ethereum Authors
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

package types

// The 0x7C BtcAttributesDeposited TX-LEVEL accessor contract the apply/fee/mempool paths rely on: zero
// gas/value/nonce/effective-price, fixed To, defensive-copied big.Int getters, and the unsupported sign operation
// PANICS (not silently zero). None of these were pinned at the Transaction level.

import (
	"bytes"
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"
)

func TestBtcAttrTxAccessorContract(t *testing.T) {
	tip := chainhash.Hash{0x01, 0x02, 0x03}
	inner, err := MakeBtcAttributesDepositedTx(&tip, []wire.BlockHeader{{Version: 1, Bits: 0x207fffff, Nonce: 7}})
	require.NoError(t, err)
	tx := NewTx(inner)

	// Zero economic fields.
	require.Zero(t, tx.Value().Sign(), "Value is zero")
	require.Zero(t, tx.GasPrice().Sign(), "GasPrice is zero")
	require.Zero(t, tx.GasTipCap().Sign(), "GasTipCap is zero")
	require.Zero(t, tx.GasFeeCap().Sign(), "GasFeeCap is zero")
	require.Equal(t, uint64(0), tx.Nonce(), "Nonce is zero (set during execution)")

	// Structural fields pass through. Pin Gas to the hardcoded constructor constant (1M) rather than to inner.Gas
	// (a self-comparison: both sides resolve to the same field, so a constructor gas-value mutant would survive).
	require.Equal(t, uint64(1_000_000), tx.Gas(), "BtcAttributesDeposited must use the hardcoded 1M system-tx gas")
	require.Equal(t, inner.To, tx.To())
	require.True(t, bytes.Equal(inner.Data, tx.Data()))
	// Data must be DEFENSIVELY COPIED by the constructor's copy(): mutating the wrapped tx's Data must not affect the
	// original inner.Data. bytes.Equal alone passes even if both share one backing array, so mutate-and-recheck.
	d := tx.Data()
	require.NotEmpty(t, d, "anti-vacuity: Data must be non-empty for the mutation to be observable")
	innerSnapshot := append([]byte{}, inner.Data...)
	for i := range d {
		d[i] ^= 0xFF
	}
	require.Equal(t, innerSnapshot, inner.Data, "the constructor must defensively copy Data (no shared backing array)")

	// Defensive copy: the big.Int getters must not alias internal state.
	a, b := tx.GasPrice(), tx.GasPrice()
	a.SetInt64(99)
	require.Zero(t, b.Sign(), "GasPrice must return a fresh copy each call (no alias leak)")

	// Cost is zero (zero value + zero gas price) regardless of the large 1M gas limit.
	require.Greater(t, tx.Gas(), uint64(0), "anti-vacuity: a nonzero gas-price mutant would surface in Cost")
	require.Zero(t, tx.Cost().Sign(), "Cost is zero for a fee-free system tx")

	// EffectiveGasTip: zero with no base fee; below-base-fee with a positive base fee (gasFeeCap 0 < baseFee).
	gt, err := tx.EffectiveGasTip(nil)
	require.NoError(t, err)
	require.Zero(t, gt.Sign())
	_, err = tx.EffectiveGasTip(big.NewInt(1000))
	require.ErrorIs(t, err, ErrGasFeeCapTooLow, "a zero fee cap is below any positive base fee")

	// The unsupported sign operation must PANIC (reachable via Signer.Hash -> inner.sigHash), not silently return zero.
	require.Panics(t, func() { _ = LatestSignerForChainID(big.NewInt(1)).Hash(tx) },
		"signing a BtcAttr tx must panic (it is force-included, never signed)")
}

// TestMakeBtcAttributesDepositedTxToField pins that the CONSTRUCTOR MakeBtcAttributesDepositedTx sets To to the
// hardcoded consensus sender (BtcAttributesDepositedSenderAddress, 0x8888...). The accessor-contract test compares
// the constructor's output To against ITSELF (a wrapper pass-through), so a mutant changing the constructor's To
// assignment (e.g. to HvmStateAddress) survives it; the sender-identity tests build To manually. This pins the
// actual assignment line. Value comparison (Transaction.To() returns a fresh copy, so pointer-eq would not hold).
func TestMakeBtcAttributesDepositedTxToField(t *testing.T) {
	inner, err := MakeBtcAttributesDepositedTx(&chainhash.Hash{0x01}, nil)
	require.NoError(t, err)
	tx := NewTx(inner)
	require.NotNil(t, tx.To(), "the constructor must set a non-nil To")
	require.Equal(t, BtcAttributesDepositedSenderAddress, *tx.To(),
		"MakeBtcAttributesDepositedTx must set To = the hardcoded consensus sender (kills a constructor To-reassignment mutant)")
}
