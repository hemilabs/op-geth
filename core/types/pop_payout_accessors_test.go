// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

// The 0x7D PopPayout TX-LEVEL accessor contract the apply/fee/mempool paths rely on, mirroring
// TestBtcAttrTxAccessorContract for 0x7C: zero gas-price/value/tip/feecap/nonce, fixed To/Gas/Data pass-through,
// defensive-copied big.Int getters, zero Cost, EffectiveGasTip behavior, and the unsupported sign operation PANICS.

import (
	"bytes"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

func TestPopPayoutTxAccessorContract(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	inner := &PopPayoutTx{To: &to, Gas: 50_000, Data: []byte{0xc9, 0x4f}}
	tx := NewTx(inner)

	// Zero economic fields.
	require.Zero(t, tx.Value().Sign(), "Value is zero")
	require.Zero(t, tx.GasPrice().Sign(), "GasPrice is zero")
	require.Zero(t, tx.GasTipCap().Sign(), "GasTipCap is zero")
	require.Zero(t, tx.GasFeeCap().Sign(), "GasFeeCap is zero")
	require.Equal(t, uint64(0), tx.Nonce(), "Nonce is zero (set during execution)")

	// Structural fields pass through.
	require.Equal(t, inner.Gas, tx.Gas())
	require.Equal(t, inner.To, tx.To())
	require.True(t, bytes.Equal(inner.Data, tx.Data()))

	// Defensive copy: the big.Int getters must not alias internal state.
	a, b := tx.GasPrice(), tx.GasPrice()
	a.SetInt64(99)
	require.Zero(t, b.Sign(), "GasPrice must return a fresh copy each call (no alias leak)")

	// Cost is zero (zero value + zero gas price).
	require.Greater(t, tx.Gas(), uint64(0), "anti-vacuity: a nonzero gas-price mutant would surface in Cost")
	require.Zero(t, tx.Cost().Sign(), "Cost is zero for a fee-free system tx")

	// EffectiveGasTip: zero with no base fee; below-base-fee error with a positive base fee.
	gt, err := tx.EffectiveGasTip(nil)
	require.NoError(t, err)
	require.Zero(t, gt.Sign())
	_, err = tx.EffectiveGasTip(big.NewInt(1000))
	require.ErrorIs(t, err, ErrGasFeeCapTooLow, "a zero fee cap is below any positive base fee")

	// The unsupported sign operation must PANIC (reachable via Signer.Hash -> inner.sigHash).
	require.Panics(t, func() { _ = LatestSignerForChainID(big.NewInt(1)).Hash(tx) },
		"signing a PoP tx must panic (it is force-included, never signed)")
}
