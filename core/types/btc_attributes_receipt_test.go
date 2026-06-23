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

// The PER-RECEIPT step of the public read path Receipts.DeriveFields for a 0x7C BtcAttr receipt. The DA/L1-fee
// (deriveOPStackFields) half is covered by TestCalcDAFootprintEqualsReceiptBlobGasSum (which calls
// deriveOPStackFields directly). NOT covered: the FIRST step — (*Receipt).DeriveFields — which sets Type, GasUsed
// (position math), EffectiveGasPrice (zero for BtcAttr), sets BlobGasUsed only for BlobTxType, and must preserve the
// BtcAttributesDepositedNonce. Every existing Receipts.DeriveFields test uses bundles without a 0x7C.

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

func TestDeriveFieldsBtcAttrReceiptPerReceiptStep(t *testing.T) {
	config := jovianTestChainConfig()
	config.ChainID = big.NewInt(1) // the per-receipt sender derivation builds a signer from ChainID
	// l1-info (0x7E) + BtcAttr (0x7C): both fixed-sender system txs, so the per-receipt sender derivation needs no
	// signature recovery (an unsigned user LegacyTx would panic on chainID). The per-receipt step still runs for
	// every receipt regardless of the deriveOPStackFields skip.
	txs := []*Transaction{jovianL1InfoTx(400), systemTxBtcAttrTx(t)}
	nonce := uint64(7)
	rs := Receipts{
		{Status: ReceiptStatusSuccessful, CumulativeGasUsed: 5},
		{Status: ReceiptStatusSuccessful, CumulativeGasUsed: 12, BtcAttributesDepositedNonce: &nonce},
	}
	require.NoError(t, rs.DeriveFields(config, common.HexToHash("0xb10c"), 1, 0, big.NewInt(1000), big.NewInt(920), txs))

	btc := rs[1] // the 0x7C receipt
	require.Equal(t, uint8(BtcAttributesDepositedTxType), btc.Type, "Type must be derived to 0x7C")
	require.Equal(t, uint64(12-5), btc.GasUsed, "GasUsed must be the per-position cumulative delta")
	require.NotNil(t, btc.EffectiveGasPrice)
	require.Zero(t, btc.EffectiveGasPrice.Sign(), "a BtcAttr tx has zero effective gas price")
	require.Zero(t, btc.BlobGasUsed, "a non-blob system tx must have zero BlobGasUsed")
	require.NotNil(t, btc.BtcAttributesDepositedNonce, "the BtcAttributesDepositedNonce must be preserved through derivation")
	require.Equal(t, nonce, *btc.BtcAttributesDepositedNonce)
	require.Nil(t, btc.L1Fee, "a zero-DA BtcAttr tx must carry no L1Fee")
	// The l1-info deposit receipt confirms the per-receipt step ran across the bundle (Type derived to 0x7E).
	require.Equal(t, uint8(DepositTxType), rs[0].Type)
}

// TestDeriveFieldsPopPayoutReceiptPerReceiptStep mirrors the 0x7C DeriveFields test for the 0x7D (PoP) sibling: a
// PopPayout receipt's Type derives to 0x7D, GasUsed is the per-position cumulative delta, effective gas price + blob
// gas are zero, and CRITICALLY the PoPPayoutNonce SURVIVES DeriveFields (the per-receipt step must not clobber it).
// The existing PoPPayoutNonce coverage is RLP/JSON round-trips only — none drives DeriveFields, so a type-specific
// nil-out mutant in DeriveFields would escape.
func TestDeriveFieldsPopPayoutReceiptPerReceiptStep(t *testing.T) {
	config := jovianTestChainConfig()
	config.ChainID = big.NewInt(1)
	txs := []*Transaction{jovianL1InfoTx(400), systemTxPopTx()}
	nonce := uint64(7)
	rs := Receipts{
		{Status: ReceiptStatusSuccessful, CumulativeGasUsed: 5},
		{Status: ReceiptStatusSuccessful, CumulativeGasUsed: 12, PoPPayoutNonce: &nonce},
	}
	require.NoError(t, rs.DeriveFields(config, common.HexToHash("0xb10c"), 1, 0, big.NewInt(1000), big.NewInt(920), txs))

	pop := rs[1] // the 0x7D receipt
	require.Equal(t, uint8(PopPayoutTxType), pop.Type, "Type must be derived to 0x7D")
	require.Equal(t, uint64(12-5), pop.GasUsed, "GasUsed must be the per-position cumulative delta")
	require.NotNil(t, pop.EffectiveGasPrice)
	require.Zero(t, pop.EffectiveGasPrice.Sign(), "a PoP tx has zero effective gas price")
	require.Zero(t, pop.BlobGasUsed, "a non-blob system tx must have zero BlobGasUsed")
	require.NotNil(t, pop.PoPPayoutNonce, "the PoPPayoutNonce must be preserved through derivation")
	require.Equal(t, nonce, *pop.PoPPayoutNonce)
	require.Equal(t, uint8(DepositTxType), rs[0].Type, "the l1-info deposit receipt confirms the per-receipt step ran across the bundle")
}
