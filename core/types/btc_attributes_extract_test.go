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

// Direct unit tests for Transactions.ExtractBtcAttrData — the consensus entry that feeds attacker-influenceable
// calldata into UnmarshalBinary. All prior coverage was indirect (a single BtcAttr tx at a fixed index, always
// valid). These pin: the not-found path, position-independence (found at any index), the empty set, the
// multi-tx dedup error, and that a parse error from the FIRST BtcAttr tx propagates (dedup never reached).

import (
	"math/big"
	"testing"

	"github.com/stretchr/testify/require"
)

func tipOf(b byte) [BitcoinHashLengthBytes]byte {
	var t [BitcoinHashLengthBytes]byte
	for i := range t {
		t[i] = b
	}
	return t
}

// validBtcAttrTxWithTip builds a well-formed BtcAttributesDeposited tx carrying the given canonical tip and no
// headers (a valid shape; ExtractBtcAttrData only parses, it does not validate the BTC chain).
func validBtcAttrTxWithTip(t *testing.T, tip byte) *Transaction {
	t.Helper()
	data, err := (&BtcAttributesDepositData{CanonicalTip: tipOf(tip)}).MarshalBinary()
	require.NoError(t, err)
	return NewTx(&BtcAttributesDepositedTx{To: &BtcAttributesDepositedSenderAddress, Gas: 1_000_000, Data: data})
}

// invalidBtcAttrTx builds a tx of the BtcAttr TYPE but with calldata too short to parse (under the minimum) so
// UnmarshalBinary fails — exercising the parse-error propagation path.
func invalidBtcAttrTx() *Transaction {
	return NewTx(&BtcAttributesDepositedTx{To: &BtcAttributesDepositedSenderAddress, Gas: 1_000_000, Data: UpdateHvmStateFuncBytes4[:]})
}

func nonBtcAttrTx() *Transaction { return NewTx(&LegacyTx{}) }

func TestExtractBtcAttrData_NotPresentAndEmpty(t *testing.T) {
	// No BtcAttr tx among non-BtcAttr txs -> (nil, nil), no error.
	got, err := Transactions{nonBtcAttrTx(), nonBtcAttrTx()}.ExtractBtcAttrData()
	require.NoError(t, err)
	require.Nil(t, got, "no BtcAttr tx present -> nil result")

	// Empty tx set -> (nil, nil).
	got, err = Transactions{}.ExtractBtcAttrData()
	require.NoError(t, err)
	require.Nil(t, got, "empty tx set -> nil result")
}

func TestExtractBtcAttrData_FoundAtAnyIndex(t *testing.T) {
	// The BtcAttr tx is the THIRD entry (not index 0/1) — pins the "allow it anywhere" contract; a mutant that
	// only inspects index 0 or 1, or returns early, would miss it.
	txs := Transactions{nonBtcAttrTx(), nonBtcAttrTx(), validBtcAttrTxWithTip(t, 0xAB)}
	got, err := txs.ExtractBtcAttrData()
	require.NoError(t, err)
	require.NotNil(t, got, "a BtcAttr tx at index 2 must be found")
	require.Equal(t, tipOf(0xAB), got.CanonicalTip, "the parsed canonical tip must match the found tx")
}

func TestExtractBtcAttrData_ParseErrorPropagates(t *testing.T) {
	// A BtcAttr tx whose calldata cannot be parsed must surface the UnmarshalBinary error, not be swallowed.
	got, err := Transactions{invalidBtcAttrTx()}.ExtractBtcAttrData()
	require.Error(t, err, "an unparseable BtcAttr tx must propagate the parse error")
	require.Nil(t, got)
	require.Contains(t, err.Error(), "at least", "the error must be the UnmarshalBinary length-floor error")
}

func TestExtractBtcAttrData_MultipleBtcAttrTxsRejected(t *testing.T) {
	// Two VALID BtcAttr txs -> the dedup error (first parsed, second triggers the "more than one" rejection).
	got, err := Transactions{validBtcAttrTxWithTip(t, 0x11), validBtcAttrTxWithTip(t, 0x22)}.ExtractBtcAttrData()
	require.Error(t, err)
	require.Nil(t, got)
	require.Contains(t, err.Error(), "more than one Bitcoin Attributes Deposited transaction",
		"two BtcAttr txs must be rejected by the dedup guard")
}

func TestExtractBtcAttrData_FirstInvalidWinsOverDedup(t *testing.T) {
	// When the FIRST BtcAttr tx is invalid and a valid one follows, the FIRST tx's parse error surfaces — the
	// dedup branch is never reached (first-match-then-parse ordering). Kills a mutant that parses the last tx or
	// moves the dedup check before the parse.
	got, err := Transactions{invalidBtcAttrTx(), validBtcAttrTxWithTip(t, 0x33)}.ExtractBtcAttrData()
	require.Error(t, err)
	require.Nil(t, got)
	require.Contains(t, err.Error(), "at least", "the FIRST (invalid) tx's parse error must surface")
	require.NotContains(t, err.Error(), "more than one", "the dedup guard must NOT be reached when the first tx fails to parse")
}

// TestExtractBtcAttrData_RealisticSystemTxComposition drives ExtractBtcAttrData over the PRODUCTION body shape: a
// deposit/l1-info tx (0x7E) at index 0, a PoP-payout (0x7D) at index 1, and the BtcAttr (0x7C) at index 2 — the
// exact {index 2 with PoP present} layout ExtractBtcAttrData's comment reserves. The type bytes are ADJACENT
// (0x7E/0x7D/0x7C) and detection is an exact Type()==0x7C compare, so a degraded compare (>=, off-by-one, switch
// fall-through) would misread the 0x7D PoP at the reserved slot as the BtcAttr. The existing extract tests use only
// LegacyTx (0x00) decoys, nowhere near the boundary; this is the realistic system-tx mix.
func TestExtractBtcAttrData_RealisticSystemTxComposition(t *testing.T) {
	deposit := NewTx(&DepositTx{Value: big.NewInt(0), Gas: 21000, Data: []byte{0x01}}) // 0x7E
	popTo := PoPPayoutSenderAddress
	pop := NewTx(&PopPayoutTx{To: &popTo, Gas: 21000, Data: []byte{0x11, 0x22, 0x33}}) // 0x7D
	require.Equal(t, uint8(DepositTxType), deposit.Type())
	require.Equal(t, uint8(PopPayoutTxType), pop.Type())

	// (A) realistic {deposit, PoP, BtcAttr}: the BtcAttr at index 2 is found; the adjacent 0x7D PoP is NOT mistaken.
	got, err := Transactions{deposit, pop, validBtcAttrTxWithTip(t, 0xCD)}.ExtractBtcAttrData()
	require.NoError(t, err)
	require.NotNil(t, got)
	require.Equal(t, tipOf(0xCD), got.CanonicalTip, "the BtcAttr (0x7C) must be found among adjacent system-tx types, with the right tip")

	// (B) {deposit, PoP} with NO BtcAttr (the real shape of a non-BtcAttr hVM block): a stray 0x7D must NOT produce
	// a phantom BtcAttr result.
	got, err = Transactions{deposit, pop}.ExtractBtcAttrData()
	require.NoError(t, err)
	require.Nil(t, got, "a PoP-payout (0x7D) must never be misread as a BtcAttr (0x7C)")

	// (C) PoP AFTER the BtcAttr — still exactly one 0x7C, found regardless of the 0x7D's position.
	got, err = Transactions{deposit, validBtcAttrTxWithTip(t, 0xEF), pop}.ExtractBtcAttrData()
	require.NoError(t, err)
	require.NotNil(t, got)
	require.Equal(t, tipOf(0xEF), got.CanonicalTip)
}
