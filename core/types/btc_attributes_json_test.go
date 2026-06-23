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

// The 0x7C receipt JSON (eth_getTransactionReceipt) contract: btcAttributesDepositedNonce is surfaced exactly when
// set (omitempty), and round-trips through MarshalJSON/UnmarshalJSON. The receipt RLP + per-receipt DeriveFields are
// covered; the JSON path for the 0x7C nonce field was not (the existing TestReceiptJSON bundle has no 0x7C fixtures).

import (
	"encoding/json"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestBtcAttrReceiptJSONNonce(t *testing.T) {
	// With a nonce: the field is present and round-trips.
	b, err := json.Marshal(btcAttributesDepositedWithNonce)
	require.NoError(t, err)
	require.Contains(t, string(b), "btcAttributesDepositedNonce", "a set nonce must appear in the receipt JSON")
	var got Receipt
	require.NoError(t, json.Unmarshal(b, &got))
	require.NotNil(t, got.BtcAttributesDepositedNonce)
	require.Equal(t, *btcAttributesDepositedWithNonce.BtcAttributesDepositedNonce, *got.BtcAttributesDepositedNonce)

	// Without a nonce: omitempty drops the field and it round-trips as nil.
	b2, err := json.Marshal(btcAttributesDepositedWithNoNonce)
	require.NoError(t, err)
	require.NotContains(t, string(b2), "btcAttributesDepositedNonce", "an unset nonce must be omitted (omitempty)")
	var got2 Receipt
	require.NoError(t, json.Unmarshal(b2, &got2))
	require.Nil(t, got2.BtcAttributesDepositedNonce)
}
