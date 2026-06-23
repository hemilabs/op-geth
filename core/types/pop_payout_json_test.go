// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

// The 0x7D (PoP payout) receipt JSON (eth_getTransactionReceipt) contract: popPayoutNonce is surfaced exactly when
// set (omitempty) and round-trips through MarshalJSON/UnmarshalJSON. Mirrors TestBtcAttrReceiptJSONNonce for 0x7C —
// the PoP receipt RLP is covered but its JSON nonce path (the field RPC clients read) was not.

import (
	"encoding/json"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestPopPayoutReceiptJSONNonce(t *testing.T) {
	// With a nonce: the field is present and round-trips.
	b, err := json.Marshal(popPayoutReceiptWithNonce)
	require.NoError(t, err)
	require.Contains(t, string(b), "popPayoutNonce", "a set PoP nonce must appear in the receipt JSON")
	var got Receipt
	require.NoError(t, json.Unmarshal(b, &got))
	require.NotNil(t, got.PoPPayoutNonce)
	require.Equal(t, *popPayoutReceiptWithNonce.PoPPayoutNonce, *got.PoPPayoutNonce)

	// Without a nonce: omitempty drops the field and it round-trips as nil.
	b2, err := json.Marshal(popPayoutReceiptNoNonce)
	require.NoError(t, err)
	require.NotContains(t, string(b2), "popPayoutNonce", "an unset PoP nonce must be omitted (omitempty)")
	var got2 Receipt
	require.NoError(t, json.Unmarshal(b2, &got2))
	require.Nil(t, got2.PoPPayoutNonce)
}
