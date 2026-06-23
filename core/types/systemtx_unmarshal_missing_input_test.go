// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package types

// The 0x7C (BtcAttributesDeposited) and 0x7D (PoPPayout) UnmarshalJSON arms dereference *dec.Input, so a missing
// "input" field must be rejected with a clean "missing required field 'input'" error (as every other tx type does)
// rather than nil-deref panicking. Block import / RPC decode must never panic on malformed JSON.

import (
	"encoding/json"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestSystemTxUnmarshalJSONMissingInput(t *testing.T) {
	for _, tc := range []struct {
		name string
		json string
	}{
		{"btcattr-0x7c", `{"type":"0x7c","to":"0x8888888888888888888888888888888888888888","gas":"0xf4240","gasPrice":"0x0"}`},
		{"poppayout-0x7d", `{"type":"0x7d","to":"0x4200000000000000000000000000000000000042","gas":"0xc350","gasPrice":"0x0"}`},
	} {
		t.Run(tc.name, func(t *testing.T) {
			var tx Transaction
			var err error
			require.NotPanics(t, func() { err = json.Unmarshal([]byte(tc.json), &tx) },
				"a %s tx JSON without 'input' must not panic", tc.name)
			require.Error(t, err, "missing 'input' must be a decode error")
			require.Contains(t, err.Error(), "input", "the error must name the missing 'input' field")
		})
	}
}
