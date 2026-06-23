// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

import (
	"encoding/json"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

// TestSystemTxMarshalJSONRoundTrip pins that the Hemi-added system tx types (BtcAttributesDeposited 0x7C and
// PopPayout 0x7D) round-trip through the GENERIC Transaction.MarshalJSON/UnmarshalJSON.
//
// Both types define an UnmarshalJSON arm; without a matching MarshalJSON arm a generic marshal emits
// to/gas/input/gasPrice as null and the symmetric unmarshal then fails ("missing required field 'to'") — the same
// oversight a MarshalJSON arm on depositTxWithNonce exists to avoid. The live RPC path (newRPCTransaction) is
// unaffected (it populates fields directly), but the generic path (signer/rules.go, t8n tooling) would break.
// This test locks the symmetric behavior and would catch a regression that drops the MarshalJSON arms.
func TestSystemTxMarshalJSONRoundTrip(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000015")
	data := []byte{0x01, 0x02, 0x03, 0x04}

	cases := []struct {
		name  string
		inner TxData
		typ   byte
		nonce uint64 // expected effective nonce (0 when unset)
	}{
		{"btcattr", &BtcAttributesDepositedTx{To: &to, Gas: 1_000_000, Data: data}, BtcAttributesDepositedTxType, 0},
		{"btcattr-nonce", &btcAttributesDepositedTxWithNonce{BtcAttributesDepositedTx: BtcAttributesDepositedTx{To: &to, Gas: 1_000_000, Data: data}, EffectiveNonce: 42}, BtcAttributesDepositedTxType, 42},
		{"pop", &PopPayoutTx{To: &to, Gas: 500_000, Data: data}, PopPayoutTxType, 0},
		{"pop-nonce", &popPayoutTxWithNonce{PopPayoutTx: PopPayoutTx{To: &to, Gas: 500_000, Data: data}, EffectiveNonce: 7}, PopPayoutTxType, 7},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			// setDecoded (not NewTx) mirrors how UnmarshalJSON installs the inner: the *WithNonce wrappers define no
			// copy(), so NewTx().copy() would fall through to the embedded type and silently drop the nonce. A
			// re-marshal in production always operates on a setDecoded-installed inner.
			tx := new(Transaction)
			tx.setDecoded(tc.inner, 0)

			b, err := json.Marshal(tx)
			require.NoError(t, err)

			// The fields UnmarshalJSON requires non-nil must be populated (not the null output a missing MarshalJSON arm would produce).
			var raw map[string]json.RawMessage
			require.NoError(t, json.Unmarshal(b, &raw))
			for _, f := range []string{"to", "gas", "input", "gasPrice"} {
				require.NotEqual(t, "null", string(raw[f]), "field %q must not marshal to null", f)
			}
			require.Equal(t, `"0x0"`, string(raw["gasPrice"]), "system tx gasPrice must serialize as 0")

			// Round-trip back through the generic path.
			var got Transaction
			require.NoError(t, json.Unmarshal(b, &got), "the symmetric unmarshal must succeed")
			require.Equal(t, tc.typ, got.Type())
			require.Equal(t, to, *got.To())
			require.Equal(t, tx.Gas(), got.Gas())
			require.Equal(t, data, got.Data())
			// The nonce surfaces via EffectiveNonce() (the inner nonce() is always 0 for these system txs).
			require.Equal(t, tc.nonce, *got.EffectiveNonce(), "effective nonce must round-trip (0 when unset)")
		})
	}
}

// TestBtcAttrTxUnmarshalJSONWithNonce pins the 0x7C UnmarshalJSON nonce arm directly from a hand-written JSON
// literal (independent of MarshalJSON): when "nonce" is present, the decoder wraps the inner in
// btcAttributesDepositedTxWithNonce and preserves it via EffectiveNonce(). When absent, EffectiveNonce reports 0.
// A mutant deleting the wrapper construction (transaction_marshalling.go ~654) or corrupting the stored nonce
// would survive every other test (no test decoded a 0x7C JSON object). The decode dereferences "input" with no
// nil-guard, so the literal includes it (along with the required to/gas).
func TestBtcAttrTxUnmarshalJSONWithNonce(t *testing.T) {
	withNonce := `{"type":"0x7c","nonce":"0x2a","to":"0x4200000000000000000000000000000000000015",` +
		`"gas":"0xf4240","gasPrice":"0x0","input":"0x01020304"}`
	var tx Transaction
	require.NoError(t, json.Unmarshal([]byte(withNonce), &tx))
	require.Equal(t, byte(BtcAttributesDepositedTxType), tx.Type())
	_, ok := tx.inner.(*btcAttributesDepositedTxWithNonce)
	require.True(t, ok, "a 0x7C JSON carrying a nonce must decode into the *WithNonce wrapper")
	require.Equal(t, uint64(0x2a), *tx.EffectiveNonce(), "the decoded nonce must be preserved")

	noNonce := `{"type":"0x7c","to":"0x4200000000000000000000000000000000000015",` +
		`"gas":"0xf4240","gasPrice":"0x0","input":"0x01020304"}`
	var tx2 Transaction
	require.NoError(t, json.Unmarshal([]byte(noNonce), &tx2))
	_, ok = tx2.inner.(*BtcAttributesDepositedTx)
	require.True(t, ok, "a 0x7C JSON without a nonce must decode into the bare type")
	require.Equal(t, uint64(0), *tx2.EffectiveNonce())
}
