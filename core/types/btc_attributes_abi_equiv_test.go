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

// Dual-commit consistency: processing an hVM block mutates BOTH the EVM state (the updateHvmState(bytes32,bytes[])
// call to the 0x8400 predeploy, decoded with the canonical Solidity/accounts/abi decoder, its state root part of the
// L2 block hash) AND the BTC view (BtcAttributesDepositData.UnmarshalBinary of the SAME tx.Data()). The two are
// independent parsers. Existing tests prove only MarshalBinary matches a hand-asserted golden and round-trips with
// its own UnmarshalBinary — nothing machine-checks the emitted bytes against the ABI decoder the EVM actually uses.
// A format change that kept the bespoke round-trip green but broke ABI-equivalence would make the predeploy and the
// view extract DIFFERENT (tip, headers), silently diverging EVM-recorded hVM state from the consensus BTC view.

import (
	"testing"

	"github.com/ethereum/go-ethereum/accounts/abi"
	"github.com/stretchr/testify/require"
)

func TestBtcAttrCalldataAbiEquivalence(t *testing.T) {
	bytes32T, err := abi.NewType("bytes32", "", nil)
	require.NoError(t, err)
	bytesArrT, err := abi.NewType("bytes[]", "", nil)
	require.NoError(t, err)
	args := abi.Arguments{{Type: bytes32T}, {Type: bytesArrT}}

	mkHdr := func(seed byte) [BitcoinHeaderLengthBytes]byte {
		var h [BitcoinHeaderLengthBytes]byte
		for i := range h {
			h[i] = seed + byte(i)
		}
		return h
	}

	for _, n := range []int{0, 1, 2, MaximumBtcHeadersInTx} {
		hdrs := make([][BitcoinHeaderLengthBytes]byte, n)
		for i := range hdrs {
			hdrs[i] = mkHdr(byte(i + 1))
		}
		tip := tipOf(byte(0x40 + n))
		data, err := (&BtcAttributesDepositData{CanonicalTip: tip, Headers: hdrs}).MarshalBinary()
		require.NoError(t, err)
		require.Equal(t, UpdateHvmStateFuncBytes4[:], data[:4], "selector prefix (%d headers)", n)

		// Decode the calldata with the SAME ABI decoder the 0x8400 predeploy uses.
		vals, err := args.UnpackValues(data[4:])
		require.NoErrorf(t, err, "the EVM ABI decoder must accept the emitted calldata (%d headers)", n)
		abiTip := vals[0].([32]byte)
		abiHdrs := vals[1].([][]byte)
		require.Equalf(t, [32]byte(tip), abiTip, "ABI-decoded canonical tip must equal the source (%d headers)", n)
		require.Lenf(t, abiHdrs, n, "ABI-decoded header count (%d headers)", n)
		for i := range hdrs {
			require.Equalf(t, hdrs[i][:], abiHdrs[i], "ABI-decoded header %d must be the exact 80 bytes the predeploy sees (%d headers)", i, n)
		}

		// And the view's bespoke parser must agree on the same bytes.
		var view BtcAttributesDepositData
		require.NoError(t, view.UnmarshalBinary(data))
		require.Equal(t, tip, view.CanonicalTip)
		require.Equal(t, hdrs, view.Headers)
	}

	// The view must be STRICTLY stronger than the ABI decoder: a bytes[] element of length != 80 is valid ABI (the
	// predeploy would decode a wrong-length header) but UnmarshalBinary must REJECT it — so the view can never apply
	// something the predeploy would silently accept as a header.
	shortPacked, err := args.Pack([32]byte(tipOf(0x99)), [][]byte{make([]byte, 79)})
	require.NoError(t, err)
	roundtrip, err := args.UnpackValues(shortPacked)
	require.NoError(t, err, "the ABI decoder accepts a 79-byte bytes[] element")
	require.Len(t, roundtrip[1].([][]byte)[0], 79)
	bad := append(append([]byte{}, UpdateHvmStateFuncBytes4[:]...), shortPacked...)
	require.Error(t, new(BtcAttributesDepositData).UnmarshalBinary(bad),
		"the view must REJECT a non-80-byte header the ABI decoder accepts (view is stricter than ABI)")
}
