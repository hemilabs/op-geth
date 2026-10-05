// Copyright 2026 Hemi Labs, Inc.
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

package ethapi

import (
	"encoding/json"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/core/types"
)

// TestRPCMarshalHeaderAmsterdamFields checks that the EIP-7928 and EIP-7843 header fields
// are exposed over JSON-RPC under upstream's names when set, and omitted when nil, so a
// header served by this node round-trips to the same hash on the consumer side.
func TestRPCMarshalHeaderAmsterdamFields(t *testing.T) {
	legacy := &types.Header{Number: big.NewInt(1), Difficulty: big.NewInt(0)}
	out := RPCMarshalHeader(legacy)
	if _, ok := out["blockAccessListHash"]; ok {
		t.Fatalf("legacy header must not expose blockAccessListHash")
	}
	if _, ok := out["slotNumber"]; ok {
		t.Fatalf("legacy header must not expose slotNumber")
	}

	bal := types.EmptyBlockAccessListHash
	slot := uint64(42)
	amsterdam := &types.Header{Number: big.NewInt(1), Difficulty: big.NewInt(0), BlockAccessListHash: &bal, SlotNumber: &slot}
	out = RPCMarshalHeader(amsterdam)
	if got, ok := out["blockAccessListHash"].(*common.Hash); !ok || *got != bal {
		t.Fatalf("blockAccessListHash: have %v, want %s", out["blockAccessListHash"], bal)
	}
	if got, ok := out["slotNumber"].(hexutil.Uint64); !ok || uint64(got) != slot {
		t.Fatalf("slotNumber: have %v, want %d", out["slotNumber"], slot)
	}
	if got := out["hash"].(common.Hash); got != amsterdam.Hash() {
		t.Fatalf("hash: have %s, want %s", got, amsterdam.Hash())
	}

	// What this node serves over eth_getBlockByNumber must decode on a consumer (op-node,
	// ethclient) into a Header with the same hash.
	enc, err := json.Marshal(out)
	if err != nil {
		t.Fatal(err)
	}
	var consumer types.Header
	if err := json.Unmarshal(enc, &consumer); err != nil {
		t.Fatal(err)
	}
	if consumer.Hash() != amsterdam.Hash() {
		t.Fatalf("RPC round trip: have %s, want %s", consumer.Hash(), amsterdam.Hash())
	}
	if consumer.SlotNumber == nil || *consumer.SlotNumber != slot || consumer.BlockAccessListHash == nil || *consumer.BlockAccessListHash != bal {
		t.Fatalf("RPC round trip lost the Amsterdam fields")
	}
}
