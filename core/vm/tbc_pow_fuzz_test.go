// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package vm

// Fuzz coverage for the PURE BTC-header PoW batch check (CheckBTCHeaderBatchPoWForNetwork). It validates header PoW
// without the embedded full node, so it is corpus-free. Block-apply and snap paths feed it untrusted header bytes;
// the property is that arbitrary input never panics (it returns nil or an error).

import (
	"bytes"
	"testing"

	"github.com/btcsuite/btcd/wire"
)

func FuzzCheckBTCHeaderBatchPoW(f *testing.F) {
	f.Add([]byte{})
	f.Add(make([]byte, 80))
	f.Add(make([]byte, 160))
	f.Fuzz(func(t *testing.T, raw []byte) {
		// Slice raw into up to 8 candidate 80-byte headers; skip blobs that don't deserialize.
		var hdrs []*wire.BlockHeader
		for off := 0; off+80 <= len(raw) && len(hdrs) < 8; off += 80 {
			h := new(wire.BlockHeader)
			if err := h.Deserialize(bytes.NewReader(raw[off : off+80])); err != nil {
				return
			}
			hdrs = append(hdrs, h)
		}
		// Property: never panics for any network/header combination (returns nil or an error).
		_ = CheckBTCHeaderBatchPoWForNetwork("localnet", hdrs)
		_ = CheckBTCHeaderBatchPoWForNetwork("mainnet", hdrs)
	})
}
