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

package ethash

import (
	"math/big"
	"strings"
	"testing"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
)

type amsterdamHeaderReader struct{ cfg *params.ChainConfig }

func (r amsterdamHeaderReader) Config() *params.ChainConfig                 { return r.cfg }
func (r amsterdamHeaderReader) CurrentHeader() *types.Header                { return nil }
func (r amsterdamHeaderReader) GetHeader(common.Hash, uint64) *types.Header { return nil }
func (r amsterdamHeaderReader) GetHeaderByNumber(uint64) *types.Header      { return nil }
func (r amsterdamHeaderReader) GetHeaderByHash(common.Hash) *types.Header   { return nil }
func (r amsterdamHeaderReader) GetTd(common.Hash, uint64) *big.Int          { return nil }

// TestVerifyHeaderRejectsAmsterdamFields checks that the proof-of-work engine, like
// upstream go-ethereum, never accepts headers carrying the EIP-7928 / EIP-7843 fields.
func TestVerifyHeaderRejectsAmsterdamFields(t *testing.T) {
	cfg := &params.ChainConfig{
		ChainID:             big.NewInt(1),
		HomesteadBlock:      big.NewInt(0),
		EIP150Block:         big.NewInt(0),
		EIP155Block:         big.NewInt(0),
		EIP158Block:         big.NewInt(0),
		ByzantiumBlock:      big.NewInt(0),
		ConstantinopleBlock: big.NewInt(0),
		PetersburgBlock:     big.NewInt(0),
		IstanbulBlock:       big.NewInt(0),
		BerlinBlock:         big.NewInt(0),
		Ethash:              new(params.EthashConfig),
	}
	chain := amsterdamHeaderReader{cfg: cfg}
	engine := NewFaker()
	parent := &types.Header{Number: big.NewInt(0), Difficulty: big.NewInt(131072), GasLimit: 8_000_000, Time: 0}
	mk := func() *types.Header {
		h := &types.Header{Number: big.NewInt(1), GasLimit: 8_000_000, Time: 10, UncleHash: types.EmptyUncleHash}
		h.Difficulty = engine.CalcDifficulty(chain, h.Time, parent)
		return h
	}
	if err := engine.verifyHeader(chain, mk(), parent, false, time.Now().Unix()); err != nil {
		t.Fatalf("baseline header rejected: %v", err)
	}
	slot := uint64(7)
	bal := types.EmptyBlockAccessListHash
	for _, tc := range []struct {
		name    string
		mutate  func(h *types.Header)
		wantErr string
	}{
		{"slotNumber", func(h *types.Header) { h.SlotNumber = &slot }, "invalid slotNumber"},
		{"blockAccessListHash", func(h *types.Header) { h.BlockAccessListHash = &bal }, "invalid blockAccessListHash"},
	} {
		h := mk()
		tc.mutate(h)
		err := engine.verifyHeader(chain, h, parent, false, time.Now().Unix())
		if err == nil || !strings.Contains(err.Error(), tc.wantErr) {
			t.Fatalf("%s: expected error containing %q, got %v", tc.name, tc.wantErr, err)
		}
		func() {
			defer func() {
				if recover() == nil {
					t.Fatalf("%s: SealHash did not panic", tc.name)
				}
			}()
			engine.SealHash(h)
		}()
	}
}
