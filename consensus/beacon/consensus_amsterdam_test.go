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

package beacon

import (
	"math/big"
	"strings"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/consensus/misc/eip1559"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
)

// amsterdamFieldsConfig is a post-merge, London-only chain configuration (no Shanghai or
// later timestamp forks), so verifyHeader exercises exactly the base checks plus the
// Amsterdam header-field rule under test.
func amsterdamFieldsConfig(amsterdamTime *uint64) *params.ChainConfig {
	return &params.ChainConfig{
		ChainID:                 big.NewInt(1),
		HomesteadBlock:          big.NewInt(0),
		EIP150Block:             big.NewInt(0),
		EIP155Block:             big.NewInt(0),
		EIP158Block:             big.NewInt(0),
		ByzantiumBlock:          big.NewInt(0),
		ConstantinopleBlock:     big.NewInt(0),
		PetersburgBlock:         big.NewInt(0),
		IstanbulBlock:           big.NewInt(0),
		BerlinBlock:             big.NewInt(0),
		LondonBlock:             big.NewInt(0),
		TerminalTotalDifficulty: big.NewInt(0),
		AmsterdamTime:           amsterdamTime,
	}
}

func amsterdamFieldsHeaders(cfg *params.ChainConfig) (parent, header *types.Header) {
	parent = &types.Header{
		Number:     big.NewInt(0),
		Difficulty: big.NewInt(0),
		GasLimit:   30_000_000,
		BaseFee:    big.NewInt(params.InitialBaseFee),
		Time:       0,
	}
	header = &types.Header{
		ParentHash: parent.Hash(),
		UncleHash:  types.EmptyUncleHash,
		Number:     big.NewInt(1),
		Difficulty: big.NewInt(0),
		GasLimit:   30_000_000,
		Time:       1,
		BaseFee:    eip1559.CalcBaseFee(cfg, parent, 1),
	}
	return parent, header
}

// TestVerifyHeaderAmsterdamFields checks the presence / absence rules for the EIP-7928
// blockAccessListHash and EIP-7843 slotNumber header fields. Every chain this build runs
// must reject headers carrying them (core.NewBlockChain refuses an amsterdamTime); the
// post-Amsterdam branch is kept identical to upstream go-ethereum so the rule is complete
// if the fork is ever implemented, and is exercised here with a config built directly.
func TestVerifyHeaderAmsterdamFields(t *testing.T) {
	var (
		zero  = uint64(0)
		slot  = uint64(7)
		bal   = types.EmptyBlockAccessListHash
		noBAL *common.Hash
		noSlt *uint64
	)
	tests := []struct {
		name          string
		amsterdamTime *uint64
		bal           *common.Hash
		slot          *uint64
		wantErr       string
	}{
		{"pre-amsterdam: no fields", nil, noBAL, noSlt, ""},
		{"pre-amsterdam: blockAccessListHash present", nil, &bal, noSlt, "invalid block access list hash"},
		{"pre-amsterdam: slotNumber present", nil, noBAL, &slot, "invalid slotNumber"},
		{"pre-amsterdam: both present", nil, &bal, &slot, "invalid block access list hash"},
		{"amsterdam: both present", &zero, &bal, &slot, ""},
		{"amsterdam: missing blockAccessListHash", &zero, noBAL, &slot, "missing block access list hash"},
		{"amsterdam: missing slotNumber", &zero, &bal, noSlt, "missing slotNumber"},
		{"amsterdam: missing both", &zero, noBAL, noSlt, "missing block access list hash"},
	}
	engine := New(ethash.NewFaker())
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := amsterdamFieldsConfig(tt.amsterdamTime)
			parent, header := amsterdamFieldsHeaders(cfg)
			header.BlockAccessListHash = tt.bal
			header.SlotNumber = tt.slot
			err := engine.verifyHeader(extraDataHeaderReader{cfg: cfg}, header, parent)
			switch {
			case tt.wantErr == "" && err != nil:
				t.Fatalf("unexpected error: %v", err)
			case tt.wantErr != "" && err == nil:
				t.Fatalf("expected error containing %q, got nil", tt.wantErr)
			case tt.wantErr != "" && !strings.Contains(err.Error(), tt.wantErr):
				t.Fatalf("expected error containing %q, got %v", tt.wantErr, err)
			}
		})
	}
}
