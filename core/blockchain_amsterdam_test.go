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

package core

import (
	"strings"
	"testing"

	"github.com/ethereum/go-ethereum/consensus/beacon"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
)

// TestInsertChainRejectsAmsterdamHeaderFields checks, at the block-import level, that a
// locally served chain (which never activates Amsterdam on this build) rejects blocks
// whose headers carry the EIP-7928 blockAccessListHash or EIP-7843 slotNumber fields,
// while the untouched block imports normally. This exercises the block-import path
// (insertChain -> VerifyHeaders -> beacon.verifyHeader) shared by InsertChain,
// InsertBlockWithoutSetHead (engine_newPayload) and the downloader.
func TestInsertChainRejectsAmsterdamHeaderFields(t *testing.T) {
	engine := beacon.New(ethash.NewFaker())
	gspec := &Genesis{Config: params.MergedTestChainConfig, Alloc: types.GenesisAlloc{}}
	_, blocks, _ := GenerateChainWithGenesis(gspec, engine, 2, nil)

	tamper := func(b *types.Block, mutate func(h *types.Header)) *types.Block {
		h := b.Header()
		mutate(h)
		return b.WithSeal(h)
	}
	slot := uint64(7)
	bal := types.EmptyBlockAccessListHash
	cases := []struct {
		name    string
		block   *types.Block
		wantErr string
	}{
		{"slotNumber present", tamper(blocks[0], func(h *types.Header) { h.SlotNumber = &slot }), "invalid slotNumber: have 7, expected nil"},
		{"blockAccessListHash present", tamper(blocks[0], func(h *types.Header) { h.BlockAccessListHash = &bal }), "invalid block access list hash"},
		{"both present", tamper(blocks[0], func(h *types.Header) { h.SlotNumber = &slot; h.BlockAccessListHash = &bal }), "invalid block access list hash"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			chain, err := NewBlockChain(rawdb.NewMemoryDatabase(), gspec, nil, engine, nil, nil, nil, t.Context())
			if err != nil {
				t.Fatal(err)
			}
			defer chain.Stop()
			if tc.block.Hash() == blocks[0].Hash() {
				t.Fatalf("tampered header did not change the block hash")
			}
			_, err = chain.InsertChain([]*types.Block{tc.block})
			if err == nil || !strings.Contains(err.Error(), tc.wantErr) {
				t.Fatalf("expected error containing %q, got %v", tc.wantErr, err)
			}
			if chain.CurrentBlock().Number.Uint64() != 0 {
				t.Fatalf("tampered block was imported")
			}
			// The genuine blocks import fine afterwards.
			if _, err := chain.InsertChain(blocks); err != nil {
				t.Fatalf("importing untampered chain: %v", err)
			}
			if have := chain.CurrentBlock().Hash(); have != blocks[1].Hash() {
				t.Fatalf("head: have %s, want %s", have, blocks[1].Hash())
			}
			if hdr := chain.CurrentBlock(); hdr.SlotNumber != nil || hdr.BlockAccessListHash != nil {
				t.Fatalf("locally produced header carries Amsterdam fields")
			}
		})
	}
}

// TestNewBlockChainRejectsAmsterdamTime checks that this build refuses to run a chain
// whose configuration activates Amsterdam, whether or not it is an OP-Stack chain, while
// the same configuration without the fork time is accepted.
func TestNewBlockChainRejectsAmsterdamTime(t *testing.T) {
	zero := uint64(0)
	plain := *params.MergedTestChainConfig
	plain.BlobScheduleConfig = &params.BlobScheduleConfig{
		Cancun:    params.DefaultCancunBlobConfig,
		Prague:    params.DefaultPragueBlobConfig,
		Osaka:     params.DefaultOsakaBlobConfig,
		Amsterdam: params.DefaultOsakaBlobConfig,
	}
	op := *params.MergedTestChainConfig
	op.Optimism = &params.OptimismConfig{EIP1559Elasticity: 6, EIP1559Denominator: 50}
	op.BlobScheduleConfig = nil

	for _, tc := range []struct {
		name string
		cfg  params.ChainConfig
	}{{"plain", plain}, {"op-stack", op}} {
		t.Run(tc.name, func(t *testing.T) {
			cfg := tc.cfg
			gspec := &Genesis{Config: &cfg, Alloc: types.GenesisAlloc{}}
			chain, err := NewBlockChain(rawdb.NewMemoryDatabase(), gspec, nil, beacon.New(ethash.NewFaker()), nil, nil, nil, t.Context())
			if err != nil {
				t.Fatalf("config without amsterdamTime rejected: %v", err)
			}
			chain.Stop()

			cfg.AmsterdamTime = &zero
			gspec = &Genesis{Config: &cfg, Alloc: types.GenesisAlloc{}}
			chain, err = NewBlockChain(rawdb.NewMemoryDatabase(), gspec, nil, beacon.New(ethash.NewFaker()), nil, nil, nil, t.Context())
			if err == nil {
				chain.Stop()
				t.Fatalf("config with amsterdamTime accepted")
			}
			if !strings.Contains(err.Error(), "amsterdamTime is not supported by this build") {
				t.Fatalf("unexpected error: %v", err)
			}
		})
	}
}
