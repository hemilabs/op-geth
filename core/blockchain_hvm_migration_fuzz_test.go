// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

import (
	"context"
	"encoding/hex"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/core/vm"
)

// ---------------------------------------------------------------------------
// (a) FuzzClassifyHvmGenesisPairing — never panics; result is exactly one of 3
//     enum values; for a checkpointed network an exact match is Canonical and a
//     single-field match is Mismatch.
// ---------------------------------------------------------------------------

func FuzzClassifyHvmGenesisPairing(f *testing.F) {
	// Seeds: real checkpointed nets, the empty/whitespace net, a malformed hash.
	f.Add("mainnet", vm.MainnetHvmGenesisHeight, vm.MainnetHvmGenesisHash)
	f.Add("testnet3", uint64(3522419), "000000000000000096c98151accc5ee217d7cc4ff1e59a3d91e4c9365c4ea144")
	f.Add("upgradetest", uint64(3522419), "000000000000000096c98151accc5ee217d7cc4ff1e59a3d91e4c9365c4ea144")
	f.Add("", uint64(0), "")
	f.Add("   ", uint64(883092), "zzzz")
	f.Add("mainnet", vm.MainnetHvmGenesisHeight, "deadbeef") // height matches, hash diverges
	f.Add("mainnet", uint64(1), vm.MainnetHvmGenesisHash)    // hash matches, height diverges
	f.Add("localnet", uint64(0), "")

	f.Fuzz(func(t *testing.T, network string, height uint64, hash string) {
		got := classifyHvmGenesisPairing(network, height, hash)

		// INVARIANT 1: exactly one of the three enum values.
		switch got {
		case hvmGenesisPairingCanonical, hvmGenesisPairingCustom, hvmGenesisPairingMismatch:
			// ok
		default:
			t.Fatalf("classifyHvmGenesisPairing returned out-of-range value %d for (%q,%d,%q)", got, network, height, hash)
		}

		// INVARIANT 2: for a checkpointed network, exact match => Canonical, single-field match => Mismatch.
		cps := hvmGenesisCheckpoints[network]
		anyExact, anyHeightOnly, anyHashOnly := false, false, false
		for _, cp := range cps {
			hEq, sEq := cp.height == height, cp.hash == hash
			switch {
			case hEq && sEq:
				anyExact = true
			case hEq && !sEq:
				anyHeightOnly = true
			case !hEq && sEq:
				anyHashOnly = true
			}
		}
		if anyExact && got != hvmGenesisPairingCanonical {
			t.Fatalf("exact checkpoint match must be Canonical, got %d for (%q,%d,%q)", got, network, height, hash)
		}
		// A single-field match with NO exact match must be Mismatch.
		if !anyExact && (anyHeightOnly || anyHashOnly) && got != hvmGenesisPairingMismatch {
			t.Fatalf("single-field checkpoint match (no exact) must be Mismatch, got %d for (%q,%d,%q)", got, network, height, hash)
		}
		// No checkpoint touched at all => Custom.
		if !anyExact && !anyHeightOnly && !anyHashOnly && got != hvmGenesisPairingCustom {
			t.Fatalf("no-checkpoint-touch must be Custom, got %d for (%q,%d,%q)", got, network, height, hash)
		}

		// INVARIANT 3: IsCanonicalHvmGenesisPairing agrees with the classifier.
		if IsCanonicalHvmGenesisPairing(network, height, hash) != (got == hvmGenesisPairingCanonical) {
			t.Fatalf("IsCanonicalHvmGenesisPairing disagrees with classifier for (%q,%d,%q)", network, height, hash)
		}
	})
}

// ---------------------------------------------------------------------------
// (b) FuzzCanonicalBTCNetwork — idempotent; only "upgradetest" changes.
// ---------------------------------------------------------------------------

func FuzzCanonicalBTCNetwork(f *testing.F) {
	f.Add("mainnet")
	f.Add("testnet3")
	f.Add("upgradetest")
	f.Add("localnet")
	f.Add("")
	f.Add("UpgradeTest") // case sensitivity probe
	f.Add(" upgradetest ")

	f.Fuzz(func(t *testing.T, network string) {
		c := canonicalBTCNetwork(network)

		// INVARIANT 1: idempotent.
		if cc := canonicalBTCNetwork(c); cc != c {
			t.Fatalf("canonicalBTCNetwork not idempotent: canonical(%q)=%q, canonical(canonical)=%q", network, c, cc)
		}

		// INVARIANT 2: only "upgradetest" changes; everything else is identity.
		if network == "upgradetest" {
			if c != "testnet3" {
				t.Fatalf("upgradetest must canonicalize to testnet3, got %q", c)
			}
		} else if c != network {
			t.Fatalf("canonicalBTCNetwork(%q) changed a non-upgradetest network to %q", network, c)
		}
	})
}

// ---------------------------------------------------------------------------
// (c) Property test for gatherHeadersBackToGenesis over randomly-linked fake
//     chains (incl. cycles): termination + ascending + genesis-exclusion.
//     The seed corpus drives both adversarial topologies and a randomized loop.
// ---------------------------------------------------------------------------

// adversarialLookup serves arbitrary, possibly-malicious header graphs (cycles,
// dead ends, non-descending heights) to stress gatherHeadersBackToGenesis.
type adversarialLookup struct {
	byHash map[chainhash.Hash]*wire.BlockHeader
	height map[chainhash.Hash]uint64
}

func (a *adversarialLookup) BlockHeaderByHash(_ context.Context, h chainhash.Hash) (*wire.BlockHeader, uint64, error) {
	hdr, ok := a.byHash[h]
	if !ok {
		return nil, 0, errNotFoundFuzz
	}
	return hdr, a.height[h], nil
}

var errNotFoundFuzz = &notFoundErr{}

type notFoundErr struct{}

func (e *notFoundErr) Error() string { return "not found" }

// buildGraphFromSeed deterministically builds a header graph from a byte seed by
// linking each header's PrevBlock to an arbitrary other header (possibly itself,
// possibly forming cycles), with arbitrary (possibly non-descending) heights.
func buildGraphFromSeed(seed []byte, n int, genesisHeight uint64) (*adversarialLookup, []chainhash.Hash, chainhash.Hash) {
	if n < 1 {
		n = 1
	}
	if n > 64 {
		n = 64
	}
	lk := &adversarialLookup{byHash: map[chainhash.Hash]*wire.BlockHeader{}, height: map[chainhash.Hash]uint64{}}
	hdrs := make([]*wire.BlockHeader, n)
	hashes := make([]chainhash.Hash, n)
	for i := 0; i < n; i++ {
		hdrs[i] = &wire.BlockHeader{Version: 1, Bits: 0x207fffff, Nonce: uint32(i)*7919 + 1}
	}
	// Link PrevBlock by seed bytes (allows cycles, self-loops, forward links).
	for i := 0; i < n; i++ {
		var sel byte
		if len(seed) > 0 {
			sel = seed[i%len(seed)]
		}
		target := int(sel) % n
		hdrs[i].PrevBlock = hdrs[target].BlockHash()
	}
	for i := 0; i < n; i++ {
		hh := hdrs[i].BlockHash()
		hashes[i] = hh
		lk.byHash[hh] = hdrs[i]
		// Arbitrary heights from the seed — may be non-descending along PrevBlock links.
		var hsel byte
		if len(seed) > 1 {
			hsel = seed[(i*3+1)%len(seed)]
		}
		lk.height[hh] = genesisHeight + uint64(hsel)
	}
	// Pick an arbitrary genesis hash NOT in the graph (so the only termination is
	// via the height-floor / cycle guards), or in-graph if seed says so.
	genesis := chainhash.Hash{0xde, 0xad}
	if len(seed) > 2 && seed[2]&1 == 1 && n > 0 {
		genesis = hashes[int(seed[0])%n]
	}
	return lk, hashes, genesis
}

func FuzzGatherHeadersBackToGenesis(f *testing.F) {
	f.Add([]byte{1, 2, 3, 4}, 8)
	f.Add([]byte{0, 0, 0, 0}, 4) // all link to header 0 -> potential self/cycle
	f.Add([]byte{255, 1, 1}, 16) // genesis-in-graph probe
	f.Add([]byte{}, 1)           // single node, links to self -> cycle
	f.Add([]byte{7, 7, 7, 7, 7}, 32)

	const gh = uint64(883092)

	f.Fuzz(func(t *testing.T, seed []byte, n int) {
		lk, hashes, genesis := buildGraphFromSeed(seed, n, gh)

		// Pick a tip from the seed.
		tip := genesis
		if len(hashes) > 0 {
			idx := 0
			if len(seed) > 0 {
				idx = int(seed[len(seed)-1]) % len(hashes)
			}
			tip = hashes[idx]
		}

		// INVARIANT (termination): this call MUST return. The test harness itself
		// catches a hang via the test timeout; we rely on the cycle/height guards.
		got, ok := gatherHeadersBackToGenesis(context.Background(), lk, tip, genesis, gh)

		if !ok {
			// Defer path: ok=false MUST come with an empty slice. Callers treat ok=false as defer and
			// must never consume a partial slice; returning partial headers here would pass silently.
			if len(got) != 0 {
				t.Fatalf("ok=false (defer) must return an empty slice, got %d headers", len(got))
			}
			return
		}

		// INVARIANT (genesis-exclusion): genesis hash never appears in the result.
		for i, h := range got {
			hh := h.BlockHash()
			if hh == genesis {
				t.Fatalf("genesis hash present in gathered result at index %d", i)
			}
		}

		// INVARIANT (ascending by height): each successive header strictly ascends.
		for i := 1; i < len(got); i++ {
			prevH := lk.height[got[i-1].BlockHash()]
			curH := lk.height[got[i].BlockHash()]
			if curH <= prevH {
				t.Fatalf("gathered headers not strictly ascending: idx %d height %d <= idx %d height %d", i, curH, i-1, prevH)
			}
		}

		// INVARIANT (all above floor): every gathered header is strictly above genesisHeight.
		for i, h := range got {
			if lk.height[h.BlockHash()] <= gh {
				t.Fatalf("gathered header at idx %d has height %d <= genesisHeight %d", i, lk.height[h.BlockHash()], gh)
			}
		}
	})
}

// Sanity: decode helper used by seeds (keeps imports honest if seeds change).
var _ = hex.DecodeString
