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

package vm

// Tests for the hard per-validation walk-hop bound (maxHeaderCtxWalkHops /
// tbcCtxResolver.walkExceeded). The bound makes per-header ancestry-lookup work provably O(maxHops) on
// the enforced, network-reachable gossip path, regardless of stored-chain shape, and fails safe to
// skip (never a false difficulty rejection).

import (
	"context"
	"fmt"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"
)

// countingLookup wraps a headerLookup and counts BlockHeaderByHash calls so a test can assert the
// walk-hop bound actually caps store work.
type countingLookup struct {
	inner headerLookup
	calls int
}

func (c *countingLookup) BlockHeaderByHash(ctx context.Context, h chainhash.Hash) (*wire.BlockHeader, uint64, error) {
	c.calls++
	return c.inner.BlockHeaderByHash(ctx, h)
}

var _ headerLookup = (*countingLookup)(nil)

func TestMaxHeaderCtxWalkHops(t *testing.T) {
	// All three reachable networks derive BlocksPerRetarget == 2016, so the bound is 2*2016+256.
	require.Equal(t, 2*2016+256, maxHeaderCtxWalkHops(&chaincfg.MainNetParams))
	require.Equal(t, 2*2016+256, maxHeaderCtxWalkHops(&chaincfg.TestNet3Params))
	require.Equal(t, 2*2016+256, maxHeaderCtxWalkHops(&chaincfg.RegressionNetParams),
		"localnet/regtest derives the same 2016 retarget interval (PoWNoRetargeting does not change the divisor)")

	// Pin the formula with the correct operand order recomputed from the params, so a
	// TargetTimePerBlock/TargetTimespan operand-swap (which the bpr<1 floor could otherwise mask) is
	// caught: TargetTimePerBlock/TargetTimespan == 0 -> floor 2016 -> 4288 would still match a naive
	// `== 4288`, but recomputing with the right order does not.
	for _, p := range []*chaincfg.Params{&chaincfg.MainNetParams, &chaincfg.TestNet3Params, &chaincfg.RegressionNetParams} {
		bpr := int(p.TargetTimespan / p.TargetTimePerBlock)
		require.Equal(t, 2*bpr+256, maxHeaderCtxWalkHops(p), "bound must derive from TargetTimespan/TargetTimePerBlock")
	}

	// The bound must exceed a single legitimate retarget walk (BlocksPerRetarget-1 = 2015) plus the
	// ~11-block MTP window, or honest boundary headers would be false-skipped.
	require.Greater(t, maxHeaderCtxWalkHops(&chaincfg.MainNetParams), 2015+16)

	// Exercise the bpr<1 floor branch (the three real networks never do — all derive 2016): params
	// whose TargetTimespan/TargetTimePerBlock truncates to 0 must floor to 2016 -> 4288. Kills a
	// floor-constant change, a guard inversion, and deletion of the floor block.
	floored := &chaincfg.Params{TargetTimespan: time.Second, TargetTimePerBlock: time.Minute}
	require.Equal(t, 2*2016+256, maxHeaderCtxWalkHops(floored), "bpr<1 must floor to 2016 (=4288)")
}

// TestParamsForNetwork regression-locks op-geth's network->params mapping (the lockstep invariant in
// contracts.go): the enforced validator computes expected difficulty against these params, so a silent
// edit that remapped a network would, under enforcement, drop every honest boundary header.
// Distinguishes by GenesisHash (not PowLimitBits — mainnet and testnet3 share 0x1d00ffff) and pins the
// fail-closed default arm.
func TestParamsForNetwork(t *testing.T) {
	for net, want := range map[string]*chaincfg.Params{
		"mainnet":     &chaincfg.MainNetParams,
		"testnet3":    &chaincfg.TestNet3Params,
		"upgradetest": &chaincfg.TestNet3Params, // lockstep with the TBC node: upgradetest == testnet3
		"localnet":    &chaincfg.RegressionNetParams,
	} {
		got, err := paramsForNetwork(net)
		require.NoError(t, err, "known network %q must map", net)
		require.Same(t, want, got, "network %q must map to its exact chaincfg params", net)
		require.Equal(t, want.GenesisHash.String(), got.GenesisHash.String(), "genesis hash for %q", net)
	}
	// Fail closed on anything else — including testnet variants and case/spelling drift — so an
	// unknown network never silently leaves tbcChainParams nil. Pin both that params is nil (the exact
	// fail-closed contract — a default arm leaking non-nil params would be the dangerous bug) and the
	// exact error text.
	for _, bad := range []string{"", "testnet", "mainnett", "regtest", "MAINNET", "Testnet3"} {
		got, err := paramsForNetwork(bad)
		require.Nil(t, got, "unknown network %q must return nil params (fail closed)", bad)
		require.EqualError(t, err, fmt.Sprintf("unknown TBC network: %q", bad))
	}
}

// TestWalkHopBoundTripsToSkip exercises the bound mechanism directly: a walk longer than the cap
// latches walkExceeded, returns interface-nil, and performs no more than maxHops store lookups.
func TestWalkHopBoundTripsToSkip(t *testing.T) {
	const chainLen = 60
	store, hdrs := buildChainTS(chainLen, mainBits, func(i int) int64 { return int64(1_600_000_000 + i*600) })
	cnt := &countingLookup{inner: store}

	const cap = 10
	res := &tbcCtxResolver{ctx: context.Background(), lookup: cnt, params: &chaincfg.MainNetParams, maxHops: cap}
	tip := &tbcHeaderCtx{hdr: hdrs[chainLen-1], height: uint64(chainLen - 1), res: res}

	// Ask for more hops than the cap permits.
	anc := tip.RelativeAncestorCtx(int32(chainLen - 1))
	require.Nil(t, anc, "a walk exceeding the hop cap must return interface-nil")
	require.True(t, res.walkExceeded, "exceeding maxHops must latch walkExceeded")
	require.Equal(t, cap, cnt.calls, "store lookups must be capped at exactly maxHops")

	// Once latched, further fetches short-circuit without touching the store and without even
	// incrementing hops — the `if r.walkExceeded { return }` guard precedes hops++. Asserting res.hops
	// (not just cnt.calls) is the only oracle that distinguishes that early-return from the independent
	// hops>maxHops check, so it kills a deletion of the walkExceeded short-circuit.
	callsBefore, hopsBefore := cnt.calls, res.hops
	_, _, ok := res.fetch(hdrs[0].BlockHash())
	require.False(t, ok, "a latched resolver must report not-found")
	require.Equal(t, callsBefore, cnt.calls, "a latched walk performs no further store lookups")
	require.Equal(t, hopsBefore, res.hops, "a latched resolver must short-circuit before hops++ (kills early-return deletion)")
}

// TestWalkHopBoundAllowsLegitRetargetWalk proves the bound does not false-trip on an honest
// retarget-boundary header whose full ancestry is present: the deep ~2015-hop RelativeAncestorCtx walk
// runs, stays well under the bound, and the header resolves to a real accept/reject verdict (never the
// skip sentinel).
func TestWalkHopBoundAllowsLegitRetargetWalk(t *testing.T) {
	const n = 2016 // heights 0..2015
	store, hdrs := buildChainTS(n, mainBits, func(i int) int64 { return int64(1_231_006_505 + i*600) })
	cnt := &countingLookup{inner: store}

	// Candidate at height 2016 => (2015+1) % 2016 == 0 => retarget boundary => RelativeAncestorCtx(2015).
	cand := childOf(hdrs[n-1], mainBits, int64(1_231_006_505+n*600))

	err := validateBTCHeaderContextWith(context.Background(), cnt, &chaincfg.MainNetParams, cand)

	// The verdict is a deterministic difficulty rejection: at this boundary the recomputed expected
	// difficulty (0x1d00ffde, from a 1209000s actual vs 1209600s target timespan) differs from the
	// candidate's mainBits (0x1d00ffff) -> ErrUnexpectedDifficulty. Not a skip — full ancestry is
	// present.
	requireReject(t, err, blockchain.ErrUnexpectedDifficulty)
	// Exact walk cost: 1 parent pre-resolve + 2015 RelativeAncestorCtx hops. The difficulty check
	// fires before the median-time-past walk, so no MTP fetches occur -> exactly 2016, well under the
	// 4288 bound. Pinning the exact count (not a band) kills a RelativeAncestorCtx off-by-one (2017) and
	// any check-reorder that runs MTP first (~2027) — both of which a (2015,4288) band missed.
	require.Equal(t, 2016, cnt.calls, "boundary validation does exactly 1 pre-resolve + 2015 ancestor lookups")
}

// TestWalkHopBoundTerminatesCyclicAncestry drives the real production validation wiring (inside
// validateBTCHeaderContextWith) against a pathological ancestry cycle: btcd's findPrevTestNetDifficulty
// Parent() walk would loop forever without termination. Since the height-contiguity hardening
// (fetchContiguousParent), this cycle is terminated by the contiguity check — its heights (100<->101)
// are non-contiguous, so the first Parent() hop fails closed (heightInconsistent -> skip) in O(1),
// strictly before the hop bound. So this test now pins contiguity termination (fast, fail-safe-to-skip),
// not the hop bound. The maxHops bound is consequently subsumed for cyclic/non-contiguous ancestry (a
// contiguous chain can never reach it — retarget=2015, MTP~11, the testnet3 min-diff walk stops at the
// next %2016 boundary — and any non-contiguous chain trips contiguity first), so it is retained only as
// a defense-in-depth backstop; its mechanism (walkExceeded latching at exactly the cap) is still pinned
// by TestWalkHopBoundTripsToSkip on a hand-built resolver. A production maxHops:0 mutant is now benign
// (the cycle terminates via contiguity regardless) — the intended consequence of the deeper hardening,
// not a coverage gap to backfill.
func TestWalkHopBoundTerminatesCyclicAncestry(t *testing.T) {
	store := newFakeStore()
	minBits := chaincfg.TestNet3Params.PowLimitBits // testnet3 min-difficulty bits keep the walk going

	// Two entries whose PrevBlock fields point at each other, keyed manually (the keys need not equal
	// BlockHash() — fetch resolves by the looked-up key, and the walk follows PrevBlock).
	var keyA, keyB chainhash.Hash
	keyA[0], keyB[0] = 0xAA, 0xBB
	hdrA := &wire.BlockHeader{Version: 1, PrevBlock: keyB, Bits: minBits, Timestamp: time.Unix(1_600_000_000, 0)}
	hdrB := &wire.BlockHeader{Version: 1, PrevBlock: keyA, Bits: minBits, Timestamp: time.Unix(1_600_000_000, 0)}
	store.byHash[keyA] = fakeEntry{hdr: hdrA, height: 100} // 100,101 are non-retarget-boundary heights,
	store.byHash[keyB] = fakeEntry{hdr: hdrB, height: 101} // so findPrevTestNetDifficulty never stops on Height()%2016==0

	// Candidate builds on hdrA (height 100 -> candidate height 101, non-boundary) with a timestamp
	// inside testnet3's 20-min minimum-difficulty window, so calcNextRequiredDifficulty routes into
	// the findPrevTestNetDifficulty parent walk over the cycle.
	cand := &wire.BlockHeader{Version: 1, PrevBlock: keyA, Bits: minBits, Timestamp: time.Unix(1_600_000_060, 0)}

	// Run under a watchdog: with the bound the walk terminates in ~maxHops lookups; under a maxHops:0
	// regression it loops forever (btcd's findPrevTestNetDifficulty has no cancellation point and
	// fakeHeaderStore ignores ctx), so a plain call would hang the whole package for the 10-minute
	// global timeout. The watchdog converts that into a fast, named failure.
	cnt := &countingLookup{inner: store}
	done := make(chan error, 1)
	go func() {
		done <- validateBTCHeaderContextWith(context.Background(), cnt, &chaincfg.TestNet3Params, cand)
	}()
	select {
	case err := <-done:
		requireSkip(t, err) // a cyclic / non-contiguous walk must fail closed to skip
		// Since the height-contiguity hardening (fetchContiguousParent), this cycle is terminated far
		// earlier than the hop bound: the cycle's heights (100<->101) are non-contiguous, so the first
		// Parent() hop trips the height cross-check (heightInconsistent -> skip) in O(1) lookups, not
		// ~maxHops. Assert termination is fast (well under maxHops), proving the contiguity check — not the
		// hop bound — caught it. The hop bound remains a now-subsumed backstop: on a contiguous chain no
		// walk reaches it (retarget=2015, MTP~11, and the testnet3 min-diff walk stops at the next %2016
		// boundary), and any non-contiguous chain trips contiguity first — so the cycle that used to need
		// the hop bound is now caught for free, sooner.
		require.Less(t, cnt.calls, 100,
			"a non-contiguous cyclic walk must be terminated by the height-contiguity check in O(1) hops, not run to ~maxHops")
	case <-time.After(5 * time.Second):
		t.Fatal("validateBTCHeaderContextWith did not terminate: neither the height-contiguity check nor the hop bound capped the cyclic ancestry walk")
	}
}

// TestWalkHopBoundAllowsLongTestnet3MinDiffWalk proves the bound does not false-skip an honest
// testnet3 minimum-difficulty header whose validation routes through findPrevTestNetDifficulty (the
// Parent()-walk path, distinct from mainnet's RelativeAncestorCtx path). A long single-epoch run of
// PowLimitBits headers drives a deep but legitimate Parent walk that must stay under the bound and
// resolve to a real (non-skip) verdict. This mechanizes the maxHeaderCtxWalkHops doc claim that the
// min-diff walk is "comparable length" and safe.
func TestWalkHopBoundAllowsLongTestnet3MinDiffWalk(t *testing.T) {
	minBits := chaincfg.TestNet3Params.PowLimitBits
	const n = 2000 // heights 0..1999, all within one retarget epoch (< 2016), all min-difficulty
	base := int64(1_600_000_000)
	store, hdrs := buildChainTS(n, minBits, func(i int) int64 { return base + int64(i)*600 })
	cnt := &countingLookup{inner: store}

	// Candidate at height 2000 (non-boundary), timestamp inside the 20-min reduction window of its
	// parent so calcNextRequiredDifficulty walks back via findPrevTestNetDifficulty (not the
	// >reductionTime shortcut) to the genesis boundary at height 0.
	cand := childOf(hdrs[n-1], minBits, base+int64(n-1)*600+60)

	err := validateBTCHeaderContextWith(context.Background(), cnt, &chaincfg.TestNet3Params, cand)

	// Deterministic accept: findPrevTestNetDifficulty returns h0.Bits (PowLimitBits) == candidate Bits,
	// so difficulty passes; the candidate timestamp is after the MTP median and Version 1 is below
	// testnet3's BIP0034 height -> nil.
	require.NoError(t, err, "an honest testnet3 min-difficulty header must validate (accept), not skip/reject")
	// Exact walk cost: 1 pre-resolve + 1999 findPrevTestNetDifficulty Parent hops (h1999 down to the
	// height-0 retarget boundary) + 11 CalcPastMedianTime hops = 2011. Pinning the exact count kills a
	// findPrevTestNetDifficulty stop off-by-one and a medianTimeBlocks (11) change — both of which
	// landed inside the old (1900,4288) band.
	require.Equal(t, 2011, cnt.calls, "exactly 1 pre-resolve + 1999 min-diff walk + 11 MTP lookups")
}
