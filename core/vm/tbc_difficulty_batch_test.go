// Copyright 2024 The go-ethereum Authors
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

package vm

// Unit tests for the floor-aware consensus-path batch validator. Bases are built at heights
// well above floorClearance(mainnet)=2027 so that with floorHeight=0 the floor gate is satisfied and
// the enforce path runs (accept/reject); a high floorHeight exercises the defer path.

import (
	"errors"
	"math/big"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"
)

// testFloorBase places synthetic base chains well above floorClearance(&MainNetParams)==2027, so a
// floorHeight of 0 satisfies the floor gate and the enforce path runs.
const testFloorBase = 5000

// buildChainFrom is buildChainTS but with heights starting at `start` (so the lowest header sits
// above the floor clearance). The first header's PrevBlock is the zero hash (acts as the floor).
func buildChainFrom(start, n int, bits uint32, ts func(i int) int64) (*fakeHeaderStore, []*wire.BlockHeader) {
	store := newFakeStore()
	hdrs := make([]*wire.BlockHeader, n)
	var prev chainhash.Hash
	for i := 0; i < n; i++ {
		h := &wire.BlockHeader{Version: 1, PrevBlock: prev, Bits: bits, Timestamp: time.Unix(ts(i), 0), Nonce: uint32(i)}
		store.put(h, uint64(start+i))
		hdrs[i] = h
		prev = h.BlockHash()
	}
	return store, hdrs
}

func extendBatch(base []*wire.BlockHeader, count int, bits uint32, ts func(i int) int64) []*wire.BlockHeader {
	batch := make([]*wire.BlockHeader, count)
	prev := base[len(base)-1].BlockHash()
	for i := 0; i < count; i++ {
		h := &wire.BlockHeader{Version: 1, PrevBlock: prev, Bits: bits, Timestamp: time.Unix(ts(i), 0), Nonce: uint32(1000 + i)}
		batch[i] = h
		prev = h.BlockHash()
	}
	return batch
}

// baseTS builds a committed base of n mainBits headers starting at testFloorBase, 600s apart.
func baseTS(n int) (*fakeHeaderStore, []*wire.BlockHeader) {
	return buildChainFrom(testFloorBase, n, mainBits, func(i int) int64 { return int64(1_600_000_000 + i*600) })
}
func contTS(start int) func(i int) int64 {
	return func(i int) int64 { return int64(1_600_000_000 + (start+i)*600) }
}

func TestValidateBTCHeaderBatchEmpty(t *testing.T) {
	store, _ := baseTS(20)
	require.NoError(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, nil),
		"an empty batch has nothing to validate")
}

// Enforce accept: a connected constant-difficulty batch above the floor validates. Proves the overlay
// resolves intra-batch parents (only headers[0] anchors in base; headers[1..N] anchor on a
// not-yet-committed predecessor) and that the floor gate permits enforcement above the clearance.
func TestValidateBTCHeaderBatchAcceptsConnectedBatch(t *testing.T) {
	store, hdrs := baseTS(20) // heights 5000..5019
	batch := extendBatch(hdrs, 6, mainBits, contTS(20))
	require.NoError(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, batch),
		"a connected constant-difficulty batch above the floor must accept")
}

// A nil header anywhere in the batch fails CLOSED to the recoverable skip sentinel
// (ErrBTCHeaderContextUnavailable) — never a nil-deref panic and never a false reject. unflattenBTCHeaders
// never yields a nil, but ValidateBTCHeaderBatchForNetwork is exported, so the defensive h==nil guard must
// hold; removing it nil-derefs h.PrevBlock on the next line.
func TestValidateBTCHeaderBatchNilHeaderSkips(t *testing.T) {
	store, hdrs := baseTS(20)
	for _, pos := range []int{0, 2} {
		batch := extendBatch(hdrs, 4, mainBits, contTS(20))
		batch[pos] = nil
		var err error
		require.NotPanics(t, func() {
			err = validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, batch)
		}, "a nil header at index %d must not nil-deref", pos)
		require.ErrorIs(t, err, ErrBTCHeaderContextUnavailable,
			"a nil header at index %d must fail closed to the recoverable skip sentinel, not a false reject", pos)
	}
}

// Enforce reject: a mid-batch header carries the wrong difficulty -> ErrUnexpectedDifficulty, even
// though its parent is an in-batch (uncommitted) header.
func TestValidateBTCHeaderBatchRejectsWrongDifficulty(t *testing.T) {
	store, hdrs := baseTS(20)
	batch := extendBatch(hdrs, 4, mainBits, contTS(20))
	bad := &wire.BlockHeader{Version: 1, PrevBlock: batch[1].BlockHash(), Bits: 0x1d00fffe, Timestamp: time.Unix(contTS(20)(2), 0), Nonce: 7}
	batch[2] = bad
	batch[3] = &wire.BlockHeader{Version: 1, PrevBlock: bad.BlockHash(), Bits: mainBits, Timestamp: time.Unix(contTS(20)(3), 0), Nonce: 8}
	requireReject(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, batch), blockchain.ErrUnexpectedDifficulty)
}

// Unconnected: the first header's parent is genuinely absent (NotFound) from the committed store ->
// the batch does not connect to consensus state -> ErrBTCBatchUnconnected (caller -> bad block), not
// skip/corrupt.
func TestValidateBTCHeaderBatchUnconnected(t *testing.T) {
	store, _ := baseTS(20)
	orphan := &wire.BlockHeader{Version: 1, PrevBlock: chainhash.Hash{0xde, 0xad}, Bits: mainBits, Timestamp: time.Unix(contTS(20)(0), 0), Nonce: 1}
	batch := []*wire.BlockHeader{orphan}
	err := validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, batch)
	require.ErrorIs(t, err, ErrBTCBatchUnconnected, "a non-connecting batch must be reported unconnected (bad block), not skip")
	require.NotErrorIs(t, err, ErrBTCHeaderContextUnavailable, "unconnected must be distinct from the corrupt/skip sentinel")
}

// Near-floor unconnected: a batch whose first header connects near the floor (so minHeight is within
// floorClearance — the floor gate would fire) but whose second header builds on an absent parent. The
// anchor loop must report ErrBTCBatchUnconnected before the floor gate returns ErrBTCBatchBelowFloor.
// This is the precondition that justifies the apply path setting batchConnectivityConfirmed=true on
// the BelowFloor arm: a non-connecting near-floor batch is never classified BelowFloor (which would
// mark it connectivity-confirmed and, on a torn store, route it to corrupt/self-heal). Neither
// TestValidateBTCHeaderBatchUnconnected (floorHeight=0, gate never fires) nor
// TestValidateBTCHeaderBatchBelowFloor (fully-connecting batch, anchor loop never returns Unconnected)
// pins that the anchor loop runs strictly before the floor gate; this does. Kills a reorder mutant
// that checks the floor gate per-header inside the anchor loop.
func TestValidateBTCHeaderBatchUnconnectedDominatesBelowFloor(t *testing.T) {
	store, hdrs := baseTS(20)                             // heights 5000..5019
	good := extendBatch(hdrs, 1, mainBits, contTS(20))[0] // connects to base tip 5019 -> height 5020
	orphan := &wire.BlockHeader{Version: 1, PrevBlock: chainhash.Hash{0xde, 0xad, 0xbe, 0xef}, Bits: mainBits, Timestamp: time.Unix(contTS(20)(1), 0), Nonce: 2}
	batch := []*wire.BlockHeader{good, orphan}
	// floorHeight=testFloorBase(5000): good's height 5020 is within floorClearance(2027) of 5000, so the
	// floor gate would return BelowFloor if it were consulted before connectivity was fully established.
	err := validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, testFloorBase, batch)
	require.ErrorIs(t, err, ErrBTCBatchUnconnected, "a non-connecting near-floor batch must be Unconnected, not deferred")
	require.NotErrorIs(t, err, ErrBTCBatchBelowFloor, "the anchor loop must report Unconnected BEFORE the floor gate")
}

// IO error while resolving the anchor -> the recoverable corrupt/skip sentinel, not unconnected.
func TestValidateBTCHeaderBatchIOErrIsSkip(t *testing.T) {
	store, hdrs := baseTS(20)
	batch := extendBatch(hdrs, 2, mainBits, contTS(20))
	// Force a non-NotFound IO error on the anchor lookup (the batch's first parent = base tip).
	store.errOn[hdrs[19].BlockHash()] = errors.New("simulated leveldb IO error")
	err := validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, batch)
	require.ErrorIs(t, err, ErrBTCHeaderContextUnavailable, "an IO error must map to the corrupt/skip sentinel")
	require.NotErrorIs(t, err, ErrBTCBatchUnconnected, "an IO error is not a non-connecting batch")
}

// Below floor: with a high floorHeight the batch sits within floorClearance of the floor, so it is
// unverifiable by construction -> ErrBTCBatchBelowFloor (caller defers, does not enforce).
// A near-floor batch is neither false-rejected nor routed to corrupt state.
func TestValidateBTCHeaderBatchBelowFloor(t *testing.T) {
	store, hdrs := baseTS(20) // heights 5000..5019; batch ~5020..
	batch := extendBatch(hdrs, 4, mainBits, contTS(20))
	// floorHeight just below the batch so batch heights are within floorClearance(=2027) of it.
	err := validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, testFloorBase, batch)
	require.ErrorIs(t, err, ErrBTCBatchBelowFloor, "a near-floor batch must defer, not enforce")
	require.NotErrorIs(t, err, ErrBTCHeaderContextUnavailable)
	// The same batch with floorHeight=0 (well clear of the floor) enforces and accepts — proving the
	// gate is what defers, not a validation problem.
	require.NoError(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, batch))
}

// Reject dominates skip (non-vacuous, correctly-ordered): the skipping header comes first, the
// rejecting header second — so the loop observes a skip before the reject, yet reject must win. P:
// correct difficulty (so it does not reject) but an IO error on one of its median-time-past ancestors
// forces a skip during its validation. Q: P's child, wrong difficulty -> reject. The batch must
// return the RuleError, proving firstReject precedence over sawSkip.
func TestValidateBTCHeaderBatchRejectDominatesSkip(t *testing.T) {
	store, hdrs := baseTS(20)
	p := &wire.BlockHeader{Version: 1, PrevBlock: hdrs[19].BlockHash(), Bits: mainBits, Timestamp: time.Unix(contTS(20)(0), 0), Nonce: 1}
	q := &wire.BlockHeader{Version: 1, PrevBlock: p.BlockHash(), Bits: 0x1d00fffe, Timestamp: time.Unix(contTS(20)(1), 0), Nonce: 2}
	// hdrs[14] (height 5014) lies in P's MTP window (the 11 ancestors of P's parent 5019) but is not
	// P's immediate parent, so the anchor loop does not touch it — only P's validation walk does.
	store.errOn[hdrs[14].BlockHash()] = errors.New("simulated IO during MTP walk")
	err := validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, []*wire.BlockHeader{p, q})
	requireReject(t, err, blockchain.ErrUnexpectedDifficulty)
	require.NotErrorIs(t, err, ErrBTCHeaderContextUnavailable, "a genuine reject must dominate a co-occurring skip")
}

// Skip wins when no header rejects: an above-floor header whose validation hits an IO error on a deep
// median-time-past ancestor returns the skip sentinel, and with no rejecting header the batch result
// is skip (recoverable corrupt at the caller), not a silent accept. This is the only test that reaches
// the pure sawSkip return arm (the RejectDominatesSkip test has a rejecting header, so firstReject
// pre-empts it; the IOErr test trips the anchor loop, not the validation loop). It kills a skip->nil
// mutant that would silently accept an unverified-difficulty batch on the consensus path.
func TestValidateBTCHeaderBatchSkipWinsNoReject(t *testing.T) {
	store, hdrs := baseTS(20)                           // heights 5000..5019
	batch := extendBatch(hdrs, 1, mainBits, contTS(20)) // single header at height 5020 (above floor)
	// IO error on a header inside the candidate's MTP window (5009..5019), not its immediate parent
	// (5019) — so the anchor loop resolves cleanly and the skip arises only during validation.
	store.errOn[hdrs[14].BlockHash()] = errors.New("simulated IO during MTP walk")
	err := validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, batch)
	requireSkip(t, err)
	require.NotErrorIs(t, err, ErrBTCBatchUnconnected, "an IO during validation (not anchor) is a skip, not unconnected")
}

// Nil params / nil base -> skip (fail-closed), matching the single-header validator.
func TestValidateBTCHeaderBatchFailClosed(t *testing.T) {
	store, hdrs := baseTS(20)
	batch := extendBatch(hdrs, 2, mainBits, contTS(20))
	requireSkip(t, validateBTCHeaderBatchWith(ctx(), store, nil, 0, batch))
	requireSkip(t, validateBTCHeaderBatchWith(ctx(), nil, &chaincfg.MainNetParams, 0, batch))
}

// ValidateBTCHeaderBatchForNetwork resolves params from the network name (independent of the
// full-node global) and fails closed to skip on an unknown network.
func TestValidateBTCHeaderBatchForNetwork(t *testing.T) {
	store, hdrs := baseTS(20)
	batch := extendBatch(hdrs, 4, mainBits, contTS(20))
	require.NoError(t, ValidateBTCHeaderBatchForNetwork(ctx(), store, "mainnet", 0, batch),
		"a valid above-floor mainnet batch must accept under resolved mainnet params")
	requireSkip(t, ValidateBTCHeaderBatchForNetwork(ctx(), store, "bogus-network", 0, batch))
}

// The overlay must serve in-batch headers (by hash, with assigned heights) and fall through to base,
// and resolve() must classify found / NotFound / IO.
func TestBTCBatchOverlayResolution(t *testing.T) {
	store, hdrs := baseTS(5)
	h := &wire.BlockHeader{Version: 1, PrevBlock: hdrs[4].BlockHash(), Bits: mainBits, Timestamp: time.Unix(contTS(5)(0), 0), Nonce: 1}
	o := &btcBatchOverlay{base: store, in: map[chainhash.Hash]batchEntry{h.BlockHash(): {hdr: h, height: uint64(testFloorBase + 5)}}}

	got, height, st := o.resolve(ctx(), h.BlockHash())
	require.Equal(t, resolveFound, st)
	require.Equal(t, h, got)
	require.Equal(t, uint64(testFloorBase+5), height)

	_, _, st = o.resolve(ctx(), hdrs[4].BlockHash())
	require.Equal(t, resolveFound, st, "base header resolves via fall-through")

	_, _, st = o.resolve(ctx(), chainhash.Hash{0x99})
	require.Equal(t, resolveNotFound, st, "absent header classifies NotFound")

	store.errOn[hdrs[0].BlockHash()] = errors.New("io")
	_, _, st = o.resolve(ctx(), hdrs[0].BlockHash())
	require.Equal(t, resolveIOErr, st, "non-NotFound error classifies IOErr")
}

// Retarget-boundary crossing: a boundary candidate's RelativeAncestorCtx(2015) walk must cross the
// overlay->base seam. Anchor at 4032, committed base 4032..6042, batch 6043..6048 (6048 = 3*2016 is
// the boundary). The 2015-back walk from 6047 reaches the anchor 4032 in committed base, crossing the
// seam. The candidate carries mainBits; the boundary timespan (2015*600=1209000 < target 1209600)
// recomputes a slightly-harder expected difficulty != mainBits -> ErrUnexpectedDifficulty. Proves the
// deep walk resolves across the seam (not a skip) and the boundary path actually ran.
func TestValidateBTCHeaderBatchCrossesRetargetBoundary(t *testing.T) {
	const anchor = 4032 // 6047 - 2015
	const baseEnd = 6042
	tsAt := func(h int) int64 { return int64(1_231_006_505 + (h-anchor)*600) }
	store, baseHdrs := buildChainFrom(anchor, baseEnd-anchor+1, mainBits, func(i int) int64 { return tsAt(anchor + i) })
	batch := extendBatch(baseHdrs, 6048-baseEnd, mainBits, func(i int) int64 { return tsAt(baseEnd + 1 + i) }) // 6043..6048

	cnt := &countingLookup{inner: store}
	err := validateBTCHeaderBatchWith(ctx(), cnt, &chaincfg.MainNetParams, 0, batch)
	requireReject(t, err, blockchain.ErrUnexpectedDifficulty)
	require.Greater(t, cnt.calls, 2000,
		"the boundary candidate's RelativeAncestorCtx(2015) walk must cross the overlay->base seam into committed base")

	// Differential: the same boundary candidate validated against a fully-committed chain (no overlay)
	// yields the identical reject — proving the overlay seam is transparent.
	store2, allHdrs := buildChainFrom(anchor, 6048-anchor+1, mainBits, func(i int) int64 { return tsAt(anchor + i) })
	cand := allHdrs[len(allHdrs)-1] // height 6048
	requireReject(t, validateBTCHeaderBatchWith(ctx(), store2, &chaincfg.MainNetParams, 0, []*wire.BlockHeader{cand}), blockchain.ErrUnexpectedDifficulty)
}

// Testnet3 min-difficulty seam: testnet3 ReduceMinDifficulty routes within-20-min non-boundary
// headers through findPrevTestNetDifficulty, which walks Parent() — here across the overlay->base seam
// down to the boundary at 4032 (returning PowLimitBits). The testnet3 min-difficulty walk must
// validate correctly over the overlay above the floor (a walk that crosses below the floor would
// false-reject near-floor headers).
func TestValidateBTCHeaderBatchTestnet3MinDiffSeam(t *testing.T) {
	const anchor = 4032                                                                                             // a retarget boundary; findPrevTestNetDifficulty stops here
	tsAt := func(h int) int64 { return int64(1_600_000_000 + (h-anchor)*600) }                                      // 600s < 1200s -> within-20-min
	store, baseHdrs := buildChainFrom(anchor, 4050-anchor, mainBits, func(i int) int64 { return tsAt(anchor + i) }) // 4032..4049
	batch := extendBatch(baseHdrs, 6, mainBits, func(i int) int64 { return tsAt(4050 + i) })                        // 4050..4055 (above floorClearance 2027)

	require.NoError(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.TestNet3Params, 0, batch),
		"an above-floor testnet3 min-difficulty batch must accept (findPrevTestNetDifficulty walks the seam to PowLimitBits)")

	// reject: a mid-batch header carries hard (non-min) Bits != the expected PowLimitBits. Use a
	// 4-header batch and replace [2]+[3] so every subsequent header is re-linked (no dangling parent).
	rbatch := extendBatch(baseHdrs, 4, mainBits, func(i int) int64 { return tsAt(4050 + i) })
	bad := &wire.BlockHeader{Version: 1, PrevBlock: rbatch[1].BlockHash(), Bits: 0x1d00fffe, Timestamp: time.Unix(tsAt(4052), 0), Nonce: 99}
	rbatch[2] = bad
	rbatch[3] = &wire.BlockHeader{Version: 1, PrevBlock: bad.BlockHash(), Bits: mainBits, Timestamp: time.Unix(tsAt(4053), 0), Nonce: 100}
	requireReject(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.TestNet3Params, 0, rbatch), blockchain.ErrUnexpectedDifficulty)
}

// TestValidateBTCHeaderBatchFloorGateBoundary pins the exact defer/enforce transition at the
// clearance: a batch whose minHeight == floorHeight+floorClearance enforces (and a constant-Bits batch
// accepts), while minHeight one below that defers. Pins both the floorClearance value and the gate's
// strict `<` (widening clearance to 2*BlocksPerRetarget, or flipping `<`->`<=`, flips one assertion).
// The lowest batch header (5020) is not a retarget boundary (5020 % 2016 != 0), so the enforce branch
// validates Bits==prev + MTP (both present in the base store) — no anchor walk crosses below floor.
func TestValidateBTCHeaderBatchFloorGateBoundary(t *testing.T) {
	store, hdrs := baseTS(20)                           // heights 5000..5019
	batch := extendBatch(hdrs, 4, mainBits, contTS(20)) // minHeight 5020
	const minHeight = uint64(testFloorBase + 20)        // 5020 (first batch header)
	clearance := floorClearance(&chaincfg.MainNetParams)

	// floorHeight s.t. minHeight == floorHeight+clearance exactly -> not below floor (strict <) -> enforce.
	atFloor := minHeight - clearance
	require.NoError(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, atFloor, batch),
		"minHeight == floorHeight+floorClearance must ENFORCE (gate is strict <) and a constant-Bits batch accepts")
	// One higher -> minHeight < floorHeight+clearance -> defer.
	require.ErrorIs(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, atFloor+1, batch), ErrBTCBatchBelowFloor,
		"minHeight one below floorHeight+floorClearance must DEFER")
}

// floorClearance == BlocksPerRetarget (2016 on every real network) + medianTimeBlocks. The deepest
// contextual walk (the retarget anchor) reads exactly BlocksPerRetarget back, so that is the exact
// minimal-presence clearance; +medianTimeBlocks is a conservative margin. A larger value (e.g.
// 2*BlocksPerRetarget) needlessly defers the upper ~BlocksPerRetarget of the band.
func TestFloorClearance(t *testing.T) {
	require.Equal(t, uint64(2016+11), floorClearance(&chaincfg.MainNetParams))
	require.Equal(t, uint64(2016+11), floorClearance(&chaincfg.TestNet3Params))
	require.Equal(t, uint64(2016+11), floorClearance(&chaincfg.RegressionNetParams))
	// Safety invariant (must never shrink below the exact minimal-presence threshold): the lowest
	// enforced header at floorHeight+floorClearance reads its deepest ancestor (the retarget anchor) at
	// floorHeight+floorClearance-BlocksPerRetarget; that must be >= floorHeight (the present, seeded
	// checkpoint), i.e. floorClearance >= BlocksPerRetarget. A value below this would let the gate admit
	// a header whose walk crosses below the floor -> a persistent missing-context skip -> restore wedge.
	for _, p := range []*chaincfg.Params{&chaincfg.MainNetParams, &chaincfg.TestNet3Params, &chaincfg.RegressionNetParams} {
		require.GreaterOrEqual(t, floorClearance(p), uint64(blocksPerRetarget(p)),
			"floorClearance must stay >= BlocksPerRetarget or near-floor enforced headers walk below the floor")
	}
}

// TestBTCFloorClearanceForNetwork pins the exported wrapper: every network paramsForNetwork accepts
// must resolve to the same clearance as the internal floorClearance (lockstep), and an unknown network
// must fail closed (error, zero) — never silently return a usable (0, nil) that would let the snap-sync
// caller compute a too-low enforce floor and under-enforce contextual-difficulty validation.
func TestBTCFloorClearanceForNetwork(t *testing.T) {
	cases := map[string]*chaincfg.Params{
		"mainnet":     &chaincfg.MainNetParams,
		"testnet3":    &chaincfg.TestNet3Params,
		"upgradetest": &chaincfg.TestNet3Params,
		"localnet":    &chaincfg.RegressionNetParams,
	}
	for network, params := range cases {
		got, err := BTCFloorClearanceForNetwork(network)
		require.NoErrorf(t, err, "known network %q must resolve", network)
		require.Equalf(t, floorClearance(params), got, "network %q must match the internal floorClearance", network)
		require.Equal(t, uint64(2016+11), got)
	}

	got, err := BTCFloorClearanceForNetwork("nonsense-network")
	require.Error(t, err, "an unknown network must fail closed, not return a usable clearance")
	require.Zero(t, got)
}

// TestBTCConsensusParamsForwardCompatLock is a tripwire for btcd consensus drift. The
// contextual-difficulty validator reuses btcd's CheckBlockHeaderContext difficulty algorithm, whose
// behavior is governed by these chaincfg.Params fields. A btcd module bump (pulled in transitively via
// the TBC dependency with no op-geth code change and no compile error) could alter the enforced
// difficulty rule — e.g. btcd v0.25.0 added an EnforceBIP94 timewarp-fix path inside the same
// CheckBlockHeaderContext. If real Bitcoin adopts a rule the pinned btcd does not implement (or a bump
// flips one of these), honest headers would start failing contextual-difficulty validation, halting the
// forward apply path and the sequencer build, and tripping the observe-only snap alert. Pinning the
// difficulty-relevant params here forces any such drift to fail CI, so the contextual-difficulty rule
// (incl. BIP94/timewarp) must be re-verified against real Bitcoin history and these expectations updated
// deliberately before shipping.
func TestBTCConsensusParamsForwardCompatLock(t *testing.T) {
	const (
		fortnight   = 14 * 24 * time.Hour
		tenMinutes  = 10 * time.Minute
		twentyMin   = 20 * time.Minute
		mainPowBits = uint32(0x1d00ffff)
		regPowBits  = uint32(0x207fffff)
	)
	// PowLimit is the *big.Int the retarget clamp reads directly (newTarget > PowLimit => PowLimit),
	// distinct from the PowLimitBits compact form; mainnet/testnet3 are 2^224-1, regtest is 2^255-1.
	mainPowLimit := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 224), big.NewInt(1))
	regPowLimit := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 255), big.NewInt(1))
	check := func(name string, p *chaincfg.Params, powBits uint32, powLimit *big.Int, reduceMinDiff, noRetarget bool, minDiffReduction time.Duration) {
		require.Equalf(t, powBits, p.PowLimitBits, "%s PowLimitBits drift", name)
		require.Equalf(t, 0, powLimit.Cmp(p.PowLimit), "%s PowLimit (big.Int) drift", name)
		require.Equalf(t, reduceMinDiff, p.ReduceMinDifficulty, "%s ReduceMinDifficulty drift", name)
		require.Equalf(t, noRetarget, p.PoWNoRetargeting, "%s PoWNoRetargeting drift", name)
		require.Equalf(t, fortnight, p.TargetTimespan, "%s TargetTimespan drift", name)
		require.Equalf(t, tenMinutes, p.TargetTimePerBlock, "%s TargetTimePerBlock drift", name)
		require.Equalf(t, int64(4), p.RetargetAdjustmentFactor, "%s RetargetAdjustmentFactor drift", name)
		require.Equalf(t, minDiffReduction, p.MinDiffReductionTime, "%s MinDiffReductionTime drift", name)
		// BlocksPerRetarget is derived from the two timing params; pin the consequence too.
		require.Equalf(t, 2016, int(p.TargetTimespan/p.TargetTimePerBlock), "%s BlocksPerRetarget drift", name)
	}
	check("mainnet", &chaincfg.MainNetParams, mainPowBits, mainPowLimit, false, false, 0)
	check("testnet3", &chaincfg.TestNet3Params, mainPowBits, mainPowLimit, true, false, twentyMin)
	check("regtest", &chaincfg.RegressionNetParams, regPowBits, regPowLimit, true, true, twentyMin)
}

// TestValidateBTCHeaderBatchReturnsFirstReject pins that validateBTCHeaderBatchWith returns the FIRST rejecting
// header's RuleError in iteration order. With two rejecting headers of DISTINCT codes (header[0] wrong-difficulty
// -> ErrUnexpectedDifficulty, header[1] too-old timestamp -> ErrTimeTooOld), the returned code must be header[0]'s.
// A mutant that returns the LAST reject (dropping the `if firstReject == nil` guard) survives single-reject tests.
func TestValidateBTCHeaderBatchReturnsFirstReject(t *testing.T) {
	store, hdrs := baseTS(20) // heights 5000..5019, mainBits, 600s apart
	// header[0]: wrong difficulty (parent is base tip mainBits; carries 0x1d00fffe) -> ErrUnexpectedDifficulty.
	p := &wire.BlockHeader{Version: 1, PrevBlock: hdrs[19].BlockHash(), Bits: 0x1d00fffe, Timestamp: time.Unix(contTS(20)(0), 0), Nonce: 7}
	// header[1]: inherits p's 0x1d00fffe (so NO difficulty error) but a far-too-old timestamp -> ErrTimeTooOld.
	q := &wire.BlockHeader{Version: 1, PrevBlock: p.BlockHash(), Bits: 0x1d00fffe, Timestamp: time.Unix(1_600_000_000, 0), Nonce: 8}
	requireReject(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, []*wire.BlockHeader{p, q}),
		blockchain.ErrUnexpectedDifficulty)

	// Control: a single header in q's shape but with CORRECT difficulty rejects with ErrTimeTooOld — proving the
	// two rejects carry distinct codes, so the assertion above genuinely pins iteration order.
	qGood := &wire.BlockHeader{Version: 1, PrevBlock: hdrs[19].BlockHash(), Bits: mainBits, Timestamp: time.Unix(1_600_000_000, 0), Nonce: 9}
	requireReject(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, []*wire.BlockHeader{qGood}),
		blockchain.ErrTimeTooOld)
}

// TestValidateBTCHeaderBatchOrderPermutationBreaksConnectivity is the metamorphic relation: a batch that is
// contiguous in CONTENT but MIS-ORDERED (a child placed before its parent) must be rejected as
// ErrBTCBatchUnconnected — never silently accepted, never mis-classified as a difficulty violation. The validator
// anchors each header at the one height its declared parent fixes, so a child seen before its parent resolves
// against neither the overlay-so-far nor the committed base. Every other batch test builds in ascending order.
func TestValidateBTCHeaderBatchOrderPermutationBreaksConnectivity(t *testing.T) {
	store, hdrs := baseTS(20) // committed base heights 5000..5019
	b := extendBatch(hdrs, 4, mainBits, contTS(20))

	// Control: the in-order batch is clean (so the permutations below are a pure reordering, not a content defect).
	require.NoError(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, b),
		"the in-order contiguous batch must be the clean baseline")

	perms := map[string][]*wire.BlockHeader{
		"swap-first-two": {b[1], b[0], b[2], b[3]}, // a child (b1) before its parent (b0)
		"reverse":        {b[3], b[2], b[1], b[0]},
		"gap-skip-b2":    {b[0], b[1], b[3]}, // contiguous-prefix then a hole: b3's parent b2 is absent
	}
	for name, perm := range perms {
		t.Run(name, func(t *testing.T) {
			err := validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, perm)
			require.ErrorIs(t, err, ErrBTCBatchUnconnected, "a mis-ordered batch must be reported unconnected")
			require.NotErrorIs(t, err, ErrBTCHeaderContextUnavailable, "mis-ordering is not a skip/corrupt")
			var re blockchain.RuleError
			require.False(t, errors.As(err, &re), "mis-ordering must NOT be mis-classified as a difficulty RuleError")
		})
	}
}

// TestValidateBTCHeaderBatchPrefixMonotonicity pins the modeling assumption longestEnforceableBTCHeaderPrefix
// relies on, against the REAL validator: header validity depends only on its own ancestry, so the verdict is
// prefix-monotonic. (1) Every prefix of an all-clean above-floor batch validates clean. (2) For a batch with the
// first fault at index k, every prefix [:j] is clean for j<=k and a difficulty RuleError for j>k — a well-defined
// first-invalid index. If the real validator were non-monotone (e.g. near a retarget boundary), the shrink-from-end
// build algorithm could return a prefix the apply path rejects.
func TestValidateBTCHeaderBatchPrefixMonotonicity(t *testing.T) {
	store, hdrs := baseTS(20)

	// (1) all-clean batch: every leading prefix validates clean.
	good := extendBatch(hdrs, 6, mainBits, contTS(20))
	for i := 1; i <= len(good); i++ {
		require.NoError(t, validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, good[:i]),
			"every prefix of an all-clean batch must validate clean (prefix len %d)", i)
	}

	// (2) first fault at index k=2: clean for j<=2, difficulty RuleError for j>2.
	const k = 2
	b := extendBatch(hdrs, 5, mainBits, contTS(20))
	bad := &wire.BlockHeader{Version: 1, PrevBlock: b[k-1].BlockHash(), Bits: 0x1d00fffe, Timestamp: time.Unix(contTS(20)(k), 0), Nonce: 77}
	b[k] = bad
	for i := k + 1; i < len(b); i++ { // re-link the tail onto the forged header so connectivity is preserved
		b[i] = &wire.BlockHeader{Version: 1, PrevBlock: b[i-1].BlockHash(), Bits: mainBits, Timestamp: time.Unix(contTS(20)(i), 0), Nonce: uint32(80 + i)}
	}
	for j := 1; j <= len(b); j++ {
		err := validateBTCHeaderBatchWith(ctx(), store, &chaincfg.MainNetParams, 0, b[:j])
		if j <= k {
			require.NoError(t, err, "prefix [:%d] is entirely before the first fault -> clean", j)
		} else {
			requireReject(t, err, blockchain.ErrUnexpectedDifficulty) // monotone: once the fault is included it stays rejected
		}
	}
}
