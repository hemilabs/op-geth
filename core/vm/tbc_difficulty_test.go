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

// Unit tests for the contextual-difficulty adapters. These use synthetic headers with no valid
// proof-of-work: CheckBlockHeaderContext validates difficulty (Bits == expected), median-time-past,
// and block version, not the hash-meets-target PoW (that is the separate context-free
// CheckBlockSanity). So we can exercise the adapter wiring and the reused engine without mining.
// Real-PoW / real-chain retarget vectors (clamp regimes, out-of-band oracle, testnet3 min-diff) are
// covered by the differential-replay tests (tbc_difficulty_replay_test.go).

import (
	"context"
	"errors"
	"fmt"
	"math"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/hemilabs/heminetwork/database"
	"github.com/stretchr/testify/require"
)

// --- in-memory header store satisfying headerLookup ---

type fakeEntry struct {
	hdr    *wire.BlockHeader
	height uint64
}

type fakeHeaderStore struct {
	byHash map[chainhash.Hash]fakeEntry
	errOn  map[chainhash.Hash]error // force a non-NotFound IO error for these hashes
}

func newFakeStore() *fakeHeaderStore {
	return &fakeHeaderStore{byHash: map[chainhash.Hash]fakeEntry{}, errOn: map[chainhash.Hash]error{}}
}

func (f *fakeHeaderStore) put(h *wire.BlockHeader, height uint64) {
	f.byHash[h.BlockHash()] = fakeEntry{hdr: h, height: height}
}

func (f *fakeHeaderStore) BlockHeaderByHash(_ context.Context, hash chainhash.Hash) (*wire.BlockHeader, uint64, error) {
	if err, ok := f.errOn[hash]; ok {
		return nil, 0, err
	}
	e, ok := f.byHash[hash]
	if !ok {
		// Mirror the header store's lookup exactly: a genuinely-absent header surfaces as a
		// database.NotFoundError wrapped with fmt.Errorf %w, so this exercises
		// the errors.As unwrap the live fail-closed path depends on, not just a bare NotFoundError.
		return nil, 0, fmt.Errorf("db block header by hash: %w", database.NotFoundError("block header not found"))
	}
	return e.hdr, e.height, nil
}

var _ headerLookup = (*fakeHeaderStore)(nil)

// buildChainTS builds n chained synthetic headers (heights 0..n-1) at the given Bits,
// with timestamps from ts(i). Each header's PrevBlock links the previous header's
// real BlockHash, and all are inserted into a fresh store.
func buildChainTS(n int, bits uint32, ts func(i int) int64) (*fakeHeaderStore, []*wire.BlockHeader) {
	store := newFakeStore()
	hdrs := make([]*wire.BlockHeader, n)
	var prev chainhash.Hash
	for i := 0; i < n; i++ {
		h := &wire.BlockHeader{
			Version:   1,
			PrevBlock: prev,
			Bits:      bits,
			Timestamp: time.Unix(ts(i), 0),
			Nonce:     uint32(i),
		}
		store.put(h, uint64(i))
		hdrs[i] = h
		prev = h.BlockHash()
	}
	return store, hdrs
}

// childOf builds a candidate header on top of parent with the given Bits/timestamp.
func childOf(parent *wire.BlockHeader, bits uint32, ts int64) *wire.BlockHeader {
	return &wire.BlockHeader{
		Version:   1,
		PrevBlock: parent.BlockHash(),
		Bits:      bits,
		Timestamp: time.Unix(ts, 0),
		Nonce:     0xdead,
	}
}

const mainBits = 0x1d00ffff // mainnet/testnet3 PowLimitBits

func ctx() context.Context { return context.Background() }

// requireSkip asserts err is the missing-context skip sentinel and not a btcd RuleError, locking the
// skip/reject separability the whole scheme rests on.
func requireSkip(t *testing.T, err error) {
	t.Helper()
	require.ErrorIs(t, err, ErrBTCHeaderContextUnavailable, "expected the skip sentinel")
	var re blockchain.RuleError
	require.False(t, errors.As(err, &re), "a skip must NOT be a btcd RuleError (skip and reject must stay separable)")
}

// requireReject asserts err is a genuine btcd RuleError of the given code and not the skip sentinel.
func requireReject(t *testing.T, err error, code blockchain.ErrorCode) {
	t.Helper()
	require.Error(t, err)
	require.NotErrorIs(t, err, ErrBTCHeaderContextUnavailable, "a rejection must NOT be the skip sentinel")
	var re blockchain.RuleError
	require.True(t, errors.As(err, &re), "expected a btcd RuleError")
	require.Equal(t, code, re.ErrorCode)
}

// --- ChainCtx derivation ---

func TestTBCChainCtxDerivation(t *testing.T) {
	for _, tc := range []struct {
		name   string
		params *chaincfg.Params
	}{
		{"mainnet", &chaincfg.MainNetParams},
		{"testnet3", &chaincfg.TestNet3Params},
		{"regtest", &chaincfg.RegressionNetParams},
	} {
		c := &tbcChainCtx{params: tc.params}
		require.Equal(t, int32(2016), c.BlocksPerRetarget(), tc.name+": blocks per retarget")
		// Independent identity (not the production formula): blocks * per-block-time == timespan.
		// Catches a `return 2016` constant or any derivation untethered from the params.
		require.Equal(t, int64(tc.params.TargetTimespan/time.Second),
			int64(c.BlocksPerRetarget())*int64(tc.params.TargetTimePerBlock/time.Second),
			tc.name+": BlocksPerRetarget*TargetTimePerBlock must equal TargetTimespan")
		// Min/Max are TargetTimespanSeconds /4 and *4.
		target := int64(tc.params.TargetTimespan / time.Second)
		require.Equal(t, target/tc.params.RetargetAdjustmentFactor, c.MinRetargetTimespan(), tc.name+": min")
		require.Equal(t, target*tc.params.RetargetAdjustmentFactor, c.MaxRetargetTimespan(), tc.name+": max")
		require.Same(t, tc.params, c.ChainParams())
	}
	// mainnet & testnet3 concrete values.
	main := &tbcChainCtx{params: &chaincfg.MainNetParams}
	require.Equal(t, int64(302400), main.MinRetargetTimespan())
	require.Equal(t, int64(4838400), main.MaxRetargetTimespan())
}

// --- non-retarget: inherit parent Bits ---

func TestValidateNonRetargetInherit(t *testing.T) {
	// 12 headers (heights 0..11), parent = height 11, candidate = height 12 (12 % 2016 != 0).
	store, h := buildChainTS(12, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	parent := h[11]

	// Correct: candidate inherits parent.Bits -> accept.
	cand := childOf(parent, mainBits, parent.Timestamp.Unix()+600)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand),
		"non-retarget block inheriting parent Bits must be accepted")

	// Wrong: a different (easier) Bits -> ErrUnexpectedDifficulty (a real rejection, not a skip).
	require.NotEqual(t, uint32(mainBits), uint32(0x1d00fffe)) // anti-vacuity: good != bad
	bad := childOf(parent, 0x1d00fffe, parent.Timestamp.Unix()+600)
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, bad), blockchain.ErrUnexpectedDifficulty)
}

// --- retarget boundary: no-adjustment case (actualTimespan == TargetTimespan) ---
//
// At a boundary the expected target = oldTarget * adjustedTimespan / TargetTimespan. When
// actualTimespan == TargetTimespan there is no adjustment, so expected == parent Bits (round-tripped).
// This exercises the RelativeAncestorCtx PrevBlock walk back to the window start (height H-2016) plus
// the reused retarget path, without needing an out-of-band oracle.
func TestValidateRetargetBoundaryNoAdjustment(t *testing.T) {
	const base = int64(1_600_000_000)
	target := int64(chaincfg.MainNetParams.TargetTimespan / time.Second) // 1209600
	// heights 0..2016. firstNode for the boundary at H=2016 is height H-2016 = 0.
	// Set ts so ts[2015]-ts[0] == target exactly (no adjustment); keep monotonic.
	tsFn := func(i int) int64 {
		switch {
		case i == 2015:
			return base + target
		case i == 2016:
			return base + target + 600
		default:
			return base + int64(i)*600
		}
	}
	store, h := buildChainTS(2017, mainBits, tsFn)
	parent := h[2015]
	// Confirm the candidate height H=2016 is genuinely a retarget boundary for these params:
	// btcd recalculates iff (lastNode.Height()+1) % BlocksPerRetarget == 0.
	require.Equal(t, int32(0), (int32(2015)+1)%(&tbcChainCtx{params: &chaincfg.MainNetParams}).BlocksPerRetarget(),
		"H=2016 must be a retarget boundary")

	// Correct: candidate Bits == parent Bits (no adjustment) -> accept.
	cand := childOf(parent, mainBits, parent.Timestamp.Unix()+600)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand),
		"boundary with actualTimespan==TargetTimespan must accept the unchanged difficulty")

	// Wrong: any other Bits at the boundary -> rejection.
	require.NotEqual(t, uint32(mainBits), uint32(0x1d00fffe)) // anti-vacuity
	bad := childOf(parent, 0x1d00fffe, parent.Timestamp.Unix()+600)
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, bad), blockchain.ErrUnexpectedDifficulty)
}

// --- missing context must SKIP (ErrBTCHeaderContextUnavailable), never reject ---

func TestValidateParentAbsentSkips(t *testing.T) {
	store, h := buildChainTS(12, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	// Candidate whose parent is NOT in the store.
	orphanParent := &wire.BlockHeader{Version: 1, PrevBlock: h[11].BlockHash(), Bits: mainBits, Timestamp: time.Unix(1_700_000_000, 0), Nonce: 7}
	cand := childOf(orphanParent, mainBits, 1_700_000_600)
	requireSkip(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand))
}

func TestValidateParentIOErrorSkips(t *testing.T) {
	store, h := buildChainTS(12, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	parent := h[11]
	cand := childOf(parent, mainBits, parent.Timestamp.Unix()+600)
	// Force a non-NotFound IO error resolving the parent.
	store.errOn[parent.BlockHash()] = errors.New("leveldb: simulated IO error")
	requireSkip(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand))
}

func TestValidateBoundaryAnchorAbsentSkips(t *testing.T) {
	const base = int64(1_600_000_000)
	target := int64(chaincfg.MainNetParams.TargetTimespan / time.Second)
	tsFn := func(i int) int64 {
		switch {
		case i == 2015:
			return base + target
		case i == 2016:
			return base + target + 600
		default:
			return base + int64(i)*600
		}
	}
	store, h := buildChainTS(2017, mainBits, tsFn)
	parent := h[2015]
	// Remove the window-start (height 0) so RelativeAncestorCtx(2015) can't resolve it.
	delete(store.byHash, h[0].BlockHash())

	cand := childOf(parent, mainBits, parent.Timestamp.Unix()+600)
	requireSkip(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand))
}

// --- IO error during a deeper in-call walk (MTP) must also skip ---

func TestValidateDeepIOErrorSkips(t *testing.T) {
	store, h := buildChainTS(12, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	parent := h[11]
	cand := childOf(parent, mainBits, parent.Timestamp.Unix()+600)
	// Precondition: with no injected error these exact inputs accept (btcd's standalone verdict is
	// nil). So the skip below is the IO-error override beating a would-be-accept, not btcd itself
	// erroring — this distinguishes "skip overrides accept" from a reorder that returns btcd's result
	// before checking the sink.
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand))
	// Now a grandparent the MTP walk needs IO-errors -> must fail closed to skip, not accept.
	store.errOn[h[10].BlockHash()] = errors.New("leveldb: simulated IO error mid-walk")
	requireSkip(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand))

	// Twin: a NotFound (not IO) mid-MTP-walk is the genuine chain-floor case and must still accept
	// (truncated median), pinning the accept side of fetch's NotFound-vs-IO classification.
	store2, h2 := buildChainTS(12, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	cand2 := childOf(h2[11], mainBits, h2[11].Timestamp.Unix()+600)
	delete(store2.byHash, h2[10].BlockHash())
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store2, &chaincfg.MainNetParams, cand2),
		"a NotFound mid-MTP-walk truncates the median and accepts; only a non-NotFound IO error skips")
}

// --- typed-nil contract: ancestry getters return UNTYPED interface-nil ---

func TestHeaderCtxTypedNilContract(t *testing.T) {
	store := newFakeStore()
	// A header whose parent is absent.
	hdr := &wire.BlockHeader{Version: 1, PrevBlock: chainhash.Hash{0x01}, Bits: mainBits, Timestamp: time.Unix(1_600_000_000, 0)}
	res := &tbcCtxResolver{ctx: ctx(), lookup: store, params: &chaincfg.MainNetParams}
	hc := &tbcHeaderCtx{hdr: hdr, height: 100, res: res}

	// Direct interface-equality (not require.Nil, which would also pass for a typed nil).
	p := hc.Parent()
	require.True(t, p == nil, "Parent() must return untyped interface-nil when absent")

	a := hc.RelativeAncestorCtx(1)
	require.True(t, a == nil, "RelativeAncestorCtx() must return untyped interface-nil when absent")
}

// --- median-time-past rejection (rides along in CheckBlockHeaderContext) ---

func TestValidateMTPTooOldRejects(t *testing.T) {
	// 12 headers 600s apart, parent = height 11. CalcPastMedianTime(parent) is the median of the last
	// up-to-11 ancestors (heights 1..11); with evenly-spaced timestamps the median is height 6's. A
	// candidate with correct difficulty but a timestamp at/before that median must reject as
	// ErrTimeTooOld (not skip).
	store, h := buildChainTS(12, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	parent := h[11]
	median := h[6].Timestamp.Unix()

	bad := childOf(parent, mainBits, median) // == median -> not After(median) -> too old
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, bad), blockchain.ErrTimeTooOld)

	// Control: strictly after the median (and the parent) -> accepted.
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
		childOf(parent, mainBits, parent.Timestamp.Unix()+600)))
}

// --- block-version gate (rides along under skipCheckpoint=true) ---

func TestValidateVersionGateRejects(t *testing.T) {
	// Clone mainnet params with a low BIP0034 activation so a version-1 candidate at a low height trips
	// the version gate. Real mainnet activation is 227931; the height-32256 version-1 anchor used in
	// the differential-replay tests is safe precisely because it is below activation.
	p := chaincfg.MainNetParams
	p.BIP0034Height = 5
	store, h := buildChainTS(12, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	parent := h[11] // candidate height 12 >= BIP0034Height=5

	bad := childOf(parent, mainBits, parent.Timestamp.Unix()+600) // Version 1 (childOf default)
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &p, bad), blockchain.ErrBlockVersionTooOld)

	// Control: a sufficient version passes the gate (and difficulty + MTP) -> accepted.
	good := childOf(parent, mainBits, parent.Timestamp.Unix()+600)
	good.Version = 4
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &p, good))
}

// --- exported entry fails closed when the full node / params are not set up ---

func TestValidateBTCHeaderContextNilGlobals(t *testing.T) {
	// In package tests TBCFullNode / tbcChainParams are nil (no SetupTBCFullNode).
	require.Nil(t, TBCFullNode)
	hdr := &wire.BlockHeader{Version: 1, Bits: mainBits, Timestamp: time.Unix(1_600_000_000, 0)}
	requireSkip(t, ValidateBTCHeaderContext(hdr))
}

// TestRelativeAncestorHeightCrossCheck pins the contextual-difficulty walk-distance height cross-check: the retarget
// boundary is positioned off absolute stored heights, so a round-tripping height corruption at the
// retarget window-start (the anchor RelativeAncestorCtx resolves) must fail closed to the skip
// sentinel — never a difficulty verdict computed from a height-inconsistent window. An honest
// (contiguous-height) chain must not trip it.
func TestRelativeAncestorHeightCrossCheck(t *testing.T) {
	p := chaincfg.MainNetParams // no ReduceMinDifficulty -> a boundary recompute calls RelativeAncestorCtx
	// 2016 headers at heights 0..2015; the candidate sits at height 2016 (2016 % 2016 == 0 -> a retarget
	// boundary), so validation walks RelativeAncestorCtx(2015) from the parent (2015) back to height 0.
	store, h := buildChainTS(2016, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	parent := h[2015]
	cand := childOf(parent, mainBits, parent.Timestamp.Unix()+600)
	cand.Version = 4 // clear the BIP version gates (inactive at height 2016 anyway)

	// Honest store: the boundary recompute runs to a verdict (accept or reject), not a skip — proving
	// the retarget walk completed and the cross-check passed on a contiguous chain.
	require.NotErrorIs(t, validateBTCHeaderContextWith(ctx(), store, &p, cand), ErrBTCHeaderContextUnavailable,
		"honest contiguous-height chain must reach a difficulty verdict, not skip")

	// Corrupt ONLY the stored height of the window-start anchor (height 0 header). The per-hop contiguity
	// check trips at the h[1]->h[0] hop (h[0] no longer reports height 0 = h[1].height-1) -> skip.
	store.put(h[0], 5)
	requireSkip(t, validateBTCHeaderContextWith(ctx(), store, &p, cand))
	store.put(h[0], 0) // restore

	// Mid-walk corruption: an interior hop's height is also caught (the per-hop check, unlike an
	// endpoint-only span check). Corrupt h[1000] -> the h[1001]->h[1000] hop trips it.
	require.NotErrorIs(t, validateBTCHeaderContextWith(ctx(), store, &p, cand), ErrBTCHeaderContextUnavailable,
		"sanity: honest before the mid-walk corruption")
	store.put(h[1000], 999)
	requireSkip(t, validateBTCHeaderContextWith(ctx(), store, &p, cand))
	store.put(h[1000], 1000) // restore

	// Restore: back to a verdict (proves each skip was caused by the corruption, not a latent property).
	require.NotErrorIs(t, validateBTCHeaderContextWith(ctx(), store, &p, cand), ErrBTCHeaderContextUnavailable,
		"restoring honest heights must return to a verdict (non-vacuous)")
}

// TestParentHeightContiguityTestnet3MinDiff pins that the per-hop contiguity check also hardens the
// testnet3 minimum-difficulty walk (findPrevTestNetDifficulty), which is Parent()-driven and uses
// iterNode.Height()%BlocksPerRetarget as its stop condition — a parallel height-corruption hole the
// retarget-only check would have left open. A corrupt height in that walk must fail closed to skip.
func TestParentHeightContiguityTestnet3MinDiff(t *testing.T) {
	p := chaincfg.TestNet3Params
	minBits := p.PowLimitBits
	// A contiguous min-difficulty chain above a retarget boundary (heights 2017..2030, none divisible
	// by 2016 until 2016 itself), so a min-diff candidate routes calcNextRequiredDifficulty into the
	// findPrevTestNetDifficulty parent walk (which scans back over min-diff headers).
	store := newFakeStore()
	hdrs := make([]*wire.BlockHeader, 0, 14)
	var prev chainhash.Hash
	base := int64(1_600_000_000)
	for i := 0; i < 14; i++ {
		hh := &wire.BlockHeader{Version: 4, PrevBlock: prev, Bits: minBits, Timestamp: time.Unix(base+int64(i)*600, 0), Nonce: uint32(i)}
		store.put(hh, uint64(2017+i))
		hdrs = append(hdrs, hh)
		prev = hh.BlockHash()
	}
	parent := hdrs[len(hdrs)-1] // height 2030
	// Candidate within the 20-min reduction window (<1200s after parent) -> not the easy-min path, so
	// it walks findPrevTestNetDifficulty back over the min-diff parents.
	cand := childOf(parent, minBits, parent.Timestamp.Unix()+600)
	cand.Version = 4

	require.NotErrorIs(t, validateBTCHeaderContextWith(ctx(), store, &p, cand), ErrBTCHeaderContextUnavailable,
		"honest contiguous min-diff chain must reach a verdict (the testnet3 walk completes)")

	// Corrupt an interior node's height in the min-diff parent walk -> the contiguity check in Parent()
	// trips -> skip (without the hardening, the walk would mis-stop on a wrong Height()%2016).
	store.put(hdrs[6], 5000)
	requireSkip(t, validateBTCHeaderContextWith(ctx(), store, &p, cand))
	store.put(hdrs[6], 2023) // restore (2017+6)
	require.NotErrorIs(t, validateBTCHeaderContextWith(ctx(), store, &p, cand), ErrBTCHeaderContextUnavailable,
		"restoring the honest height must return to a verdict (non-vacuous)")
}

// TestContiguousParentRejectsHeightZeroChild pins fetchContiguousParent's childHeight==0 guard: a node
// reporting height 0 that nonetheless resolves a parent is anomalous (height 0 is the floor; its parent
// is below the store) and must fail closed, not underflow childHeight-1.
func TestContiguousParentRejectsHeightZeroChild(t *testing.T) {
	r := &tbcCtxResolver{ctx: ctx(), lookup: newFakeStore(), params: &chaincfg.MainNetParams, maxHops: 0}
	store := r.lookup.(*fakeHeaderStore)
	par := &wire.BlockHeader{Version: 1, Bits: mainBits, Timestamp: time.Unix(1_600_000_000, 0)}
	// Non-vacuity: store the parent at height math.MaxUint64 — the exact value childHeight-1 underflows
	// to for childHeight==0. Without the `childHeight == 0 ||` guard, `pheight != childHeight-1` would be
	// `MaxUint64 != MaxUint64` == false -> it would wrongly accept the parent. So this fixture kills the
	// guard-deletion mutant (a smaller pheight would fail closed via the underflow regardless, making the
	// test vacuous).
	store.put(par, math.MaxUint64)
	_, _, ok := r.fetchContiguousParent(par.BlockHash(), 0)
	require.False(t, ok, "a height-0 child resolving a parent must fail closed (the childHeight==0 guard, not luck)")
	require.True(t, r.heightInconsistent, "the childHeight==0 guard must latch heightInconsistent (no underflow-accept)")
}

// TestValidateVersionGateBIP66And65 covers the SECOND and THIRD clauses of btcd's version gate
// (Version<3 && >=BIP0066Height; Version<4 && >=BIP0065Height). TestValidateVersionGateRejects only trips
// the FIRST clause (Version<2 via a lowered BIP0034Height). A bump/mutant dropping either of the other two
// OR-clauses would let an outdated-version header pass the consensus-binding apply path unnoticed.
func TestValidateVersionGateBIP66And65(t *testing.T) {
	store, h := buildChainTS(12, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	parent := h[11] // candidate height 12

	// BIP0066 (Version<3): clone with a low BIP0066Height; BIP0034/0065 keep their huge mainnet defaults so
	// only the BIP0066 clause can fire for a Version-2 candidate.
	p66 := chaincfg.MainNetParams
	p66.BIP0066Height = 5
	require.NotEqual(t, int32(5), chaincfg.MainNetParams.BIP0066Height, "anti-vacuity: the gate height must be load-bearing")
	v2 := childOf(parent, mainBits, parent.Timestamp.Unix()+600)
	v2.Version = 2
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &p66, v2), blockchain.ErrBlockVersionTooOld)
	v3 := childOf(parent, mainBits, parent.Timestamp.Unix()+600)
	v3.Version = 3
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &p66, v3), "Version 3 clears the BIP0066 gate")

	// BIP0065 (Version<4): clone with a low BIP0065Height; a Version-3 candidate now trips it.
	p65 := chaincfg.MainNetParams
	p65.BIP0065Height = 5
	v3b := childOf(parent, mainBits, parent.Timestamp.Unix()+600)
	v3b.Version = 3
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &p65, v3b), blockchain.ErrBlockVersionTooOld)
	v4 := childOf(parent, mainBits, parent.Timestamp.Unix()+600)
	v4.Version = 4
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &p65, v4), "Version 4 clears the BIP0065 gate")
}

// TestValidateMTPEvenWindowMedian covers btcd's median-time-past selection for an EVEN node count near the chain
// floor: CalcPastMedianTime returns the sorted-ascending element at index numNodes/2 — deliberately the
// UPPER-middle for an even window (btcd's documented "incorrectly calculate the median for even numbers of
// blocks" consensus quirk). Every existing MTP test uses an ODD window (11 nodes), where (n-1)/2 == n/2, so none
// can distinguish the upper-middle from a lower-middle selection. A 4-node window (parent walked to the floor)
// makes index 2 (h[2]) vs index 1 (h[1]) select DIFFERENT ancestors — the only configuration that pins the quirk.
func TestValidateMTPEvenWindowMedian(t *testing.T) {
	// Heights 0..3, 600s apart. The candidate at height 4 walks its parent (h[3]) back to the floor: h[3],h[2],
	// h[1],h[0] = 4 nodes (even). Ascending timestamps -> sorted == input -> median = input[4/2] = h[2].
	store, h := buildChainTS(4, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	parent := h[3]
	median := h[2].Timestamp.Unix() // the UPPER-middle of the 4-node window

	// (1) exact-equality boundary: timestamp == median is NOT After(median) -> ErrTimeTooOld.
	atMedian := childOf(parent, mainBits, median)
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, atMedian), blockchain.ErrTimeTooOld)

	// (2) strictly after the upper-middle median -> accept (non-retarget height 4 inherits parent mainBits).
	afterMedian := childOf(parent, mainBits, median+1)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, afterMedian),
		"a timestamp strictly after the upper-middle median must be accepted")

	// (3) anti-mutant: a timestamp AFTER the LOWER-middle (h[1]) but NOT after the upper-middle (h[2]) must STILL
	// reject. A (n-1)/2 lower-middle mutant would compute median=h[1] and ACCEPT this; correct code rejects it.
	betweenMiddles := childOf(parent, mainBits, h[1].Timestamp.Unix()+1)
	require.Less(t, h[1].Timestamp.Unix()+1, median, "anti-vacuity: the probe sits strictly between the lower and upper middles")
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, betweenMiddles), blockchain.ErrTimeTooOld)
}
