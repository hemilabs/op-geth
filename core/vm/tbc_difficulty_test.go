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

import (
	"bytes"
	"context"
	_ "embed"
	"encoding/hex"
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/rand"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/hemilabs/heminetwork/database"
	"github.com/stretchr/testify/require"
)

// Unit tests for the contextual-difficulty adapters. These use synthetic headers with no valid
// proof-of-work: CheckBlockHeaderContext validates difficulty (Bits == expected), median-time-past,
// and block version, not the hash-meets-target PoW (that is the separate context-free
// CheckBlockSanity). So we can exercise the adapter wiring and the reused engine without mining.
// Real-PoW / real-chain retarget vectors (clamp regimes, out-of-band oracle, testnet3 min-diff) are
// covered by the differential-replay tests (tbc_difficulty_replay_test.go).
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

// Direct edge-case tests of the contextual difficulty validator (validateBTCHeaderContextWith) against the
// in-memory fakeHeaderStore harness — corpus-free, exercising two difficulty-engine arms the real-fixture
// differential-replay gates never deterministically force:
//
//   - the testnet3 minimum-difficulty RESTORE arm: after a 20-minute-rule min-difficulty (PowLimitBits) block,
//     the next normally-spaced block must restore the PRIOR real difficulty via findPrevTestNetDifficulty
//     (walk back past the min-diff block). The existing min-diff tests only cover the all-PowLimitBits epoch
//     where the walk returns PowLimitBits; this covers the walk returning a DIFFERENT (harder) value.
//   - the PowLimit CEILING clamp: a retarget boundary whose recomputed target would exceed PowLimit must clamp
//     to PowLimitBits, so the boundary header carries PowLimitBits, not the un-clamped (harder) inherited bits.
//
// TestTestnet3MinDifficultyRestoresPriorDifficulty: testnet3's 20-minute rule lets a slowly-mined block carry
// PowLimitBits, but the NEXT normally-spaced block must restore the real (harder) difficulty that preceded the
// min-difficulty block — findPrevTestNetDifficulty walks back past the PowLimitBits block to the last real one.
func TestTestnet3MinDifficultyRestoresPriorDifficulty(t *testing.T) {
	const realBits = uint32(0x1d00fffe) // one notch harder than testnet3 PowLimitBits (0x1d00ffff)
	minBits := chaincfg.TestNet3Params.PowLimitBits
	require.NotEqual(t, realBits, minBits, "anti-vacuity: the real difficulty must differ from PowLimitBits")

	// Real-difficulty epoch, heights 0..11, normal 10-minute spacing.
	store, h := buildChainTS(12, realBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	parent := h[11]

	// A min-difficulty block B (height 12): mined >20 min after its parent, so the rule REQUIRES PowLimitBits.
	bTime := parent.Timestamp.Unix() + 1260 // 21 min > 2*TargetTimePerBlock (20 min)
	bMin := childOf(parent, minBits, bTime)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params, bMin),
		"a >20-min-spaced testnet3 block carrying PowLimitBits must be accepted (min-difficulty rule)")
	// Same slot but carrying the harder real difficulty: the rule REQUIRES PowLimitBits here -> reject.
	bWrong := childOf(parent, realBits, bTime)
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params, bWrong), blockchain.ErrUnexpectedDifficulty)

	// Commit the min-difficulty block so the next block's ancestry walk can see it.
	store.put(bMin, 12)

	// Restore block C (height 13): normally spaced after B, so the rule does NOT apply and difficulty must be
	// RESTORED to realBits — findPrevTestNetDifficulty walks back over the PowLimitBits block B to the real one.
	cTime := bMin.Timestamp.Unix() + 600
	cRestore := childOf(bMin, realBits, cTime)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params, cRestore),
		"a normally-spaced block after a min-difficulty block must RESTORE the prior real difficulty")
	// The same block carrying PowLimitBits (as if the min-difficulty were sticky) must be rejected.
	cWrong := childOf(bMin, minBits, cTime)
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params, cWrong), blockchain.ErrUnexpectedDifficulty)
}

// TestRetargetClampsToPowLimitCeiling: at a retarget boundary where the recomputed target would exceed PowLimit
// (a near-floor difficulty plus a max-clamped slow timespan), the expected difficulty must clamp to PowLimitBits.
// The boundary header must carry PowLimitBits; the un-clamped (harder) inherited bits must be rejected.
func TestRetargetClampsToPowLimitCeiling(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a full 2016-header retarget epoch")
	}
	const n = 2016                     // heights 0..2015; candidate at 2016 is a retarget boundary
	const oldBits = uint32(0x1d00fffe) // a hair harder than mainnet PowLimit, so target*4 overshoots PowLimit
	powLimitBits := chaincfg.MainNetParams.PowLimitBits
	require.NotEqual(t, oldBits, powLimitBits, "anti-vacuity: the epoch difficulty must differ from the clamp result")

	// 50-minute spacing => actual epoch timespan far exceeds 4x the 2-week target => clamped to MAX (ratio 4),
	// so newTarget = oldTarget*4, which overshoots PowLimit and must be clamped down to the PowLimit ceiling.
	store, h := buildChainTS(n, oldBits, func(i int) int64 { return 1_231_006_505 + int64(i)*3000 })
	parent := h[n-1]
	candTime := parent.Timestamp.Unix() + 3000

	// Correct: the boundary expects the clamped PowLimitBits.
	cand := childOf(parent, powLimitBits, candTime)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand),
		"a retarget overshooting PowLimit must clamp to PowLimitBits and accept that boundary header")
	// Wrong: the un-clamped (harder) inherited difficulty must be rejected.
	bad := childOf(parent, oldBits, candTime)
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, bad), blockchain.ErrUnexpectedDifficulty)
}

// TestTestnet3MinDiffWalkOffFloorReturnsPowLimit covers btcd findPrevTestNetDifficulty's FLOOR-FALLBACK arm:
// a min-difficulty candidate whose entire stored ancestry is PowLimitBits and runs OFF the chain floor
// (Parent()->nil) WITHOUT hitting a %2016 boundary must accept with the default PowLimitBits. Every existing
// testnet3 min-diff test stops the walk at a %2016==0 boundary, so the nil-fallback default is unexercised.
func TestTestnet3MinDiffWalkOffFloorReturnsPowLimit(t *testing.T) {
	minBits := chaincfg.TestNet3Params.PowLimitBits
	// Heights 100..110 (none divisible by 2016), all PowLimitBits; the height-100 header's parent is absent
	// (zero hash) -> the floor. So the walk runs to the floor before any boundary.
	store := newFakeStore()
	hdrs := make([]*wire.BlockHeader, 11)
	var prev chainhash.Hash
	base := int64(1_600_000_000)
	for i := 0; i < 11; i++ {
		hdr := &wire.BlockHeader{Version: 1, PrevBlock: prev, Bits: minBits, Timestamp: time.Unix(base+int64(i)*600, 0), Nonce: uint32(i)}
		store.put(hdr, uint64(100+i))
		hdrs[i] = hdr
		prev = hdr.BlockHash()
	}
	tip := hdrs[10] // height 110

	cnt := &countingLookup{inner: store}
	// Candidate at 111, within the 20-min window so it routes into findPrevTestNetDifficulty (not the
	// >reductionTime shortcut). It must carry the fallback PowLimitBits.
	cand := childOf(tip, minBits, tip.Timestamp.Unix()+600)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), cnt, &chaincfg.TestNet3Params, cand),
		"a min-diff candidate whose ancestry runs off the floor must accept with the PowLimitBits fallback")
	require.Less(t, cnt.calls, maxHeaderCtxWalkHops(&chaincfg.TestNet3Params),
		"the walk must terminate at the floor (Parent->nil), well under the hop bound")

	// Anti-case: a harder difficulty is rejected, proving the fallback value (PowLimitBits) is actually enforced.
	bad := childOf(tip, 0x1d00fffe, tip.Timestamp.Unix()+600)
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params, bad), blockchain.ErrUnexpectedDifficulty)
}

// TestTestnet3MinDiffMultiHopRestore strengthens the restore arm: findPrevTestNetDifficulty must walk back over
// a RUN of several consecutive min-difficulty (PowLimitBits) blocks to recover the real difficulty, not stop
// after one hop. TestTestnet3MinDifficultyRestoresPriorDifficulty only steps back one min-diff block.
func TestTestnet3MinDiffMultiHopRestore(t *testing.T) {
	const realBits = uint32(0x1d00fffe)
	minBits := chaincfg.TestNet3Params.PowLimitBits

	store, h := buildChainTS(12, realBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	prev := h[11]
	// A run of 3 consecutive min-difficulty blocks, each >20 min after its predecessor (so each legitimately
	// carries PowLimitBits), committed into the store as the walk traverses them.
	for n := 0; n < 3; n++ {
		mb := childOf(prev, minBits, prev.Timestamp.Unix()+1260)
		require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params, mb),
			"min-diff block %d (>20 min gap) must accept as PowLimitBits", n)
		store.put(mb, uint64(12+n))
		prev = mb
	}

	cnt := &countingLookup{inner: store}
	// Normally-spaced restore candidate: must recover realBits by walking back over all 3 min-diff blocks.
	restore := childOf(prev, realBits, prev.Timestamp.Unix()+600)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), cnt, &chaincfg.TestNet3Params, restore),
		"the restore candidate must recover the real difficulty across a multi-block min-diff run")
	require.Greater(t, cnt.calls, 3, "the walk must traverse more than one hop into the min-diff run")
	wrong := childOf(prev, minBits, prev.Timestamp.Unix()+600)
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params, wrong), blockchain.ErrUnexpectedDifficulty)
}

// Adapter-fidelity differential for (*tbcHeaderCtx).RelativeAncestorCtx. Its load-bearing claim (tbc_difficulty.go
// lines 207-216) is that the retarget window-start MUST be resolved by walking the candidate's OWN PrevBlock chain,
// NOT a height index — because under a same-height fork in the store a height index would return the wrong fork's
// header (which would still pass the height-contiguity check) and corrupt the retarget timespan. Every existing
// retarget test uses a SINGLE linear chain (one header per height), so a height-indexed resolution and an
// ancestry-exact PrevBlock walk are observationally identical. The fakeHeaderStore is hash-keyed, so it can hold TWO
// distinct full windows at the same heights — this is the only test that makes the anchor selection discriminating.
// putWindowInto builds a full retarget window (heights 0..2015) into a SHARED store: ts[0]=base,
// ts[2015]=base+actualTimespan (so the boundary recompute sees exactly actualTimespan), monotone between. The
// base offset + nonceOff keep two branches' headers distinct (different hashes) so they coexist at the same heights.
func putWindowInto(store *fakeHeaderStore, bits uint32, actualTimespan, base int64, nonceOff uint32) []*wire.BlockHeader {
	step := actualTimespan / 2016
	hdrs := make([]*wire.BlockHeader, 2016)
	var prev chainhash.Hash
	for i := 0; i < 2016; i++ {
		ts := base + int64(i)*step
		if i == 0 {
			ts = base
		} else if i == 2015 {
			ts = base + actualTimespan
		}
		h := &wire.BlockHeader{Version: 1, PrevBlock: prev, Bits: bits, Timestamp: time.Unix(ts, 0), Nonce: nonceOff + uint32(i)}
		store.put(h, uint64(i))
		hdrs[i] = h
		prev = h.BlockHash()
	}
	return hdrs
}

func TestRelativeAncestorCtxForkAnchorDifferential(t *testing.T) {
	const baseA, baseB = int64(1_600_000_000), int64(1_600_000_001) // +1s so branch B headers never collide with A
	const actualA = int64(1_209_600)                                // == TargetTimespan -> no adjustment -> expected_A == mainBits
	const actualB = int64(100_000)                                  // << MinRetargetTimespan -> clamp -> expected_B harder

	// Both full windows coexist in ONE hash-keyed store; each height 0..2015 holds two distinct headers.
	store := newFakeStore()
	hA := putWindowInto(store, mainBits, actualA, baseA, 0)
	hB := putWindowInto(store, mainBits, actualB, baseB, 2_000_000)
	require.NotEqual(t, hA[0].BlockHash(), hB[0].BlockHash(), "the two branches must not share the height-0 header")

	expA := mainnetRetargetExpected(mainBits, actualA)
	expB := mainnetRetargetExpected(mainBits, actualB)
	require.NotEqual(t, expA, expB, "anti-vacuity: the two branches' boundary difficulties must diverge")

	// Candidate on branch A's parent: the walk must resolve A's height-0 anchor (timespan actualA) -> expA, NOT B's
	// (same height, different timestamp). A height-indexed resolution returning B's height-0 would pass the
	// height-contiguity check yet compute expB, flipping the verdict.
	candA := childOf(hA[2015], expA, hA[2015].Timestamp.Unix()+600)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, candA),
		"on branch A the boundary difficulty must be A's own window (expA); the anchor is ancestry-exact")
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
		childOf(hA[2015], expB, hA[2015].Timestamp.Unix()+600)), blockchain.ErrUnexpectedDifficulty)

	// Symmetric twin on branch B's parent -> expB accepted, expA rejected.
	candB := childOf(hB[2015], expB, hB[2015].Timestamp.Unix()+600)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, candB),
		"on branch B the boundary difficulty must be B's own window (expB)")
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
		childOf(hB[2015], expA, hB[2015].Timestamp.Unix()+600)), blockchain.ErrUnexpectedDifficulty)
}

// Mutation-hardening tests for the contextual-difficulty adapters. Each targets a specific one-line
// production change that the baseline suite would not catch, plus durability against future
// btcd/TBC drift. All synthetic (no PoW mining): CheckBlockHeaderContext checks difficulty +
// median-time-past + version, not hash-meets-target.
// buildBoundaryWindow builds heights 0..2016 (a full retarget window + the boundary) at the given
// Bits, with ts[0]=base, ts[2015]=base+actualTimespan (so the boundary recompute at H=2016 sees
// exactly actualTimespan), monotonic in between, and the boundary candidate slot at 2016. Requires
// actualTimespan >= 2016 for monotonicity.
func buildBoundaryWindow(bits uint32, actualTimespan int64) (*fakeHeaderStore, []*wire.BlockHeader) {
	const base = int64(1_600_000_000)
	step := actualTimespan / 2016
	tsFn := func(i int) int64 {
		switch i {
		case 0:
			return base
		case 2015:
			return base + actualTimespan
		case 2016:
			return base + actualTimespan + 600
		default:
			return base + int64(i)*step
		}
	}
	return buildChainTS(2017, bits, tsFn)
}

// mainnetRetargetExpected recomputes the expected boundary Bits using hardcoded mainnet constants (not
// the tbcChainCtx getters), so it is an independent oracle for the Min/Max clamp direction: if
// production swaps Min<->Max or /4 vs *4, production's expected diverges from this and the
// accept/reject flips. Mirrors btcd's exact Mul-then-Div integer math.
//
// Cross-file: this is also the differential-replay exact-value oracle (TestBtcDiffMainnetBoundaryDifferential in
// tbc_difficulty_replay_test.go). The hardcoded 302400/4838400/1209600 constants are anti-rot-pinned
// against the params only inside TestValidateRetargetClamp below — do not delete that test without
// relocating those param-vs-constant assertions.
func mainnetRetargetExpected(oldBits uint32, actualTimespan int64) uint32 {
	const minTS, maxTS, targetTS = int64(302400), int64(4838400), int64(1209600)
	adj := actualTimespan
	if adj < minTS {
		adj = minTS
	} else if adj > maxTS {
		adj = maxTS
	}
	oldTarget := blockchain.CompactToBig(oldBits)
	nt := new(big.Int).Mul(oldTarget, big.NewInt(adj))
	nt.Div(nt, big.NewInt(targetTS))
	if nt.Cmp(chaincfg.MainNetParams.PowLimit) > 0 {
		nt.Set(chaincfg.MainNetParams.PowLimit)
	}
	return blockchain.BigToCompact(nt)
}

// TestValidateRetargetClamp drives the Min/Max-clamped retarget regimes through the real engine — the
// single biggest blind spot, since the only other boundary test uses actualTimespan==TargetTimespan
// where neither clamp branch is taken and Min/Max are never consulted. A Min<->Max swap or /4-vs-*4
// inversion in tbcChainCtx flips these.
func TestValidateRetargetClamp(t *testing.T) {
	cc := &tbcChainCtx{params: &chaincfg.MainNetParams}
	// Anti-rot: the hardcoded constants in mainnetRetargetExpected must match the params.
	require.Equal(t, int64(302400), cc.MinRetargetTimespan())
	require.Equal(t, int64(4838400), cc.MaxRetargetTimespan())
	require.Equal(t, int64(1209600), int64(chaincfg.MainNetParams.TargetTimespan/time.Second))
	require.EqualValues(t, 4, chaincfg.MainNetParams.RetargetAdjustmentFactor)

	t.Run("low-clamp", func(t *testing.T) {
		// actualTimespan << Min -> adj=Min -> expected = oldTarget/4 (harder).
		const actual = int64(100000) // < 302400
		store, h := buildBoundaryWindow(mainBits, actual)
		parent := h[2015]
		want := mainnetRetargetExpected(mainBits, actual)
		require.NotEqual(t, uint32(mainBits), want, "clamped result must differ from the unclamped parent Bits (non-vacuous)")
		require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
			childOf(parent, want, parent.Timestamp.Unix()+600)))
		requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
			childOf(parent, mainBits, parent.Timestamp.Unix()+600)), blockchain.ErrUnexpectedDifficulty)
	})

	t.Run("high-clamp", func(t *testing.T) {
		// actualTimespan >> Max -> adj=Max -> expected = oldTarget*4. Use a sub-PowLimit parent so
		// oldTarget*4 does not hit the PowLimit cap (which would confound).
		const subPowLimitBits = uint32(0x1c00ffff)
		const actual = int64(10_000_000) // > 4838400
		store, h := buildBoundaryWindow(subPowLimitBits, actual)
		parent := h[2015]
		want := mainnetRetargetExpected(subPowLimitBits, actual)
		require.NotEqual(t, subPowLimitBits, want, "clamped result must differ from the unclamped parent Bits (non-vacuous)")
		// Confirm no PowLimit-cap confound: want decodes below PowLimit.
		require.True(t, blockchain.CompactToBig(want).Cmp(chaincfg.MainNetParams.PowLimit) < 0)
		require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
			childOf(parent, want, parent.Timestamp.Unix()+600)))
		requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
			childOf(parent, subPowLimitBits, parent.Timestamp.Unix()+600)), blockchain.ErrUnexpectedDifficulty)
	})
}

// TestRelativeAncestorCtxHopCount directly pins the PrevBlock walk: every distance d must land on
// height-d on the own branch, overshoot returns interface-nil + sets missingAnchor, and distance<=0
// hits the defensive branch. Catches an off-by-one in the hop loop and removal of the distance<=0
// guard — both invisible to the full pipeline (which masks hop errors via retarget rounding and never
// uses distance<=0).
func TestRelativeAncestorCtxHopCount(t *testing.T) {
	store, h := buildChainTS(6, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	res := &tbcCtxResolver{ctx: ctx(), lookup: store, params: &chaincfg.MainNetParams}
	hc := &tbcHeaderCtx{hdr: h[5], height: 5, res: res}

	for d := int32(1); d <= 5; d++ {
		res.missingAnchor = false
		got := hc.RelativeAncestorCtx(d)
		require.NotNil(t, got, "distance %d must resolve", d)
		anc := got.(*tbcHeaderCtx)
		require.Equal(t, h[5-d].BlockHash(), anc.hdr.BlockHash(), "distance %d must land on height %d", d, 5-d)
		require.Equal(t, uint64(5-d), anc.height)
		require.False(t, res.missingAnchor, "a resolved ancestor must not flag missingAnchor")
	}

	// Overshoot past genesis -> nil + missingAnchor.
	res.missingAnchor = false
	require.Nil(t, hc.RelativeAncestorCtx(6))
	require.True(t, res.missingAnchor, "overshoot must flag missingAnchor")

	// Defensive distance<=0 branch -> nil + missingAnchor.
	for _, d := range []int32{0, -1} {
		res.missingAnchor = false
		require.Nil(t, hc.RelativeAncestorCtx(d))
		require.True(t, res.missingAnchor, "distance %d must flag missingAnchor", d)
	}
}

// TestFetchNotFoundDoesNotSetIOErr / TestFetchIOErrorSetsIOErr pin both legs of the NotFound-vs-IO
// classification at the sink. Dropping the !errors.As(NotFoundError) guard would record a NotFound as
// an IO error and break shallow/near-genesis headers while every deep happy-path accept stays green.
func TestFetchNotFoundDoesNotSetIOErr(t *testing.T) {
	res := &tbcCtxResolver{ctx: ctx(), lookup: newFakeStore(), params: &chaincfg.MainNetParams}
	_, _, ok := res.fetch(chainhash.Hash{0xAB})
	require.False(t, ok)
	require.NoError(t, res.ioErr, "a genuine NotFound must NOT be recorded as an IO error")
	require.False(t, res.missingAnchor)
}

func TestFetchIOErrorSetsIOErr(t *testing.T) {
	store := newFakeStore()
	h := &wire.BlockHeader{Bits: mainBits, Timestamp: time.Unix(1_600_000_000, 0)}
	store.put(h, 1)
	store.errOn[h.BlockHash()] = errors.New("leveldb: simulated IO error")
	res := &tbcCtxResolver{ctx: ctx(), lookup: store, params: &chaincfg.MainNetParams}
	_, _, ok := res.fetch(h.BlockHash())
	require.False(t, ok)
	require.Error(t, res.ioErr, "a non-NotFound error must be recorded as an IO error")
	var nfe database.NotFoundError
	require.False(t, errors.As(res.ioErr, &nfe), "the recorded IO error must not be a NotFoundError")
}

// TestValidateShallowChainHitsFloorButAccepts is the end-to-end converse: a short chain whose MTP walk
// reaches the genesis floor (Parent -> NotFound) must accept, not skip. Depth 3 is chosen so the
// 11-block MTP walk genuinely consumes the floor NotFound; a future refactor must not silently deepen
// past it.
func TestValidateShallowChainHitsFloorButAccepts(t *testing.T) {
	store, h := buildChainTS(3, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	cand := childOf(h[2], mainBits, h[2].Timestamp.Unix()+600)
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand),
		"a NotFound at the genesis floor during the MTP walk must accept (it must not set ioErr -> skip)")
}

// checkpointSpy records whether the checkpoint methods are consulted.
type checkpointSpy struct {
	*tbcChainCtx
	verifyCalled bool
	findCalled   bool
	verifyResult bool
}

func (s *checkpointSpy) VerifyCheckpoint(height int32, hash *chainhash.Hash) bool {
	s.verifyCalled = true
	return s.verifyResult
}

func (s *checkpointSpy) FindPreviousCheckpoint() (blockchain.HeaderCtx, error) {
	s.findCalled = true
	return nil, nil
}

// TestSkipCheckpointIsLoadBearing proves skipCheckpoint=true is load-bearing: flipping it to false
// survives the entire baseline suite (the production stubs accept under either flag). (a) the
// production call must not consult the checkpoint methods; (b) the converse with skipCheckpoint=false
// on the same inputs does reach them and rejects, proving the spy would have fired if reached.
func TestSkipCheckpointIsLoadBearing(t *testing.T) {
	store, h := buildChainTS(12, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	cand := childOf(h[11], mainBits, h[11].Timestamp.Unix()+600)
	mkPrev := func() blockchain.HeaderCtx {
		res := &tbcCtxResolver{ctx: ctx(), lookup: store, params: &chaincfg.MainNetParams}
		return &tbcHeaderCtx{hdr: h[11], height: 11, res: res}
	}

	// (a) production path (checkBTCHeaderContext uses skipCheckpoint=true).
	spyA := &checkpointSpy{tbcChainCtx: &tbcChainCtx{params: &chaincfg.MainNetParams}, verifyResult: false}
	require.NoError(t, checkBTCHeaderContext(cand, mkPrev(), spyA))
	require.False(t, spyA.verifyCalled, "skipCheckpoint=true must not call VerifyCheckpoint")
	require.False(t, spyA.findCalled, "skipCheckpoint=true must not call FindPreviousCheckpoint")

	// (b) converse: with skipCheckpoint=false the same (verify=false) spy IS consulted and rejects.
	spyB := &checkpointSpy{tbcChainCtx: &tbcChainCtx{params: &chaincfg.MainNetParams}, verifyResult: false}
	errB := blockchain.CheckBlockHeaderContext(cand, mkPrev(), blockchain.BFNone, spyB, false)
	require.True(t, spyB.verifyCalled, "skipCheckpoint=false must consult VerifyCheckpoint")
	requireReject(t, errB, blockchain.ErrBadCheckpoint)
}

// TestCheckBTCHeaderContextRunsDifficultyAndMTP pins BFNone at the function boundary: BFFastAdd would
// gate both the difficulty and MTP checks behind `if !fastAdd`, so a BFNone->BFFastAdd mutation would
// silently accept wrong difficulty and stale timestamps.
func TestCheckBTCHeaderContextRunsDifficultyAndMTP(t *testing.T) {
	require.Equal(t, blockchain.BehaviorFlags(0), blockchain.BFNone) // enum pin
	store, h := buildChainTS(12, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	cc := &tbcChainCtx{params: &chaincfg.MainNetParams}
	mkPrev := func() blockchain.HeaderCtx {
		res := &tbcCtxResolver{ctx: ctx(), lookup: store, params: &chaincfg.MainNetParams}
		return &tbcHeaderCtx{hdr: h[11], height: 11, res: res}
	}
	// difficulty IS enforced
	requireReject(t, checkBTCHeaderContext(childOf(h[11], 0x1d00fffe, h[11].Timestamp.Unix()+600), mkPrev(), cc),
		blockchain.ErrUnexpectedDifficulty)
	// MTP IS enforced (ts == median -> not After)
	requireReject(t, checkBTCHeaderContext(childOf(h[11], mainBits, h[6].Timestamp.Unix()), mkPrev(), cc),
		blockchain.ErrTimeTooOld)
	// correct -> accept
	require.NoError(t, checkBTCHeaderContext(childOf(h[11], mainBits, h[11].Timestamp.Unix()+600), mkPrev(), cc))
}

// TestValidateMTPWalkHitsGenesisFloor drives CheckBlockHeaderContext's real MTP walk to the genesis
// floor across many chain lengths; a typed (*tbcHeaderCtx)(nil) returned from a deeper Parent hop
// would survive btcd's `iterNode != nil` guard then panic on .Timestamp(). The baseline typed-nil test
// only checks the immediate getter in isolation.
func TestValidateMTPWalkHitsGenesisFloor(t *testing.T) {
	for _, n := range []int{1, 2, 3, 6, 11, 12} {
		n := n
		t.Run(fmt.Sprintf("len%d", n), func(t *testing.T) {
			store, h := buildChainTS(n, mainBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
			cand := childOf(h[n-1], mainBits, h[n-1].Timestamp.Unix()+600)
			require.NotPanics(t, func() {
				require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand))
			})
		})
	}
}

// TestValidateMinDiffParamGating exercises the testnet3 ReduceMinDifficulty path (the deployed
// default), exercised by zero baseline tests. It locks that the min-difficulty branch is gated on
// params.ReduceMinDifficulty, not a network-name string: the same inputs accept PowLimitBits on
// testnet3 but the inherited hard Bits on mainnet.
func TestValidateMinDiffParamGating(t *testing.T) {
	require.Equal(t, chaincfg.MainNetParams.PowLimitBits, chaincfg.TestNet3Params.PowLimitBits,
		"clean differential: PowLimitBits identical, only ReduceMinDifficulty differs")
	const hardBits = uint32(0x1d00fffe) // harder than PowLimit 0x1d00ffff
	powBits := chaincfg.TestNet3Params.PowLimitBits
	require.NotEqual(t, hardBits, powBits)

	gap := int64(chaincfg.TestNet3Params.MinDiffReductionTime/time.Second) + 500 // > reduction time
	store, h := buildChainTS(12, hardBits, func(i int) int64 { return 1_600_000_000 + int64(i)*600 })
	parent := h[11]
	candTs := parent.Timestamp.Unix() + gap

	// testnet3: gap > MinDiffReductionTime -> expected = PowLimitBits.
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params, childOf(parent, powBits, candTs)),
		"testnet3 min-diff: a >20min gap must accept PowLimitBits")
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params, childOf(parent, hardBits, candTs)),
		blockchain.ErrUnexpectedDifficulty)

	// mainnet mirror: ReduceMinDifficulty=false -> expected = parent (hard) Bits, identical inputs.
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, childOf(parent, hardBits, candTs)),
		"mainnet: no min-diff rule, inherit the parent Bits")
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, childOf(parent, powBits, candTs)),
		blockchain.ErrUnexpectedDifficulty)
}

// TestValidateRegtestNoRetarget covers the regtest PoWNoRetargeting short-circuit — the one difficulty
// branch owned by neither the boundary nor the min-diff coverage, and spec-mandated (the regtest
// vector). On localnet/regtest calcNextRequiredDifficulty returns PowLimitBits for every block before
// the retarget predicate; the candidate sits at height 2016 (a mainnet retarget boundary) to prove the
// short-circuit fires before any window-start walk.
func TestValidateRegtestNoRetarget(t *testing.T) {
	regBits := chaincfg.RegressionNetParams.PowLimitBits
	require.True(t, chaincfg.RegressionNetParams.PoWNoRetargeting, "regtest must have PoWNoRetargeting")
	require.NotEqual(t, regBits, uint32(0x1d00ffff))

	store := newFakeStore()
	base := int64(1_700_000_000)
	var prev chainhash.Hash
	var top *wire.BlockHeader
	for i, h := range []uint64{2013, 2014, 2015} {
		hh := &wire.BlockHeader{Version: 1, PrevBlock: prev, Bits: regBits, Timestamp: time.Unix(base+int64(i)*600, 0), Nonce: uint32(i)}
		store.put(hh, h)
		prev, top = hh.BlockHash(), hh
	}
	// Candidate at height 2016 (parent 2015), version 4 to clear the BIP gate regardless of regtest heights.
	mkCand := func(bits uint32) *wire.BlockHeader {
		return &wire.BlockHeader{Version: 4, PrevBlock: top.BlockHash(), Bits: bits, Timestamp: time.Unix(top.Timestamp.Unix()+600, 0), Nonce: 9}
	}
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.RegressionNetParams, mkCand(regBits)),
		"regtest must accept PowLimitBits at a (mainnet-)boundary height without retargeting")
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.RegressionNetParams, mkCand(0x1d00ffff)),
		blockchain.ErrUnexpectedDifficulty)
}

// TestHeaderCtxAccessorsExact directly pins the adapter getters to exact values — catches a narrow
// arithmetic mutation (e.g. a +offset on Timestamp()) that survives the full A+B suite because the
// retarget timespan cancels it and the MTP equality reject only gets 1s stricter.
func TestHeaderCtxAccessorsExact(t *testing.T) {
	h := &wire.BlockHeader{Version: 1, Bits: 0x1b04864c, Timestamp: time.Unix(1_600_000_123, 0)}
	hc := &tbcHeaderCtx{hdr: h, height: 770000, res: &tbcCtxResolver{ctx: ctx(), lookup: newFakeStore(), params: &chaincfg.MainNetParams}}
	require.Equal(t, int32(770000), hc.Height())
	require.Equal(t, uint32(0x1b04864c), hc.Bits())
	require.Equal(t, int64(1_600_000_123), hc.Timestamp(), "Timestamp() must equal the exact Unix time (kills a +offset mutation)")
}

// TestValidateNilGuards covers the inner defensive guard in validateBTCHeaderContextWith: a nil
// lookup, params, or header must fail closed to the skip sentinel (never panic, never accept). The
// sole production caller pre-guards the globals, so this is defense-in-depth that closes the last
// uncovered branch before consensus-path wiring.
func TestValidateNilGuards(t *testing.T) {
	store := newFakeStore()
	hdr := &wire.BlockHeader{Version: 1, Bits: mainBits, Timestamp: time.Unix(1_600_000_000, 0)}
	requireSkip(t, validateBTCHeaderContextWith(ctx(), nil, &chaincfg.MainNetParams, hdr))   // nil lookup
	requireSkip(t, validateBTCHeaderContextWith(ctx(), store, nil, hdr))                     // nil params
	requireSkip(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, nil)) // nil hdr
}

// TestSentinelIsNotRuleError locks the axiom the separability scheme rests on.
func TestSentinelIsNotRuleError(t *testing.T) {
	var re blockchain.RuleError
	require.False(t, errors.As(ErrBTCHeaderContextUnavailable, &re), "skip sentinel must never be a btcd RuleError")
	require.ErrorIs(t, ErrBTCHeaderContextUnavailable, ErrBTCHeaderContextUnavailable)
}

// TestValidatePostBoundaryInherits pins that the block after a boundary (H=k*2016+1) is non-retarget
// and inherits the parent's (already-retargeted) Bits. The parent at height 2016 carries a distinct
// Bits; a spurious retarget at 2017 (off-by-one in the height cast or boundary modulo) would, given
// the compressed window timestamps, clamp low and yield distinctBits/4 != distinctBits, flipping
// accept->reject.
func TestValidatePostBoundaryInherits(t *testing.T) {
	const distinctBits = uint32(0x1c00ffff)
	bpr := (&tbcChainCtx{params: &chaincfg.MainNetParams}).BlocksPerRetarget()
	require.NotEqual(t, int32(0), (int32(2016)+1)%bpr, "H=2017 must be non-retarget")

	const base = int64(1_600_000_000)
	store := newFakeStore()
	hdrs := make([]*wire.BlockHeader, 2017)
	var prev chainhash.Hash
	for i := 0; i < 2017; i++ {
		bits := uint32(mainBits)
		if i == 2016 {
			bits = distinctBits
		}
		ts := base
		if i > 1 {
			ts = base + int64(i-1)*5 // compressed so a spurious [1..2016] retarget clamps low
		}
		hh := &wire.BlockHeader{Version: 1, PrevBlock: prev, Bits: bits, Timestamp: time.Unix(ts, 0), Nonce: uint32(i)}
		store.put(hh, uint64(i))
		hdrs[i] = hh
		prev = hh.BlockHash()
	}
	parent := hdrs[2016] // height 2016, Bits = distinctBits

	// Correct: candidate at 2017 inherits distinctBits.
	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
		childOf(parent, distinctBits, parent.Timestamp.Unix()+600)))
	// Wrong: any other Bits rejects (and a spurious retarget would also reject distinctBits).
	require.NotEqual(t, distinctBits, uint32(mainBits))
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
		childOf(parent, mainBits, parent.Timestamp.Unix()+600)), blockchain.ErrUnexpectedDifficulty)
}

// TestValidateTrichotomyAndNoPanicFuzz: seeded property test over many random synthetic chains.
// Universal invariants: never panics; the result is exactly one of {nil, skip sentinel, btcd
// RuleError}; and skip occurs only when context is genuinely missing.
func TestValidateTrichotomyAndNoPanicFuzz(t *testing.T) {
	const seed = int64(0xC0FFEE) // arbitrary fixed value for reproducibility
	r := rand.New(rand.NewSource(seed))
	bitsChoices := []uint32{mainBits, 0x1d00fffe}

	for iter := 0; iter < 1000; iter++ {
		n := 1 + r.Intn(40)
		bits := bitsChoices[r.Intn(len(bitsChoices))]
		tsv := make([]int64, n)
		acc := int64(1_600_000_000)
		for i := range tsv {
			tsv[i] = acc
			acc += int64(300 + r.Intn(900))
		}
		store, h := buildChainTS(n, bits, func(i int) int64 { return tsv[i] })

		deleted, ioInjected := false, false
		if n > 1 && r.Intn(3) == 0 {
			delete(store.byHash, h[r.Intn(n)].BlockHash())
			deleted = true
		}
		if r.Intn(3) == 0 {
			store.errOn[h[r.Intn(n)].BlockHash()] = errors.New("io")
			ioInjected = true
		}

		inChain := r.Intn(4) != 0
		var cand *wire.BlockHeader
		if inChain {
			cand = childOf(h[n-1], bits, h[n-1].Timestamp.Unix()+600)
		} else {
			cand = &wire.BlockHeader{Version: 1, PrevBlock: chainhash.Hash{byte(r.Intn(256)), 0x9}, Bits: bits, Timestamp: time.Unix(2_000_000_000, 0)}
		}

		var err error
		require.NotPanics(t, func() { err = validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand) },
			"seed=%#x iter=%d must never panic", seed, iter)

		isSkip := errors.Is(err, ErrBTCHeaderContextUnavailable)
		var re blockchain.RuleError
		isRule := errors.As(err, &re)
		if err == nil {
			require.False(t, isSkip || isRule, "seed=%#x iter=%d: nil cannot also be skip/rule", seed, iter)
		} else {
			require.True(t, isSkip || isRule, "seed=%#x iter=%d: a non-nil result must be skip or RuleError, got %v", seed, iter, err)
			require.False(t, isSkip && isRule, "seed=%#x iter=%d: cannot be both skip and RuleError", seed, iter)
		}
		// skip iff genuinely missing: with full ancestry, no deletion, no IO error, and an
		// in-chain (sub-2016) candidate, the result must NOT be the skip sentinel.
		if inChain && !deleted && !ioInjected {
			require.False(t, isSkip, "seed=%#x iter=%d: a fully-resolvable header must not skip", seed, iter)
		}
	}
}

// Differential replay against real Bitcoin headers.
//
// The oracle is the Bitcoin chain itself: each embedded header carries the difficulty (Bits) Bitcoin
// actually used, so the reused btcd engine, driven through our adapters, must reproduce every real
// difficulty decision. This is independent (real-chain), not the circular CompactToBig/BigToCompact
// self-check. Fixtures are committed (fetched once by testdata/gen_difficulty_replay_fixtures.go) and embedded —
// the tests never touch the network.
//
// Coverage:
//   - mainnet non-boundary run -> full production validator (validateBTCHeaderContextWith) reproduces
//     the constant-epoch difficulty end-to-end.
//   - mainnet retarget boundaries (2016 PowLimit-cap, 32256 first real change, 800352 modern) -> the
//     difficulty engine, fed the real 2016-back window start, reproduces the real recalculated Bits.
//     Driven via a by-height context so we need only the window start + MTP window, not 2016
//     consecutive headers; the production PrevBlock walk is covered in TestRelativeAncestorCtxHopCount.
//   - testnet3 run -> the production validator reproduces the real ReduceMinDifficulty /
//     20-minute-rule decisions and findPrevTestNetDifficulty restores end-to-end.
//
//go:embed testdata/difficulty_replay_mainnet_run.txt
var difficultyReplayMainnetRun string

//go:embed testdata/difficulty_replay_mainnet_boundaries.txt
var difficultyReplayMainnetBoundaries string

//go:embed testdata/difficulty_replay_testnet3_run.txt
var difficultyReplayTestnet3Run string

type fixHdr struct {
	height uint64
	hdr    *wire.BlockHeader
}

func parseFixture(t *testing.T, data string) []fixHdr {
	t.Helper()
	var out []fixHdr
	for _, line := range strings.Split(strings.TrimSpace(data), "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		parts := strings.Fields(line)
		require.Len(t, parts, 2, "fixture line %q", line)
		height, err := strconv.ParseUint(parts[0], 10, 64)
		require.NoError(t, err)
		raw, err := hex.DecodeString(parts[1])
		require.NoError(t, err)
		require.Len(t, raw, 80, "height %d header must be 80 bytes", height)
		var hdr wire.BlockHeader
		require.NoError(t, hdr.Deserialize(bytes.NewReader(raw)), "deserialize height %d", height)
		out = append(out, fixHdr{height: height, hdr: &hdr})
	}
	require.NotEmpty(t, out)
	return out
}

func storeFrom(fixs []fixHdr) *fakeHeaderStore {
	store := newFakeStore()
	for _, f := range fixs {
		store.put(f.hdr, f.height)
	}
	return store
}

func heightMap(fixs []fixHdr) map[uint64]*wire.BlockHeader {
	m := make(map[uint64]*wire.BlockHeader, len(fixs))
	for _, f := range fixs {
		m[f.height] = f.hdr
	}
	return m
}

// copyWithBits returns a shallow copy of hdr with a different Bits (for negative tests).
func copyWithBits(hdr *wire.BlockHeader, bits uint32) *wire.BlockHeader {
	c := *hdr
	c.Bits = bits
	return &c
}

// --- mainnet non-boundary run: full production validator on real headers ---

func TestBtcDiffMainnetNonBoundaryReplay(t *testing.T) {
	fixs := parseFixture(t, difficultyReplayMainnetRun)
	store := storeFrom(fixs)

	validated := 0
	for i, f := range fixs {
		if i < 11 { // need parent + 10 MTP ancestors present in the run
			continue
		}
		require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, f.hdr),
			"real mainnet header %d must validate (the chain accepted it)", f.height)
		validated++
	}
	require.GreaterOrEqual(t, validated, 8, "expected a meaningful number of real blocks replayed")

	// Negative: a real block with its Bits perturbed must reject as wrong difficulty.
	mid := fixs[len(fixs)-1]
	require.NotEqual(t, uint32(0x1d00ffff), mid.hdr.Bits)
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
		copyWithBits(mid.hdr, 0x1d00ffff)), blockchain.ErrUnexpectedDifficulty)
}

// --- mainnet retarget boundaries: engine reproduces the real recalculated Bits ---

// heightCtx serves embedded real headers by height (Parent = height-1, RelativeAncestorCtx =
// height-distance), so a boundary recompute can reach the real 2016-back window start without
// embedding 2016 consecutive headers. It is a test-only context for the difficulty math differential;
// the production PrevBlock-walk resolution is covered by the synthetic adapter tests.
//
// Maintenance: this is a second blockchain.HeaderCtx implementation parallel to the production
// tbcHeaderCtx, and it shares the same load-bearing typed-nil contract — at() returns an untyped
// interface-nil at the chain floor (below). A change to that contract must be reflected in both this
// type and tbcHeaderCtx in tbc_difficulty.go.
type heightCtx struct {
	height uint64
	hdr    *wire.BlockHeader
	by     map[uint64]*wire.BlockHeader
}

func (c *heightCtx) Height() int32    { return int32(c.height) }
func (c *heightCtx) Bits() uint32     { return c.hdr.Bits }
func (c *heightCtx) Timestamp() int64 { return c.hdr.Timestamp.Unix() }

func (c *heightCtx) at(h uint64) blockchain.HeaderCtx {
	hdr, ok := c.by[h]
	if !ok {
		return nil // untyped interface-nil (chain floor / not embedded)
	}
	return &heightCtx{height: h, hdr: hdr, by: c.by}
}
func (c *heightCtx) Parent() blockchain.HeaderCtx { return c.at(c.height - 1) }
func (c *heightCtx) RelativeAncestorCtx(distance int32) blockchain.HeaderCtx {
	return c.at(c.height - uint64(distance))
}

var _ blockchain.HeaderCtx = (*heightCtx)(nil)

// TestBothHeaderCtxFloorNilContract mechanizes the maintenance note above: both the production
// tbcHeaderCtx and the test-only heightCtx must return an untyped interface-nil at the chain floor (a
// typed (*T)(nil) would pass btcd's iterNode != nil guards and then panic). This converts the prose
// cross-reference into a tripwire that fails if either type regresses.
func TestBothHeaderCtxFloorNilContract(t *testing.T) {
	res := &tbcCtxResolver{ctx: ctx(), lookup: newFakeStore(), params: &chaincfg.MainNetParams}
	var prodFloor blockchain.HeaderCtx = (&tbcHeaderCtx{hdr: &wire.BlockHeader{}, height: 1, res: res}).Parent()
	require.True(t, prodFloor == nil, "production tbcHeaderCtx must return untyped interface-nil at the floor")
	var testFloor blockchain.HeaderCtx = (&heightCtx{height: 1, hdr: &wire.BlockHeader{}, by: map[uint64]*wire.BlockHeader{}}).Parent()
	require.True(t, testFloor == nil, "test-only heightCtx must return untyped interface-nil at the floor")
}

func TestBtcDiffMainnetBoundaryDifferential(t *testing.T) {
	by := heightMap(parseFixture(t, difficultyReplayMainnetBoundaries))
	cc := &tbcChainCtx{params: &chaincfg.MainNetParams}

	// Pinned out-of-band anchors documenting the real oracle values (tamper tripwires). All three real
	// boundaries are unclamped (actual timespans within [302400, 4838400]); 2016 is the real-data
	// PowLimit-cap vector. The 4x Min/Max clamp regime is covered synthetically by
	// TestValidateRetargetClamp — that synthetic/real-data split is intentional (mainnet history never
	// lands on the exact integer-second clamp bound).
	require.Equal(t, uint32(0x1d00d86a), by[32256].Bits, "32256 is the first real difficulty change")
	require.Equal(t, uint32(0x1d00ffff), by[2016].Bits, "2016 stayed at the PowLimit cap")
	require.Equal(t, uint32(0x17056102), by[800352].Bits, "800352 modern large-exponent boundary")

	bpr := uint64(cc.BlocksPerRetarget())
	require.EqualValues(t, 2016, bpr) // window-start offset is bound to the params, not a literal

	for _, H := range []uint64{2016, 32256, 800352} {
		require.NotNil(t, by[H], "boundary %d header", H)
		require.NotNil(t, by[H-bpr], "window start %d", H-bpr)
		require.Zero(t, H%bpr, "H=%d must be a retarget boundary", H)

		// Enforce (not just comment) that every real boundary is unclamped: the 4x Min/Max clamp regime
		// is owned by TestValidateRetargetClamp. A regeneration that landed a clamp-binding boundary
		// here would fail loudly.
		actual := by[H-1].Timestamp.Unix() - by[H-bpr].Timestamp.Unix()
		require.Greater(t, actual, cc.MinRetargetTimespan(), "boundary %d must be unclamped-low", H)
		require.Less(t, actual, cc.MaxRetargetTimespan(), "boundary %d must be unclamped-high", H)

		prev := &heightCtx{height: H - 1, hdr: by[H-1], by: by}
		// (a) The engine, fed the real parent + real window start, must reproduce the real Bits.
		require.NoError(t, checkBTCHeaderContext(by[H], prev, cc),
			"engine must reproduce real recalculated difficulty at boundary %d", H)
		// (b) Exact-value independent oracle: an out-of-band recompute (the standalone helper, not
		// btcd) over the real parent+window-start timestamps must equal the real next Bits. This pins,
		// in one value-diff, oldTarget-sourced-from-parent, the H-2016 window indexing, Mul-then-Div
		// order, the 1209600 divisor, and the PowLimit cap.
		require.Equal(t, by[H].Bits, mainnetRetargetExpected(by[H-1].Bits, actual),
			"independent recompute over real timestamps must equal real Bits at boundary %d", H)

		// Negative: perturb the boundary block's Bits -> rejected as wrong difficulty.
		bad := uint32(0x1d00ffff)
		if by[H].Bits == bad {
			bad = 0x1d00d86a
		}
		require.NotEqual(t, by[H].Bits, bad)
		requireReject(t, checkBTCHeaderContext(copyWithBits(by[H], bad), prev, cc), blockchain.ErrUnexpectedDifficulty)
	}

	// Real-data regime mix (machine-checked): pin one INCREASE and one DECREASE so a
	// regeneration cannot silently leave only a single direction covered.
	require.Negative(t, blockchain.CompactToBig(by[32256].Bits).Cmp(blockchain.CompactToBig(by[32255].Bits)),
		"32256 must be a difficulty INCREASE (target decreased)")
	require.Positive(t, blockchain.CompactToBig(by[800352].Bits).Cmp(blockchain.CompactToBig(by[800351].Bits)),
		"800352 must be a difficulty DECREASE (target increased)")
}

// TestBtcDiffWindowStartIdentity pins each boundary's 2016-back window-start to its real block hash.
// The integrity test's PrevBlock linkage skips the window start (it is isolated by a gap in the
// boundaries fixture), so without this a mis-fetched/mislabeled header at the wrong height with valid
// PoW would silently corrupt the recompute timespan.
func TestBtcDiffWindowStartIdentity(t *testing.T) {
	by := heightMap(parseFixture(t, difficultyReplayMainnetBoundaries))
	require.Equal(t, chaincfg.MainNetParams.GenesisHash.String(), by[0].BlockHash().String(),
		"boundary 2016 window start must be the real genesis")
	require.Equal(t, "000000000fa8bfa0f0dd32f956b874b2c7f1772c5fbedcb1b35e03335c7fb0a8", by[30240].BlockHash().String(),
		"boundary 32256 window start must be the real height-30240 block")
	require.Equal(t, "00000000000000000003f5303e4e1f069d5875557fe99ed9f61ce8b8998d2006", by[798336].BlockHash().String(),
		"boundary 800352 window start must be the real height-798336 block")
}

// TestBtcDiffMainnetTimestampIrrelevance validates a real mainnet block whose timestamp is below its
// parent (100007, ~63s backwards) through the full production validator: mainnet
// (ReduceMinDifficulty=false) ignores the candidate's own timestamp for difficulty and inherits the
// parent Bits. Catches a mutation that drops the ReduceMinDifficulty guard so the testnet3-style
// PowLimit fallback could fire on mainnet.
func TestBtcDiffMainnetTimestampIrrelevance(t *testing.T) {
	fixs := parseFixture(t, difficultyReplayMainnetRun)
	store := storeFrom(fixs)
	by := heightMap(fixs)
	cand, parent := by[100007], by[100006]
	require.NotNil(t, cand)
	require.NotNil(t, parent)
	require.Less(t, cand.Timestamp.Unix(), parent.Timestamp.Unix(), "100007 timestamp must be below its parent (fixture-drift tripwire)")

	require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams, cand),
		"mainnet must inherit the parent Bits regardless of a backwards candidate timestamp")
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.MainNetParams,
		copyWithBits(cand, 0x1d00ffff)), blockchain.ErrUnexpectedDifficulty)
}

// TestBtcDiffCorpusShape pins the exact curated cardinality so a truncated / over-fetched /
// partially-committed regeneration fails loudly (the validated>=N floors tolerate silent shrinkage).
// Also gives a generator-pointing message if an embed is empty (clean clone).
func TestBtcDiffCorpusShape(t *testing.T) {
	for name, data := range map[string]string{"mainnet_run": difficultyReplayMainnetRun, "mainnet_boundaries": difficultyReplayMainnetBoundaries, "testnet3_run": difficultyReplayTestnet3Run} {
		require.NotEmpty(t, strings.TrimSpace(data),
			"fixture %s is empty — run: cd core/vm/testdata && go run gen_difficulty_replay_fixtures.go (and commit the result)", name)
	}
	require.Len(t, parseFixture(t, difficultyReplayMainnetRun), 21)
	require.Len(t, parseFixture(t, difficultyReplayMainnetBoundaries), 39) // genesis + 12 + 13 + 13
	require.Len(t, parseFixture(t, difficultyReplayTestnet3Run), 57)
}

// --- fixture integrity: prove the embedded headers are genuinely real & untampered ---

// TestBtcDiffFixturesIntegrity makes any future tamper or mis-fetch self-evident: every embedded header
// must satisfy its own proof-of-work (real Bitcoin work), and within each contiguous run each header
// must link to the previous one by PrevBlock. CheckBlockHeaderContext itself does not verify PoW, so
// this is the corpus's tamper tripwire.
func TestBtcDiffFixturesIntegrity(t *testing.T) {
	cases := []struct {
		data       string
		contiguous bool // the two run files must be gapless; the boundaries file is intentionally gapped
	}{
		{difficultyReplayMainnetRun, true},
		{difficultyReplayTestnet3Run, true},
		{difficultyReplayMainnetBoundaries, false},
	}
	for _, c := range cases {
		fixs := parseFixture(t, c.data)
		for i, f := range fixs {
			// Real PoW: the header hash must meet its own claimed target (proves a real mined header).
			hash := f.hdr.BlockHash()
			require.LessOrEqual(t, blockchain.HashToBig(&hash).Cmp(blockchain.CompactToBig(f.hdr.Bits)), 0,
				"height %d header must satisfy its own PoW target", f.height)
			if i == 0 {
				continue
			}
			if c.contiguous {
				// A gap in a run file silently breaks the MTP / findPrevTestNetDifficulty walk
				// guarantees, so it must fail loudly here.
				require.Equal(t, fixs[i-1].height+1, f.height, "run file must be strictly contiguous at height %d", f.height)
				require.Equal(t, fixs[i-1].hdr.BlockHash(), f.hdr.PrevBlock, "height %d must link to %d via PrevBlock", f.height, fixs[i-1].height)
			} else if fixs[i-1].height+1 == f.height {
				require.Equal(t, fixs[i-1].hdr.BlockHash(), f.hdr.PrevBlock, "height %d must link to %d via PrevBlock", f.height, fixs[i-1].height)
			}
		}
	}
}

// TestBtcDiffCompactCodecAnchor anchors btcd's compact<->target codec to external Bitcoin constants
// (not btcd-vs-btcd): 2^224-1 -> 0x1d00ffff, CompactToBig(0x1d00ffff) == 0xffff<<208, plus a canonical
// round-trip over the Bits actually observed in the real fixtures. Satisfies the reference-table /
// round-trip oracle requirement.
func TestBtcDiffCompactCodecAnchor(t *testing.T) {
	powLimit := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 224), big.NewInt(1)) // 2^224-1
	require.Equal(t, uint32(0x1d00ffff), blockchain.BigToCompact(powLimit),
		"BigToCompact(2^224-1) must be the canonical PowLimitBits 0x1d00ffff")
	require.Equal(t, new(big.Int).Lsh(big.NewInt(0xffff), 208), blockchain.CompactToBig(0x1d00ffff),
		"CompactToBig(0x1d00ffff) must be the genesis/min target 0xffff<<208")
	for _, b := range []uint32{0x1d00ffff, 0x1d00d86a, 0x1b04864c, 0x1c018167, 0x17053894, 0x17056102, 0x207fffff} {
		require.Equal(t, b, blockchain.BigToCompact(blockchain.CompactToBig(b)), "canonical compact %#x must round-trip", b)
	}
}

// --- testnet3 run: production validator reproduces ReduceMinDifficulty + restores ---

func TestBtcDiffTestnet3MinDiffReplay(t *testing.T) {
	fixs := parseFixture(t, difficultyReplayTestnet3Run)
	store := storeFrom(fixs)
	by := heightMap(fixs)
	bpr := uint64((&tbcChainCtx{params: &chaincfg.TestNet3Params}).BlocksPerRetarget())
	reductionTime := int64(chaincfg.TestNet3Params.MinDiffReductionTime / time.Second) // derived, not hardcoded 1200

	// Corpus guards: the run must be a single epoch starting at a boundary, strictly contiguous, with
	// the pinned epoch difficulty. A regen that crosses the next boundary (a second,
	// never-differentially-checked epoch) or drops/dupes a line fails here.
	require.Zero(t, fixs[0].height%bpr, "the testnet3 run must START at a retarget boundary so findPrevTestNetDifficulty is in-fixture")
	require.Equal(t, uint32(0x1c018167), fixs[0].hdr.Bits, "pinned testnet3 epoch difficulty (tamper tripwire)")
	boundaries := 0
	for i, f := range fixs {
		if f.height%bpr == 0 {
			boundaries++
		}
		if i > 0 {
			require.Equal(t, fixs[i-1].height+1, f.height, "testnet3 run must be strictly contiguous")
		}
	}
	require.Equal(t, 1, boundaries, "the run must contain exactly one (the starting) boundary — a single epoch")

	gapOf := func(f fixHdr) int64 { return f.hdr.Timestamp.Unix() - by[f.height-1].Timestamp.Unix() }

	var minDiff, walkRestore, inherit int
	validated := 0
	for i, f := range fixs {
		if i < 12 || f.height%bpr == 0 { // need parent+11 MTP present; skip the boundary block (needs off-fixture window start)
			continue
		}
		require.NoError(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params, f.hdr),
			"real testnet3 header %d must validate (the chain accepted it)", f.height)
		validated++
		switch {
		case f.hdr.Bits == 0x1d00ffff:
			minDiff++ // >20-min gap -> PowLimitBits rule path
		case by[f.height-1].Bits == 0x1d00ffff:
			// non-min child of a min parent -> findPrevTestNetDifficulty walked back over the min run.
			// The walk is bounded in-fixture: it stops at the run's starting boundary (the %2016==0
			// stop condition, asserted above), so it can never run off the fixture floor.
			walkRestore++
		default:
			inherit++ // non-min child of a non-min parent -> plain inheritance
		}
	}
	require.GreaterOrEqual(t, validated, 30)
	require.Positive(t, minDiff, "must exercise the >20-min PowLimitBits branch")
	require.Positive(t, walkRestore, "must exercise the findPrevTestNetDifficulty WALK-restore branch (non-min child of a min parent)")
	require.Positive(t, inherit, "must exercise plain non-min inheritance")

	// Negatives, each targeting a specific rule branch with its gap precondition asserted:
	// (a) a >20-min min-diff block flipped to the epoch bits must reject (rule mandates PowLimitBits);
	// (b) a walk-restore block (non-min child of a min parent) flipped to PowLimitBits must reject —
	//     proving the value findPrevTestNetDifficulty walked back to is enforced, not blanket-accepted.
	var aMin, aWalk *fixHdr
	for i := range fixs {
		f := &fixs[i]
		if f.height%bpr == 0 || f.height < fixs[0].height+12 {
			continue
		}
		if aMin == nil && f.hdr.Bits == 0x1d00ffff {
			aMin = f
		}
		if aWalk == nil && f.hdr.Bits != 0x1d00ffff && by[f.height-1].Bits == 0x1d00ffff {
			aWalk = f
		}
	}
	require.NotNil(t, aMin)
	require.NotNil(t, aWalk)
	require.Greater(t, gapOf(*aMin), reductionTime, "the min-diff negative block must genuinely be a >20-min block")
	require.LessOrEqual(t, gapOf(*aWalk), reductionTime, "the walk-restore negative block must genuinely be a within-20-min block")
	require.NotEqual(t, uint32(0x1d00ffff), aWalk.hdr.Bits)

	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params,
		copyWithBits(aMin.hdr, aWalk.hdr.Bits)), blockchain.ErrUnexpectedDifficulty)
	requireReject(t, validateBTCHeaderContextWith(ctx(), store, &chaincfg.TestNet3Params,
		copyWithBits(aWalk.hdr, 0x1d00ffff)), blockchain.ErrUnexpectedDifficulty)
}

// Tests for the hard per-validation walk-hop bound (maxHeaderCtxWalkHops /
// tbcCtxResolver.walkExceeded). The bound makes per-header ancestry-lookup work provably O(maxHops) on
// the enforced, network-reachable gossip path, regardless of stored-chain shape, and fails safe to
// skip (never a false difficulty rejection).
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
