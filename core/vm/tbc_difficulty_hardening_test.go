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

// Mutation-hardening tests for the contextual-difficulty adapters. Each targets a specific one-line
// production change that the baseline suite would not catch, plus durability against future
// btcd/TBC drift. All synthetic (no PoW mining): CheckBlockHeaderContext checks difficulty +
// median-time-past + version, not hash-meets-target.

import (
	"errors"
	"fmt"
	"math/big"
	"math/rand"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/hemilabs/heminetwork/database"
	"github.com/stretchr/testify/require"
)

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
