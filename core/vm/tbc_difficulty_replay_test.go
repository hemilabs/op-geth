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

import (
	"bytes"
	_ "embed"
	"encoding/hex"
	"math/big"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"
)

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
