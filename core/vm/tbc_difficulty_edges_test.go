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

import (
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"
)

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
