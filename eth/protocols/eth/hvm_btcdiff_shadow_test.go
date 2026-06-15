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

package eth

// Shadow (log-only) wiring of the contextual-difficulty validator into handleBTCBlocks. Shadow mode
// changes no behavior, so these tests pin the only new logic: verdict classification (skip stays
// distinct from reject) and that the shadow observer is benign. The end-to-end "shadow does not
// enforce" integration test needs the full TBC node harness and lives in the enforce tests.

import (
	"errors"
	"fmt"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/metrics"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/enode"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
	"golang.org/x/time/rate"
)

func TestClassifyBTCDiffShadow(t *testing.T) {
	require.Equal(t, btcDiffShadowAccept, classifyBTCDiffShadow(nil),
		"nil = accept")
	require.Equal(t, btcDiffShadowSkip, classifyBTCDiffShadow(vm.ErrBTCHeaderContextUnavailable),
		"the skip sentinel = skip, not reject")
	require.Equal(t, btcDiffShadowSkip, classifyBTCDiffShadow(
		errors.Join(errors.New("wrap"), vm.ErrBTCHeaderContextUnavailable)),
		"a wrapped skip sentinel must still classify as skip (errors.Is)")
	require.Equal(t, btcDiffShadowReject, classifyBTCDiffShadow(errors.New("difficulty violation")),
		"a non-sentinel error = reject (would drop in enforce mode)")

	// The validator's actual rejection type is a btcd blockchain.RuleError (from
	// CheckBlockHeaderContext). Pin classification on the production type, not a generic error.
	ruleErr := blockchain.RuleError{ErrorCode: blockchain.ErrUnexpectedDifficulty, Description: "bad difficulty"}
	require.Equal(t, btcDiffShadowReject, classifyBTCDiffShadow(ruleErr),
		"a real btcd RuleError = reject")
	// Tripwire: a RuleError must never satisfy the skip sentinel. btcd v0.24.2's RuleError has no
	// Unwrap/Is so this holds today; a future btcd bump adding one that matched would silently
	// downgrade reject to skip, accepting an easier-than-consensus header when enforcing.
	require.False(t, errors.Is(ruleErr, vm.ErrBTCHeaderContextUnavailable),
		"a RuleError must not be classified as skip via errors.Is")

	// Precedence: the skip sentinel is checked before the default reject, so a skip sentinel
	// co-present with a RuleError classifies as skip, order-independently. The validator never
	// emits both (skip-override and RuleError branches are mutually exclusive, see
	// core/vm/tbc_difficulty.go), so this only pins the documented precedence rule.
	require.Equal(t, btcDiffShadowSkip,
		classifyBTCDiffShadow(errors.Join(ruleErr, vm.ErrBTCHeaderContextUnavailable)),
		"skip sentinel dominates a co-present RuleError (join, sentinel second)")
	require.Equal(t, btcDiffShadowSkip,
		classifyBTCDiffShadow(errors.Join(vm.ErrBTCHeaderContextUnavailable, ruleErr)),
		"skip sentinel dominates a co-present RuleError (join, sentinel first)")
	// A doubly-wrapped (%w within %w) skip sentinel must still classify as skip.
	require.Equal(t, btcDiffShadowSkip,
		classifyBTCDiffShadow(fmt.Errorf("outer: %w", fmt.Errorf("inner: %w", vm.ErrBTCHeaderContextUnavailable))),
		"doubly-wrapped skip sentinel still classifies as skip")
}

// TestEvaluateBTCDiffSkipCounterDelta pins the only reachable side effect of the shadow observer in
// unit tests: the skip-counter increment. The benign test asserts NotPanics but never checks which
// counter moved, so deleting hvmBTCDiffShadowSkip.Inc(1) or misrouting skip to reject survives it.
// A delta-based assertion kills both (counters are never-reset process-global atomic.Int64s, so
// absolute values are meaningless). Works with metrics off: this fork's metrics.Counter is a
// concrete atomic.Int64 with unconditional Inc/Snapshot and no NilCounter.
//
// Must stay non-parallel and be the sole incrementer of these counters during its run (alongside the
// concurrent test below), or the exact-delta goes flaky.
func TestEvaluateBTCDiffSkipCounterDelta(t *testing.T) {
	require.Nil(t, vm.TBCFullNode, "precondition: full node not initialized (validator returns skip)")

	accept0 := hvmBTCDiffShadowAccept.Snapshot().Count()
	skip0 := hvmBTCDiffShadowSkip.Snapshot().Count()
	reject0 := hvmBTCDiffShadowReject.Snapshot().Count()

	hdr := &wire.BlockHeader{Version: 1, Bits: 0x1d00ffff, Timestamp: time.Unix(1_600_000_000, 0)}
	verdict := evaluateBTCDiff(chainhash.Hash{0x01}, hdr)

	// The returned verdict (what the enforce caller consumes) must equal skip too, catching a mutant
	// that keeps the correct skip Inc but corrupts `return verdict`.
	require.Equal(t, btcDiffShadowSkip, verdict, "returned verdict must be skip (counter/return consistency)")
	require.Equal(t, skip0+1, hvmBTCDiffShadowSkip.Snapshot().Count(),
		"skip counter must increment by exactly 1 (kills a deleted/misrouted skip Inc)")
	require.Equal(t, accept0, hvmBTCDiffShadowAccept.Snapshot().Count(),
		"accept counter must not move on a skip verdict")
	require.Equal(t, reject0, hvmBTCDiffShadowReject.Snapshot().Count(),
		"reject counter must not move on a skip verdict")
}

// TestShadowCounterRegistration pins that each package counter var is the object registered under its
// metric name and that the three names are distinct. metrics.Register discards a duplicate-name
// registration (returns ErrDuplicateMetric, no panic), so a name typo or collision would silently
// detach a counter: Inc lands on a registered orphan, the scraped metric stays zero, no test fails.
func TestShadowCounterRegistration(t *testing.T) {
	for name, want := range map[string]*metrics.Counter{
		"eth/hvm/btcdiff/shadow/accept": hvmBTCDiffShadowAccept,
		"eth/hvm/btcdiff/shadow/skip":   hvmBTCDiffShadowSkip,
		"eth/hvm/btcdiff/shadow/reject": hvmBTCDiffShadowReject,
	} {
		got, ok := metrics.DefaultRegistry.Get(name).(*metrics.Counter)
		require.True(t, ok, "metric %q must be registered as a *Counter", name)
		require.Same(t, want, got, "package var must be the counter registered under %q", name)
	}
	// The require.Same loop above is the collision detector: on a duplicate metric name, Register
	// discards the second and Get returns the first, so Same(secondVar, firstVar) fails. These
	// NotSame checks guard a different mutation: a copy/paste aliasing two package vars to the same
	// *Counter (e.g. hvmBTCDiffShadowSkip = hvmBTCDiffShadowAccept), so two verdicts share one counter.
	require.NotSame(t, hvmBTCDiffShadowAccept, hvmBTCDiffShadowSkip, "accept and skip must be distinct counters")
	require.NotSame(t, hvmBTCDiffShadowSkip, hvmBTCDiffShadowReject, "skip and reject must be distinct counters")
	require.NotSame(t, hvmBTCDiffShadowAccept, hvmBTCDiffShadowReject, "accept and reject must be distinct counters")

	// Prefix-exclusivity: exactly the three known counters live under the namespace, with no stray or
	// typo'd sibling (e.g. ".../rejct") and nothing registered as a non-Counter type. The per-name
	// loop above only checks the three known names resolve; this enumerates the registry.
	gotUnderPrefix := map[string]bool{}
	metrics.DefaultRegistry.Each(func(name string, v interface{}) {
		if strings.HasPrefix(name, "eth/hvm/btcdiff/shadow/") {
			_, ok := v.(*metrics.Counter)
			require.True(t, ok, "metric %q under the shadow prefix must be a *Counter", name)
			gotUnderPrefix[name] = true
		}
	})
	require.Equal(t, map[string]bool{
		"eth/hvm/btcdiff/shadow/accept": true,
		"eth/hvm/btcdiff/shadow/skip":   true,
		"eth/hvm/btcdiff/shadow/reject": true,
	}, gotUnderPrefix, "exactly the three known shadow counters must exist under the prefix")
}

// TestEvaluateBTCDiffConcurrent drives the shadow observer from many goroutines at once, matching the
// live shape (handleBTCBlocks runs one goroutine per peer). This is a no-panic + exact-delta smoke
// test, not a deep race test: with vm.TBCFullNode==nil the validator short-circuits to skip before
// allocating its resolver or any header lookup, so the only concurrent work is the atomic counter Inc
// (which -race treats as synchronized and cannot flag). It does not race-validate the validator body
// (gated behind a non-nil TBCFullNode, covered by the live-TBC-node harness).
//
// Must stay non-parallel and be the sole incrementer of these counters during its run (with the delta
// test above), or the exact-delta assertion goes flaky.
func TestEvaluateBTCDiffConcurrent(t *testing.T) {
	require.Nil(t, vm.TBCFullNode, "precondition: full node not initialized (validator returns skip)")

	const n = 64
	skip0 := hvmBTCDiffShadowSkip.Snapshot().Count()
	accept0 := hvmBTCDiffShadowAccept.Snapshot().Count()
	reject0 := hvmBTCDiffShadowReject.Snapshot().Count()

	// Recover any panic into a shared slice and assert on the test goroutine after Wait(). testify
	// require.* calls t.FailNow() -> runtime.Goexit(), which Go requires run only on the test
	// goroutine, so require.* must not be used inside these spawned goroutines.
	var (
		mu     sync.Mutex
		panics []any
	)
	var wg sync.WaitGroup
	wg.Add(n)
	for i := 0; i < n; i++ {
		go func(i int) {
			defer wg.Done()
			defer func() {
				if r := recover(); r != nil {
					mu.Lock()
					panics = append(panics, r)
					mu.Unlock()
				}
			}()
			// hdr/hash are inert on the skip path (validator returns before reading them); varied
			// only so each goroutine owns its own stack-local values.
			hdr := &wire.BlockHeader{Version: 1, Bits: 0x1d00ffff, Timestamp: time.Unix(1_600_000_000+int64(i), 0)}
			evaluateBTCDiff(chainhash.Hash{byte(i)}, hdr)
		}(i)
	}
	wg.Wait()

	require.Empty(t, panics, "evaluateBTCDiff must not panic under concurrent calls: %v", panics)
	require.Equal(t, skip0+n, hvmBTCDiffShadowSkip.Snapshot().Count(),
		"N concurrent skip verdicts must produce a +N skip delta; a short delta means a call was "+
			"misrouted to accept/reject or a goroutine bailed before Inc (counts cannot tear — Inc is atomic)")
	require.Equal(t, accept0, hvmBTCDiffShadowAccept.Snapshot().Count(), "accept unchanged")
	require.Equal(t, reject0, hvmBTCDiffShadowReject.Snapshot().Count(), "reject unchanged")
}

// TestEvaluateBTCDiffBenign confirms the evaluator does not panic and, with no TBC full node set up
// (vm.TBCFullNode nil in unit tests), returns skip so the enforce caller (shouldDropBTCHeader) would
// not drop the header. Exercises the skip path end-to-end through the real validator + classifier.
func TestEvaluateBTCDiffBenign(t *testing.T) {
	require.Nil(t, vm.TBCFullNode, "precondition: full node not initialized in unit tests")
	hdr := &wire.BlockHeader{Version: 1, Bits: 0x1d00ffff, Timestamp: time.Unix(1_600_000_000, 0)}
	var verdict btcDiffShadowVerdict
	require.NotPanics(t, func() { verdict = evaluateBTCDiff(chainhash.Hash{0x01}, hdr) },
		"evaluation must never panic")
	require.Equal(t, btcDiffShadowSkip, verdict, "nil-full-node verdict must be skip, not reject")
	require.False(t, shouldDropBTCHeader(verdict), "a skip verdict must NOT drop the header")
}

// TestShouldDropBTCHeader pins the gossip-path contextual-difficulty enforce policy: only a genuine contextual-difficulty
// rejection drops a gossiped header. The load-bearing invariant is the skip case: dropping on skip
// (ancestry not yet available during IBD) would stall sync, so it is asserted explicitly.
func TestShouldDropBTCHeader(t *testing.T) {
	require.True(t, shouldDropBTCHeader(btcDiffShadowReject), "a reject MUST drop the header")
	require.False(t, shouldDropBTCHeader(btcDiffShadowSkip), "a skip MUST NOT drop (would stall IBD)")
	require.False(t, shouldDropBTCHeader(btcDiffShadowAccept), "an accept MUST NOT drop")

	// Fail open on any non-reject value: the zero-value verdict and any out-of-range int must not
	// drop, so an uninitialized verdict or a future enum addition never silently discards honest
	// headers (the safe default under enforce is insert, not drop).
	require.Equal(t, btcDiffShadowAccept, btcDiffShadowVerdict(0), "zero-value verdict must be accept (iota 0)")
	require.False(t, shouldDropBTCHeader(btcDiffShadowVerdict(0)), "zero-value verdict must not drop")
	require.False(t, shouldDropBTCHeader(btcDiffShadowVerdict(99)), "an out-of-range verdict must fail open (not drop)")

	// Enum-ordering tripwire: reject is value 2 (accept=0, skip=1, reject=2). Inserting a verdict
	// before reject shifts its value; this breaks loudly to force revisiting
	// classifyBTCDiffShadow/shouldDropBTCHeader.
	require.Equal(t, btcDiffShadowVerdict(2), btcDiffShadowReject, "verdict enum order changed — revisit the drop policy")
}

// TestShouldDropBTCHeaderPoW pins the gossip-path PoW drop policy:
// drop only on a genuine PoW RuleError, never on a valid header (nil) or the skip sentinel (params not
// yet configured). Dropping on skip would discard honest headers on a transient config gap. This gate
// is gossip-path defense-in-depth, not the consensus enforcement point.
func TestShouldDropBTCHeaderPoW(t *testing.T) {
	require.True(t, shouldDropBTCHeaderPoW(blockchain.RuleError{ErrorCode: blockchain.ErrHighHash}),
		"a genuine PoW failure (forged-Bits/zero-PoW) MUST drop")
	require.True(t, shouldDropBTCHeaderPoW(blockchain.RuleError{ErrorCode: blockchain.ErrUnexpectedDifficulty}),
		"an out-of-range target MUST drop")
	require.False(t, shouldDropBTCHeaderPoW(nil), "valid PoW (nil) MUST NOT drop")
	require.False(t, shouldDropBTCHeaderPoW(vm.ErrBTCHeaderContextUnavailable),
		"the skip sentinel (params unconfigured) MUST NOT drop (never discard honest headers on a config gap)")
	require.False(t, shouldDropBTCHeaderPoW(fmt.Errorf("ctx: %w", vm.ErrBTCHeaderContextUnavailable)),
		"a wrapped skip sentinel must still classify as skip (errors.Is), not drop")
}

// TestBTCDiffRejectLogLimiterConfig pins the reject-log throttle config via the read-only getters
// (not advancing the token bucket, which would be time-dependent). A zero/Inf rate or zero burst
// would either flood the log or suppress the throttled reject alert.
func TestBTCDiffRejectLogLimiterConfig(t *testing.T) {
	require.Equal(t, rate.Every(5*time.Second), btcDiffRejectLogLimiter.Limit(),
		"reject-log limiter must stay throttled at ~1 line / 5s")
	require.Equal(t, 4, btcDiffRejectLogLimiter.Burst(), "reject-log limiter burst must stay 4")
}

// fakeBTCDecoder copies a prepared *BTCBlocksPacket into the handler's decode target, bypassing RLP
// so a test can drive handleBTCBlocks with an arbitrary header count.
type fakeBTCDecoder struct{ pkt *BTCBlocksPacket }

func (d fakeBTCDecoder) Decode(val interface{}) error { *(val.(*BTCBlocksPacket)) = *d.pkt; return nil }
func (d fakeBTCDecoder) Time() time.Time              { return time.Time{} }

// TestHandleBTCBlocksRejectsOversizedMessage pins the per-message header cap: a BtcBlocks message
// with more than maxBtcBlocksServe entries is rejected. Reachable without a live node: a non-nil
// zero-value *tbc.Server passes the nil-guard, and the cap returns before any node method runs
// (FullBlockAvailable is inside the per-header loop). Kills a cap-removal mutant and a `>`->`>=`
// off-by-one (33 > 32 must reject).
func TestHandleBTCBlocksRejectsOversizedMessage(t *testing.T) {
	orig := vm.TBCFullNode
	vm.TBCFullNode = &tbc.Server{} // non-nil; never dereferenced before the cap return
	defer func() { vm.TBCFullNode = orig }()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	pkt := &BTCBlocksPacket{}
	pkt.BTCBlocksResponse = make(BTCBlocksResponse, maxBtcBlocksServe+1) // 33 > cap 32; cap checks len only

	err := handleBTCBlocks(nil, fakeBTCDecoder{pkt: pkt}, peer)
	require.ErrorIs(t, err, errMsgTooLarge, "an oversized BtcBlocks message must be rejected by the per-message cap")
	// Pin the exact diagnostic text (count + cap) so a %d operand swap or len/const substitution,
	// invisible to ErrorIs, is caught.
	require.EqualError(t, err, "message too long: BtcBlocks response of 33 exceeds cap 32")
}

// TestHandleBTCBlocksAcceptsAtCapBoundary pins the cap boundary: exactly maxBtcBlocksServe entries
// (an honest peer's max-size response) must not be rejected by the cap, killing a `>`->`>=` mutation.
// The entries are invalid wire bytes, so the per-header loop fails to deserialize and `continue`s
// without touching the zero-value node; the cap is the only path that returns errMsgTooLarge here.
func TestHandleBTCBlocksAcceptsAtCapBoundary(t *testing.T) {
	orig := vm.TBCFullNode
	vm.TBCFullNode = &tbc.Server{}
	defer func() { vm.TBCFullNode = orig }()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	pkt := &BTCBlocksPacket{}
	pkt.BTCBlocksResponse = make(BTCBlocksResponse, maxBtcBlocksServe) // exactly 32 (== cap, must pass)
	for i := range pkt.BTCBlocksResponse {
		bb := common.BitcoinBlock([]byte{0x00}) // invalid wire block -> loop Deserialize fails -> continue
		pkt.BTCBlocksResponse[i] = &bb
	}

	err := handleBTCBlocks(nil, fakeBTCDecoder{pkt: pkt}, peer)
	// Exactly nil: 32 is not > 32 (cap passes), each invalid entry deserialize-fails + continues
	// without touching the node, and the handler falls through to `return nil`. NoError is tighter
	// than NotErrorIs(errMsgTooLarge): it also kills a `>`->`>=` that re-wraps a different sentinel
	// and a `continue`->`return err` leak.
	require.NoError(t, err, "exactly maxBtcBlocksServe entries must pass the cap and the handler returns nil")
}
