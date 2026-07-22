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

package core

// Extend the contextual Bitcoin-difficulty closure from the consensus apply path
// (applyHvmHeaderConsensusUpdate) to the two other writers that feed the lightweight hVM header node:
//
//   1. the sequencer build path (getBitcoinAttributesForNextBlock): validate headers before packaging
//      them into a BtcAttributesDeposited tx, truncating to the longest prefix the apply path will accept.
//      Pure liveness: without it the sequencer could package a header the apply path rejects, stalling
//      block production. Validators re-derive the BtcAttr independently, so this never changes consensus,
//      only what the sequencer proposes.
//
//   2. the snap-sync reconstruction (SnapSyncHvm): observe-only contextual-difficulty check of the
//      bulk-loaded header chain. It never halts — enforcement there is redundant (the load is pinned to
//      the snap target's ancestry by the post-add canonical-tip crit) and unsafe (halting would split a
//      snap node from forward/restore nodes that grandfather the same committed header). It emits an
//      alertable signal and proceeds; real enforcement stays in the apply path. See SnapSyncHvm.
//
// Both reuse the apply path's floor-aware validator (vm.ValidateBTCHeaderBatchForNetwork), so there is
// one contextual-difficulty implementation. The two pure helpers below isolate the loader-specific
// control flow (sequencer prefix truncation; snap check/skip split) for unit testing without a live TBC node.

import (
	"context"
	"errors"

	"github.com/btcsuite/btcd/wire"

	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
)

// btcSnapEnforceFloor is the lowest absolute BTC height at which the snap-sync bulk loader checks
// (observe-only) contextual-difficulty: floorHeight (effective-genesis offset) + clearance (the
// validator's unverifiable near-floor band) + (MaximumBtcHeadersInTx - 1). The trailing (maxBatch-1) term
// keeps the checked band a subset of the forward apply path's enforce set (see btcEnforceableSuffix), so
// the alert never flags a header the forward path itself defers. Single definition of the floor; both
// SnapSyncHvm and TestSnapEnforceFloorAboveValidatorGate use it, so the test pins the production value.
func btcSnapEnforceFloor(floorHeight, clearance uint64) uint64 {
	return floorHeight + clearance + (types.MaximumBtcHeadersInTx - 1)
}

// btcHeaderBatchClassifier classifies a candidate batch of contiguous BTC headers as the contextual-difficulty apply
// path would: nil / vm.ErrBTCBatchBelowFloor / vm.ErrBTCBatchUnconnected (apply path will not
// contextually-reject), vm.ErrBTCHeaderContextUnavailable (transient/corrupt read — caller skips and
// retries, never truncates), or a btcd RuleError (a contextual-difficulty violation — caller must not
// include the offending header).
type btcHeaderBatchClassifier func(headers []*wire.BlockHeader) error

// longestEnforceableBTCHeaderPrefix returns the longest leading sub-slice of `headers` (an ascending,
// parent->child contiguous chain) that the contextual-difficulty apply path will not contextually-reject, using
// `classify` to evaluate a candidate prefix.
//
// Liveness rationale (sequencer build path only): the apply path applies the contextual-difficulty gate
// at whole-batch granularity, so one invalid header rejects the whole block. A header's validity depends
// only on its own ancestry (at or below it in this contiguous chain), so validity is prefix-monotonic: if
// header k is the first invalid one, every prefix [0:k] is valid and every longer prefix still contains k
// and is rejected. We shrink from the end one header at a time, converging on [0:k] (or the full slice).
// n is tiny on the build path, so the repeated classify cost is negligible.
//
// Outcomes:
//   - acceptable verdict (nil / below-floor / unconnected): return the current prefix, skip=false.
//     Below-floor means the apply path defers; unconnected is preserved as pre-difficulty-enforcement
//     AddExternalHeaders behavior, not truncated.
//   - context-unavailable: transient/corrupt read; do not truncate (could silently drop honest headers).
//     Return skip=true so the caller skips this build and retries.
//   - btcd RuleError: drop the last header and re-evaluate. If the chain empties, the first new header is
//     invalid: return an empty prefix (caller builds no BtcAttr this round).
//
// The returned prefix always aliases a leading sub-slice of the input (no copy); callers must not retain
// the input beyond the returned length.
func longestEnforceableBTCHeaderPrefix(headers []*wire.BlockHeader, classify btcHeaderBatchClassifier) (prefix []*wire.BlockHeader, skip bool, err error) {
	prefix = headers
	for len(prefix) > 0 {
		verr := classify(prefix)
		switch {
		case verr == nil,
			isAcceptableBTCBatchVerdict(verr):
			return prefix, false, nil
		case isRecoverableBTCBatchVerdict(verr):
			// Transient/corrupt read while resolving ancestry, not a statement about the headers — never
			// truncate. Surface it so the caller skips and retries next build.
			return nil, true, verr
		default:
			// A contextual-difficulty RuleError. The offending header is at some index < len; drop the
			// last and re-evaluate (converges on the longest valid prefix).
			prefix = prefix[:len(prefix)-1]
		}
	}
	return nil, false, nil
}

// isAcceptableBTCBatchVerdict reports whether a non-nil verdict means the apply path will not
// contextually-reject this batch (builder keeps all headers): below-floor (apply path defers) or
// unconnected (preserved as the existing AddExternalHeaders no-orphan behavior — the dry-run add, not
// contextual-difficulty, decides it).
func isAcceptableBTCBatchVerdict(err error) bool {
	return errors.Is(err, vm.ErrBTCBatchBelowFloor) || errors.Is(err, vm.ErrBTCBatchUnconnected)
}

// isRecoverableBTCBatchVerdict reports whether a verdict is a transient/corrupt read (skip+retry),
// as opposed to a statement about the headers themselves.
func isRecoverableBTCBatchVerdict(err error) bool {
	return errors.Is(err, vm.ErrBTCHeaderContextUnavailable)
}

// btcEnforceableSuffix splits an ascending, parent->child contiguous BTC header chain whose first element
// sits at absolute height firstHeight into the leading prefix the snap loader skips and the trailing
// suffix it checks (observe-only) for contextual-difficulty, using enforceFloor as the lowest
// checked height. Returns the checked suffix (a leading-aligned sub-slice tail, possibly empty) and the
// number of skipped headers (the prefix length).
//
// Why enforceFloor sits where it does (keeps the alert low-noise; was the split-safety bound back when
// snap enforced): the forward apply path defers a whole BtcAttr batch when its lowest header is below
// floor+clearance; a batch spans up to maxBatch headers, so the highest header that can sit in a
// forward-deferred batch is at floor+clearance+(maxBatch-2). Setting enforceFloor = floor + clearance +
// (maxBatch-1), one above that, makes the checked band a subset of the forward path's enforce set, so the
// alert only fires on a header the forward path itself would enforce, never on one it defers.
func btcEnforceableSuffix(headers []*wire.BlockHeader, firstHeight, enforceFloor uint64) (suffix []*wire.BlockHeader, deferred int) {
	if len(headers) == 0 {
		return nil, 0
	}
	if firstHeight >= enforceFloor {
		// The entire chain is at/above the enforce floor (e.g. a high effective-genesis floor); enforce
		// all of it.
		return headers, 0
	}
	// headers[i] is at firstHeight+i; the first enforceable index is enforceFloor-firstHeight.
	c := enforceFloor - firstHeight
	if c >= uint64(len(headers)) {
		// The whole chain is within the defer band (snap target close to the effective genesis).
		return nil, len(headers)
	}
	return headers[c:], int(c)
}

// snapBtcDiffObservation is the observe-only action SnapSyncHvm takes for a snap-base contextual-difficulty
// verdict. Snap-sync never halts on a contextual-difficulty reject (see SnapSyncHvm), so the only consequential distinction is
// which verdict is alertable.
type snapBtcDiffObservation int

const (
	snapObsClean      snapBtcDiffObservation = iota // nil: the checked suffix is contextually clean
	snapObsBelowFloor                               // ErrBTCBatchBelowFloor: not checked (benign; unexpected above the floor)
	snapObsIncomplete                               // unconnected / IO-corrupt: the check could not complete
	snapObsReject                                   // a btcd RuleError: alertable (the only arm that marks the meter)
)

// snapObserveResult is the advisory outcome of the observe-only contextual-difficulty check SnapSyncHvm runs on its
// reconstructed BTC base. Every field is telemetry (snap never halts on a contextual-difficulty reject), so the caller decides
// which fields alert or log. Returned by observeSnapBtcDiff so the verdict-dispatch composition is
// unit-testable without a live indexed full node. The parts of SnapSyncHvm that need a live full node and
// stay in the caller: the block-availability wait/refetch loop, the walk-back that builds headersToAdd
// (both read vm.TBCFullNode), and updateFullTBCToLightweight. The subsequent AddExternalHeaders into the
// lightweight node + canonical-tip crit is not full-node-bound and is covered against a real lightweight
// node by TestHvmApplyPathRollsBackOnWrongCanonicalTipRegtest.
type snapObserveResult struct {
	powFailed           bool  // a header in the base failed the context-free PoW check
	powErr              error // the PoW failure (for the alert log), nil if powFailed is false
	clearanceErr        error // non-nil => contextual observation SKIPPED (unknown network: no chaincfg params)
	firstHeightErr      error // non-nil => contextual observation SKIPPED (could not read the first header's height)
	firstHeight         uint64
	enforceFloor        uint64
	firstHeightMismatch bool // tripwire: firstHeight != genesisOffset+1 (reset/walk-back did not start at genesis)
	enforcedCount       int  // headers in the enforceable (>= enforceFloor) suffix that were checked
	deferredCount       int  // near-floor headers NOT checked (below enforceFloor)
	contextualRan       bool // the contextual validator actually ran (enforceable suffix was non-empty)
	ctxObservation      snapBtcDiffObservation
	ctxErr              error // the validator verdict (for the alert log when ctxObservation == snapObsReject)
}

// observeSnapBtcDiff runs the observe-only (never-halting, never-mutating) contextual-difficulty check on the
// snap-reconstructed BTC base `headers` against `lookup`, the header store holding the base's ancestry
// (vm.TBCFullNode in production; a seeded lightweight node in tests). It performs (1) a context-free PoW
// check over all headers, then (2) a contextual-difficulty check of the enforceable above-floor suffix
// (btcEnforceableSuffix keeps the checked band a subset of the forward path's enforce set), returning a
// structured advisory result. The caller (SnapSyncHvm) marks meters and emits logs from the result.
// Extracted from SnapSyncHvm's inline block so the verdict-dispatch composition is testable with any
// vm.BTCHeaderLookup; only `lookup` differs from the production call (vm.TBCFullNode), so behavior is identical.
func observeSnapBtcDiff(ctx context.Context, lookup vm.BTCHeaderLookup, network string, genesisOffset uint64,
	headers []*wire.BlockHeader) snapObserveResult {
	var r snapObserveResult
	if len(headers) == 0 {
		return r
	}
	// (1) PoW: context-free, over all headers (hash<=target needs no ancestry). A skip sentinel (unknown
	// network) is not a PoW failure.
	if powErr := vm.CheckBTCHeaderBatchPoWForNetwork(network, headers); powErr != nil &&
		!errors.Is(powErr, vm.ErrBTCHeaderContextUnavailable) {
		r.powFailed = true
		r.powErr = powErr
	}
	// (2) contextual: split off the enforceable above-floor suffix and validate it.
	clearance, cerr := vm.BTCFloorClearanceForNetwork(network)
	if cerr != nil {
		r.clearanceErr = cerr
		return r
	}
	_, firstHeight, fhErr := lookup.BlockHeaderByHash(ctx, headers[0].BlockHash())
	if fhErr != nil {
		r.firstHeightErr = fhErr
		return r
	}
	r.firstHeight = firstHeight
	r.firstHeightMismatch = firstHeight != genesisOffset+1
	r.enforceFloor = btcSnapEnforceFloor(genesisOffset, clearance)
	enforceable, deferred := btcEnforceableSuffix(headers, firstHeight, r.enforceFloor)
	r.enforcedCount, r.deferredCount = len(enforceable), deferred
	if len(enforceable) == 0 {
		return r
	}
	verr := vm.ValidateBTCHeaderBatchForNetwork(ctx, lookup, network, genesisOffset, enforceable)
	r.contextualRan = true
	r.ctxErr = verr
	r.ctxObservation = classifySnapBtcDiffObservation(verr)
	return r
}

// classifySnapBtcDiffObservation maps a vm.ValidateBTCHeaderBatchForNetwork verdict to the observe-only
// action. Pure function so the verdict routing — which verdict trips the alert meter — is unit-testable
// without a live TBC full node (parity with the sequencer's longestEnforceableBTCHeaderPrefix seam). Any
// non-sentinel error is a RuleError => reject/alert.
func classifySnapBtcDiffObservation(verr error) snapBtcDiffObservation {
	switch {
	case verr == nil:
		return snapObsClean
	case errors.Is(verr, vm.ErrBTCBatchBelowFloor):
		return snapObsBelowFloor
	case errors.Is(verr, vm.ErrBTCBatchUnconnected), errors.Is(verr, vm.ErrBTCHeaderContextUnavailable):
		return snapObsIncomplete
	default:
		return snapObsReject
	}
}
