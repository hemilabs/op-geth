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

// Full contextual Bitcoin difficulty validation.
//
// This file builds the adapters + entry point that let op-geth run btcd's contextual-header
// consensus check (difficulty retarget rules + median-time-past) against the TBC full node's
// header store. This reuses, rather than reimplements, btcd v0.24.2's CheckBlockHeaderContext,
// which it exports over the HeaderCtx/ChainCtx interfaces so external libraries can supply their
// own context. The difficulty engine (calcNextRequiredDifficulty / findPrevTestNetDifficulty)
// runs over those interfaces, so the Bitcoin math (2015-interval off-by-one, 4x clamp,
// CompactToBig/BigToCompact precision, testnet3 minimum-difficulty rule) is byte-exact vs btcd by
// construction.
//
// Placement: package vm, not eth. The same validator is reused by the eth gossip-path hook
// (handleBTCBlocks) and, later, the native-path hook wired from SetupTBCFullNode here
// in vm. Since eth/protocols/eth already imports core/vm, putting the validator in eth would
// create an import cycle at the SetupTBCFullNode wiring; vm is the single cycle-free home.
//
// Rollout status: the adapters, the pure validator, and the resolving entry point
// (ValidateBTCHeaderContext) live here. The validator is enforced on the eth gossip path
// (handleBTCBlocks): a contextual-difficulty rejection drops the header there (defense-in-depth +
// observability over the non-consensus full node). It is also enforced on the consensus-binding
// feed — the AddExternalHeaders apply path into the lightweight header node
// (ValidateBTCHeaderBatchForNetwork, floor-aware), which is the authoritative enforcement point. The
// snap-sync and sequencer-build writers run the same validator in non-halting modes (observe-only and
// build-time truncation). Because the enforced paths are reachable over the network, this file also
// carries a hard per-validation walk-hop bound (maxHeaderCtxWalkHops) that caps ancestry-lookup
// work and fails safe to skip. A per-batch base-read memoization / per-window anchor cache remains
// a deferred throughput optimization: the hop cap alone bounds work, and the lightweight consensus
// node runs with its header cache disabled so each enforced walk hits cold leveldb.

import (
	"context"
	"errors"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/hemilabs/heminetwork/service/tbc"
)

// ErrBTCHeaderContextUnavailable is returned by ValidateBTCHeaderContext when the ancestry needed
// to validate a header — its parent, or the 2015-back retarget anchor — is absent or unreadable
// from the TBC store. The caller must treat this as "skip this header" (do not insert), not as a
// difficulty rejection: on the gossip path the subsequent insert would fail anyway, and during
// initial block download the ancestry may not be there yet. It is distinct from a genuine
// contextual violation, which surfaces as some other non-nil error.
var ErrBTCHeaderContextUnavailable = errors.New("btc header context unavailable")

// headerLookup is the subset of the TBC full node used to resolve header ancestry.
// Abstracted so the adapters and validator are unit-testable against an in-memory
// fixture set without a live P2P node.
type headerLookup interface {
	BlockHeaderByHash(ctx context.Context, hash chainhash.Hash) (*wire.BlockHeader, uint64, error)
}

// The real backing store satisfies headerLookup.
var _ headerLookup = (*tbc.Server)(nil)

// tbcCtxResolver carries the shared lookup backend, request context, and the fail-closed sinks
// across the adapter tree built for one header validation. CheckBlockHeaderContext is synchronous
// and each ValidateBTCHeaderContext call builds its own resolver, so the resolver is
// single-goroutine — no locking needed.
//
// The HeaderCtx interface methods (Parent/RelativeAncestorCtx) cannot return an error, so two
// conditions that must not be silently treated as a clean result are captured here and inspected
// by the caller after the validation call:
//   - ioErr:          a non-NotFound IO error during a lookup (must not look like "header absent",
//     which could otherwise false-accept).
//   - missingAnchor:  the retarget window-start (RelativeAncestorCtx) could not be resolved; the
//     boundary difficulty cannot be computed, so the header must be skipped, not rejected as
//     wrong-difficulty.
type tbcCtxResolver struct {
	ctx    context.Context
	lookup headerLookup
	params *chaincfg.Params

	// hops counts ancestry lookups performed during this one validation; maxHops is the hard cap
	// (see maxHeaderCtxWalkHops). Once exceeded, walkExceeded latches and every further fetch
	// short-circuits — the validation then resolves to the skip sentinel. This bounds per-header
	// work to O(maxHops) store lookups on the enforced, network-reachable gossip path regardless of
	// stored-chain shape, without relying on btcd's walks being self-bounding. Overrun -> skip is
	// fail-safe: over-skipping only inflates the IBD skip count, never a false difficulty rejection.
	hops         int
	maxHops      int
	walkExceeded bool

	ioErr         error
	missingAnchor bool

	// heightInconsistent latches when a resolved ancestor's stored height is not exactly one less
	// than its child's (a round-tripping store corruption that survives fetch's IO/NotFound guards).
	// The two height-driven walks position themselves off these absolute heights: the retarget
	// anchor (RelativeAncestorCtx, off (parentHeight+1)%BlocksPerRetarget) and the testnet3
	// minimum-difficulty walk (findPrevTestNetDifficulty, off iterNode.Height()%BlocksPerRetarget) —
	// a wrong height there mis-locates the boundary / mis-stops the walk -> a wrong expected
	// difficulty. The median-time-past walk also goes through Parent(), but it is timestamp-driven
	// (median of the last medianTimeBlocks timestamps) and does not use these heights; the contiguity
	// check on its hops is harmless (it can only fail-closed-skip a height-corrupt window, never alter
	// an honest MTP). The caller maps this to the skip sentinel. Honest chains store contiguous
	// heights (each header's height = parent's + 1), so this never latches.
	heightInconsistent bool
}

// fetch resolves a header by hash, distinguishing a genuine absence (NotFound ->
// nil,false with no sink set) from an IO error (records ioErr, returns nil,false).
func (r *tbcCtxResolver) fetch(hash chainhash.Hash) (*wire.BlockHeader, uint64, bool) {
	// Hard walk-hop bound. Latch once exceeded so an in-progress btcd walk (RelativeAncestorCtx /
	// findPrevTestNetDifficulty / CalcPastMedianTime) stops cleanly and the caller maps
	// walkExceeded -> skip. maxHops <= 0 means unbounded (used only by direct unit tests that set no
	// cap).
	if r.maxHops > 0 {
		if r.walkExceeded {
			return nil, 0, false
		}
		r.hops++
		if r.hops > r.maxHops {
			r.walkExceeded = true
			return nil, 0, false
		}
	}
	hdr, height, err := r.lookup.BlockHeaderByHash(r.ctx, hash)
	if err != nil {
		// Reuse the package's canonical TBC "header not found" predicate (isTBCMissingHeader:
		// matches database.NotFoundError, not the distinct database.BlockNotFoundError or IO/context
		// errors) so this classification shares the real-error-type tripwire TestIsTBCMissingHeader
		// instead of re-deriving it. A non-NotFound error (IO/corruption/context) must fail closed:
		// record it so the caller skips rather than mistaking the header for absent. A misclassified
		// NotFound still fails closed to skip, never a false-accept.
		if !isTBCMissingHeader(err) && r.ioErr == nil {
			r.ioErr = err
		}
		return nil, 0, false
	}
	return hdr, height, true
}

// fetchContiguousParent resolves childHash (the PrevBlock of a node at childHeight) and additionally
// height-contiguity cross-checks it: a resolved parent's stored height must be exactly childHeight-1.
// This is the free per-hop hardening that every height-driven ancestry walk (retarget anchor,
// testnet3 min-difficulty, median-time-past) shares — each walk fetches a parent given its child's
// height, so the check costs nothing extra and catches a round-tripping height corruption at any hop,
// interior or endpoint. A genuine absence (NotFound at the chain floor) or IO error is left to fetch's
// existing fail-closed handling (returns !ok with no heightInconsistent set), so Parent()'s legitimate
// floor-stop is preserved. A height mismatch (or a childHeight of 0 that nonetheless resolved a parent)
// latches heightInconsistent and returns !ok, so the caller skips rather than computing a verdict.
func (r *tbcCtxResolver) fetchContiguousParent(childHash chainhash.Hash, childHeight uint64) (*wire.BlockHeader, uint64, bool) {
	phdr, pheight, ok := r.fetch(childHash)
	if !ok {
		return nil, 0, false
	}
	if childHeight == 0 || pheight != childHeight-1 {
		r.heightInconsistent = true
		return nil, 0, false
	}
	return phdr, pheight, true
}

// tbcHeaderCtx adapts a Bitcoin header (+ its TBC height) to btcd's HeaderCtx,
// lazily resolving ancestry through the shared resolver.
type tbcHeaderCtx struct {
	hdr    *wire.BlockHeader
	height uint64
	res    *tbcCtxResolver
}

func (h *tbcHeaderCtx) Height() int32    { return int32(h.height) } // Bitcoin heights fit int32
func (h *tbcHeaderCtx) Bits() uint32     { return h.hdr.Bits }
func (h *tbcHeaderCtx) Timestamp() int64 { return h.hdr.Timestamp.Unix() }

// Parent returns the header's parent, or an untyped interface-nil when genuinely absent (the chain
// floor, where btcd's MTP / min-difficulty walks legitimately stop) or when a lookup IO error was
// recorded (fail-closed via the resolver sink). Returning a typed (*tbcHeaderCtx)(nil) here would be
// != nil as an interface and would defeat btcd's `iterNode != nil` loop guards, then panic on the
// next method call — so this must return a bare nil from an interface-typed function.
func (h *tbcHeaderCtx) Parent() blockchain.HeaderCtx {
	// fetchContiguousParent: besides absence/IO (the legitimate floor-stop / fail-closed skip), this
	// rejects a parent whose stored height != h.height-1, closing the height-corruption hole on the
	// height-driven Parent() walk: the testnet3 minimum-difficulty findPrevTestNetDifficulty walk,
	// which uses iterNode.Height()%BlocksPerRetarget as a stop condition. The median-time-past walk
	// also uses Parent() but is timestamp-driven, so the check is harmless there.
	phdr, pheight, ok := h.res.fetchContiguousParent(h.hdr.PrevBlock, h.height)
	if !ok {
		return nil
	}
	return &tbcHeaderCtx{hdr: phdr, height: pheight, res: h.res}
}

// RelativeAncestorCtx returns the ancestor `distance` blocks back, resolved by walking this header's
// own PrevBlock chain (ancestry-exact, reproducing btcd's blockNode.RelativeAncestor). It must not be
// resolved via a height index: that returns every fork's header at the height with no ancestry marker,
// so the wrong same-height header could be chosen under a reorg and corrupt the retarget timespan.
//
// On any missing or unreadable hop it returns interface-nil and marks the resolver's missingAnchor
// sink. btcd's calcNextRequiredDifficulty turns a nil here into an AssertError; either way the caller
// converts it to ErrBTCHeaderContextUnavailable (skip) rather than a difficulty rejection. The walk is
// inherently bounded: it is only ever called with distance == BlocksPerRetarget()-1 (2015) at a
// retarget boundary, one walk per boundary block.
func (h *tbcHeaderCtx) RelativeAncestorCtx(distance int32) blockchain.HeaderCtx {
	if distance <= 0 {
		// btcd only calls this with BlocksPerRetarget()-1 > 0; defensive.
		h.res.missingAnchor = true
		return nil
	}
	cursor := h.hdr
	height := h.height
	for i := int32(0); i < distance; i++ {
		// Per-hop fetchContiguousParent: each hop verifies the parent's stored height == this node's
		// height-1, so a round-tripping height corruption at any hop, interior or endpoint, fails closed
		// to the missing-anchor skip — never a retarget boundary/difficulty computed from a
		// height-inconsistent window.
		phdr, pheight, ok := h.res.fetchContiguousParent(cursor.PrevBlock, height)
		if !ok {
			h.res.missingAnchor = true
			return nil
		}
		cursor, height = phdr, pheight
	}
	return &tbcHeaderCtx{hdr: cursor, height: height, res: h.res}
}

// tbcChainCtx adapts the active Bitcoin chain params to btcd's ChainCtx. The retarget constants are
// derived from the params (no hardcoded interval) and are numerically equivalent to btcd's New()
// derivation for every reachable network: BlocksPerRetarget uses a Duration/Duration ratio rather
// than btcd's seconds-first form, which yields the identical 2016 for all params whose timespans are
// whole-second multiples (mainnet/testnet3/regtest all are).
type tbcChainCtx struct {
	params *chaincfg.Params
}

func (c *tbcChainCtx) ChainParams() *chaincfg.Params { return c.params }

func (c *tbcChainCtx) BlocksPerRetarget() int32 {
	return int32(c.params.TargetTimespan / c.params.TargetTimePerBlock)
}

func (c *tbcChainCtx) MinRetargetTimespan() int64 {
	return int64(c.params.TargetTimespan/time.Second) / c.params.RetargetAdjustmentFactor
}

func (c *tbcChainCtx) MaxRetargetTimespan() int64 {
	return int64(c.params.TargetTimespan/time.Second) * c.params.RetargetAdjustmentFactor
}

// VerifyCheckpoint / FindPreviousCheckpoint are stubbed because we always call
// CheckBlockHeaderContext with skipCheckpoint=true: TBC has no btcd checkpoint table and no
// pre-checkpoint history; checkpoints add zero cumulative-work impact and are a false-positive source.
func (c *tbcChainCtx) VerifyCheckpoint(height int32, hash *chainhash.Hash) bool { return true }
func (c *tbcChainCtx) FindPreviousCheckpoint() (blockchain.HeaderCtx, error)    { return nil, nil }

// Compile-time interface conformance. These also fail the build if a btcd downgrade
// drops the HeaderCtx/ChainCtx surface the reuse approach depends on.
var (
	_ blockchain.HeaderCtx = (*tbcHeaderCtx)(nil)
	_ blockchain.ChainCtx  = (*tbcChainCtx)(nil)
)

// checkBTCHeaderContext runs btcd's contextual header validation (difficulty + MTP + block version,
// skipping checkpoints) against an injected parent and chain context. Pure with respect to its inputs;
// unit tests pass fixtures directly. It does not resolve ancestry or interpret the resolver sinks; the
// caller does.
func checkBTCHeaderContext(hdr *wire.BlockHeader, prevCtx blockchain.HeaderCtx, chainCtx blockchain.ChainCtx) error {
	return blockchain.CheckBlockHeaderContext(hdr, prevCtx, blockchain.BFNone, chainCtx, true /*skipCheckpoint*/)
}

// validateBTCHeaderContextWith validates that hdr carries the contextually-correct
// difficulty and a valid median-time-past, resolving ancestry through the supplied
// lookup and params. Split out from ValidateBTCHeaderContext so tests can inject a
// fixture lookup and params.
//
// Returns (callers should branch with errors.Is on the sentinel, not a concrete-type switch):
//   - nil:                              hdr is contextually valid (accept).
//   - ErrBTCHeaderContextUnavailable:   parent / retarget anchor absent or unreadable, or the
//     ancestry walk hit the hard hop bound (skip, not a rejection). A genuinely-missing retarget
//     anchor surfaces inside CheckBlockHeaderContext as a btcd AssertError, but res.missingAnchor
//     (and likewise res.walkExceeded) reclassifies it to this sentinel below, so callers never see
//     the AssertError.
//   - any other non-nil error:          a genuine contextual violation — in practice always a
//     blockchain.RuleError (ErrUnexpectedDifficulty / ErrTimeTooOld / ErrBlockVersionTooOld) — reject.
func validateBTCHeaderContextWith(ctx context.Context, lookup headerLookup, params *chaincfg.Params, hdr *wire.BlockHeader) error {
	if lookup == nil || params == nil || hdr == nil {
		return ErrBTCHeaderContextUnavailable
	}
	res := &tbcCtxResolver{ctx: ctx, lookup: lookup, params: params, maxHops: maxHeaderCtxWalkHops(params)}

	// Pre-resolve the immediate parent. CheckBlockHeaderContext dereferences prevNode
	// (Height, CalcPastMedianTime) with no nil-guard, so we must not call it when the
	// parent is absent/unreadable.
	phdr, pheight, ok := res.fetch(hdr.PrevBlock)
	if !ok {
		return ErrBTCHeaderContextUnavailable
	}
	prevCtx := &tbcHeaderCtx{hdr: phdr, height: pheight, res: res}
	chainCtx := &tbcChainCtx{params: params}

	err := checkBTCHeaderContext(hdr, prevCtx, chainCtx)

	// A non-NotFound IO error, a genuinely missing retarget anchor, or a walk that hit the hard hop
	// bound was swallowed by the error-less HeaderCtx interface during the in-call ancestry walks (MTP
	// / findPrevTestNetDifficulty / RelativeAncestorCtx). Surface any of them as skip, overriding
	// whatever CheckBlockHeaderContext returned, so none can manifest as a false accept (ioErr) or a
	// spurious difficulty rejection (missingAnchor / walkExceeded).
	if res.ioErr != nil || res.missingAnchor || res.walkExceeded || res.heightInconsistent {
		return ErrBTCHeaderContextUnavailable
	}
	return err
}

// maxHeaderCtxWalkHops bounds the total ancestry lookups one header validation may perform,
// converting any overrun into the skip sentinel (never a false reject; see fetch/walkExceeded). A
// legitimate validation does at most one retarget walk of BlocksPerRetarget()-1 hops (or a testnet3
// minimum-difficulty walk of comparable length, mutually exclusive with it), plus an ~11-block
// median-time-past walk, plus the parent pre-resolve — roughly BlocksPerRetarget() + 12. We cap at 2x
// that span plus a fixed margin: high enough that honest boundary headers never trip it (the differential-replay
// real-chain retarget vectors do ~2015-hop walks and stay well under), low enough that a corrupt or
// pathological stored chain shape cannot drive an unbounded walk on the enforced, network-reachable
// path. Derived from params (not hardcoded) so it tracks any network whose retarget interval differs.
func maxHeaderCtxWalkHops(params *chaincfg.Params) int {
	return 2*blocksPerRetarget(params) + 256
}

// blocksPerRetarget derives the retarget interval (2016 for every real network) from params,
// with a defensive floor so it never returns < a real walk. Shared by maxHeaderCtxWalkHops and the
// contextual-difficulty floor-clearance (floorClearance) so both track the same value.
func blocksPerRetarget(params *chaincfg.Params) int {
	bpr := int(params.TargetTimespan / params.TargetTimePerBlock)
	if bpr < 1 {
		bpr = 2016 // defensive: every real network derives 2016; never cap below a real walk
	}
	return bpr
}

// ValidateBTCHeaderContext is the single contextual-difficulty entry reused by the gossip-path hook
// (eth handleBTCBlocks) and, later, the native-path hook. It validates
// hdr against the live TBC full node's header store. See validateBTCHeaderContextWith for the return
// contract.
func ValidateBTCHeaderContext(hdr *wire.BlockHeader) error {
	if TBCFullNode == nil || tbcChainParams == nil {
		return ErrBTCHeaderContextUnavailable
	}
	return validateBTCHeaderContextWith(MainCtx, TBCFullNode, tbcChainParams, hdr)
}
