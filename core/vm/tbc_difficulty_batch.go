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

// Contextual-difficulty validation for a connected batch of Bitcoin headers on the hVM
// consensus path (the lightweight header node fed by BtcAttributesDeposited txs via
// AddExternalHeaders). It reuses the single-header validator over an intra-batch overlay so headers
// 2..N resolve their not-yet-committed parents.
//
// Floor-awareness is the load-bearing correctness property: the lightweight node is seeded from an
// effective-genesis floor (HvmGenesisHeight), not Bitcoin height 0, so the deep ancestry contextual
// difficulty needs (a ~BlocksPerRetarget-back retarget anchor and a ~medianTimeBlocks-back MTP
// window) are absent for headers near the floor. Validating such a header would either spuriously
// skip (retarget) or — worse, on testnet3 — let btcd's truncated findPrevTestNetDifficulty fabricate
// PowLimitBits as the expected difficulty and false-reject an honest block. So this defers (does not
// enforce) any batch whose lowest header is within floorClearance of the floor; above that, every
// required walk provably stays above the floor.
//
// Distinct outcomes (the caller maps each to consensus semantics):
//   - nil:                            enforced and every header is contextually valid -> commit.
//   - ErrBTCBatchBelowFloor:          near-floor, unverifiable by construction -> defer (commit via
//     AddExternalHeaders, relying on its cumulative-work + the canonical-tip check; bounded window).
//   - ErrBTCBatchUnconnected:         a header's parent is genuinely absent -> the batch does not
//     connect to committed state -> invalid block (preserves pre-enforcement behavior).
//   - ErrBTCHeaderContextUnavailable: an IO/corrupt read while resolving ancestry -> recoverable
//     corrupt state (transient; never a silent accept, never a false bad-block).
//   - a btcd RuleError:               a genuine contextual violation -> reject the block.

import (
	"context"
	"errors"

	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
)

// medianTimeBlocks mirrors btcd's unexported blockchain.medianTimeBlocks (the MTP window length).
const medianTimeBlocks = 11

var (
	// ErrBTCBatchUnconnected: a header's parent is genuinely NotFound in both the in-batch set and
	// the committed store — the batch does not extend committed consensus state. The caller treats
	// this as an invalid block (the pre-difficulty-enforcement AddExternalHeaders behavior), not as corrupt state.
	ErrBTCBatchUnconnected = errors.New("btc header batch does not connect to committed state")

	// ErrBTCBatchBelowFloor: a batch header's required contextual-difficulty walk would cross below
	// the effective-genesis floor, so it is unverifiable by construction on this node. The caller
	// defers enforcement (commits via AddExternalHeaders, whose cumulative-work + canonical-tip
	// checks still apply) rather than false-rejecting or crit-looping. Bounded to the floor-clearance
	// band above the effective genesis (re-enterable only by a reorg back below floor+clearance).
	ErrBTCBatchBelowFloor = errors.New("btc header batch below contextual-difficulty floor")
)

// BTCHeaderLookup is the exported header-store interface the batch validator resolves against. Both
// the full node and the lightweight hVM header node (*tbc.Server) satisfy it; the consensus caller
// passes the lightweight node.
type BTCHeaderLookup = headerLookup

// batchEntry is an in-batch header with its positionally-assigned height.
type batchEntry struct {
	hdr    *wire.BlockHeader
	height uint64
}

type batchResolveStatus int

const (
	resolveFound    batchResolveStatus = iota // header present (in batch or committed store)
	resolveNotFound                           // genuinely absent (NotFound) -> non-connecting
	resolveIOErr                              // non-NotFound IO/context error -> transient/corrupt
)

// btcBatchOverlay resolves not-yet-committed batch headers first (by hash, with heights assigned
// from the committed anchor), then falls back to the committed base store. Read-only over the base,
// single-goroutine (one validation call).
type btcBatchOverlay struct {
	base BTCHeaderLookup
	in   map[chainhash.Hash]batchEntry
}

// BlockHeaderByHash satisfies headerLookup so the reused validator's resolver walks across the
// batch->committed seam transparently.
func (o *btcBatchOverlay) BlockHeaderByHash(ctx context.Context, hash chainhash.Hash) (*wire.BlockHeader, uint64, error) {
	if e, ok := o.in[hash]; ok {
		return e.hdr, e.height, nil
	}
	return o.base.BlockHeaderByHash(ctx, hash)
}

var _ headerLookup = (*btcBatchOverlay)(nil)

// resolve classifies a lookup as found / genuinely-absent / IO-error (reusing the package's
// canonical isTBCMissingHeader predicate), so the caller can distinguish a non-connecting batch
// (reject) from a transient/corrupt read (skip).
func (o *btcBatchOverlay) resolve(ctx context.Context, hash chainhash.Hash) (*wire.BlockHeader, uint64, batchResolveStatus) {
	if e, ok := o.in[hash]; ok {
		return e.hdr, e.height, resolveFound
	}
	hdr, height, err := o.base.BlockHeaderByHash(ctx, hash)
	if err != nil {
		if isTBCMissingHeader(err) {
			return nil, 0, resolveNotFound
		}
		return nil, 0, resolveIOErr
	}
	return hdr, height, resolveFound
}

// ValidateBTCHeaderBatchForNetwork validates the batch against the chain params for the given TBC
// network name (the consensus caller passes the lightweight node's own configured network, so it
// does not depend on the full-node global tbcChainParams). floorHeight is the node's
// effective-genesis height (GenesisHeightOffset). An unknown network fails closed to the skip
// sentinel (recoverable, never a silent accept). validateBTCHeaderBatchWith is split out so tests
// inject params + floor directly (mirroring the ValidateBTCHeaderContext split).
func ValidateBTCHeaderBatchForNetwork(ctx context.Context, base BTCHeaderLookup, network string, floorHeight uint64, headers []*wire.BlockHeader) error {
	params, err := paramsForNetwork(network)
	if err != nil {
		return ErrBTCHeaderContextUnavailable
	}
	return validateBTCHeaderBatchWith(ctx, base, params, floorHeight, headers)
}

func validateBTCHeaderBatchWith(ctx context.Context, base BTCHeaderLookup, params *chaincfg.Params, floorHeight uint64, headers []*wire.BlockHeader) error {
	if base == nil || params == nil {
		return ErrBTCHeaderContextUnavailable
	}
	if len(headers) == 0 {
		return nil
	}

	overlay := &btcBatchOverlay{base: base, in: make(map[chainhash.Hash]batchEntry, len(headers))}

	// Anchor + height-assign each header (parent in overlay-so-far or committed base). Classify a
	// missing parent: genuinely-absent -> the batch does not connect to committed state (reject);
	// IO error -> transient/corrupt (skip). Track the lowest assigned height for the floor gate.
	minHeight := ^uint64(0)
	for _, h := range headers {
		if h == nil {
			// Defensive: unflattenBTCHeaders never yields a nil header, but this validator is exported.
			// Fail closed to skip (recoverable), never a false reject or a nil-deref panic.
			return ErrBTCHeaderContextUnavailable
		}
		phdr, pheight, st := overlay.resolve(ctx, h.PrevBlock)
		switch st {
		case resolveFound:
			_ = phdr
			height := pheight + 1
			overlay.in[h.BlockHash()] = batchEntry{hdr: h, height: height}
			if height < minHeight {
				minHeight = height
			}
		case resolveNotFound:
			return ErrBTCBatchUnconnected
		default: // resolveIOErr
			return ErrBTCHeaderContextUnavailable
		}
	}

	// Floor gate: if the lowest header is within floorClearance of the effective-genesis floor, its
	// required ancestry walks could cross below the floor (where the chain is absent), so the batch is
	// unverifiable by construction -> defer (do not enforce). Above the clearance, every walk provably
	// stays above the floor and enforcement is exact.
	if minHeight < floorHeight+floorClearance(params) {
		return ErrBTCBatchBelowFloor
	}

	// Validate each header against the overlay using the exact single-header validator (hop bound, MTP,
	// retarget math, skip/reject contract carry over). With the floor gate satisfied, no walk crosses
	// the floor, so a skip here can only be a genuine IO/corrupt read. Reject dominates skip.
	var firstReject error
	sawSkip := false
	for _, h := range headers {
		switch err := validateBTCHeaderContextWith(ctx, overlay, params, h); {
		case err == nil:
			// accept this header
		case errors.Is(err, ErrBTCHeaderContextUnavailable):
			sawSkip = true
		default:
			if firstReject == nil {
				firstReject = err // a genuine RuleError
			}
		}
	}
	if firstReject != nil {
		return firstReject
	}
	if sawSkip {
		return ErrBTCHeaderContextUnavailable
	}
	return nil
}

// floorClearance is the minimum height above the effective-genesis floor at which a header's
// contextual-difficulty walks are guaranteed to stay at/above the floor (so the batch is enforceable
// rather than deferred). The three walks btcd's CheckBlockHeaderContext drives for a header validated
// at child-height H (parent lastNode at H-1) are parallel, not additive — all rooted at lastNode:
//   - retarget anchor (boundary only): RelativeAncestor(BlocksPerRetarget-1) from H-1 -> reads H-BlocksPerRetarget
//   - testnet3 min-difficulty walk: stops at the prior boundary (tests Height%BlocksPerRetarget before
//     Parent()), depth <= BlocksPerRetarget-1 from H-1 -> reads >= H-BlocksPerRetarget (never deeper)
//   - MTP window: medianTimeBlocks back from H-1 -> reads H-medianTimeBlocks (much shallower)
//
// so the single deepest read is H-BlocksPerRetarget. The exact minimal-presence clearance is therefore
// BlocksPerRetarget (at clearance==BlocksPerRetarget the lowest enforced header H=floor+BlocksPerRetarget
// reads its anchor at exactly floorHeight, the seeded+trusted effective-genesis checkpoint — present).
// We add medianTimeBlocks as a conservative margin: the failure mode of a too-small clearance is a walk
// crossing below the floor -> a NotFound -> the missing-context skip (ErrBTCHeaderContextUnavailable,
// which the apply path maps to recoverable corrupt/restore), not a false reject; the +medianTimeBlocks
// guards against any off-by-<=medianTimeBlocks error in the depth analysis so honest near-floor headers
// never skip.
//
// This was 2*BlocksPerRetarget+medianTimeBlocks — a ~2x over-margin that needlessly deferred the upper
// ~BlocksPerRetarget of the band (headers whose anchors are present at/above the floor), leaving their
// contextual difficulty unverified. Shrinking to BlocksPerRetarget+medianTimeBlocks brings that ~50% of
// the band under real enforcement; it does not close the irreducible band [floor, floor+BlocksPerRetarget)
// whose anchors are genuinely pre-checkpoint/absent (the load-bearing near-floor defer band). Because this
// changes which headers the validator accepts, it must be deployed consistently across the fleet
// (transparent on honest history).
func floorClearance(params *chaincfg.Params) uint64 {
	return uint64(blocksPerRetarget(params) + medianTimeBlocks)
}

// BTCFloorClearanceForNetwork exposes floorClearance for the given TBC network name so the
// consensus-path bulk loaders (snap-sync reconstruction) can compute, in package core, the absolute
// BTC height band above the effective-genesis floor in which contextual difficulty is enforceable.
// Below floorHeight+clearance a header's required ancestry walk would cross below the floor and is
// unverifiable by construction (exactly the band validateBTCHeaderBatchWith defers). An unknown
// network returns an error (the caller fails closed, never silently enforces with wrong params).
func BTCFloorClearanceForNetwork(network string) (uint64, error) {
	params, err := paramsForNetwork(network)
	if err != nil {
		return 0, err
	}
	return floorClearance(params), nil
}
