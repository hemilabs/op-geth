// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Unit tests for the pure loader-control-flow helpers (no live TBC node):
//   - longestEnforceableBTCHeaderPrefix: the sequencer build-path truncation logic.
//   - btcEnforceableSuffix:              the snap-sync enforce/defer split.
// The contextual-difficulty validator itself is exercised against a real lightweight node in
// blockchain_hvm_btcdiff_test.go and core/vm; these tests pin the control flow that wraps it.

import (
	"errors"
	"fmt"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/stretchr/testify/require"
)

// TestClassifySnapBtcDiffObservation pins the snap-sync observe-only verdict routing: only a RuleError
// (snapObsReject) is the alertable arm (the one SnapSyncHvm marks on the meter), and the
// benign/incomplete verdicts never reach it. Pure seam for the otherwise-inline snap dispatch (no live
// TBC node). A wrapped sentinel must still classify correctly.
func TestClassifySnapBtcDiffObservation(t *testing.T) {
	require.Equal(t, snapObsClean, classifySnapBtcDiffObservation(nil))
	require.Equal(t, snapObsBelowFloor, classifySnapBtcDiffObservation(vm.ErrBTCBatchBelowFloor))
	require.Equal(t, snapObsIncomplete, classifySnapBtcDiffObservation(vm.ErrBTCBatchUnconnected))
	require.Equal(t, snapObsIncomplete, classifySnapBtcDiffObservation(vm.ErrBTCHeaderContextUnavailable))
	// Any non-sentinel error is a btcd RuleError -> the alertable arm.
	require.Equal(t, snapObsReject, classifySnapBtcDiffObservation(errors.New("simulated btcd RuleError")))
	// Wrapped sentinels must still route by identity, not collapse to reject.
	require.Equal(t, snapObsBelowFloor, classifySnapBtcDiffObservation(fmt.Errorf("ctx: %w", vm.ErrBTCBatchBelowFloor)))
	require.Equal(t, snapObsIncomplete, classifySnapBtcDiffObservation(fmt.Errorf("ctx: %w", vm.ErrBTCHeaderContextUnavailable)))
	require.Equal(t, snapObsReject, classifySnapBtcDiffObservation(fmt.Errorf("ctx: %w", errors.New("rule"))))
}

// mkHeaders returns n distinct (non-nil) header pointers. The pure helpers never dereference header
// contents, so empty headers are sufficient to test the control flow.
func mkHeaders(n int) []*wire.BlockHeader {
	hs := make([]*wire.BlockHeader, n)
	for i := range hs {
		hs[i] = &wire.BlockHeader{}
	}
	return hs
}

func TestLongestEnforceableBTCHeaderPrefix(t *testing.T) {
	ruleErr := errors.New("simulated btcd RuleError")

	// rejectFromIndex models a contiguous chain whose first contextually-invalid header is at index k: the
	// apply path's whole-batch gate rejects any prefix that includes index k (len > k). A header's
	// validity is prefix-monotonic, so this matches the real validator's shape.
	rejectFromIndex := func(k int) btcHeaderBatchClassifier {
		return func(headers []*wire.BlockHeader) error {
			if len(headers) > k {
				return ruleErr
			}
			return nil
		}
	}

	t.Run("all valid returns full slice", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, rejectFromIndex(8))
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 8)
	})

	t.Run("first header invalid returns empty prefix", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, rejectFromIndex(0))
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 0)
	})

	t.Run("middle invalid truncates to prefix before it", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, rejectFromIndex(3))
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 3)
		// The returned prefix must be the leading sub-slice (alias the same backing pointers).
		require.Same(t, in[0], got[0])
		require.Same(t, in[2], got[2])
	})

	t.Run("last header invalid keeps all but the last", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, rejectFromIndex(7))
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 7)
	})

	t.Run("below-floor is acceptable (no truncation)", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, func([]*wire.BlockHeader) error {
			return vm.ErrBTCBatchBelowFloor
		})
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 8, "below-floor means the apply path DEFERS, so keep all headers")
	})

	t.Run("unconnected is acceptable (no truncation)", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, func([]*wire.BlockHeader) error {
			return vm.ErrBTCBatchUnconnected
		})
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 8, "unconnected is preserved for AddExternalHeaders to decide, not truncated")
	})

	t.Run("context-unavailable signals skip, never truncates", func(t *testing.T) {
		in := mkHeaders(8)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, func([]*wire.BlockHeader) error {
			return vm.ErrBTCHeaderContextUnavailable
		})
		require.True(t, skip)
		require.ErrorIs(t, err, vm.ErrBTCHeaderContextUnavailable)
		require.Nil(t, got, "a transient read must not silently drop honest headers")
	})

	t.Run("empty input returns empty", func(t *testing.T) {
		got, skip, err := longestEnforceableBTCHeaderPrefix(nil, rejectFromIndex(0))
		require.NoError(t, err)
		require.False(t, skip)
		require.Len(t, got, 0)
	})

	// A context-unavailable verdict that only appears once the prefix has shrunk past the reject point
	// must still abort (skip), never silently accept a shorter prefix. (Defends the dominance of the
	// recoverable check over truncation across iterations.)
	t.Run("late context-unavailable still skips", func(t *testing.T) {
		in := mkHeaders(5)
		got, skip, err := longestEnforceableBTCHeaderPrefix(in, func(headers []*wire.BlockHeader) error {
			switch len(headers) {
			case 5, 4, 3:
				return errors.New("rule error")
			default:
				return vm.ErrBTCHeaderContextUnavailable
			}
		})
		require.True(t, skip)
		require.ErrorIs(t, err, vm.ErrBTCHeaderContextUnavailable)
		require.Nil(t, got)
	})
}

func TestBtcEnforceableSuffix(t *testing.T) {
	t.Run("empty input", func(t *testing.T) {
		suffix, deferred := btcEnforceableSuffix(nil, 100, 200)
		require.Nil(t, suffix)
		require.Equal(t, 0, deferred)
	})

	t.Run("entire chain at or above floor is fully enforced (firstHeight == enforceFloor)", func(t *testing.T) {
		in := mkHeaders(10)
		suffix, deferred := btcEnforceableSuffix(in, 1000, 1000)
		require.Len(t, suffix, 10)
		require.Equal(t, 0, deferred)
		require.Same(t, in[0], suffix[0])
	})

	t.Run("firstHeight STRICTLY above enforceFloor enforces all (underflow guard)", func(t *testing.T) {
		// firstHeight > enforceFloor exercises the `firstHeight >= enforceFloor` guard's strictly-greater
		// case. Without it (e.g. a `>=`->`==` mutant), c = enforceFloor-firstHeight underflows in uint64 to
		// a huge value -> c >= len -> the whole chain is WRONGLY deferred instead of fully enforced.
		in := mkHeaders(10) // heights 2000..2009, enforceFloor 1000 => all strictly above
		suffix, deferred := btcEnforceableSuffix(in, 2000, 1000)
		require.Len(t, suffix, 10, "a chain wholly above the enforce floor must be fully enforced, not deferred")
		require.Equal(t, 0, deferred)
		require.Same(t, in[0], suffix[0])
	})

	t.Run("entire chain below floor is fully deferred", func(t *testing.T) {
		in := mkHeaders(10) // heights 100..109, enforceFloor 200 => all deferred
		suffix, deferred := btcEnforceableSuffix(in, 100, 200)
		require.Nil(t, suffix)
		require.Equal(t, 10, deferred)
	})

	t.Run("split in the middle defers the prefix, enforces the suffix", func(t *testing.T) {
		in := mkHeaders(10) // heights 100..109
		// enforceFloor 105 => indices 0..4 (heights 100..104) deferred, indices 5..9 enforced.
		suffix, deferred := btcEnforceableSuffix(in, 100, 105)
		require.Equal(t, 5, deferred)
		require.Len(t, suffix, 5)
		require.Same(t, in[5], suffix[0])
		require.Same(t, in[9], suffix[4])
	})

	t.Run("first enforceable height exactly at the boundary", func(t *testing.T) {
		in := mkHeaders(4) // heights 50..53
		// enforceFloor 53 => only the last header (height 53) enforced.
		suffix, deferred := btcEnforceableSuffix(in, 50, 53)
		require.Equal(t, 3, deferred)
		require.Len(t, suffix, 1)
		require.Same(t, in[3], suffix[0])
	})

	t.Run("c exactly equals len defers the whole chain", func(t *testing.T) {
		in := mkHeaders(10) // heights 100..109; enforceFloor 110 => c = 10 == len => all deferred
		suffix, deferred := btcEnforceableSuffix(in, 100, 110)
		require.Nil(t, suffix)
		require.Equal(t, 10, deferred)
	})

	t.Run("c just below len enforces exactly the last header", func(t *testing.T) {
		in := mkHeaders(10) // heights 100..109; enforceFloor 109 => c = 9 => enforce only index 9
		suffix, deferred := btcEnforceableSuffix(in, 100, 109)
		require.Equal(t, 9, deferred)
		require.Len(t, suffix, 1)
		require.Same(t, in[9], suffix[0])
	})
}

// TestSnapEnforceFloorAboveValidatorGate pins the snap-sync alignment invariant. Snap-sync is
// observe-only for contextual-difficulty (never halts — see SnapSyncHvm), so this keeps the snap-base alert meaningful
// and low-noise: the snap enforce floor (GenesisHeightOffset + clearance + (MaximumBtcHeadersInTx-1))
// must sit above the validator's own defer gate (GenesisHeightOffset + clearance) and above the highest
// header any forward batch could defer, so the observed band is exactly the band the forward apply path
// enforces. If a future change lowered the floor below the gate, btcEnforceableSuffix would hand the
// validator a suffix it reports ErrBTCBatchBelowFloor for, and the observation would go quiet. Cheap
// structural guard; real-node enforce/defer behavior at the gate is covered by
// TestHvmBtcDiffFloorAwareAgainstRealLightweightNode.
func TestSnapEnforceFloorAboveValidatorGate(t *testing.T) {
	const maxBatch = uint64(types.MaximumBtcHeadersInTx)
	require.Greater(t, maxBatch, uint64(1), "the (maxBatch-1) margin is only meaningful for batches > 1 header")

	for _, network := range []string{"mainnet", "testnet3", "upgradetest", "localnet"} {
		clearance, err := vm.BTCFloorClearanceForNetwork(network)
		require.NoError(t, err)
		const floor = uint64(3488421) // an arbitrary non-zero effective-genesis offset

		// Drive the production helper (not a re-derived copy), so a mutation in btcSnapEnforceFloor — the
		// single definition SnapSyncHvm uses — is caught here.
		enforceFloor := btcSnapEnforceFloor(floor, clearance)

		// (1) The lowest observed height must not fall in the validator's defer band [floor,
		// floor+clearance), else the suffix would be reported ErrBTCBatchBelowFloor and the alert would go
		// quiet. A mutant dropping the +clearance term (e.g. enforceFloor = floor + (maxBatch-1)) fails this
		// on every network whose clearance > (maxBatch-1) — true for all (clearance in the thousands >> 29).
		require.Greaterf(t, enforceFloor, floor+clearance,
			"network %q: enforce floor must be strictly above the validator defer gate, else the snap alert goes silent", network)
		// (2) It must be strictly above the highest header any forward-deferred batch can contain
		// (floor+clearance+(maxBatch-2)), so snap's enforce set is a strict subset of the forward path's. A
		// mutant that dropped or shrank the (maxBatch-1) split-safety margin fails this.
		require.Greaterf(t, enforceFloor, floor+clearance+(maxBatch-2),
			"network %q: enforce floor must clear the highest forward-deferrable header (split-safety)", network)
		// (3) And it must be EXACTLY one above that highest forward-deferred header — not needlessly higher
		// (which would deepen the unenforced band). Pins the precise constant.
		require.Equalf(t, floor+clearance+(maxBatch-1), enforceFloor,
			"network %q: enforce floor must be exactly floor+clearance+(maxBatch-1)", network)
	}
}
