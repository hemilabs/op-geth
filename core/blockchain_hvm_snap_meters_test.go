// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// SnapSyncHvm's observe-only difficulty check NEVER halts (by design) — its ONLY externally-visible effect is
// marking an alert meter when a malicious/corrupt full node serves a forged snap base. That meter mark is the
// GUARDED ACTION, yet every snap-observe test asserts only the obs struct returned by observeSnapBtcDiff, never that
// the caller's dispatch actually marks the meter (the symmetric MIGRATION dispatch IS covered end-to-end). A mutant
// dropping hvmSnapBtcDiffRejectMeter.Mark / mis-mapping the switch / inverting the powFailed branch would silently
// disable the snap safety net while the whole suite stayed green. markSnapBtcDiffObservation is the extracted
// dispatch; this pins the meters fire on exactly their reject arms and stay silent on clean/skip/below-floor.

import (
	"errors"
	"testing"

	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

func TestMarkSnapBtcDiffObservation(t *testing.T) {
	bc := &BlockChain{tbcHeaderNodeConfig: &tbc.Config{Network: "localnet", GenesisHeightOffset: 0}}

	cases := []struct {
		name      string
		obs       snapObserveResult
		powDelta  int64
		diffDelta int64
	}{
		{"pow-failed", snapObserveResult{powFailed: true, powErr: errors.New("bad pow")}, 1, 0},
		{"ctx-reject", snapObserveResult{contextualRan: true, ctxObservation: snapObsReject, ctxErr: errors.New("bad diff")}, 0, 1},
		{"pow-and-ctx-reject", snapObserveResult{powFailed: true, contextualRan: true, ctxObservation: snapObsReject}, 1, 1},
		{"ctx-clean", snapObserveResult{contextualRan: true, ctxObservation: snapObsClean}, 0, 0},
		{"ctx-incomplete", snapObserveResult{contextualRan: true, ctxObservation: snapObsIncomplete, ctxErr: errors.New("gap")}, 0, 0},
		{"ctx-below-floor", snapObserveResult{contextualRan: true, ctxObservation: snapObsBelowFloor}, 0, 0},
		{"contextual-did-not-run", snapObserveResult{contextualRan: false}, 0, 0},
		{"clearance-err-skip", snapObserveResult{clearanceErr: errors.New("unknown net")}, 0, 0},
		{"first-height-err-skip", snapObserveResult{firstHeightErr: errors.New("read")}, 0, 0},
		// A reject verdict that the contextual validator NEVER RAN must not fire the btcdiff-reject meter (the meter
		// is gated on contextualRan, not merely on ctxObservation): kills a mutant dropping the contextualRan guard.
		{"ctx-reject-but-not-ran", snapObserveResult{contextualRan: false, ctxObservation: snapObsReject, ctxErr: errors.New("bad diff")}, 0, 0},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			powBefore := hvmSnapPoWRejectMeter.Snapshot().Count()
			diffBefore := hvmSnapBtcDiffRejectMeter.Snapshot().Count()
			bc.markSnapBtcDiffObservation(tc.obs, "abc123")
			require.Equal(t, tc.powDelta, hvmSnapPoWRejectMeter.Snapshot().Count()-powBefore, "PoW-reject meter delta")
			require.Equal(t, tc.diffDelta, hvmSnapBtcDiffRejectMeter.Snapshot().Count()-diffBefore, "BtcDiff-reject meter delta")
		})
	}
}
