// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// The operator-facing canonical-tip-mismatch DIAGNOSTIC (blockchain.go ~2952). The dishonest-claim tests pin the
// returned error class (ErrInvalidHVMHeaders), but the descriptive log message — which reports the headers added and
// the divergence between the CLAIMED and the ACTUAL computed tip, and is the primary signal an operator/tooling sees
// when a BtcAttr tx commits the wrong tip — lives only in the log, untested. A refactor that drops or garbles it
// would leave the rejection silent-but-cryptic. Corpus-free (regtest); captures the root logger for the apply only.

import (
	"bytes"
	"log/slog"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/log"
	"github.com/stretchr/testify/require"
)

func TestHvmCanonicalTipMismatchLogMessage(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)
	a1 := *mineRegtestChild(t, p, 100) // the header actually added -> becomes the real canonical tip
	d := *mineRegtestChild(t, p, 777)  // a distinct sibling; its hash is the WRONG claimed tip
	require.NotEqual(t, a1.BlockHash(), d.BlockHash(), "the claimed tip must differ from the produced tip")

	// Capture the root logger for the duration of the apply only (harness setup above logs to the real logger).
	var buf bytes.Buffer
	prev := log.Root()
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(&buf, slog.LevelDebug, false)))
	err := applyForkBtcAttr(t, chain, 11, d, []wire.BlockHeader{a1}, true)
	log.SetDefault(prev) // restore before asserting

	require.ErrorIs(t, err, consensus.ErrInvalidHVMHeaders,
		"a claim naming a tip other than the one produced by adding the headers must be rejected")
	out := buf.String()
	require.Contains(t, out, "claims that after adding",
		"the operator-facing canonical-tip-mismatch diagnostic must be emitted")
	require.Contains(t, out, "but after adding the headers to TBC the canonical tip is",
		"the diagnostic must report the actual computed tip vs the claimed one")
}
