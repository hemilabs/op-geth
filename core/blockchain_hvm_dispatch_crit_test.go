// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// The updateHvmHeaderConsensus dispatcher's UNRECOGNIZED-error backstop (the single-block-apply arm, ~blockchain.go
// 4477): when applyHvmHeaderConsensusUpdate returns an error that is NOT one of the three handled sentinels
// (ErrInvalidHVMBlockFormat / ErrInvalidHVMHeaders / ErrCorruptHVMHeaderOnlyModeState), the dispatcher log.Crits
// ("Encountered an error applying hVM header state transition") rather than silently swallowing a torn-write. Reached
// here via a direct-child block whose BODY is absent from disk+pen (apply returns the plain "unable to get block"
// error). Downgrading the crit to log.Warn+return-nil would keep the suite green; log.Crit can't be caught in-process,
// hence the re-exec.

import (
	"math/big"
	"os"
	"os/exec"
	"testing"

	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/stretchr/testify/require"
)

const hvmDispatchUnrecognizedCritChildEnv = "HVM_DISPATCH_UNRECOGNIZED_ERR_CHILD"

func TestUpdateHvmHeaderConsensusUnrecognizedErrorCritChild(t *testing.T) {
	if os.Getenv(hvmDispatchUnrecognizedCritChildEnv) == "" {
		t.Skip("child-only: driven by TestUpdateHvmHeaderConsensusUnrecognizedErrorCrit via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	// currentHead P (activation block @11). Apply it -> state-id = P. P is also written to rawdb so the dispatcher's
	// findCommonAncestor (rawdb-only GetHeader) can resolve it.
	preP := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	p := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preP.Hash()})
	chain.tempHeaders[preP.Hash().String()] = preP
	chain.tempBlocks[preP.Hash().String()] = types.NewBlockWithHeader(preP)
	chain.tempHeaders[p.Hash().String()] = p.Header()
	chain.tempBlocks[p.Hash().String()] = p
	rawdb.WriteBlock(chain.db, p)
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(p.Header(), false, false))

	// newHead T: a DIRECT CHILD of P (so the single-apply arm runs), but its BLOCK is absent from disk + pen, so
	// apply returns the plain "unable to get block" error (a non-sentinel) -> the unrecognized-error crit fires.
	target := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: p.Hash()})
	// Deliberately do NOT seed target's block anywhere.
	chain.updateHvmHeaderConsensus(target.Header(), false)
	t.Fatalf("updateHvmHeaderConsensus returned for an unrecognized apply error; expected the dispatcher backstop to os.Exit")
}

func TestUpdateHvmHeaderConsensusUnrecognizedErrorCrit(t *testing.T) {
	cmd := exec.Command(os.Args[0], "-test.run=^TestUpdateHvmHeaderConsensusUnrecognizedErrorCritChild$", "-test.v")
	cmd.Env = append(os.Environ(), hvmDispatchUnrecognizedCritChildEnv+"=1")
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "the dispatcher unrecognized-error backstop must os.Exit non-zero, output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "Encountered an error applying hVM header state transition",
		"the crit must be the dispatcher's unrecognized-error backstop")
	require.NotContains(t, string(out), "updateHvmHeaderConsensus returned for an unrecognized apply error",
		"the backstop must os.Exit BEFORE returning (a returned-marker means it was downgraded)")
}

const hvmRestoreApplyErrCritChildEnv = "HVM_RESTORE_APPLY_ERR_CHILD"

// TestPerformFullHvmHeaderStateRestoreApplyErrorCritChild is the subprocess child: it seeds a disk chain whose
// activation block carries CORRUPT BtcAttr calldata, so the restore forward-walk's first apply fails with
// ErrInvalidHVMBlockFormat -> performFullHvmHeaderStateRestore log.Crits ("Failed to fully restore hVM state").
func TestPerformFullHvmHeaderStateRestoreApplyErrorCritChild(t *testing.T) {
	if os.Getenv(hvmRestoreApplyErrCritChildEnv) == "" {
		t.Skip("child-only: driven by TestPerformFullHvmHeaderStateRestoreApplyErrorCrit via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	gen := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(0), Time: hvm0Time - 500}) // pre-hVM0
	// Activation block (#1, Hvm0-active) carrying a 0x7C tx whose calldata is just the 4-byte selector — far below the
	// minimum serialized length, so ExtractBtcAttrData fails and apply returns ErrInvalidHVMBlockFormat.
	corrupt := types.NewTx(&types.BtcAttributesDepositedTx{
		To:   &types.BtcAttributesDepositedSenderAddress,
		Gas:  1_000_000,
		Data: types.UpdateHvmStateFuncBytes4[:],
	})
	block1 := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(1), Time: hvm0Time, ParentHash: gen.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{corrupt}})
	for _, b := range []*types.Block{gen, block1} {
		rawdb.WriteBlock(chain.db, b)
		rawdb.WriteCanonicalHash(chain.db, b.Hash(), b.NumberU64())
	}
	rawdb.WriteHeadBlockHash(chain.db, block1.Hash())
	chain.currentBlock.Store(block1.Header())

	chain.performFullHvmHeaderStateRestore()
	t.Fatalf("performFullHvmHeaderStateRestore returned despite a corrupt-calldata activation block; expected log.Crit")
}

func TestPerformFullHvmHeaderStateRestoreApplyErrorCrit(t *testing.T) {
	cmd := exec.Command(os.Args[0], "-test.run=^TestPerformFullHvmHeaderStateRestoreApplyErrorCritChild$", "-test.v")
	cmd.Env = append(os.Environ(), hvmRestoreApplyErrCritChildEnv+"=1")
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "a restore apply error must os.Exit non-zero, output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "Failed to fully restore hVM state",
		"the restore apply-error crit must fire on a corrupt block during the disk forward-walk")
	require.NotContains(t, string(out), "performFullHvmHeaderStateRestore returned despite",
		"the restore must os.Exit on the apply error, not return")
}
