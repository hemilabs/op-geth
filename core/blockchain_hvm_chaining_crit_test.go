// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Upstream-state-id chaining strictness: the apply path's last-line backstop. When the prior-state block resolves
// (check != nil) but its hash != the target block's ParentHash — a skipped block (apply N+2 while the view is at N)
// or a stale/forked parent — applyHvmHeaderConsensusUpdate must FAIL-STOP (hvmMigrationAwareCrit -> log.Crit ->
// os.Exit), never silently commit the target's BTC headers onto the wrong prior state. The check==nil arm
// (orphaned prior-state) is covered; this sibling arm (resolves-but-mismatches) is the chaining enforcement and is
// asserted by no other test (the empty-present sibling test only proves the crit is AVOIDED). A deleted/weakened guard would
// silently mis-commit and the suite would stay green; log.Crit cannot be caught in-process, hence the re-exec.

import (
	"math/big"
	"os"
	"os/exec"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/stretchr/testify/require"
)

const hvmChainingCritChildEnv = "HVM_APPLY_PARENT_MISMATCH_CHILD"

// TestApplyHvmHeaderParentMismatchCritChild is the subprocess child for TestApplyHvmHeaderParentMismatchCrit.
func TestApplyHvmHeaderParentMismatchCritChild(t *testing.T) {
	if os.Getenv(hvmChainingCritChildEnv) == "" {
		t.Skip("child-only: driven by TestApplyHvmHeaderParentMismatchCrit via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	// Prior-state block P (activation block, parent pre-hVM). Applying it sets the upstream-state-id to P.
	preP := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	p := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preP.Hash()})
	chain.tempHeaders[preP.Hash().String()] = preP
	chain.tempBlocks[preP.Hash().String()] = types.NewBlockWithHeader(preP)
	chain.tempHeaders[p.Hash().String()] = p.Header()
	chain.tempBlocks[p.Hash().String()] = p
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(p.Header(), false, false))
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, p.Hash().Bytes(), sid[:], "precondition: state-id is P")

	// Target T whose ParentHash is NOT P (a skipped/forked parent): the prior-state P resolves, but P.Hash() !=
	// T.ParentHash -> the chaining backstop must fire.
	target := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: common.Hash{0x99}})
	chain.tempHeaders[target.Hash().String()] = target.Header()
	chain.tempBlocks[target.Hash().String()] = target

	chain.applyHvmHeaderConsensusUpdate(target.Header(), false, false)
	t.Fatalf("applyHvmHeaderConsensusUpdate returned for a parent-mismatch block; expected the chaining backstop to os.Exit")
}

// TestApplyHvmHeaderParentMismatchCrit drives the chaining backstop via subprocess re-exec.
func TestApplyHvmHeaderParentMismatchCrit(t *testing.T) {
	cmd := exec.Command(os.Args[0], "-test.run=^TestApplyHvmHeaderParentMismatchCritChild$", "-test.v")
	cmd.Env = append(os.Environ(), hvmChainingCritChildEnv+"=1")
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "the chaining backstop must os.Exit non-zero, output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "but parent of updated block",
		"the crit must be the parent-mismatch chaining backstop, not another log.Crit site")
	require.NotContains(t, string(out), "applyHvmHeaderConsensusUpdate returned for a parent-mismatch block",
		"the backstop must os.Exit BEFORE returning; the returned-marker means it was downgraded to log.Warn")
}
