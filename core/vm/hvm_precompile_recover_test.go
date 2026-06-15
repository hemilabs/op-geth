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

import (
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
)

// These tests lock in the recover() boundary that contains faults reached through hVM precompiles on
// malformed or inconsistent indexed Bitcoin data. Without it, such a fault would unwind through
// StateProcessor.Process / core.ApplyTransaction (no recover there) and crash the builder and every
// validating node.

const panickingHVMGas = uint64(5000)

// panickingHVMPrecompile simulates an hVM precompile whose embedded Bitcoin-node call faults on
// invalid data.
type panickingHVMPrecompile struct{}

func (panickingHVMPrecompile) RequiredGas([]byte) uint64 { return panickingHVMGas }
func (panickingHVMPrecompile) Run([]byte, common.Hash) ([]byte, error) {
	panic("simulated invalid Bitcoin data")
}
func (panickingHVMPrecompile) Name() string { return "panicking-hvm-test" }

// A panic in an hVM precompile must be recovered and normalized to an empty,
// successful no-op consuming only RequiredGas — never propagated (which would
// crash the node) and never a revert.
func TestRunPrecompileRecoversHVMPanic(t *testing.T) {
	p := panickingHVMPrecompile{}
	// Mark the test precompile as an hVM one (same membership the real Bitcoin
	// precompiles have) so the guard applies, then clean up.
	hvmPrecompileSet[p] = struct{}{}
	defer delete(hvmPrecompileSet, p)
	require.True(t, isHVMPrecompile(p))

	evm := &EVM{} // zero value is sufficient: runPrecompile only reads blockExecutionContext + Config.Tracer

	const gas = uint64(100_000)
	var (
		ret          []byte
		remainingGas uint64
		err          error
	)
	// The recover counter is the fleet-wide malformed-data alert; pin its increment as a load-bearing side
	// effect (before/after delta — the counter is a package global, so a delta is order-independent).
	before := hvmPrecompileInvalidDataCounter.Snapshot().Count()
	require.NotPanics(t, func() { ret, remainingGas, err = evm.runPrecompile(p, []byte{0x01, 0x02, 0x03}, gas) },
		"a panic in an hVM precompile must be recovered, not propagated")
	require.NoError(t, err, "recovered panic is normalized to a successful empty no-op")
	require.Nil(t, ret, "no-op returns empty data")
	require.Equal(t, gas-panickingHVMGas, remainingGas, "only the precompile's RequiredGas is consumed, mirroring the malformed-input no-op")
	require.Equal(t, before+1, hvmPrecompileInvalidDataCounter.Snapshot().Count(),
		"a recovered hVM-precompile panic must increment the alert counter exactly once")
}

// A panic in a non-hVM precompile must not be recovered: that is a genuine bug and silently swallowing
// it could diverge from other clients. The guard is scoped to hVM precompiles only.
func TestRunPrecompileDoesNotRecoverNonHVMPanic(t *testing.T) {
	p := panickingHVMPrecompile{} // deliberately not added to hvmPrecompileSet
	require.False(t, isHVMPrecompile(p))

	evm := &EVM{}
	before := hvmPrecompileInvalidDataCounter.Snapshot().Count()
	require.Panics(t, func() { _, _, _ = evm.runPrecompile(p, nil, 100_000) },
		"non-hVM precompile panics must propagate (not be swallowed)")
	require.Equal(t, before, hvmPrecompileInvalidDataCounter.Snapshot().Count(),
		"a non-hVM panic must NOT bump the recover counter (only hVM-scoped recoveries alert)")
}

// All real hVM (Bitcoin) precompiles must be recognized by the guard, and a
// standard precompile must not be.
func TestIsHVMPrecompileMembership(t *testing.T) {
	require.NotEmpty(t, PrecompiledContractsHvm0)
	for addr, p := range PrecompiledContractsHvm0 {
		require.Truef(t, isHVMPrecompile(p), "hVM precompile at %s must be guarded", addr)
	}
	// ecrecover (0x01) is a standard precompile and must not be guarded.
	require.False(t, isHVMPrecompile(&ecrecover{}))
}

// btcTxOutValueAt is the bounds-check shared by the hVM Bitcoin precompiles. An out-of-range index —
// which malformed or inconsistent indexed Bitcoin data can produce — must return
// ErrHVMInvalidPrecompileInput (normalized to an empty no-op) instead of panicking.
// These exercise the bounds logic directly, with no TBC node required.
func TestBtcTxOutValueAt(t *testing.T) {
	tx := &wire.MsgTx{TxOut: []*wire.TxOut{
		{Value: 100},
		{Value: 200},
		{Value: 300},
	}}

	// In-range indices return the exact output value, no error.
	for i, want := range []int64{100, 200, 300} {
		v, err := btcTxOutValueAt(tx, uint32(i))
		require.NoError(t, err, "index %d in range", i)
		require.Equal(t, want, v)
	}

	// Out-of-range indices are rejected with the sentinel, never an OOB panic.
	for _, idx := range []uint32{3, 4, 1 << 20, ^uint32(0)} {
		require.NotPanics(t, func() {
			v, err := btcTxOutValueAt(tx, idx)
			require.ErrorIs(t, err, ErrHVMInvalidPrecompileInput, "index %d out of range must be rejected", idx)
			require.Zero(t, v)
		})
	}
}

// An empty (or nil) output set must reject every index — guarding the empty-TxOut
// edge that would index out of range at [0].
func TestBtcTxOutValueAtEmptyAndNil(t *testing.T) {
	for _, tx := range []*wire.MsgTx{
		nil,
		{TxOut: nil},
		{TxOut: []*wire.TxOut{}},
	} {
		require.NotPanics(t, func() {
			v, err := btcTxOutValueAt(tx, 0)
			require.ErrorIs(t, err, ErrHVMInvalidPrecompileInput)
			require.Zero(t, v)
		})
	}
}
