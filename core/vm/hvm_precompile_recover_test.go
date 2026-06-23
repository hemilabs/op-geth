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
	"crypto/sha256"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"

	"math/big"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
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

	// The wrapper runPrecompile normalizes ErrHVMInvalidPrecompileInput to nil, hiding whether the recover block
	// actually set the sentinel. Assert runPrecompileGuarded's raw error contract directly.
	var ret2 []byte
	var rem2 uint64
	var err2 error
	require.NotPanics(t, func() { ret2, rem2, err2 = evm.runPrecompileGuarded(p, []byte{0x01, 0x02, 0x03}, gas) },
		"runPrecompileGuarded must recover the panic, not propagate it")
	require.ErrorIs(t, err2, ErrHVMInvalidPrecompileInput, "runPrecompileGuarded must set the sentinel in the recover block")
	require.Nil(t, ret2, "guarded panic-recovery returns empty data")
	require.Equal(t, gas-panickingHVMGas, rem2, "guarded panic-recovery consumes only RequiredGas")
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

// TestHvmPrecompileAddressesDistinct pins the hVM precompile dispatch registration: exactly 10 precompiles mapped to
// the distinct addresses 0x40..0x49. PrecompiledContractsHvm0's keys are computed via common.BytesToAddress over
// hvmContractsToAddress, and Go does not reject duplicate computed map keys (no compile error, no vet warning), so a
// byte-slice typo (two types -> {0x40}) would silently collapse the dispatch map to <10 entries, leaving a precompile
// unreachable. A test that only ranges over present entries would still pass; this pins count and distinctness at the
// source.
func TestHvmPrecompileAddressesDistinct(t *testing.T) {
	require.Len(t, hvmContractsToAddress, 10, "exactly 10 hVM precompile types are registered")
	require.Len(t, PrecompiledContractsHvm0, 10, "all 10 must survive into the dispatch map (a duplicate computed key silently collapses it)")
	require.Len(t, PrecompiledAddressesHvm0, 10)

	// The address byte-slice values must be distinct (catches the typo at its source) and non-empty.
	seenBytes := map[string]bool{}
	for typ, b := range hvmContractsToAddress {
		require.NotEmptyf(t, b, "address bytes for %s must be non-empty", typ)
		require.Falsef(t, seenBytes[string(b)], "address byte slice 0x%x is duplicated across hVM precompile types", b)
		seenBytes[string(b)] = true
	}
	require.Len(t, seenBytes, 10, "all 10 hVM precompile address byte slices must be distinct")

	// The dispatch map keys are exactly the 0x40..0x49 set, and PrecompiledAddressesHvm0 mirrors them with no dupes.
	wantAddrs := map[common.Address]bool{}
	for b := 0x40; b <= 0x49; b++ {
		wantAddrs[common.BytesToAddress([]byte{byte(b)})] = true
	}
	require.Len(t, wantAddrs, 10, "0x40..0x49 is 10 distinct addresses")
	for addr := range PrecompiledContractsHvm0 {
		require.Truef(t, wantAddrs[addr], "unexpected hVM precompile address %s (outside 0x40..0x49)", addr)
	}
	addrSet := map[common.Address]bool{}
	for _, a := range PrecompiledAddressesHvm0 {
		require.Falsef(t, addrSet[a], "PrecompiledAddressesHvm0 has a duplicate %s", a)
		require.Truef(t, wantAddrs[a], "PrecompiledAddressesHvm0 contains unexpected %s", a)
		addrSet[a] = true
	}
	require.Len(t, addrSet, 10)
}

// TestHvmPrecompileRequiredGasInputInvariance pins that every hVM precompile's RequiredGas is input-independent (a
// fixed params constant) and non-zero. RequiredGas is pure (no embedded-node deref), so no Bitcoin data is needed.
// The invariant is a live tripwire: a change making gas depend on input length would silently fork consensus.
func TestHvmPrecompileRequiredGasInputInvariance(t *testing.T) {
	inputs := [][]byte{nil, {}, make([]byte, 1), make([]byte, 32), make([]byte, 36), make([]byte, 1024), make([]byte, 10240)}
	require.Len(t, PrecompiledContractsHvm0, 10)
	expectedGas := map[common.Address]uint64{
		common.BytesToAddress([]byte{0x40}): params.BtcAddrBal,
		common.BytesToAddress([]byte{0x41}): params.BtcUtxosAddrList,
		common.BytesToAddress([]byte{0x42}): params.BtcTxByTxid,
		common.BytesToAddress([]byte{0x43}): params.BtcTxConf,
		common.BytesToAddress([]byte{0x44}): params.BtcLastHeader,
		common.BytesToAddress([]byte{0x45}): params.BtcHeaderN,
		common.BytesToAddress([]byte{0x46}): params.BtcAddrToScript,
		common.BytesToAddress([]byte{0x47}): params.BtcInputByTxid,
		common.BytesToAddress([]byte{0x48}): params.BtcOutputByTxid,
		common.BytesToAddress([]byte{0x49}): params.BtcTxGetInputWitness,
	}
	distinct := map[uint64]bool{}
	for addr, pc := range PrecompiledContractsHvm0 {
		want := pc.RequiredGas(nil)
		require.Positivef(t, want, "hVM precompile %s RequiredGas must be non-zero", addr)
		expGas, okGas := expectedGas[addr]
		require.Truef(t, okGas, "unexpected hVM precompile address %s", addr)
		require.Equalf(t, expGas, want, "hVM precompile %s RequiredGas must equal its params gas-schedule constant", addr)
		for _, in := range inputs {
			require.Equalf(t, want, pc.RequiredGas(in),
				"hVM precompile %s RequiredGas must be input-independent (got a different value for len=%d)", addr, len(in))
		}
		distinct[want] = true
	}
	// The per-precompile invariance checks above would still pass if every RequiredGas returned one shared constant;
	// require that the precompiles do not all collapse to a single gas value.
	require.Greater(t, len(distinct), 1, "hVM precompiles must not all collapse to a single RequiredGas constant")
}

// TestHvmPrecompileInputLengthGuards pins the input-length validation guards that several hVM precompiles run BEFORE
// any embedded-TBC-node dereference: a wrong-length (or nil) input is rejected with ErrHVMInvalidPrecompileInput
// without touching the full node. With no full node configured, only the early guard is reachable; a regression moving
// the node deref ahead of the guard would nil-crash here instead of returning the error.
func TestHvmPrecompileInputLengthGuards(t *testing.T) {
	require.Nil(t, TBCFullNode, "precondition: no full TBC node, so these guards must fire BEFORE any node deref")
	for _, tc := range []struct {
		name     string
		pc       PrecompiledContract
		validLen int
	}{
		{"btcHeaderN", &btcHeaderN{}, 4},
		{"btcTxConfirmations", &btcTxConfirmations{}, BTC_TXID_LENGTH_BYTES}, // 32
		{"btcInputByTxid", &btcInputByTxid{}, BTC_TXID_LENGTH_BYTES + 4},     // 36
	} {
		t.Run(tc.name, func(t *testing.T) {
			// nil is always rejected.
			_, err := tc.pc.Run(nil, common.Hash{})
			require.ErrorIs(t, err, ErrHVMInvalidPrecompileInput, "%s nil input must be rejected by the length guard", tc.name)
			// A spread of wrong lengths around the valid one (and a clearly-wrong large one) is rejected.
			for _, badLen := range []int{0, tc.validLen - 1, tc.validLen + 1, 64} {
				if badLen == tc.validLen || badLen < 0 {
					continue
				}
				_, err := tc.pc.Run(make([]byte, badLen), common.Hash{})
				require.ErrorIsf(t, err, ErrHVMInvalidPrecompileInput, "%s len=%d must be rejected by the length guard", tc.name, badLen)
			}
		})
	}
}

// TestHvmPrecompileInputGuardsRemaining covers the input-length guards of the remaining 6 hVM precompiles not pinned
// by TestHvmPrecompileInputLengthGuards, all returning ErrHVMInvalidPrecompileInput BEFORE any embedded-node deref.
// Two guard shapes: "lt" (len < threshold; only sub-threshold lengths are rejected — a >=threshold input would pass
// the guard and reach the node) and "ne" (len != validLen; any other length rejected). Probing only the safe wrong
// lengths avoids reaching the node deref or log.Crit.
func TestHvmPrecompileInputGuardsRemaining(t *testing.T) {
	require.Nil(t, TBCFullNode, "precondition: no full TBC node; these guards must fire BEFORE any node deref / log.Crit")
	const (
		lt = "lt"
		ne = "ne"
	)
	for _, tc := range []struct {
		name string
		pc   PrecompiledContract
		kind string
		n    int
	}{
		{"btcBalAddr", &btcBalAddr{}, lt, MIN_BTC_ADDRESS_LENGTH},                        // len < 24
		{"btcAddrToScript", &btcAddrToScript{}, lt, MIN_BTC_ADDRESS_LENGTH},              // len < 24
		{"btcUtxosAddrList", &btcUtxosAddrList{}, lt, MIN_BTC_ADDRESS_LENGTH + 4},        // len < 28
		{"btcTxByTxid", &btcTxByTxid{}, ne, BTC_TXID_LENGTH_BYTES + 4},                   // len != 36
		{"btcOutputByTxid", &btcOutputByTxid{}, ne, BTC_TXID_LENGTH_BYTES + 4},           // len != 36
		{"btcTxGetInputWitness", &btcTxGetInputWitness{}, ne, BTC_TXID_LENGTH_BYTES + 6}, // len != 38
	} {
		t.Run(tc.name, func(t *testing.T) {
			// nil input is rejected by both guard shapes.
			_, err := tc.pc.Run(nil, common.Hash{})
			require.ErrorIs(t, err, ErrHVMInvalidPrecompileInput, "%s nil input must be rejected", tc.name)

			var badLens []int
			if tc.kind == lt {
				badLens = []int{0, tc.n - 1} // only sub-threshold lengths are safe to probe (>= threshold reaches the node)
			} else {
				badLens = []int{0, tc.n - 1, tc.n + 1, 64}
			}
			for _, bl := range badLens {
				if bl < 0 || bl == tc.n {
					continue
				}
				_, err := tc.pc.Run(make([]byte, bl), common.Hash{})
				require.ErrorIsf(t, err, ErrHVMInvalidPrecompileInput, "%s len=%d must be rejected by the input guard", tc.name, bl)
			}
		})
	}
}

// TestCalculateHVMQueryKey pins the pure hVM precompile cache-key derivation: deterministic for identical
// (input, precompileAddress, blockContext) tuples, and sensitive to each component — a key collision across distinct
// queries would return stale/wrong cached Bitcoin data. A null block context is rejected. Pure sha256.
func TestCalculateHVMQueryKey(t *testing.T) {
	ctx := common.HexToHash("0x00000000000000000000000000000000000000000000000000000000000000aa")
	in := []byte{0x01, 0x02, 0x03}

	k1, err := calculateHVMQueryKey(in, 0x42, ctx)
	require.NoError(t, err)
	// Pin the exact concatenation ORDER (blockContext || addressByte || input): a reorder keeps every component
	// present (so the per-component sensitivity checks below still pass) but changes the digest.
	wantOrder := sha256.Sum256(append(append(append([]byte{}, ctx[:]...), 0x42), in...))
	require.Equal(t, hVMQueryKey(wantOrder), k1, "query key must be sha256(blockContext || addr || input) in that order")
	k2, err := calculateHVMQueryKey(in, 0x42, ctx)
	require.NoError(t, err)
	require.Equal(t, k1, k2, "identical (input,addr,blockContext) must produce identical keys (cache determinism)")

	// Sensitivity to each component (no collisions across distinct queries).
	kInput, err := calculateHVMQueryKey([]byte{0x01, 0x02, 0x04}, 0x42, ctx)
	require.NoError(t, err)
	require.NotEqual(t, k1, kInput, "a different input must produce a different key")
	kAddr, err := calculateHVMQueryKey(in, 0x43, ctx)
	require.NoError(t, err)
	require.NotEqual(t, k1, kAddr, "a different precompile address must produce a different key")
	kCtx, err := calculateHVMQueryKey(in, 0x42, common.HexToHash("0x00000000000000000000000000000000000000000000000000000000000000bb"))
	require.NoError(t, err)
	require.NotEqual(t, k1, kCtx, "a different block context must produce a different key")

	// A null (all-zero) block context is rejected (cannot key a query against a null containing block).
	_, err = calculateHVMQueryKey(in, 0x42, common.Hash{})
	require.Error(t, err, "a null block context must be rejected")
}

// TestActivePrecompilesHvm0Inclusion pins that ActivePrecompiles includes the hVM precompile set exactly when
// rules.IsHvm0 is active, and excludes it otherwise — the gate that makes the Bitcoin precompiles callable only
// post-activation. Pure (params.Rules in, []Address out).
func TestActivePrecompilesHvm0Inclusion(t *testing.T) {
	contains := func(addrs []common.Address, a common.Address) bool {
		for _, x := range addrs {
			if x == a {
				return true
			}
		}
		return false
	}

	active := ActivePrecompiles(params.Rules{IsHvm0: true})
	for _, a := range PrecompiledAddressesHvm0 {
		require.Truef(t, contains(active, a), "hVM precompile %s must be active when IsHvm0", a)
	}

	inactive := ActivePrecompiles(params.Rules{IsHvm0: false})
	for _, a := range PrecompiledAddressesHvm0 {
		require.Falsef(t, contains(inactive, a), "hVM precompile %s must NOT be active when !IsHvm0", a)
	}
}

// TestEVMPrecompileDispatchHvm0Gate pins the execution-time dispatch gate EVM.precompile(addr): an hVM precompile
// address (0x40..0x49) resolves to its contract only when chainRules.IsHvm0, and a standard precompile still resolves
// regardless. This is the runtime path Call/StaticCall/etc. use to route into the Bitcoin precompiles; it is distinct
// from ActivePrecompiles (a list builder) and isHVMPrecompile (a type predicate). The gate is pure — it returns the
// contract pointer without ever calling Run().
func TestEVMPrecompileDispatchHvm0Gate(t *testing.T) {
	hvmAddr := common.BytesToAddress([]byte{0x40}) // btcBalAddr
	mk := func(hvm0 bool) *EVM {
		cfg := *params.MergedTestChainConfig
		if hvm0 {
			z := uint64(0)
			cfg.Hvm0Time = &z
		} else {
			cfg.Hvm0Time = nil
		}
		statedb, err := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
		require.NoError(t, err)
		return NewEVM(BlockContext{BlockNumber: big.NewInt(1), Time: 1}, statedb, &cfg, Config{})
	}

	on := mk(true)
	require.True(t, on.chainRules.IsHvm0, "precondition: IsHvm0 active")
	for b := byte(0x40); b <= 0x49; b++ {
		a := common.BytesToAddress([]byte{b})
		pc, ok := on.precompile(a)
		require.Truef(t, ok, "hVM address %s must dispatch when IsHvm0", a)
		require.NotNil(t, pc)
		require.Truef(t, isHVMPrecompile(pc), "the dispatched contract at %s must be an hVM precompile", a)
	}
	_, okStd := on.precompile(common.BytesToAddress([]byte{0x01}))
	require.True(t, okStd, "a standard precompile (ecrecover 0x01) must still resolve under IsHvm0")

	off := mk(false)
	require.False(t, off.chainRules.IsHvm0, "precondition: IsHvm0 inactive")
	_, okOff := off.precompile(hvmAddr)
	require.False(t, okOff, "an hVM precompile address must NOT dispatch when !IsHvm0")
}

// TestActivePrecompilesHvm0PragueWithoutJovian pins the distinct ActivePrecompiles sub-branch where, when
// IsHvm0 && IsPrague && !IsOptimismJovian, the active set is ONLY the hVM precompiles — the upstream Prague
// precompiles (e.g. BLS G1ADD at 0x0b) are excluded. TestActivePrecompilesHvm0Inclusion exercises the default
// (!IsPrague) append branch; this exclusion behavior is structurally different. Pure params.Rules -> []Address.
func TestActivePrecompilesHvm0PragueWithoutJovian(t *testing.T) {
	active := ActivePrecompiles(params.Rules{IsHvm0: true, IsPrague: true, IsOptimismJovian: false})

	require.Len(t, active, len(PrecompiledAddressesHvm0), "Prague+IsHvm0+!Jovian must return ONLY the hVM precompiles")
	hvmSet := map[common.Address]bool{}
	for _, a := range PrecompiledAddressesHvm0 {
		hvmSet[a] = true
	}
	for _, a := range active {
		require.Truef(t, hvmSet[a], "only hVM addresses may be present in this branch, found %s", a)
	}
	require.NotContains(t, active, common.BytesToAddress([]byte{0x0b}),
		"the upstream Prague BLS precompile (0x0b) must be excluded in the IsHvm0+Prague+!Jovian branch")
}

// TestHvmPrecompileNameDistinctAndNonEmpty pins that every hVM precompile's Name() is non-empty and the 10 names are
// distinct. Name() is not just cosmetic: internal/ethapi builds a map keyed by Name() (precompiles[c.Name()] = addr),
// so a duplicate name would silently collapse a map entry and drop an hVM precompile address from the RPC config
// response — the same silent-collapse failure mode TestHvmPrecompileAddressesDistinct guards, on an independent symbol.
func TestHvmPrecompileNameDistinctAndNonEmpty(t *testing.T) {
	require.Len(t, PrecompiledContractsHvm0, 10)
	expectedName := map[common.Address]string{
		common.BytesToAddress([]byte{0x40}): "BTC Balance Address",
		common.BytesToAddress([]byte{0x41}): "BTC UTXOs Address List",
		common.BytesToAddress([]byte{0x42}): "BTC TX by TXID",
		common.BytesToAddress([]byte{0x43}): "BTC TX Confirmations",
		common.BytesToAddress([]byte{0x44}): "BTC Last Header",
		common.BytesToAddress([]byte{0x45}): "BTC Header N",
		common.BytesToAddress([]byte{0x46}): "BTC Addr to Script",
		common.BytesToAddress([]byte{0x47}): "BTC Input by TXID",
		common.BytesToAddress([]byte{0x48}): "BTC Output by TXID",
		common.BytesToAddress([]byte{0x49}): "BTC TX Get Input Witness",
	}
	names := map[string]bool{}
	for addr, pc := range PrecompiledContractsHvm0 {
		n := pc.Name()
		require.NotEmptyf(t, n, "hVM precompile %s must have a non-empty Name()", addr)
		expName, okName := expectedName[addr]
		require.Truef(t, okName, "unexpected hVM precompile address %s", addr)
		require.Equalf(t, expName, n, "hVM precompile %s Name() must match its expected literal", addr)
		require.Falsef(t, names[n], "hVM precompile Name() %q is duplicated (would collapse the Name-keyed RPC map)", n)
		names[n] = true
	}
	require.Len(t, names, 10, "all 10 hVM precompile Name() values must be distinct")
}
