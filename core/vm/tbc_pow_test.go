// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package vm

import (
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"
)

// mineRegtestHeader finds a nonce so the header's hash meets the regtest PowLimit target (~2^255, so
// ~2 tries on average — trivially cheap, unlike testnet3/mainnet's ~2^32). The mining oracle uses btcd's
// exported HashToBig/CompactToBig, independent of the production check (blockchain.CheckProofOfWork), so
// a passing assertion is not circular.
func mineRegtestHeader(t *testing.T, ts time.Time, nonceBase uint32) *wire.BlockHeader {
	t.Helper()
	h := &wire.BlockHeader{Version: 4, PrevBlock: chainhash.Hash{}, MerkleRoot: chainhash.Hash{}, Timestamp: ts, Bits: chaincfg.RegressionNetParams.PowLimitBits}
	target := blockchain.CompactToBig(h.Bits)
	for i := uint32(0); i < 1<<20; i++ {
		h.Nonce = nonceBase + i
		hash := h.BlockHash()
		if blockchain.HashToBig(&hash).Cmp(target) <= 0 {
			return h
		}
	}
	t.Fatal("failed to mine a regtest header within 2^20 nonces (should take ~2)")
	return nil
}

func TestCheckBTCHeaderPoW(t *testing.T) {
	reg := &chaincfg.RegressionNetParams

	t.Run("validly-mined header accepts", func(t *testing.T) {
		h := mineRegtestHeader(t, time.Unix(1_700_000_000, 0), 0)
		require.NoError(t, checkBTCHeaderPoWWith(h, reg))
		require.NoError(t, CheckBTCHeaderBatchPoWForNetwork("localnet", []*wire.BlockHeader{h}))
	})

	t.Run("unmined header (hash exceeds target) is ErrHighHash", func(t *testing.T) {
		// A testnet3-difficulty header with an arbitrary nonce: its 256-bit hash almost surely exceeds the
		// ~2^224 target (no work done) — the forged-Bits/zero-PoW case.
		h := &wire.BlockHeader{Version: 4, MerkleRoot: chainhash.Hash{}, Timestamp: time.Unix(1_700_000_000, 0), Bits: chaincfg.TestNet3Params.PowLimitBits, Nonce: 1}
		err := checkBTCHeaderPoWWith(h, &chaincfg.TestNet3Params)
		require.Error(t, err)
		var re blockchain.RuleError
		require.ErrorAs(t, err, &re)
		require.Equal(t, blockchain.ErrHighHash, re.ErrorCode, "an unmet target must be ErrHighHash, not accepted")
	})

	t.Run("zero Bits (target sign<=0) is ErrUnexpectedDifficulty", func(t *testing.T) {
		h := &wire.BlockHeader{Version: 4, Timestamp: time.Unix(1_700_000_000, 0), Bits: 0}
		err := checkBTCHeaderPoWWith(h, reg)
		require.Error(t, err)
		var re blockchain.RuleError
		require.ErrorAs(t, err, &re)
		require.Equal(t, blockchain.ErrUnexpectedDifficulty, re.ErrorCode)
	})

	t.Run("target above PowLimit is ErrUnexpectedDifficulty", func(t *testing.T) {
		// regtest PowLimit is 2^255-1 (compact 0x207fffff); a header claiming the easier target 0x2100ffff
		// (target > regtest PowLimit) must be rejected as out of range.
		h := &wire.BlockHeader{Version: 4, Timestamp: time.Unix(1_700_000_000, 0), Bits: 0x2100ffff}
		err := checkBTCHeaderPoWWith(h, reg)
		require.Error(t, err)
		var re blockchain.RuleError
		require.ErrorAs(t, err, &re)
		require.Equal(t, blockchain.ErrUnexpectedDifficulty, re.ErrorCode)
	})

	t.Run("unknown network fails closed (recoverable, never silent accept)", func(t *testing.T) {
		h := mineRegtestHeader(t, time.Unix(1_700_000_000, 0), 0)
		require.ErrorIs(t, CheckBTCHeaderBatchPoWForNetwork("nonsense", []*wire.BlockHeader{h}), ErrBTCHeaderContextUnavailable)
	})

	t.Run("nil header fails closed", func(t *testing.T) {
		require.ErrorIs(t, checkBTCHeaderPoWWith(nil, reg), ErrBTCHeaderContextUnavailable)
	})

	t.Run("batch returns the first failure", func(t *testing.T) {
		good := mineRegtestHeader(t, time.Unix(1_700_000_000, 0), 0)
		bad := &wire.BlockHeader{Version: 4, Timestamp: time.Unix(1_700_000_001, 0), Bits: chaincfg.TestNet3Params.PowLimitBits, Nonce: 7}
		err := CheckBTCHeaderBatchPoWForNetwork("testnet3", []*wire.BlockHeader{good, bad})
		// good was mined for regtest bits, which under testnet3 params is an out-of-range (too-easy) target,
		// so even the first header fails here — the point is a non-nil RuleError surfaces, never silent.
		require.Error(t, err)
		var re blockchain.RuleError
		require.ErrorAs(t, err, &re)
	})

	t.Run("batch iterates PAST a valid header to reject a LATER PoW-failing one", func(t *testing.T) {
		// header[0] genuinely PASSES regtest PoW; header[1] is forged to FAIL (hash exceeds the regtest
		// target). Both carry regtest Bits and are checked under regtest ("localnet") params, so the ONLY
		// header that can fail is index 1. A non-nil ErrHighHash here therefore proves the batch loop does
		// NOT short-circuit on header[0] — it kills a `return checkBTCHeaderPoWWith(headers[0], params)`
		// mutant that the "first failure" case above (whose own header[0] already fails) leaves green. This
		// matters because CheckBTCHeaderBatchPoWForNetwork is the consensus-enforcing apply-path PoW gate: a
		// header at batch index >0 inside a multi-header BtcAttr tx whose work is not real must still be
		// rejected.
		good := mineRegtestHeader(t, time.Unix(1_700_000_000, 0), 0)
		require.NoError(t, checkBTCHeaderPoWWith(good, reg), "header[0] must genuinely pass regtest PoW")

		// Forge a regtest-Bits header whose hash exceeds the regtest target (~50% of nonces qualify, since the
		// regtest target is ~2^255). The mining oracle (HashToBig/CompactToBig) is independent of the
		// production check, so this is not circular. Bits stays == PowLimit so the failure is ErrHighHash
		// (unmet target), not an out-of-range ErrUnexpectedDifficulty.
		regTarget := blockchain.CompactToBig(chaincfg.RegressionNetParams.PowLimitBits)
		bad := &wire.BlockHeader{Version: 4, PrevBlock: chainhash.Hash{0x09}, MerkleRoot: chainhash.Hash{}, Timestamp: time.Unix(1_700_000_500, 0), Bits: chaincfg.RegressionNetParams.PowLimitBits}
		forged := false
		for i := uint32(0); i < 1<<20; i++ {
			bad.Nonce = 1 + i
			hash := bad.BlockHash()
			if blockchain.HashToBig(&hash).Cmp(regTarget) > 0 {
				forged = true
				break
			}
		}
		require.True(t, forged, "should forge a failing regtest header within 2^20 nonces (~2 expected)")
		require.Error(t, checkBTCHeaderPoWWith(bad, reg), "header[1] must genuinely fail regtest PoW")

		err := CheckBTCHeaderBatchPoWForNetwork("localnet", []*wire.BlockHeader{good, bad})
		require.Error(t, err, "the batch must reject the forged SECOND header")
		var re blockchain.RuleError
		require.ErrorAs(t, err, &re)
		require.Equal(t, blockchain.ErrHighHash, re.ErrorCode,
			"the failure must be the LATER header's unmet target — proving the loop iterated past the valid first header")
	})
}

// TestCheckBTCHeaderPoWGlobalParams covers the global-params entry CheckBTCHeaderPoW (the gossip-ingest
// PoW gate, mirroring ValidateBTCHeaderContext). It reads the package-global tbcChainParams — save/restore
// it so the mutation cannot leak into other tests (top-level tests run sequentially).
func TestCheckBTCHeaderPoWGlobalParams(t *testing.T) {
	saved := tbcChainParams
	defer func() { tbcChainParams = saved }()

	t.Run("params unconfigured -> skip sentinel (NOT a PoW failure; caller must not drop)", func(t *testing.T) {
		tbcChainParams = nil
		require.ErrorIs(t, CheckBTCHeaderPoW(mineRegtestHeader(t, time.Unix(1_700_000_000, 0), 0)), ErrBTCHeaderContextUnavailable)
	})

	t.Run("nil header -> skip sentinel", func(t *testing.T) {
		tbcChainParams = &chaincfg.RegressionNetParams
		require.ErrorIs(t, CheckBTCHeaderPoW(nil), ErrBTCHeaderContextUnavailable)
	})

	t.Run("validly-mined header accepts against the configured params", func(t *testing.T) {
		tbcChainParams = &chaincfg.RegressionNetParams
		require.NoError(t, CheckBTCHeaderPoW(mineRegtestHeader(t, time.Unix(1_700_000_000, 0), 0)))
	})

	t.Run("a header that fails proof-of-work is a RuleError (ErrHighHash)", func(t *testing.T) {
		tbcChainParams = &chaincfg.TestNet3Params
		h := &wire.BlockHeader{Version: 4, Timestamp: time.Unix(1_700_000_000, 0), Bits: chaincfg.TestNet3Params.PowLimitBits, Nonce: 1}
		err := CheckBTCHeaderPoW(h)
		require.Error(t, err)
		var re blockchain.RuleError
		require.ErrorAs(t, err, &re)
		require.Equal(t, blockchain.ErrHighHash, re.ErrorCode)
	})
}
