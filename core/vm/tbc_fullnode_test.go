// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package vm

import (
	"bytes"
	"context"
	"encoding/binary"
	"errors"
	"fmt"
	"reflect"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/txscript"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/hemilabs/heminetwork/database"
	"github.com/hemilabs/heminetwork/database/tbcd"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

// Integration: drive the hVM Bitcoin precompiles' REAL Run() bodies against a REAL full (indexed) tbc.Server fed
// entirely SYNTHETIC regtest blocks in-process — no bitcoind, no P2P, no downloaded chaindata.
//
// Other hVM tests stub the precompiles' data source with an EXTERNAL-HEADER (header-only) tbc.Server, which CANNOT
// answer BalanceByAddress/TxById/UtxosByAddress (those return "External Header mode" errors), or they test the pure
// helpers around the precompiles. So the actual Run() bodies of btcBalAddr / btcLastHeader / btcHeaderN / btcTxByTxid
// — the lines that call TBCFullNode.BalanceByAddress, .UtxoIndexHash, .BlockHeaderByHash, .BlockHeadersByHeight,
// .TxById and serialize the result into the precompile's wire format — have no other end-to-end coverage. A
// regression in the response framing, the little/big-endian byte reversals, the height/hash plumbing, or the
// indexer-sync assumption would pass those tests while corrupting what every hVM smart contract observes about Bitcoin.
//
// Feasibility: the production construction choke point vm.SetupTBCFullNode -> go tbcNode.Run(ctx) opens the leveldb,
// inserts the regtest genesis, and (with PeersWanted=0 and no listen addresses) starts NO P2P/HTTP — it just blocks
// on ctx. Three exported methods let us feed a synthetic chain in-process: BlockHeadersInsert (checks only that the
// batch LINKS to an existing header and accumulates cumulative work from the header bits — it does NOT verify PoW,
// merkle root, or timestamps; that lives in the gated P2P handleBlock/CheckBlockSanity path), BlockInsert (a thin DB
// store that also does not check the body against the header's merkle root), and SyncIndexersToHash (populates the
// UTXO/Tx/Hemi indexes). We still mine valid PoW and build correct merkle roots so the blocks are faithful to real
// ones (and robust to any path that DOES validate); RegressionNetParams has PoWNoRetargeting, so every header carries
// PowLimitBits and mines in ~1 nonce.
const syntheticRegtestPowBits = uint32(0x207fffff) // chaincfg.RegressionNetParams.PowLimitBits

// setupSyntheticFullNode stands up a REAL full (indexed) tbc.Server via the production SetupTBCFullNode choke point,
// configured for localnet/regtest with P2P and all listeners disabled, seated at a fresh temp leveldb. It saves and
// restores every package global SetupTBCFullNode mutates (TBCFullNode/MainCtx/tbcChainParams/TBCFullNodeConfig/
// TBCFullNodeCtxCancel) and clears the precompile query cache, so the node cannot leak into any other test. It blocks
// until Run() has opened the DB and inserted the regtest genesis. These tests must NOT run in parallel (shared globals).
func setupSyntheticFullNode(t *testing.T) {
	t.Helper()
	if testing.Short() {
		t.Skip("builds a real indexed TBC full node on disk")
	}

	prevNode, prevCfg, prevCtx := TBCFullNode, TBCFullNodeConfig, MainCtx
	prevCancel, prevParams, prevUpstream := TBCFullNodeCtxCancel, tbcChainParams, TBCUpstreamTip

	ctx, cancel := context.WithCancel(context.Background())

	cfg := tbc.NewDefaultConfig()
	cfg.Network = "localnet"
	cfg.LevelDBHome = t.TempDir()
	cfg.PeersWanted = 0    // no P2P
	cfg.ListenAddress = "" // no websocket/RPC server
	cfg.PrometheusListenAddress = ""
	cfg.PprofListenAddress = ""
	cfg.AutoIndex = false // manual indexing via SyncIndexersToHash (validateTBCFullNodeConfig rejects AutoIndex=true)
	cfg.MempoolEnabled = false
	// NB: leave MaxCachedTxs at its NewDefaultConfig default (1e6) — the UTXO indexer divides by it
	// (crawler.go: len(utxos)*100/MaxCachedTxs), so a 0 here panics. The header-only liveness harness can zero it
	// because external-header mode never runs the UTXO indexer; this full node does.

	require.NoError(t, SetupTBCFullNode(ctx, cfg))

	t.Cleanup(func() {
		if TBCFullNodeCtxCancel != nil {
			TBCFullNodeCtxCancel()
		}
		cancel()
		// Give the Run goroutine a moment to release the leveldb before TempDir cleanup removes it.
		deadline := time.Now().Add(5 * time.Second)
		for TBCFullNode != nil && TBCFullNode.Running() && time.Now().Before(deadline) {
			time.Sleep(10 * time.Millisecond)
		}
		TBCFullNode, TBCFullNodeConfig, MainCtx = prevNode, prevCfg, prevCtx
		TBCFullNodeCtxCancel, tbcChainParams, TBCUpstreamTip = prevCancel, prevParams, prevUpstream
		for k := range hvmQueryMap {
			delete(hvmQueryMap, k)
		}
	})

	// Readiness: Run() must have opened the DB and inserted the regtest genesis (BlockHeaderBest succeeds).
	require.Eventually(t, func() bool {
		if TBCFullNode == nil || !TBCFullNode.Running() {
			return false
		}
		_, _, err := TBCFullNode.BlockHeaderBest(MainCtx)
		return err == nil
	}, 30*time.Second, 10*time.Millisecond, "full node must open its DB and insert the regtest genesis")
}

// mineRegtestFullBlock builds a complete synthetic regtest block extending prev: a single BIP34 coinbase paying
// `value` to `pkScript`, a correct merkle root over that one tx, and a header mined to the regtest PowLimit target
// (~1 nonce). bip34Height encodes the block height into the coinbase scriptSig; extraNonce keeps each coinbase txid
// unique. The header it carries is identical to the one passed to BlockHeadersInsert, so block.Hash()==header hash.
func mineRegtestFullBlock(t *testing.T, prev *wire.BlockHeader, bip34Height int32, pkScript []byte, value int64, extraNonce uint32) *wire.MsgBlock {
	t.Helper()

	coinbase := wire.NewMsgTx(wire.TxVersion)
	sigScript, err := txscript.NewScriptBuilder().AddInt64(int64(bip34Height)).AddInt64(int64(extraNonce)).Script()
	require.NoError(t, err)
	coinbase.AddTxIn(&wire.TxIn{
		PreviousOutPoint: wire.OutPoint{Hash: chainhash.Hash{}, Index: 0xffffffff},
		SignatureScript:  sigScript,
		Sequence:         0xffffffff,
	})
	coinbase.AddTxOut(&wire.TxOut{Value: value, PkScript: pkScript})

	// Merkle root for a single-tx block is the (recomputed) coinbase hash; build it the canonical way regardless.
	merkles := blockchain.BuildMerkleTreeStore([]*btcutil.Tx{btcutil.NewTx(coinbase)}, false)
	merkleRoot := merkles[len(merkles)-1]

	hdr := wire.BlockHeader{
		Version:    4,
		PrevBlock:  prev.BlockHash(),
		MerkleRoot: *merkleRoot,
		Timestamp:  prev.Timestamp.Add(60 * time.Second),
		Bits:       syntheticRegtestPowBits,
	}
	target := blockchain.CompactToBig(hdr.Bits)
	mined := false
	for i := uint32(0); i < 1<<22; i++ {
		hdr.Nonce = extraNonce + i
		hh := hdr.BlockHash()
		if blockchain.HashToBig(&hh).Cmp(target) <= 0 {
			mined = true
			break
		}
	}
	require.True(t, mined, "must mine a regtest full block within 2^22 nonces")

	return &wire.MsgBlock{Header: hdr, Transactions: []*wire.MsgTx{coinbase}}
}

// feedSyntheticChain mines `n` regtest full blocks (each coinbase paying `value` to `pkScript`) on top of the regtest
// genesis, inserts their headers and bodies into the full node, and syncs all indexers up to the tip. It returns the
// built blocks so callers can assert on coinbase txids/hashes.
func feedSyntheticChain(t *testing.T, n int, pkScript []byte, value int64) []*wire.MsgBlock {
	t.Helper()

	prev := &chaincfg.RegressionNetParams.GenesisBlock.Header
	blocks := make([]*wire.MsgBlock, 0, n)
	headers := make([]*wire.BlockHeader, 0, n)
	for i := 0; i < n; i++ {
		blk := mineRegtestFullBlock(t, prev, int32(i+1), pkScript, value, uint32(i)*100_000+1)
		blocks = append(blocks, blk)
		h := blk.Header
		headers = append(headers, &h)
		prev = &blocks[i].Header
	}

	_, _, _, count, err := TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: headers})
	require.NoError(t, err, "synthetic regtest headers must link to the existing chain (BlockHeadersInsert checks linkage + work, not PoW/merkle)")
	require.Equal(t, n, count, "all %d synthetic headers must be inserted", n)

	for i, blk := range blocks {
		_, err := TBCFullNode.BlockInsert(MainCtx, blk)
		require.NoError(t, err, "synthetic block %d must insert", i+1)
	}

	tip := blocks[len(blocks)-1].Header.BlockHash()
	require.NoError(t, TBCFullNode.SyncIndexersToHash(MainCtx, tip), "indexers must sync to the synthetic tip")
	return blocks
}

// regtestP2PKH returns a deterministic regtest P2PKH address, its pay-to-addr script, and the encoded string the
// btcBalAddr precompile takes as input.
func regtestP2PKH(t *testing.T, fill byte) (script []byte, encoded string) {
	t.Helper()
	pkh := bytes.Repeat([]byte{fill}, 20)
	addr, err := btcutil.NewAddressPubKeyHash(pkh, &chaincfg.RegressionNetParams)
	require.NoError(t, err)
	script, err = txscript.PayToAddrScript(addr)
	require.NoError(t, err)
	return script, addr.EncodeAddress()
}

// TestSyntheticFullNodeBalanceAndTip drives the btcBalAddr and btcLastHeader precompiles' real Run() bodies against a
// 3-block synthetic regtest chain whose coinbases all pay one address. It pins (a) btcBalAddr returns the summed
// coinbase balance as a big-endian uint64, (b) an unfunded address returns 0, and (c) btcLastHeader reports the
// indexed tip height and the little-endian-reversed tip hash in its framed response.
func TestSyntheticFullNodeBalanceAndTip(t *testing.T) {
	setupSyntheticFullNode(t)

	script, addrStr := regtestP2PKH(t, 0x42)
	const numBlocks = 3
	const coinbaseValue = int64(50 * 1e8)
	blocks := feedSyntheticChain(t, numBlocks, script, coinbaseValue)

	// (a) btcBalAddr: input is the encoded address; output is an 8-byte big-endian balance.
	balOut, err := (&btcBalAddr{}).Run([]byte(addrStr), common.Hash{})
	require.NoError(t, err)
	require.Len(t, balOut, 8)
	require.Equal(t, uint64(numBlocks)*uint64(coinbaseValue), binary.BigEndian.Uint64(balOut),
		"btcBalAddr must report the summed coinbase value paid to the address across all synthetic blocks")

	// (b) An address that received nothing must report a zero balance (proves the lookup is real, not a constant).
	_, otherAddr := regtestP2PKH(t, 0x11)
	zeroOut, err := (&btcBalAddr{}).Run([]byte(otherAddr), common.Hash{})
	require.NoError(t, err)
	require.Len(t, zeroOut, 8, "the unfunded-balance response must still be a full 8-byte frame, not a (nil) miss")
	require.Equal(t, uint64(0), binary.BigEndian.Uint64(zeroOut), "an unfunded address must report a zero balance")

	// Fail-soft: a well-sized but UNDECODABLE address must be a no-op (nil,nil), not a gas-burning error. btcBalAddr's
	// BalanceByAddress-error arm returns (nil,nil); a `return nil, err` there would burn all gas and is caught here.
	junk := bytes.Repeat([]byte{'z'}, MIN_BTC_ADDRESS_LENGTH+6)
	junkOut, err := (&btcBalAddr{}).Run(junk, common.Hash{})
	require.NoError(t, err, "an undecodable address must be a no-op, not an error")
	require.Nil(t, junkOut, "btcBalAddr must return (nil,nil) for an undecodable address")

	// (c) btcLastHeader: the FULL 116-byte frame reflecting the indexed tip, asserted field-by-field so a mutation in
	// any field (a dropped reversal, a swapped bits/nonce append, a wrong width) is caught — not just height+hash.
	// Frame: height(4) || hashRev(32) || version(4) || prevHashRev(32) || merkleRev(32) || time(4) || bits(4) || nonce(4).
	tip := blocks[numBlocks-1].Header
	tipHash := tip.BlockHash()
	hdrOut, err := (&btcLastHeader{}).Run(nil, common.Hash{})
	require.NoError(t, err)
	require.Len(t, hdrOut, 4+32+4+32+32+4+4+4, "btcLastHeader frame must be exactly 116 bytes")
	require.Equal(t, uint32(numBlocks), binary.BigEndian.Uint32(hdrOut[0:4]), "height = indexed tip height")
	require.Equal(t, tipHash[:], reverseBytes(hdrOut[4:36]), "tip block hash (reversed)")
	require.Equal(t, uint32(tip.Version), binary.BigEndian.Uint32(hdrOut[36:40]), "version")
	require.Equal(t, tip.PrevBlock[:], reverseBytes(hdrOut[40:72]), "prev block hash (reversed)")
	require.Equal(t, tip.MerkleRoot[:], reverseBytes(hdrOut[72:104]), "merkle root (reversed)")
	require.Equal(t, uint32(tip.Timestamp.Unix()), binary.BigEndian.Uint32(hdrOut[104:108]), "timestamp")
	require.Equal(t, tip.Bits, binary.BigEndian.Uint32(hdrOut[108:112]), "bits")
	require.Equal(t, tip.Nonce, binary.BigEndian.Uint32(hdrOut[112:116]), "nonce")
}

// TestSyntheticFullNodeLastHeaderUtxoIndexFault pins the consensus outcome of a real btcLastHeader UtxoIndexHash fault
// end-to-end: a normalized (nil, gas-RequiredGas, nil) CALL-success. A closed-DB fault surfaces as a PANIC inside
// goleveldb (Get/OpenTransaction on a closed handle panics — it does NOT return ErrClosed), so this injection routes
// through the precompile RECOVER BOUNDARY (evm.go), not btcLastHeader's explicit `if err != nil` guard. The deployed
// testnet3 binary reaches the same outcome via its subsequent utxoIndex.Hash nil-deref panicking into the same
// boundary, so the consensus result here matches deployed behavior for a real fault. The explicit non-panic
// error-return arm (contracts.go: guard + counter + ErrHVMInvalidPrecompileInput) is covered separately by
// TestBtcLastHeaderUtxoIndexErrorReturnArm, which a closed-DB injection cannot reach.
//
// Fault injection: shut the node's DB down (cancel ctx -> the Run goroutine closes leveldb).
func TestSyntheticFullNodeLastHeaderUtxoIndexFault(t *testing.T) {
	setupSyntheticFullNode(t)
	script, _ := regtestP2PKH(t, 0x42)
	feedSyntheticChain(t, 3, script, int64(50*1e8))

	p := &btcLastHeader{}
	gas := p.RequiredGas(nil) + 50_000 // headroom above RequiredGas so the refund (gas-RequiredGas) is non-trivial

	// Control: on the healthy node btcLastHeader returns the full last-header frame with no error (proves the fault
	// below is the injection, not an unsynced node — feedSyntheticChain already synced the UTXO indexer to the tip).
	ctrl, err := p.Run(nil, common.Hash{})
	require.NoError(t, err, "control: a healthy node's btcLastHeader must succeed")
	require.NotEmpty(t, ctrl, "control: a healthy node's btcLastHeader returns the last-header frame")

	// Inject the UtxoIndexHash fault by closing the node's DB.
	require.NotNil(t, TBCFullNodeCtxCancel, "harness must expose the node cancel func")
	TBCFullNodeCtxCancel()
	require.Eventually(t, func() bool {
		return TBCFullNode == nil || !TBCFullNode.Running()
	}, 10*time.Second, 10*time.Millisecond, "the node DB must close after ctx cancel (so UtxoIndexHash starts erroring)")

	// The required outcome for ANY UtxoIndexHash fault is a normalized (nil, gas-RequiredGas, nil) CALL-success. This
	// closed-DB fault panics inside UtxoIndexHash (goleveldb panics, not ErrClosed, on a closed DB); the precompile
	// recover boundary catches it and converts to ErrHVMInvalidPrecompileInput. btcLastHeader's explicit `if err != nil`
	// guard covers the narrower NON-panic sub-case (e.g. a stored UTXO-index hash whose header is absent); both converge
	// on the SAME (nil, gas-RequiredGas, nil). We assert that outcome through runPrecompile (which installs the recover
	// boundary and the RequiredGas refund). Breaking the consensus-safe normalization — or letting a fault propagate as
	// a raw-error CALL failure (revert + all gas burned) — diverges from the deployed binary and fails this.
	evm := &EVM{} // zero value suffices: runPrecompile only reads blockExecutionContext + Config.Tracer
	want := gas - p.RequiredGas(nil)
	require.Eventually(t, func() bool {
		ret, remGas, rerr := evm.runPrecompile(p, nil, gas)
		return rerr == nil && ret == nil && remGas == want
	}, 10*time.Second, 20*time.Millisecond,
		"btcLastHeader UtxoIndexHash fault must normalize to the deployed (nil, gas-RequiredGas, nil) CALL-success; a raw-error CALL failure (revert + full gas burn) reddens this")
}

// TestBtcLastHeaderUtxoIndexErrorReturnArm exercises the explicit NON-panic UtxoIndexHash-error arm of btcLastHeader
// (contracts.go: the `if err != nil` guard -> hvmPrecompileInvalidDataCounter.Inc(1) -> return
// ErrHVMInvalidPrecompileInput). The closed-DB integration test above cannot reach this arm — goleveldb PANICS on a
// closed handle, so that fault routes through the recover boundary, not this explicit return. We inject a CLEAN
// (non-panic) error via the utxoIndexHashForLastHeader seam (a pure forward to TBCFullNode.UtxoIndexHash in
// production). This is the no-arg corruption-class fault (e.g. a UTXO index pointing at an absent header, or a
// non-NotFound leveldb error) handled explicitly here, with the same observable (nil,nil) CALL-success the recover
// boundary produces for the panic sub-case. Two regressions are caught: `return nil, err` (raw-error CALL failure ->
// revert + full gas burn, a consensus divergence from the recover->(nil,nil) outcome) and deleting the counter Inc(1)
// (observability blind spot). No live node needed; the seam returns before any TBCFullNode method runs.
func TestBtcLastHeaderUtxoIndexErrorReturnArm(t *testing.T) {
	prevNode := TBCFullNode
	TBCFullNode = &tbc.Server{} // non-nil so Run's nil-guard passes; the seam returns before any Server method is used
	t.Cleanup(func() { TBCFullNode = prevNode })

	prevSeam := utxoIndexHashForLastHeader
	t.Cleanup(func() { utxoIndexHashForLastHeader = prevSeam })
	utxoIndexHashForLastHeader = func(context.Context) (*tbc.HashHeight, error) {
		return nil, errors.New("injected non-panic UtxoIndexHash error")
	}

	before := hvmPrecompileInvalidDataCounter.Snapshot().Count()
	out, err := (&btcLastHeader{}).Run(nil, common.Hash{})
	require.ErrorIs(t, err, ErrHVMInvalidPrecompileInput,
		"a non-panic UtxoIndexHash error must return the guarded sentinel; a `return nil, rawErr` regression (gas-burning CALL failure, diverging from the deployed recover->(nil,nil)) reddens this")
	require.Nil(t, out, "the guarded fault arm returns nil bytes alongside the sentinel")
	require.Equal(t, before+1, hvmPrecompileInvalidDataCounter.Snapshot().Count(),
		"the UtxoIndexHash-fault arm must increment hvmPrecompileInvalidDataCounter once (observability parity with the deployed panic-recover path); deleting the Inc(1) reddens this")
}

// TestSyntheticFullNodeUtxosByAddress drives the btcUtxosAddrList precompile. Each of the 3 synthetic blocks pays one
// coinbase output (index 0) to the same address, so the precompile must report exactly 3 UTXOs, each carrying the
// coinbase value at output index 0. The response framing is: count(1) || repeat[ reversedScriptHash(32) ||
// outputIndex(2) || value(8) ].
func TestSyntheticFullNodeUtxosByAddress(t *testing.T) {
	setupSyntheticFullNode(t)

	script, addrStr := regtestP2PKH(t, 0x42)
	const numBlocks = 3
	const coinbaseValue = int64(50 * 1e8)
	blocks := feedSyntheticChain(t, numBlocks, script, coinbaseValue)

	// addr || page(3 bytes, =0) || pageSize(1 byte, =100)
	in := append([]byte(addrStr), 0x00, 0x00, 0x00, 100)
	out, err := (&btcUtxosAddrList{}).Run(in, common.Hash{})
	require.NoError(t, err)
	require.NotEmpty(t, out)

	count := int(out[0])
	require.Equal(t, numBlocks, count, "btcUtxosAddrList must report one coinbase UTXO per synthetic block")
	require.Len(t, out, 1+count*(32+2+8), "the UTXO list framing must be count || count*(txid32+index2+value8)")

	// The reported per-UTXO ids must be EXACTLY the set of coinbase txids — not three copies of one UTXO. Each
	// coinbase has a distinct txid (distinct BIP34 height + extra-nonce), so a backend returning the same UTXO N
	// times, or mis-identifying which UTXO, is caught here (the value+index fields alone are identical across all three).
	wantTxids := map[chainhash.Hash]bool{}
	for _, b := range blocks {
		wantTxids[b.Transactions[0].TxHash()] = true
	}
	gotTxids := map[chainhash.Hash]bool{}
	for i := 0; i < count; i++ {
		base := 1 + i*(32+2+8)
		var txid chainhash.Hash
		copy(txid[:], reverseBytes(out[base:base+32])) // the precompile emits the txid reversed (display order)
		gotTxids[txid] = true
		require.Equal(t, uint16(0), binary.BigEndian.Uint16(out[base+32:base+34]), "each coinbase pays output index 0")
		require.Equal(t, uint64(coinbaseValue), binary.BigEndian.Uint64(out[base+34:base+42]), "each reported UTXO must carry the coinbase value")
	}
	require.Equal(t, wantTxids, gotTxids, "the reported UTXO id set must be exactly the distinct coinbase txids")

	// An unfunded address reports zero UTXOs (count byte 0), proving the lookup is real.
	_, otherAddr := regtestP2PKH(t, 0x11)
	zeroIn := append([]byte(otherAddr), 0x00, 0x00, 0x00, 100)
	zeroOut, err := (&btcUtxosAddrList{}).Run(zeroIn, common.Hash{})
	require.NoError(t, err)
	require.Equal(t, byte(0), zeroOut[0], "an unfunded address must report zero UTXOs")
}

// TestSyntheticFullNodeTxByTxid drives the btcTxByTxid precompile. With the includeContainingBlock bitflag set, the
// response leads with the reversed hash of the block that contains the tx. Querying block 1's coinbase txid must
// return block 1's hash; an unknown txid returns the (nil,nil) not-found result.
func TestSyntheticFullNodeTxByTxid(t *testing.T) {
	setupSyntheticFullNode(t)

	script, _ := regtestP2PKH(t, 0x42)
	blocks := feedSyntheticChain(t, 3, script, int64(50*1e8))

	// Query EACH block's coinbase so the txid->containing-block mapping must vary with the input: a regression
	// returning a fixed block for any txid would pass if we only ever checked block[0].
	for i, blk := range blocks {
		txid := blk.Transactions[0].TxHash()
		// Input: reversed txid(32) || bitflag1..4. bitflag1=0x40 sets includeContainingBlock (0x01<<6).
		in := append(reverseBytes(txid[:]), 0x40, 0x00, 0x00, 0x00)
		out, err := (&btcTxByTxid{}).Run(in, common.Hash{})
		require.NoError(t, err)
		require.Len(t, out, 32, "with only includeContainingBlock set, the response is the 32-byte containing block hash")
		wantBlock := blk.Header.BlockHash()
		require.Equal(t, wantBlock[:], reverseBytes(out), "btcTxByTxid must report the block containing block %d's coinbase", i+1)
	}

	// An unknown txid: the precompile returns (nil,nil) rather than erroring/panicking.
	unknown := make([]byte, 36)
	unknown[0] = 0xDE
	unknown[32] = 0x40
	missing, err := (&btcTxByTxid{}).Run(unknown, common.Hash{})
	require.NoError(t, err)
	require.Nil(t, missing, "btcTxByTxid must return (nil,nil) for an unknown txid")
}

// TestSyntheticFullNodeTxConfirmations drives btcTxConfirmations = (bestHeight - txHeight + 1), where bestHeight comes
// from the consensus global TBCUpstreamTip and txHeight is a real BlockHashByTxId->BlockHeaderByHash lookup. We build
// 5 blocks (so the CANONICAL BlockHeaderBest is at height 5), index only to 3, and point TBCUpstreamTip at the height-3
// header — DISTINCT from BlockHeaderBest. Confirmations for blocks 1/2/3 must then be 3/2/1 (sourced from
// TBCUpstreamTip); sourcing best-height from BlockHeaderBest instead would give 5/4/3, which this distinguishes. The
// not-found and underflow EDGE behaviors are frozen at the deployed testnet3 binary's behavior for consensus compat
// and are pinned as tripwires at the end of this test, so a change to (nil,nil)/clamp-0 fails — see the
// CONSENSUS-COMPAT comments on btcTxConfirmations in contracts.go.
func TestSyntheticFullNodeTxConfirmations(t *testing.T) {
	setupSyntheticFullNode(t)

	script, _ := regtestP2PKH(t, 0x42)
	const total = 5
	const indexed = 3

	prev := &chaincfg.RegressionNetParams.GenesisBlock.Header
	blocks := make([]*wire.MsgBlock, 0, total)
	headers := make([]*wire.BlockHeader, 0, total)
	for i := 0; i < total; i++ {
		blk := mineRegtestFullBlock(t, prev, int32(i+1), script, int64(50*1e8), uint32(i)*100_000+1)
		blocks = append(blocks, blk)
		h := blk.Header
		headers = append(headers, &h)
		prev = &blocks[i].Header
	}
	_, _, _, _, err := TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: headers})
	require.NoError(t, err)
	for i, b := range blocks {
		_, err = TBCFullNode.BlockInsert(MainCtx, b)
		require.NoError(t, err, "block %d insert", i+1)
	}
	// All `total` headers are inserted, so the CANONICAL header tip (BlockHeaderBest) is at `total` (=5). Index only to
	// `indexed` (=3) so blocks 1..indexed are in the tx index and queryable. Set TBCUpstreamTip to the height-`indexed`
	// (=3) header — DISTINCT from BlockHeaderBest (=5). best-height in btcTxConfirmations must come from TBCUpstreamTip
	// (height 3), so confirmations are 3/2/1; sourcing best-height from BlockHeaderBest() would give 5/4/3. Keeping
	// TBCUpstreamTip distinct from BlockHeaderBest is essential: if they were equal (both the height-5 tip), the
	// wrong-source case would produce the same numbers and go undetected.
	idxTip := blocks[indexed-1].Header.BlockHash()
	require.NoError(t, TBCFullNode.SyncIndexersToHash(MainCtx, idxTip))
	upstream := blocks[indexed-1].Header // height `indexed` (3) — NOT the canonical best (5)
	TBCUpstreamTip = &upstream           // restored by the harness on cleanup

	for i := 0; i < indexed; i++ {
		height := i + 1
		wantConf := uint32(indexed - height + 1) // 3, 2, 1 from TBCUpstreamTip(height 3); a BlockHeaderBest source would give 5,4,3
		txid := blocks[i].Transactions[0].TxHash()
		out, err := (&btcTxConfirmations{}).Run(reversedHash(txid), common.Hash{})
		require.NoError(t, err)
		require.Len(t, out, 4)
		require.Equal(t, wantConf, binary.BigEndian.Uint32(out),
			"block %d coinbase: confirmations = TBCUpstreamTip height(%d) - txHeight(%d) + 1 = %d; a BlockHeaderBest(%d) source would give %d (discriminated)", height, indexed, height, wantConf, total, total-height+1)
	}

	// CONSENSUS-FROZEN deployed-behavior tripwires. The not-found and height>upstream edges are frozen at the deployed
	// testnet3 binary's behavior (see the CONSENSUS-COMPAT comments on btcTxConfirmations in contracts.go). We pin that
	// exact behavior — NOT the sibling precompiles' (nil,nil)/clamp-0 behavior — so that a change here fails instead of
	// silently splitting a mixed (rolling-upgrade) fleet on the first such call. DO NOT relax these to (nil,nil)/0
	// without a coordinated cutover.

	// (1) not-found: a syntactically valid 32-byte txid that is simply not in the index returns the RAW heminetwork
	// not-found error. The EVM normalizes ONLY ErrHVMInvalidPrecompileInput to (nil,nil); a raw error is a CALL failure
	// (revert + all remaining gas burned). The sibling lookup precompiles instead no-op (nil,nil); harmonizing this one
	// is a deferred consensus change. A `return nil, nil` on the BlockHashByTxId not-found path fails this.
	var unknownTxid chainhash.Hash
	for i := range unknownTxid {
		unknownTxid[i] = 0xAB
	}
	nfOut, nfErr := (&btcTxConfirmations{}).Run(reversedHash(unknownTxid), common.Hash{})
	require.Error(t, nfErr,
		"DEPLOYED-COMPAT: an unindexed txid must return a RAW error (EVM CALL failure / gas burn), NOT (nil,nil); harmonizing with the sibling precompiles is a deferred consensus change")
	require.Nil(t, nfOut, "DEPLOYED-COMPAT: the not-found error path returns nil bytes alongside the raw error")

	// (2) height>upstream: point TBCUpstreamTip BELOW a queried tx's height (upstream=height 1, tx=height `indexed`=3;
	// block3's coinbase is still in the tx index — we indexed to height 3). btcTxConfirmations computes
	// uint32(heightBest-height+1) with both operands uint64, so heightBest-height UNDERFLOWS and the uint32 cast emits a
	// wrapped count (== 0xFFFFFFFF here). We pin that exact wrapped value, NOT a clamp-to-0. A clamp would fail this.
	upstreamH := 1                    // runtime ints (NOT const) so the underflow below is computed at runtime, matching production,
	txH := indexed                    // 3        rather than being rejected as a compile-time constant-overflow.
	low := blocks[upstreamH-1].Header // height 1 — DISTINCT from (and below) the tx's height
	TBCUpstreamTip = &low             // restored by the harness on cleanup
	hb, h := uint64(upstreamH), uint64(txH)
	wantWrapped := uint32(hb - h + 1) // deliberate uint64 underflow at RUNTIME, then uint32 cast (== 0xFFFFFFFF here)
	uOut, uErr := (&btcTxConfirmations{}).Run(reversedHash(blocks[txH-1].Transactions[0].TxHash()), common.Hash{})
	require.NoError(t, uErr)
	require.Len(t, uOut, 4)
	require.Equal(t, wantWrapped, binary.BigEndian.Uint32(uOut),
		"DEPLOYED-COMPAT: tx height(%d) above TBCUpstreamTip(%d) must emit the uint64-underflow wrapped count uint32(%d)=%#x, NOT a clamp-to-0; clamping is a deferred consensus change", txH, upstreamH, int64(upstreamH-txH+1), wantWrapped)
	require.NotEqual(t, uint32(0), binary.BigEndian.Uint32(uOut),
		"DEPLOYED-COMPAT: the underflow path must NOT clamp to 0 (a clamp would diverge from the deployed binary)")
}

// TestSyntheticFullNodeAddrToScript drives btcAddrToScript, which decodes a Bitcoin address against tbcChainParams
// (set by SetupTBCFullNode for localnet) and returns its pay-to-address script. The output must equal the script we
// independently derive for the same regtest P2PKH address. (This precompile reads tbcChainParams, not indexed data,
// but the assertion confirms SetupTBCFullNode wired the params and the precompile honors them.)
func TestSyntheticFullNodeAddrToScript(t *testing.T) {
	setupSyntheticFullNode(t)

	wantScript, addrStr := regtestP2PKH(t, 0x42)
	out, err := (&btcAddrToScript{}).Run([]byte(addrStr), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, wantScript, out, "btcAddrToScript must return the regtest P2PKH pay-to-address script")
}

// TestSyntheticFullNodePrecompileInputGuards pins the malformed-input REJECTION contracts the happy-path tests never
// hit: every fixed-width precompile must reject a wrong-length input with ErrHVMInvalidPrecompileInput (the guard that
// sits before the panicking input[0:32] copies / index math), and the address precompiles must surface a decode error
// for a well-sized-but-invalid address rather than crashing. A regression loosening any guard turns a malformed call
// into a consensus-halting panic with zero signal otherwise.
func TestSyntheticFullNodePrecompileInputGuards(t *testing.T) {
	setupSyntheticFullNode(t)

	// Wrong-length inputs -> ErrHVMInvalidPrecompileInput (no full-node access happens; the length guard returns first).
	for _, tc := range []struct {
		name string
		run  func([]byte) ([]byte, error)
		in   []byte
	}{
		{"btcTxConfirmations 31!=32", func(b []byte) ([]byte, error) { return (&btcTxConfirmations{}).Run(b, common.Hash{}) }, make([]byte, 31)},
		{"btcHeaderN 3!=4", func(b []byte) ([]byte, error) { return (&btcHeaderN{}).Run(b, common.Hash{}) }, make([]byte, 3)},
		{"btcTxByTxid 35!=36", func(b []byte) ([]byte, error) { return (&btcTxByTxid{}).Run(b, common.Hash{}) }, make([]byte, 35)},
		{"btcInputByTxid 35!=36", func(b []byte) ([]byte, error) { return (&btcInputByTxid{}).Run(b, common.Hash{}) }, make([]byte, 35)},
		{"btcOutputByTxid 35!=36", func(b []byte) ([]byte, error) { return (&btcOutputByTxid{}).Run(b, common.Hash{}) }, make([]byte, 35)},
		{"btcTxGetInputWitness 37!=38", func(b []byte) ([]byte, error) { return (&btcTxGetInputWitness{}).Run(b, common.Hash{}) }, make([]byte, 37)},
		{"btcBalAddr too short", func(b []byte) ([]byte, error) { return (&btcBalAddr{}).Run(b, common.Hash{}) }, make([]byte, 5)},
		{"btcUtxosAddrList too short", func(b []byte) ([]byte, error) { return (&btcUtxosAddrList{}).Run(b, common.Hash{}) }, make([]byte, 5)},
		{"btcAddrToScript too short", func(b []byte) ([]byte, error) { return (&btcAddrToScript{}).Run(b, common.Hash{}) }, make([]byte, 5)},
		// EXACT boundary probes (length == threshold-1) so a threshold-LOWERING mutation on the min-length guards is
		// caught — a far-below length like 5 would still be rejected after such a mutation, but threshold-1 would not.
		{"btcBalAddr boundary MIN-1", func(b []byte) ([]byte, error) { return (&btcBalAddr{}).Run(b, common.Hash{}) }, make([]byte, MIN_BTC_ADDRESS_LENGTH-1)},
		{"btcAddrToScript boundary MIN-1", func(b []byte) ([]byte, error) { return (&btcAddrToScript{}).Run(b, common.Hash{}) }, make([]byte, MIN_BTC_ADDRESS_LENGTH-1)},
		{"btcUtxosAddrList boundary MIN+4-1", func(b []byte) ([]byte, error) { return (&btcUtxosAddrList{}).Run(b, common.Hash{}) }, make([]byte, MIN_BTC_ADDRESS_LENGTH+4-1)},
	} {
		t.Run(tc.name, func(t *testing.T) {
			_, err := tc.run(tc.in)
			require.ErrorIs(t, err, ErrHVMInvalidPrecompileInput, "%s must reject malformed input", tc.name)
		})
	}

	// A well-sized but undecodable address -> a non-nil decode error (not a panic, not a silent script).
	junk := bytes.Repeat([]byte{'z'}, 30) // >= MIN_BTC_ADDRESS_LENGTH but not a valid address
	_, err := (&btcAddrToScript{}).Run(junk, common.Hash{})
	require.Error(t, err, "btcAddrToScript must surface a decode error for an invalid address")
}

// TestSyntheticFullNodeHeaderNLibraryLimitation pins a defect in the heminetwork library that makes the btcHeaderN
// precompile (BTC Header N, 0x45) NON-FUNCTIONAL with the pinned version (v1.6.4-0.20250716150413). btcHeaderN gates
// each candidate header on TBCFullNode.BlockInTxIndex, but the tx indexer's writer (level.BlockTxUpdate) stores a
// 33-byte block marker key ('b' || blockHash) while the reader (level.BlockInTxIndex) slices it.Key()[33:] expecting a
// 32-byte trailing hash. The trailing slice is empty, so chainhash.NewHash errors with "invalid hash length of 0, want
// 32" for EVERY block — BlockInTxIndex can never return true, so btcHeaderN always returns (nil,nil) even though the
// header data and the UTXO/Tx indexes are present.
//
// This is deterministic (every node runs the same library), so it is consensus-SAFE — all nodes agree on the nil
// result — but the precompile is functionally dead: a contract calling btcHeaderN gets nothing. The data it should
// return IS available (BlockHeadersByHeight resolves the header directly), confirming the fault is solely in the
// BlockInTxIndex marker-length mismatch, not in the synthetic feed.
//
// TRIPWIRE: this asserts the current (broken) behavior. If a heminetwork upgrade fixes BlockInTxIndex, the
// BlockInTxIndex/btcHeaderN assertions below start failing — at which point btcHeaderN should be re-tested for correct
// framing (mirroring the btcLastHeader assertions) and this limitation note removed.
func TestSyntheticFullNodeHeaderNLibraryLimitation(t *testing.T) {
	setupSyntheticFullNode(t)

	script, _ := regtestP2PKH(t, 0x42)
	const numBlocks = 4
	blocks := feedSyntheticChain(t, numBlocks, script, int64(50*1e8))

	// The header data IS present and correct: BlockHeadersByHeight resolves height 2 to our second block directly.
	headers, err := TBCFullNode.BlockHeadersByHeight(MainCtx, 2)
	require.NoError(t, err)
	require.NotEmpty(t, headers, "the header at height 2 must exist in the full node")
	wantHash := blocks[1].Header.BlockHash()
	found := false
	for _, h := range headers {
		if h.BlockHash() == wantHash {
			found = true
		}
	}
	require.True(t, found, "BlockHeadersByHeight(2) must include our synthetic block at height 2")

	// But BlockInTxIndex — btcHeaderN's canonical gate — errors on the library's marker-length mismatch...
	_, err = TBCFullNode.BlockInTxIndex(MainCtx, wantHash)
	require.Error(t, err, "pinned heminetwork BlockInTxIndex is defective; if this passes, a newer library has fixed it — re-enable btcHeaderN")
	require.Contains(t, err.Error(), "invalid hash length", "the defect is the 33-byte marker vs 32-byte tail slice")

	// ...so the btcHeaderN precompile returns (nil,nil) for a height whose header demonstrably exists.
	in := make([]byte, 4)
	binary.BigEndian.PutUint32(in, 2)
	out, err := (&btcHeaderN{}).Run(in, common.Hash{})
	require.NoError(t, err)
	require.Nil(t, out, "btcHeaderN is non-functional with the pinned heminetwork (BlockInTxIndex defect)")
}

// TestSyntheticBlockBuilderProducesConsensusValidBlocks is a positive control on the synthetic block builder itself.
// Nothing in the in-process insert/index path validates proof-of-work or the merkle root (tbc's CheckBlockSanity is
// gated behind the disabled P2P handleBlock), so without this control a builder regression (e.g. a flipped PoW loop
// comparison or a dropped merkle-root assignment) would silently produce consensus-INVALID blocks that still link,
// index, and answer identically in every other test — undermining the suite's "faithful to real blocks" premise.
func TestSyntheticBlockBuilderProducesConsensusValidBlocks(t *testing.T) {
	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header
	pkScript, _ := regtestP2PKH(t, 0x42)
	blk := mineRegtestFullBlock(t, genesis, 1, pkScript, int64(50*1e8), 1)

	require.NoError(t, blockchain.CheckProofOfWork(btcutil.NewBlock(blk), chaincfg.RegressionNetParams.PowLimit),
		"the builder must mine valid regtest proof-of-work (independent of the PoW loop's own comparison)")

	merkles := blockchain.BuildMerkleTreeStore([]*btcutil.Tx{btcutil.NewTx(blk.Transactions[0])}, false)
	require.Equal(t, *merkles[len(merkles)-1], blk.Header.MerkleRoot,
		"the builder must set the header merkle root from its transactions")
}

// TestSyntheticFullNodePrecompileQueryCache guards the query-cache key in contracts.go against a shadowing regression:
// if a precompile declares `var k hVMQueryKey` and then inside `if isValidBlock(blockContext)` writes
// `k, err := calculateHVMQueryKey(...)`, the `:=` REDECLARES k in the if-scope, so the cache WRITE `hvmQueryMap[k]`
// lands under the outer zero-value key while the READ uses the correctly-computed key — the cache never hits and every
// entry collides on key{}. Other tests cannot catch this because they pass common.Hash{} (isValidBlock==false,
// caching disabled). This test exercises the cache with a NON-null blockContext and asserts the write lands under the
// correct key, the read consults it, and distinct block contexts do not collide. With the shadow bug it fails at the
// first cache-key assertion (result stored under the zero key, lookup at the computed key misses).
func TestSyntheticFullNodePrecompileQueryCache(t *testing.T) {
	setupSyntheticFullNode(t)

	scriptA, addrA := regtestP2PKH(t, 0x42)
	scriptB, _ := regtestP2PKH(t, 0x33)
	const fund = int64(50 * 1e8)

	// Fixture: block1 coinbase->A; block2 coinbase->A + a spend T (so the input/output/witness precompiles are
	// answerable). Index to block2 and set the upstream tip (for btcTxConfirmations).
	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header
	cb1 := buildRegtestCoinbase(t, 1, scriptA, fund, 1)
	block1 := mineRegtestBlockWithTxs(t, genesis, []*wire.MsgTx{cb1}, 7_001)
	cb1Txid := cb1.TxHash()
	cb2 := buildRegtestCoinbase(t, 2, scriptA, int64(25*1e8), 2)
	spend := wire.NewMsgTx(wire.TxVersion)
	spend.AddTxIn(&wire.TxIn{PreviousOutPoint: wire.OutPoint{Hash: cb1Txid, Index: 0}, SignatureScript: []byte{0x51}, Witness: wire.TxWitness{{0xaa, 0xbb}}, Sequence: 0xffffffff})
	spend.AddTxOut(&wire.TxOut{Value: int64(30 * 1e8), PkScript: scriptB})
	spend.AddTxOut(&wire.TxOut{Value: int64(19 * 1e8), PkScript: scriptA})
	spendTxid := spend.TxHash()
	block2 := mineRegtestBlockWithTxs(t, &block1.Header, []*wire.MsgTx{cb2, spend}, 8_001)
	h1, h2 := block1.Header, block2.Header
	_, _, _, _, err := TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&h1, &h2}})
	require.NoError(t, err)
	for _, b := range []*wire.MsgBlock{block1, block2} {
		_, e := TBCFullNode.BlockInsert(MainCtx, b)
		require.NoError(t, e)
	}
	require.NoError(t, TBCFullNode.SyncIndexersToHash(MainCtx, block2.Header.BlockHash()))
	upstream := block2.Header
	TBCUpstreamTip = &upstream

	blockCtx := common.HexToHash("0x01") // non-null -> isValidBlock true -> caching active

	// Drive EVERY cache-bearing precompile (the shadow pattern is per-site identical, so a re-shadow at any one site
	// must be caught). btcHeaderN is excluded: it returns nil under the pinned heminetwork defect, so its cache WRITE is
	// dead and unreachable. Each case: clear cache, run with a non-null blockContext, then assert the result is stored
	// under the COMPUTED key (not key{}), and the read consults that key (poison-and-reread).
	cases := []struct {
		name string
		p    PrecompiledContract
		in   []byte
	}{
		{"btcBalAddr", &btcBalAddr{}, []byte(addrA)},
		{"btcUtxosAddrList", &btcUtxosAddrList{}, append([]byte(addrA), 0x00, 0x00, 0x00, 100)},
		{"btcAddrToScript", &btcAddrToScript{}, []byte(addrA)},
		{"btcLastHeader", &btcLastHeader{}, nil},
		{"btcTxByTxid", &btcTxByTxid{}, append(reversedHash(cb1Txid), 0x40, 0x00, 0x00, 0x00)},
		{"btcTxConfirmations", &btcTxConfirmations{}, reversedHash(cb1Txid)},
		{"btcInputByTxid", &btcInputByTxid{}, append(reversedHash(spendTxid), 0x00, 0x00, 0x03, 0xE8)},
		{"btcOutputByTxid", &btcOutputByTxid{}, append(reversedHash(spendTxid), 0x00, 0x00, 0x01, 0x00)},
		{"btcTxGetInputWitness", &btcTxGetInputWitness{}, append(reversedHash(spendTxid), 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF)},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			for k := range hvmQueryMap {
				delete(hvmQueryMap, k)
			}
			resp, err := tc.p.Run(tc.in, blockCtx)
			require.NoError(t, err)
			require.NotNil(t, resp, "%s must return data to populate the cache", tc.name)

			addrByte := hvmContractsToAddress[reflect.TypeOf(tc.p)][0]
			k, err := calculateHVMQueryKey(tc.in, addrByte, blockCtx)
			require.NoError(t, err)
			cached, ok := hvmQueryMap[k]
			require.True(t, ok, "%s must cache under the computed key (a re-shadow stores under key{})", tc.name)
			require.Equal(t, resp, cached, "%s cached bytes must equal the result", tc.name)
			var zero hVMQueryKey
			_, zeroExists := hvmQueryMap[zero]
			require.False(t, zeroExists, "%s must not write under the zero key", tc.name)

			sentinel := []byte{0xDE, 0xAD, 0xBE, 0xEF}
			hvmQueryMap[k] = sentinel
			resp2, err := tc.p.Run(tc.in, blockCtx)
			require.NoError(t, err)
			require.Equal(t, sentinel, resp2, "%s repeat call must return the cached entry", tc.name)
		})
	}

	// Cross-context: a DIFFERENT blockContext computes a DIFFERENT key, so it must not hit a poisoned entry from the
	// first context — pinning that the cache key incorporates the block context (no cross-context collision).
	for k := range hvmQueryMap {
		delete(hvmQueryMap, k)
	}
	resp1, err := (&btcBalAddr{}).Run([]byte(addrA), blockCtx)
	require.NoError(t, err)
	k, err := calculateHVMQueryKey([]byte(addrA), hvmContractsToAddress[reflect.TypeOf(&btcBalAddr{})][0], blockCtx)
	require.NoError(t, err)
	hvmQueryMap[k] = []byte{0x00}
	resp3, err := (&btcBalAddr{}).Run([]byte(addrA), common.HexToHash("0x02"))
	require.NoError(t, err)
	require.NotEqual(t, []byte{0x00}, resp3, "a different blockContext must not collide with the poisoned key")
	require.Equal(t, resp1, resp3, "the recomputed result for a fresh context equals the real balance")
}

// TestSyntheticFullNodeUtxosPagination exercises btcUtxosAddrList's pagination, which every other test left dead by
// hard-coding page 0 / pageSize 100 against a single-page result. The precompile forwards the 3-byte big-endian page
// as the leveldb `start` offset and the 1-byte pageSize as `count` (pageSize 0 -> default 10). With 3 UTXOs on one
// address this pins: the start offset is honored (and non-overlapping), the count limits the page, the pageSize==0
// default returns the full small set, and the high page byte (bit 16) reaches the offset.
func TestSyntheticFullNodeUtxosPagination(t *testing.T) {
	setupSyntheticFullNode(t)
	script, addrStr := regtestP2PKH(t, 0x42)
	feedSyntheticChain(t, 3, script, int64(50*1e8)) // 3 coinbase UTXOs to one address

	// returns (count, set-of-reversed-txids) for page offset `pg` and `pgSize`.
	page := func(pg uint32, pgSize byte) (int, map[chainhash.Hash]bool) {
		in := append([]byte(addrStr), byte(pg>>16), byte(pg>>8), byte(pg), pgSize)
		out, err := (&btcUtxosAddrList{}).Run(in, common.Hash{})
		require.NoError(t, err)
		n := int(out[0])
		ids := map[chainhash.Hash]bool{}
		for i := 0; i < n; i++ {
			base := 1 + i*(32+2+8)
			var id chainhash.Hash
			copy(id[:], reverseBytes(out[base:base+32]))
			ids[id] = true
		}
		return n, ids
	}

	n0, set0 := page(0, 2)
	require.Equal(t, 2, n0, "offset 0, size 2 -> first 2 of 3 UTXOs")
	n2, set2 := page(2, 2)
	require.Equal(t, 1, n2, "offset 2, size 2 -> the remaining 1 UTXO (start offset honored)")
	for id := range set2 {
		require.False(t, set0[id], "the offset-2 page must not overlap the offset-0 page")
	}
	nDefault, _ := page(0, 0)
	require.Equal(t, 3, nDefault, "pageSize 0 -> default 10 -> all 3 UTXOs (pgSize==0 default branch)")
	nHigh, _ := page(1<<16, 10)
	// NB: with only 3 UTXOs this proves the high byte is READ (a "drop the high byte" mutation would offset 0 and return
	// 3, not 0) — it does NOT pin the exact <<16 weight (a <<16->><<8 mutation also offsets past the set -> 0). Pinning
	// the weight would need >256 funded UTXOs (256+ mined blocks), which isn't worth the runtime here.
	require.Equal(t, 0, nHigh, "a page offset with the high byte set -> 0 UTXOs (the high page byte is read into the offset)")
}

// Deep btcTxByTxid bitflag coverage. btcTxByTxid is a bitflag-driven serializer; this exercises every branch
// an hVM contract can observe (hash reversal, field widths, full-vs-stripped size order, unspendable-output
// accounting, the bit6 witness-array-size alias, count/script chopping) against a fixture tx T: two
// distinct-value inputs with distinct scriptSigs/sequences/witness counts, and three outputs including one
// OP_RETURN. A cursor decoder checks the response frame field-by-field.
// cur is a tiny big-endian cursor reader for decoding precompile response frames field-by-field.
type cur struct {
	t *testing.T
	b []byte
	i int
}

func (c *cur) u16() uint16 {
	c.t.Helper()
	v := binary.BigEndian.Uint16(c.b[c.i : c.i+2])
	c.i += 2
	return v
}
func (c *cur) u32() uint32 {
	c.t.Helper()
	v := binary.BigEndian.Uint32(c.b[c.i : c.i+4])
	c.i += 4
	return v
}
func (c *cur) u64() uint64 {
	c.t.Helper()
	v := binary.BigEndian.Uint64(c.b[c.i : c.i+8])
	c.i += 8
	return v
}
func (c *cur) take(n int) []byte { c.t.Helper(); v := c.b[c.i : c.i+n]; c.i += n; return v }
func (c *cur) end() {
	c.t.Helper()
	require.Equal(c.t, len(c.b), c.i, "no trailing bytes in the frame")
}

func TestSyntheticFullNodeDeepTxByTxidBitflags(t *testing.T) {
	setupSyntheticFullNode(t)

	scriptA, _ := regtestP2PKH(t, 0x42)
	scriptB, _ := regtestP2PKH(t, 0x33)
	scriptD, _ := regtestP2PKH(t, 0x99)
	opReturn, err := txscript.NullDataScript([]byte("hvm"))
	require.NoError(t, err)

	const fund1 = int64(50 * 1e8)
	const fund2 = int64(25 * 1e8)
	const outB = int64(30 * 1e8)
	const change = int64(40 * 1e8)

	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header
	cb1 := buildRegtestCoinbase(t, 1, scriptA, fund1, 1)
	block1 := mineRegtestBlockWithTxs(t, genesis, []*wire.MsgTx{cb1}, 60_001)
	cb1Txid := cb1.TxHash()
	cb2 := buildRegtestCoinbase(t, 2, scriptA, fund2, 2)
	block2 := mineRegtestBlockWithTxs(t, &block1.Header, []*wire.MsgTx{cb2}, 61_001)
	cb2Txid := cb2.TxHash()

	sig0, wit0, seq0 := bytes.Repeat([]byte{0x51}, 20), wire.TxWitness{{0xaa, 0xbb}, {0xcc}}, uint32(0xfffffffe) // 20-byte sig so the deep script-chop is reachable
	sig1, wit1, seq1 := []byte{0x61, 0x62}, wire.TxWitness{{0x11}, {0x22, 0x23}, {0x33, 0x34, 0x35}}, uint32(0xfffffffd)
	T := wire.NewMsgTx(wire.TxVersion)
	T.AddTxIn(&wire.TxIn{PreviousOutPoint: wire.OutPoint{Hash: cb1Txid, Index: 0}, SignatureScript: sig0, Witness: wit0, Sequence: seq0})
	T.AddTxIn(&wire.TxIn{PreviousOutPoint: wire.OutPoint{Hash: cb2Txid, Index: 0}, SignatureScript: sig1, Witness: wit1, Sequence: seq1})
	T.AddTxOut(&wire.TxOut{Value: outB, PkScript: scriptB})   // output 0: spendable -> B
	T.AddTxOut(&wire.TxOut{Value: 0, PkScript: opReturn})     // output 1: UNSPENDABLE (OP_RETURN)
	T.AddTxOut(&wire.TxOut{Value: change, PkScript: scriptA}) // output 2: spendable -> A
	tTxid := T.TxHash()
	block3 := mineRegtestBlockWithTxs(t, &block2.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 3, scriptD, int64(10*1e8), 3), T}, 62_001)

	h1, h2, h3 := block1.Header, block2.Header, block3.Header
	_, _, _, _, err = TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&h1, &h2, &h3}})
	require.NoError(t, err)
	for _, b := range []*wire.MsgBlock{block1, block2, block3} {
		_, e := TBCFullNode.BlockInsert(MainCtx, b)
		require.NoError(t, e)
	}
	require.NoError(t, TBCFullNode.SyncIndexersToHash(MainCtx, block3.Header.BlockHash()))

	run := func(bf1, bf2, bf3, bf4 byte) *cur {
		t.Helper()
		out, err := (&btcTxByTxid{}).Run(append(reversedHash(tTxid), bf1, bf2, bf3, bf4), common.Hash{})
		require.NoError(t, err)
		return &cur{t: t, b: out}
	}

	// (A) Header fields: includeVersion(0x20)|includeSizes(0x10)|includeLockTime(0x08) -> version, size, strippedSize, lockTime.
	a := run(0x38, 0x00, 0x00, 0x00)
	require.Equal(t, uint32(T.Version), a.u32(), "version")
	require.Equal(t, uint32(T.SerializeSize()), a.u32(), "serialize size (with witness)")
	require.Equal(t, uint32(T.SerializeSizeStripped()), a.u32(), "stripped serialize size (no witness) — must differ from full size")
	require.NotEqual(t, T.SerializeSize(), T.SerializeSizeStripped(), "fixture must be segwit so the two size fields are distinguishable")
	require.Equal(t, T.LockTime, a.u32(), "lock time")
	a.end()

	// (B) Inputs deep: includeInputs(0x04)|includeInputSource(0x02)|includeInputScriptSig(0x01) + includeInputSeq(bf2 0x80),
	//     maxInputs=2 (bf3 0x08), maxInputScriptSigSize=32 (bf4 0x04 -> 2^(4+1) >= the 20-byte sig0, so NO chop here).
	//     Per input: value||revPrevHash||prevIdx(uint32)||sigLen||sig||seq.
	b := run(0x07, 0x80, 0x08, 0x04)
	require.Equal(t, uint16(2), b.u16(), "txInLen")
	for idx, in := range []struct {
		value int64
		prev  chainhash.Hash
		sig   []byte
		seq   uint32
	}{{fund1, cb1Txid, sig0, seq0}, {fund2, cb2Txid, sig1, seq1}} {
		require.Equal(t, uint64(in.value), b.u64(), "input %d value (via source-tx lookup)", idx)
		require.Equal(t, in.prev[:], reverseBytes(b.take(32)), "input %d reversed prev hash", idx)
		require.Equal(t, uint32(0), b.u32(), "input %d prevout index (FULL uint32 in the deep path, vs btcInputByTxid's uint16)", idx)
		sl := b.u16()
		require.Equal(t, uint16(len(in.sig)), sl, "input %d sig len", idx)
		require.Equal(t, in.sig, b.take(int(sl)), "input %d scriptSig", idx)
		require.Equal(t, in.seq, b.u32(), "input %d sequence", idx)
	}
	b.end()

	// (C) bit6 alias: includeContainingBlock(0x40)|includeInputs(0x04). bit6 ALSO enables includeWitnessArraySize, so each
	//     input emits a witness-count word. Frame: revBlockHash(32) || txInLen(2) || per input [witCount(2) || value(8)].
	c := run(0x44, 0x00, 0x08, 0x00)
	block3Hash := block3.Header.BlockHash()
	require.Equal(t, block3Hash[:], reverseBytes(c.take(32)), "containing block hash")
	require.Equal(t, uint16(2), c.u16(), "txInLen")
	require.Equal(t, uint16(len(wit0)), c.u16(), "input 0 witness-array size (bit6 alias)")
	require.Equal(t, uint64(fund1), c.u64(), "input 0 value")
	require.Equal(t, uint16(len(wit1)), c.u16(), "input 1 witness-array size")
	require.Equal(t, uint64(fund2), c.u64(), "input 1 value")
	c.end()

	// (D) Outputs with script, default (EXCLUDE unspendable): includeOutputs(0x20)|includeOutputScript(0x10), maxOutputs=2
	//     (bf3 0x01), maxOutputScriptSize=32 (bf4 0x01 -> 2^(4+1) >= 25). outLen must be 2 (the OP_RETURN is excluded).
	d := run(0x00, 0x30, 0x01, 0x01)
	require.Equal(t, uint16(2), d.u16(), "outLen excludes the unspendable OP_RETURN output")
	for idx, o := range []struct {
		value  int64
		script []byte
	}{{outB, scriptB}, {change, scriptA}} { // out0 and out2; out1 (OP_RETURN) skipped
		require.Equal(t, uint64(o.value), d.u64(), "spendable output %d value", idx)
		sl := d.u16()
		require.Equal(t, uint16(len(o.script)), sl, "spendable output %d pkScript len", idx)
		require.Equal(t, o.script, d.take(int(sl)), "spendable output %d pkScript", idx)
	}
	d.end()

	// (E) Outputs INCLUDING unspendable: add includeUnspendableOutputs(0x08), maxOutputs=4 (bf3 0x02). outLen must be 3
	//     and the OP_RETURN output (value 0) appears in its real position (index 1).
	e := run(0x00, 0x38, 0x02, 0x01)
	require.Equal(t, uint16(3), e.u16(), "outLen INCLUDES the unspendable output")
	for idx, o := range []struct {
		value  int64
		script []byte
	}{{outB, scriptB}, {0, opReturn}, {change, scriptA}} {
		require.Equal(t, uint64(o.value), e.u64(), "output %d value", idx)
		sl := e.u16()
		require.Equal(t, uint16(len(o.script)), sl, "output %d pkScript len", idx)
		require.Equal(t, o.script, e.take(int(sl)), "output %d pkScript", idx)
	}
	e.end()

	// (F) Output COUNT-chop: includeOutputs only, maxOutputs=1 (bf3 0x00). outLen reports the FULL spendable count (2)
	//     while only 1 output entry (value, no script) is emitted.
	f := run(0x00, 0x20, 0x00, 0x00)
	require.Equal(t, uint16(2), f.u16(), "outLen reports the FULL spendable count even though chopped")
	require.Equal(t, uint64(outB), f.u64(), "only the first spendable output is emitted")
	f.end()

	// (G) INPUT script-chop (deep path): includeInputs|includeInputScriptSig (bf1 0x05), maxInputs=2 (bf3 0x08),
	//     maxInputScriptSigSize=16 (bf4 0x00 -> 2^(4+0)). input 0's sig is 20 bytes -> sigLen word reports 20 (FULL)
	//     but only 16 bytes are appended; input 1's 2-byte sig is unchopped. Per input here: value(8)||sigLen(2)||sig.
	g := run(0x05, 0x00, 0x08, 0x00)
	require.Equal(t, uint16(2), g.u16(), "txInLen")
	require.Equal(t, uint64(fund1), g.u64(), "input 0 value")
	require.Equal(t, uint16(len(sig0)), g.u16(), "input 0 sigLen word reports the FULL 20-byte length")
	require.Equal(t, sig0[:16], g.take(16), "input 0 emits only maxInputScriptSigSize(16) chopped bytes")
	require.Equal(t, uint64(fund2), g.u64(), "input 1 value")
	require.Equal(t, uint16(len(sig1)), g.u16(), "input 1 sigLen word (unchopped, 2 bytes)")
	require.Equal(t, sig1, g.take(len(sig1)), "input 1 full sig (under the cap)")
	g.end()

	// (H) OUTPUT script-chop (deep path): includeOutputs|includeOutputScript (bf2 0x30), maxOutputs=2 (bf3 0x01),
	//     maxOutputScriptSize=16 (bf4 0x00). The 25-byte P2PKH pkScript -> pkScriptLen word reports 25 (FULL) but only
	//     16 bytes appended. Per output: value(8)||pkScriptLen(2)||script.
	h := run(0x00, 0x30, 0x01, 0x00)
	require.Equal(t, uint16(2), h.u16(), "outLen (spendable)")
	require.Equal(t, uint64(outB), h.u64(), "output 0 value")
	require.Equal(t, uint16(len(scriptB)), h.u16(), "output 0 pkScriptLen word reports the FULL 25-byte length")
	require.Equal(t, scriptB[:16], h.take(16), "output 0 emits only maxOutputScriptSize(16) chopped bytes")
	require.Equal(t, uint64(change), h.u64(), "output 1 (A change) value")
	require.Equal(t, uint16(len(scriptA)), h.u16(), "output 1 pkScriptLen word (FULL)")
	require.Equal(t, scriptA[:16], h.take(16), "output 1 emits only 16 chopped bytes")
	h.end()
}

// Build-path prefetch decision: vm.TBCBlocksAvailableToHeader is the consensus build/apply path's gate for
// deciding whether the full node already holds every full block needed to index up to a target header, or whether
// blocks must be prefetched first (core/blockchain.go:1969, :3098 feed its result into TBCAttemptBlockRefetch). It was
// only ever reachable with a live indexed full node, so prior tests skipped it (see blockchain_hvm_corrupt_test.go:656
// "that needs a live vm.TBCFullNode"). With the synthetic full node we can drive its three outcomes directly:
//   - every full block present                  -> (true,  nil,            nil,        nil)
//   - headers present but full blocks missing    -> (false, &missingList,   nil,        nil)
//   - a target header the node never saw         -> (false, nil,            &hash,      nil)
//
// (TBCAttemptBlockRefetch itself is NOT covered here: it calls DownloadBlockFromRandomPeers, a P2P operation with no
// peers in this harness, which belongs to live-network testing.)
func TestSyntheticFullNodeBlocksAvailableToHeader(t *testing.T) {
	setupSyntheticFullNode(t)

	script, _ := regtestP2PKH(t, 0x42)
	const val = int64(50 * 1e8)
	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header

	// Build a 3-block chain h1->h2->h3 over genesis. The index stays at genesis (we never SyncIndexersToHash), so the
	// availability walk runs from the target header all the way back to genesis.
	h1 := mineRegtestBlockWithTxs(t, genesis, []*wire.MsgTx{buildRegtestCoinbase(t, 1, script, val, 31)}, 31_001)
	h2 := mineRegtestBlockWithTxs(t, &h1.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 2, script, val, 32)}, 32_001)
	h3 := mineRegtestBlockWithTxs(t, &h2.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 3, script, val, 33)}, 33_001)
	hashesOf := func(blks ...*wire.MsgBlock) map[chainhash.Hash]bool {
		m := make(map[chainhash.Hash]bool)
		for _, b := range blks {
			m[b.Header.BlockHash()] = true
		}
		return m
	}

	hh1, hh2, hh3 := h1.Header, h2.Header, h3.Header

	// The several not-found paths exercised below must NOT mutate the shared heminetwork database.ErrNotFound sentinel:
	// they must match with errors.Is, never errors.As(err, &database.ErrNotFound) — which would overwrite this global
	// with the specific error instance on every match. Snapshot its value now; assert it is unchanged at the end.
	errNotFoundBefore := database.ErrNotFound.Error()

	// (0) Unknown header: before inserting any headers, the node has never seen h3 -> not-found hash returned.
	avail, missing, missingHash, err := TBCBlocksAvailableToHeader(MainCtx, &hh3)
	require.NoError(t, err)
	require.False(t, avail)
	require.Nil(t, missing)
	require.NotNil(t, missingHash, "an unknown target header must surface its hash as not-found")
	require.Equal(t, hh3.BlockHash(), *missingHash)

	// Insert all three HEADERS but no full blocks yet.
	_, _, _, _, err = TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&hh1, &hh2, &hh3}})
	require.NoError(t, err)

	// (1) Headers known, zero full blocks present -> all three are missing.
	avail, missing, missingHash, err = TBCBlocksAvailableToHeader(MainCtx, &hh3)
	require.NoError(t, err)
	require.False(t, avail, "no full blocks inserted -> not available")
	require.Nil(t, missingHash, "headers exist, so this is a missing-full-block case, not a missing-header case")
	require.NotNil(t, missing)
	require.Len(t, *missing, 3, "all three full blocks are missing")
	got := make(map[chainhash.Hash]bool)
	for _, m := range *missing {
		got[m.BlockHash()] = true
	}
	require.Equal(t, hashesOf(h1, h2, h3), got, "the missing set must be exactly {h1,h2,h3}")

	// (2) Insert only h1's full block -> h2,h3 still missing.
	_, err = TBCFullNode.BlockInsert(MainCtx, h1)
	require.NoError(t, err)
	avail, missing, _, err = TBCBlocksAvailableToHeader(MainCtx, &hh3)
	require.NoError(t, err)
	require.False(t, avail)
	require.NotNil(t, missing)
	got = make(map[chainhash.Hash]bool)
	for _, m := range *missing {
		got[m.BlockHash()] = true
	}
	require.Equal(t, hashesOf(h2, h3), got, "with h1 present, only h2,h3 are missing")

	// (2b) NON-CONTIGUOUS availability: insert the TIP h3 but leave the middle h2 absent (h1,h3 present, h2 missing).
	// The backward walk from h3 must NOT early-terminate on the first available block (the tip h3) — it must keep
	// walking and report ONLY h2 missing. An "available -> stop" mutation in the walk would return avail=true (since
	// h3 is present) and never discover the h2 gap.
	_, err = TBCFullNode.BlockInsert(MainCtx, h3)
	require.NoError(t, err)
	avail, missing, _, err = TBCBlocksAvailableToHeader(MainCtx, &hh3)
	require.NoError(t, err)
	require.False(t, avail, "the middle block h2 is still missing -> not available even though the tip h3 is present")
	require.NotNil(t, missing)
	got = make(map[chainhash.Hash]bool)
	for _, m := range *missing {
		got[m.BlockHash()] = true
	}
	require.Equal(t, hashesOf(h2), got, "exactly h2 missing: the walk continued past the available tip h3 to the gap")

	// (3) Insert the remaining middle block -> everything available.
	_, err = TBCFullNode.BlockInsert(MainCtx, h2)
	require.NoError(t, err)
	avail, missing, missingHash, err = TBCBlocksAvailableToHeader(MainCtx, &hh3)
	require.NoError(t, err)
	require.True(t, avail, "all full blocks present -> available")
	require.Nil(t, missing)
	require.Nil(t, missingHash)

	// (4) A header that is an ancestor of / equal to the indexed view is trivially available. Genesis is the indexed
	// tip; asking for genesis must report available with nothing missing.
	avail, missing, missingHash, err = TBCBlocksAvailableToHeader(MainCtx, genesis)
	require.NoError(t, err)
	require.True(t, avail, "the indexed tip (genesis) is trivially available")
	require.Nil(t, missing)
	require.Nil(t, missingHash)

	// (5) OFF-GENESIS indexed tip + FORKED target: advance the indexers to h2 (non-genesis), then query availability
	// for a fork f2->f3 built on h1. This drives the path where the indexed tip and target diverge ABOVE genesis, so
	// the second FindCommonAncestor must return h1 (not genesis) and the backward walk must terminate at h1 — code
	// that every prior scenario left dead because the index never left genesis.
	require.NoError(t, TBCFullNode.SyncIndexersToHash(MainCtx, h2.Header.BlockHash()), "advance the indexers to h2")
	f2 := mineRegtestBlockWithTxs(t, &h1.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 2, script, val, 41)}, 41_001)
	f3 := mineRegtestBlockWithTxs(t, &f2.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 3, script, val, 42)}, 42_001)
	hf2, hf3 := f2.Header, f3.Header
	_, _, _, _, err = TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&hf2, &hf3}})
	require.NoError(t, err)

	// f2,f3 headers known but blocks absent -> missing == {f2,f3}; the walk stops at the common ancestor h1.
	avail, missing, missingHash, err = TBCBlocksAvailableToHeader(MainCtx, &hf3)
	require.NoError(t, err)
	require.False(t, avail, "the fork's full blocks are absent")
	require.Nil(t, missingHash, "the fork headers exist, so this is a missing-block case")
	require.NotNil(t, missing)
	got = make(map[chainhash.Hash]bool)
	for _, m := range *missing {
		got[m.BlockHash()] = true
	}
	require.Equal(t, hashesOf(f2, f3), got, "only the post-(h1)-ancestor fork blocks are missing (walk terminated at h1)")

	// Insert the fork blocks -> the fork is now fully available from the h2-indexed tip across the h1 fork point.
	_, err = TBCFullNode.BlockInsert(MainCtx, f2)
	require.NoError(t, err)
	_, err = TBCFullNode.BlockInsert(MainCtx, f3)
	require.NoError(t, err)
	avail, missing, missingHash, err = TBCBlocksAvailableToHeader(MainCtx, &hf3)
	require.NoError(t, err)
	require.True(t, avail, "with the fork blocks present, the forked target is available across the non-genesis ancestor")
	require.Nil(t, missing)
	require.Nil(t, missingHash)

	// The shared heminetwork NotFound sentinel must be byte-identical to its initial value (errors.As-mutation guard).
	require.Equal(t, errNotFoundBefore, database.ErrNotFound.Error(),
		"the not-found paths must use errors.Is and must NOT mutate the shared database.ErrNotFound global")
}

// Reorg / unwind: this covers the indexer unwind path (utxoIndexerUnwind / txIndexerUnwind) — exercised whenever
// Bitcoin reorgs and the hVM view must roll its UTXO/Tx state back to a common ancestor and re-apply the new branch.
// The forward-only synthetic chains in the sibling tests wind the indexers forward and do not exercise this path.
//
// This builds a shared NON-genesis prefix block c1 (coinbase to C), then chain A (c1->a2->a3, coinbases to A) and
// indexes to a3, then a heavier chain B (c1->b2->b3->b4, coinbases to B) that wins the canonical race on cumulative
// work (regtest has PoWNoRetargeting, so c1+3 blocks outweigh c1+2). The common ancestor is therefore c1, NOT genesis,
// which is asserted directly via FindCommonAncestor. The reorg is driven through the PRODUCTION entry point
// vm.TBCIndexToHashHeight (which finds the common ancestor and orchestrates the unwind-to-ancestor + wind-to-target; a
// single raw cross-branch SyncIndexersToHash is rejected as non-linear). It then asserts via the precompiles that
// chain A's UTXOs/txs are gone, chain B's are present, the ANCESTOR c1's UTXO survives (the unwind stopped at c1), and
// the reported tip moved a3 -> b4.
func TestSyntheticFullNodeReorgUnwind(t *testing.T) {
	setupSyntheticFullNode(t)

	scriptA, addrA := regtestP2PKH(t, 0x42)
	scriptB, addrB := regtestP2PKH(t, 0x33)
	scriptC, addrC := regtestP2PKH(t, 0x55) // funded ONLY in the shared prefix block c1 (the common ancestor)
	const vc = int64(10 * 1e8)
	const va = int64(50 * 1e8)
	const vb = int64(30 * 1e8)

	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header

	balance := func(addr string) uint64 {
		t.Helper()
		out, err := (&btcBalAddr{}).Run([]byte(addr), common.Hash{})
		require.NoError(t, err)
		return binary.BigEndian.Uint64(out)
	}
	tipHeight := func() uint32 {
		t.Helper()
		out, err := (&btcLastHeader{}).Run(nil, common.Hash{})
		require.NoError(t, err)
		return binary.BigEndian.Uint32(out[0:4])
	}
	tipHash := func() []byte {
		t.Helper()
		out, err := (&btcLastHeader{}).Run(nil, common.Hash{})
		require.NoError(t, err)
		return reverseBytes(out[4:36])
	}
	insert := func(blocks ...*wire.MsgBlock) tbcd.InsertType {
		t.Helper()
		hdrs := make([]*wire.BlockHeader, len(blocks))
		for i, b := range blocks {
			h := b.Header
			hdrs[i] = &h
		}
		it, _, _, _, err := TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: hdrs})
		require.NoError(t, err)
		for _, b := range blocks {
			_, err = TBCFullNode.BlockInsert(MainCtx, b)
			require.NoError(t, err)
		}
		return it
	}

	// --- Shared prefix c1 (the NON-genesis common ancestor), then chain A (a2,a3) off c1. Index chain A to a3. ---
	c1 := mineRegtestBlockWithTxs(t, genesis, []*wire.MsgTx{buildRegtestCoinbase(t, 1, scriptC, vc, 5_001)}, 5_011)
	a2 := mineRegtestBlockWithTxs(t, &c1.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 2, scriptA, va, 11_001)}, 11_011)
	a3 := mineRegtestBlockWithTxs(t, &a2.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 3, scriptA, va, 12_001)}, 12_011)
	insert(c1, a2, a3)
	a3Hash := a3.Header.BlockHash()
	require.NoError(t, TBCFullNode.SyncIndexersToHash(MainCtx, a3Hash))

	require.Equal(t, uint64(vc), balance(addrC), "ancestor c1 credits C")
	require.Equal(t, uint64(2*va), balance(addrA), "chain A credits A twice")
	require.Equal(t, uint64(0), balance(addrB), "B has nothing yet")
	require.Equal(t, uint32(3), tipHeight(), "indexed tip is a3 (height 3)")

	// --- Chain B (b2,b3,b4) off the SAME c1. Heavier (c1+3 > c1+2) -> wins canonical. ---
	b2 := mineRegtestBlockWithTxs(t, &c1.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 2, scriptB, vb, 21_001)}, 21_011)
	b3 := mineRegtestBlockWithTxs(t, &b2.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 3, scriptB, vb, 22_001)}, 22_011)
	b4 := mineRegtestBlockWithTxs(t, &b3.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 4, scriptB, vb, 23_001)}, 23_011)
	require.Equal(t, tbcd.ITChainFork, insert(b2, b3, b4), "the heavier chain B (4 blocks > 3) must win the canonical race")
	b4Hash := b4.Header.BlockHash()

	// The canonical HEADER tip is now b4, but the indexers are still at a3. btcLastHeader must report the INDEXED tip
	// (a3), NOT the header-best tip (b4) — pinning that its height/hash come from the UTXO index, not BlockHeaderBest.
	require.Equal(t, uint32(3), tipHeight(), "btcLastHeader reports the indexed tip height (a3=3), not header-best (b4=4)")
	require.Equal(t, a3Hash[:], tipHash(), "btcLastHeader reports the indexed tip hash (a3), not header-best (b4)")

	// Pin the marquee precondition DIRECTLY: the common ancestor of a3 and b4 is the NON-genesis prefix c1 (height 1),
	// with isFork=true. The post-reorg balance asserts alone cannot prove this — c1's coinbase is re-applied on the
	// wind-forward regardless of how deep the unwind went, so an unwind-to-genesis regression yields identical final
	// balances. This assertion is what actually makes "the unwind stopped at c1, not genesis" falsifiable.
	anc, _, _, isFork, err := FindCommonAncestor(&tbc.HashHeight{Hash: a3Hash, Height: 3}, &tbc.HashHeight{Hash: b4Hash, Height: 4})
	require.NoError(t, err)
	require.True(t, isFork, "a3 and b4 are on different branches -> isFork")
	require.Equal(t, c1.Header.BlockHash(), anc.BlockHash(), "the common ancestor must be the non-genesis prefix c1")
	require.NotEqual(t, genesis.BlockHash(), anc.BlockHash(), "the common ancestor must NOT be genesis")

	// FindCommonAncestor must order the cursors by the FETCHED header heights, NOT the caller-supplied Height. Pass
	// deliberately INVERTED supplied heights (b4 tagged 0, a3 tagged 4) and assert it STILL finds c1 with no spurious
	// missing-header. If it ordered the cursors by the caller-supplied Height instead, it would mis-assign higher/lower
	// and the both-cursor walk-back would run off the bottom of the chain.
	ancBad, _, missBad, _, err := FindCommonAncestor(&tbc.HashHeight{Hash: b4Hash, Height: 0}, &tbc.HashHeight{Hash: a3Hash, Height: 4})
	require.NoError(t, err, "an inconsistent (hash,height) input must not error")
	require.Nil(t, missBad, "an inconsistent (hash,height) input must not spuriously report a missing header")
	require.NotNil(t, ancBad)
	require.Equal(t, c1.Header.BlockHash(), ancBad.BlockHash(), "FindCommonAncestor orders by fetched heights -> still c1 despite inverted supplied heights")

	// A single cross-branch sync is rejected as non-linear (the fork can't be walked in one direction)...
	require.ErrorIs(t, TBCFullNode.SyncIndexersToHash(MainCtx, b4Hash), tbc.ErrNotLinear,
		"a direct a3->b4 sync crosses a fork and must be rejected as non-linear")

	// ...so drive the reorg through the PRODUCTION entry point, which finds the common ancestor (c1, NOT genesis) and
	// orchestrates the unwind-to-ancestor + wind-to-target itself.
	require.NoError(t, TBCIndexToHashHeight(&tbc.HashHeight{Hash: b4Hash, Height: 4}), "production reorg to b4 over the c1 fork")

	// --- Post-reorg: chain A gone, chain B present, tip at b4, and crucially the ANCESTOR block c1's UTXO SURVIVES
	//     (the unwind stopped at c1, not at genesis). ---
	require.Equal(t, uint64(0), balance(addrA), "chain A's coinbases are unwound")
	require.Equal(t, uint64(3*vb), balance(addrB), "all three chain B coinbases are credited to B")
	require.Equal(t, uint64(vc), balance(addrC), "the common-ancestor block c1 stays indexed: C's balance is unchanged across the reorg")
	require.Equal(t, uint32(4), tipHeight(), "indexed tip is now b4 (height 4)")
	require.Equal(t, b4Hash[:], tipHash(), "indexed tip hash is now b4")

	// The reorg must unwind+rewind the TX index too (not just the UTXO index, which the balances above cover): a
	// chain-B coinbase now resolves through the tx index to its block, while a chain-A coinbase (a3) is GONE from the
	// tx index (TxById not-found -> nil). This is what exercises txIndexerUnwind/Wind, distinct from the UTXO path.
	outB2, err := (&btcTxByTxid{}).Run(append(reversedHash(b2.Transactions[0].TxHash()), 0x40, 0x00, 0x00, 0x00), common.Hash{})
	require.NoError(t, err)
	b2Hash := b2.Header.BlockHash()
	require.Equal(t, b2Hash[:], reverseBytes(outB2), "chain B tx resolves to its block post-reorg (tx index rewound)")
	outA3, err := (&btcTxByTxid{}).Run(append(reversedHash(a3.Transactions[0].TxHash()), 0x40, 0x00, 0x00, 0x00), common.Hash{})
	require.NoError(t, err)
	require.Nil(t, outA3, "chain A tx is gone from the tx index post-reorg (tx index unwound)")

	// The common-ancestor c1's coinbase must SURVIVE in the tx index across the reorg (txIndexerUnwind stopped at c1) —
	// the tx-index twin of the addrC UTXO-balance ancestor check above.
	outC, err := (&btcTxByTxid{}).Run(append(reversedHash(c1.Transactions[0].TxHash()), 0x40, 0x00, 0x00, 0x00), common.Hash{})
	require.NoError(t, err)
	c1Hash := c1.Header.BlockHash()
	require.Equal(t, c1Hash[:], reverseBytes(outC), "ancestor c1's coinbase stays in the tx index post-reorg")
}

// Multi-tx / spend: this covers the precompiles that read SPEND data — btcInputByTxid (0x47),
// btcTxGetInputWitness (0x49), btcOutputByTxid (0x48) — and the spent/unspent status path, which the coinbase-only
// blocks in the sibling synthetic tests do not reach. This file mines a 2-block regtest chain where block 2 contains
// a real transaction that spends block 1's coinbase output (with an arbitrary scriptSig and a 2-element witness; the
// full node does no script validation on BlockInsert, so unsigned spends index fine), producing the input-value
// lookups, witness elements, output scripts, and spent/unspent transitions those precompiles serialize.
//
// It also covers the deep btcTxByTxid includeInputs branch (the inline per-input value lookup via the source tx),
// which the coinbase-only test could not reach.
// buildRegtestCoinbase builds a BIP34 coinbase tx paying `value` to `pkScript`.
func buildRegtestCoinbase(t *testing.T, bip34Height int32, pkScript []byte, value int64, extraNonce uint32) *wire.MsgTx {
	t.Helper()
	cb := wire.NewMsgTx(wire.TxVersion)
	sig, err := txscript.NewScriptBuilder().AddInt64(int64(bip34Height)).AddInt64(int64(extraNonce)).Script()
	require.NoError(t, err)
	cb.AddTxIn(&wire.TxIn{
		PreviousOutPoint: wire.OutPoint{Hash: chainhash.Hash{}, Index: 0xffffffff},
		SignatureScript:  sig,
		Sequence:         0xffffffff,
	})
	cb.AddTxOut(&wire.TxOut{Value: value, PkScript: pkScript})
	return cb
}

// mineRegtestBlockWithTxs assembles a regtest block over prev containing txs (txs[0] must be the coinbase), with a
// correct merkle root over all txs and a header mined to the regtest PowLimit.
func mineRegtestBlockWithTxs(t *testing.T, prev *wire.BlockHeader, txs []*wire.MsgTx, extraNonce uint32) *wire.MsgBlock {
	t.Helper()
	utxs := make([]*btcutil.Tx, len(txs))
	for i, tx := range txs {
		utxs[i] = btcutil.NewTx(tx)
	}
	merkles := blockchain.BuildMerkleTreeStore(utxs, false)
	merkleRoot := merkles[len(merkles)-1]

	hdr := wire.BlockHeader{
		Version:    4,
		PrevBlock:  prev.BlockHash(),
		MerkleRoot: *merkleRoot,
		Timestamp:  prev.Timestamp.Add(60 * time.Second),
		Bits:       syntheticRegtestPowBits,
	}
	target := blockchain.CompactToBig(hdr.Bits)
	mined := false
	for i := uint32(0); i < 1<<22; i++ {
		hdr.Nonce = extraNonce + i
		hh := hdr.BlockHash()
		if blockchain.HashToBig(&hh).Cmp(target) <= 0 {
			mined = true
			break
		}
	}
	require.True(t, mined, "must mine a regtest block within 2^22 nonces")
	return &wire.MsgBlock{Header: hdr, Transactions: txs}
}

// reversedHash returns the display-order (little-endian) byte form the precompiles take as txid input.
func reversedHash(h chainhash.Hash) []byte {
	b := make([]byte, 32)
	copy(b, h[:])
	for i, j := 0, 31; i < j; i, j = i+1, j-1 {
		b[i], b[j] = b[j], b[i]
	}
	return b
}

// TestSyntheticFullNodeSpendPrecompiles builds genesis->b1(cb1=50 BTC ->A)->b2(cb2=25 BTC ->A)->b3([cb3->D, T]) where
// T spends BOTH cb1 and cb2 (two inputs with DISTINCT values/scriptSigs/sequences/witness-element-counts) and pays B
// (out0) and A-change (out1, a DISTINCT value). The two distinct-value inputs/outputs make every per-index precompile
// query discriminating: a regression that ignores the requested input/output index and returns a fixed one is caught.
// (cb1 in b1 and cb2 in b2 are both PRIOR blocks, so T never spends within its own block — avoids same-block-spend
// indexer corner cases.)
func TestSyntheticFullNodeSpendPrecompiles(t *testing.T) {
	setupSyntheticFullNode(t)

	scriptA, addrA := regtestP2PKH(t, 0x42)
	scriptB, addrB := regtestP2PKH(t, 0x33)
	scriptD, _ := regtestP2PKH(t, 0x99) // cb3 sink — keeps A's balance equal to the change output alone
	const fund1 = int64(50 * 1e8)       // cb1
	const fund2 = int64(25 * 1e8)       // cb2 — DISTINCT from cb1 so balance proves WHICH coinbase was excluded
	const outB = int64(30 * 1e8)        // T out0 -> B
	const change = int64(40 * 1e8)      // T out1 -> A  (in 75, out 70, fee 5)

	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header

	cb1 := buildRegtestCoinbase(t, 1, scriptA, fund1, 1)
	block1 := mineRegtestBlockWithTxs(t, genesis, []*wire.MsgTx{cb1}, 1_001)
	cb1Txid := cb1.TxHash()

	cb2 := buildRegtestCoinbase(t, 2, scriptA, fund2, 2)
	block2 := mineRegtestBlockWithTxs(t, &block1.Header, []*wire.MsgTx{cb2}, 2_001)
	cb2Txid := cb2.TxHash()

	// T (in block 3) spends cb1 (input 0) and cb2 (input 1) with deliberately distinct per-input data.
	sig0, wit0, seq0 := []byte{0x51, 0x52, 0x53}, wire.TxWitness{{0xaa, 0xbb}, {0xcc}}, uint32(0xfffffffe)               // 2 witness items
	sig1, wit1, seq1 := []byte{0x61, 0x62}, wire.TxWitness{{0x11}, {0x22, 0x23}, {0x33, 0x34, 0x35}}, uint32(0xfffffffd) // 3 witness items
	spend := wire.NewMsgTx(wire.TxVersion)
	spend.AddTxIn(&wire.TxIn{PreviousOutPoint: wire.OutPoint{Hash: cb1Txid, Index: 0}, SignatureScript: sig0, Witness: wit0, Sequence: seq0})
	spend.AddTxIn(&wire.TxIn{PreviousOutPoint: wire.OutPoint{Hash: cb2Txid, Index: 0}, SignatureScript: sig1, Witness: wit1, Sequence: seq1})
	spend.AddTxOut(&wire.TxOut{Value: outB, PkScript: scriptB})   // output 0 -> B
	spend.AddTxOut(&wire.TxOut{Value: change, PkScript: scriptA}) // output 1 -> A (change)
	spendTxid := spend.TxHash()
	cb3 := buildRegtestCoinbase(t, 3, scriptD, int64(10*1e8), 3)
	block3 := mineRegtestBlockWithTxs(t, &block2.Header, []*wire.MsgTx{cb3, spend}, 3_001)

	h1, h2, h3 := block1.Header, block2.Header, block3.Header
	_, _, _, count, err := TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&h1, &h2, &h3}})
	require.NoError(t, err)
	require.Equal(t, 3, count)
	for _, b := range []*wire.MsgBlock{block1, block2, block3} {
		_, err = TBCFullNode.BlockInsert(MainCtx, b)
		require.NoError(t, err)
	}
	require.NoError(t, TBCFullNode.SyncIndexersToHash(MainCtx, block3.Header.BlockHash()))

	// btcInputByTxid framing: witnessCount(2)||value(8)||reversedPrevHash(32)||prevIdx(2)||sigLen(2)||sig||seq(4).
	// Asserted for BOTH inputs; the distinct witnessCount/value/prevHash/sig/seq per input prove index selection.
	assertInput := func(inputIdx uint16, wantWitCount int, wantValue int64, wantPrev chainhash.Hash, wantSig []byte, wantSeq uint32) {
		t.Helper()
		in := append(reversedHash(spendTxid), byte(inputIdx>>8), byte(inputIdx), 0x03, 0xE8 /*maxSigScriptSize=1000*/)
		out, err := (&btcInputByTxid{}).Run(in, common.Hash{})
		require.NoError(t, err)
		require.Equal(t, uint16(wantWitCount), binary.BigEndian.Uint16(out[0:2]), "input %d witness count", inputIdx)
		require.Equal(t, uint64(wantValue), binary.BigEndian.Uint64(out[2:10]), "input %d spent-output value", inputIdx)
		require.Equal(t, wantPrev[:], reverseBytes(out[10:42]), "input %d prev txid", inputIdx)
		// NB (documented, intentional per current ABI): btcInputByTxid emits the prevout index as a CLAMPED uint16
		// (2 bytes), whereas the deep btcTxByTxid includeInputSource branch emits the full uint32. The two precompiles
		// therefore disagree on this field's width, and an index >= 65536 (e.g. a coinbase input's 0xFFFFFFFF) would be
		// truncated to 0xFFFF here. We pin the 2-byte form as the frozen wire layout. In practice the clamp is
		// unreachable: real spends use small indices (here 0), and a coinbase input bails earlier (its null source tx
		// is unlookupable), so no fixture can drive a >= 65536 index. Widening would be an ABI change, deliberately not made.
		require.Equal(t, uint16(0), binary.BigEndian.Uint16(out[42:44]), "input %d prev index (2-byte clamped field)", inputIdx)
		sigLen := binary.BigEndian.Uint16(out[44:46])
		require.Equal(t, uint16(len(wantSig)), sigLen, "input %d sig len", inputIdx)
		require.Equal(t, wantSig, out[46:46+sigLen], "input %d scriptSig", inputIdx)
		require.Equal(t, wantSeq, binary.BigEndian.Uint32(out[46+sigLen:46+sigLen+4]), "input %d sequence", inputIdx)
		require.Len(t, out, 2+8+32+2+2+len(wantSig)+4, "input %d total frame length (no trailing junk)", inputIdx)
	}
	assertInput(0, len(wit0), fund1, cb1Txid, sig0, seq0)
	assertInput(1, len(wit1), fund2, cb2Txid, sig1, seq1) // distinct from input 0 in every field -> selection is real

	// btcTxGetInputWitness: each (input, witnessIndex) returns that exact element. Cross both inputs and indices.
	assertWitness := func(inputIdx, witIdx uint16, want []byte) {
		t.Helper()
		wi := append(reversedHash(spendTxid), byte(inputIdx>>8), byte(inputIdx), byte(witIdx>>8), byte(witIdx), 0x00, 0xFF)
		wout, err := (&btcTxGetInputWitness{}).Run(wi, common.Hash{})
		require.NoError(t, err)
		require.Equal(t, uint16(len(want)), binary.BigEndian.Uint16(wout[0:2]), "in %d wit %d len", inputIdx, witIdx)
		require.Equal(t, want, wout[2:], "in %d wit %d bytes", inputIdx, witIdx)
		require.Len(t, wout, 2+len(want), "in %d wit %d total frame length", inputIdx, witIdx)
	}
	assertWitness(0, 0, wit0[0])
	assertWitness(0, 1, wit0[1])
	assertWitness(1, 0, wit1[0])
	assertWitness(1, 2, wit1[2]) // selecting input 1 + a high witness index proves both indices are honored

	// Witness index AT the exact boundary (== len) must return (nil,nil) — pins the `>=` guard (a `>` mutation would
	// pass index-past-end but panic at index==len). Probe the boundary for both inputs (lengths 2 and 3).
	for _, bc := range []struct{ in, wi uint16 }{{0, 2}, {1, 3}} {
		probe := append(reversedHash(spendTxid), byte(bc.in>>8), byte(bc.in), byte(bc.wi>>8), byte(bc.wi), 0x00, 0xFF)
		miss, err := (&btcTxGetInputWitness{}).Run(probe, common.Hash{})
		require.NoError(t, err)
		require.Nil(t, miss, "witness index == len (input %d, idx %d) must return (nil,nil)", bc.in, bc.wi)
	}

	// btcOutputByTxid: value(8)||pkScriptLen(2)||pkScript||spent(1). Query BOTH unspent outputs (distinct value+script
	// per index proves output selection). NB the trailing byte mirrors ScriptHashAvailableToSpend (true=UNSPENT),
	// so an UNSPENT output reports 1 — inverse of the field name; we pin actual behavior.
	assertOutput := func(outIdx uint16, wantValue int64, wantScript []byte) {
		t.Helper()
		oin := append(reversedHash(spendTxid), byte(outIdx>>8), byte(outIdx), 0x01, 0x00 /*maxOutScriptSize=256*/)
		o, err := (&btcOutputByTxid{}).Run(oin, common.Hash{})
		require.NoError(t, err)
		require.Equal(t, uint64(wantValue), binary.BigEndian.Uint64(o[0:8]), "output %d value", outIdx)
		pkLen := binary.BigEndian.Uint16(o[8:10])
		require.Equal(t, wantScript, o[10:10+pkLen], "output %d pkScript", outIdx)
		require.Equal(t, byte(1), o[10+pkLen], "output %d is unspent -> available-to-spend byte 1", outIdx)
		require.Len(t, o, 8+2+len(wantScript)+1, "output %d total frame length (no trailing junk)", outIdx)
	}
	assertOutput(0, outB, scriptB)
	assertOutput(1, change, scriptA) // distinct value + script from output 0

	// DISCOVERED LIMITATION (KNOWN): btcOutputByTxid returns (nil,nil) for a SPENT output, because
	// ScriptHashAvailableToSpend maps a not-found (spent) outpoint to (false, <leveldb error>) rather than (false,nil)
	// and btcOutputByTxid bails on the error before emitting the spent byte. Both cb1 and cb2 were spent by T.
	for _, spent := range []chainhash.Hash{cb1Txid, cb2Txid} {
		c, err := (&btcOutputByTxid{}).Run(append(reversedHash(spent), 0x00, 0x00, 0x01, 0x00), common.Hash{})
		require.NoError(t, err)
		require.Nil(t, c, "btcOutputByTxid returns nil for a spent output")
	}

	// deep btcTxByTxid includeInputs (bitflag1 bit2; bitflag3 maxInputsExp=1 -> maxInputs=2): txInLen(2)||value(8)*2.
	dIn, err := (&btcTxByTxid{}).Run(append(reversedHash(spendTxid), 0x04, 0x00, 0x08, 0x00), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(2), binary.BigEndian.Uint16(dIn[0:2]), "T has two inputs")
	require.Equal(t, uint64(fund1), binary.BigEndian.Uint64(dIn[2:10]), "deep input 0 value (cb1)")
	require.Equal(t, uint64(fund2), binary.BigEndian.Uint64(dIn[10:18]), "deep input 1 value (cb2)")

	// deep btcTxByTxid includeOutputs+includeOutputSpent on the SPENT cb1 -> outLen(2)||value(8)||spent(1). This is the
	// path that DOES surface a spent output (byte 0), unlike btcOutputByTxid above.
	dCb, err := (&btcTxByTxid{}).Run(append(reversedHash(cb1Txid), 0x00, 0x24, 0x00, 0x00), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(1), binary.BigEndian.Uint16(dCb[0:2]), "cb1 has one output")
	require.Equal(t, uint64(fund1), binary.BigEndian.Uint64(dCb[2:10]), "cb1 output value")
	require.Equal(t, byte(0), dCb[10], "the SPENT cb1 output reports available-to-spend byte 0")

	// deep btcTxByTxid includeOutputs+includeOutputSpent on T (2 unspent outputs, maxOutputs=2 via bitflag3=0x01).
	dT, err := (&btcTxByTxid{}).Run(append(reversedHash(spendTxid), 0x00, 0x24, 0x01, 0x00), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(2), binary.BigEndian.Uint16(dT[0:2]), "T has two outputs")
	require.Equal(t, uint64(outB), binary.BigEndian.Uint64(dT[2:10]), "T output 0 value")
	require.Equal(t, byte(1), dT[10], "T output 0 unspent")
	require.Equal(t, uint64(change), binary.BigEndian.Uint64(dT[11:19]), "T output 1 value")
	require.Equal(t, byte(1), dT[19], "T output 1 unspent")

	// Balance cross-check: A holds ONLY the change output (both cb1 AND cb2 were spent by T; cb3 went to D). Because
	// cb1 (50), cb2 (25), and change (40) are all DISTINCT, balA==40 uniquely proves both coinbases were excluded and
	// the change was added — a regression retaining either spent coinbase would yield 90 or 65, not 40.
	balA, err := (&btcBalAddr{}).Run([]byte(addrA), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint64(change), binary.BigEndian.Uint64(balA), "A's balance must be exactly the change output (both spent coinbases excluded)")
	balB, err := (&btcBalAddr{}).Run([]byte(addrB), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint64(outB), binary.BigEndian.Uint64(balB), "B's balance = T's payment output")

	// --- btcUtxosAddrList over a MUTATED (post-spend) UTXO set: the prior coverage only queried append-only coinbase
	//     chains, so per-UTXO identity under spends was unchecked. A's UTXO set must be EXACTLY {T:1 change} (cb1,cb2
	//     spent), and B's exactly {T:0 payment} — by txid+index+value, not just count/balance. ---
	type utxo struct {
		txid chainhash.Hash
		idx  uint16
		val  uint64
	}
	listUtxos := func(addr string) []utxo {
		t.Helper()
		out, err := (&btcUtxosAddrList{}).Run(append([]byte(addr), 0x00, 0x00, 0x00, 100), common.Hash{})
		require.NoError(t, err)
		n := int(out[0])
		us := make([]utxo, 0, n)
		for i := 0; i < n; i++ {
			base := 1 + i*(32+2+8)
			var id chainhash.Hash
			copy(id[:], reverseBytes(out[base:base+32]))
			us = append(us, utxo{id, binary.BigEndian.Uint16(out[base+32 : base+34]), binary.BigEndian.Uint64(out[base+34 : base+42])})
		}
		return us
	}
	require.Equal(t, []utxo{{spendTxid, 1, uint64(change)}}, listUtxos(addrA), "A's only UTXO is T's change output (idx 1); cb1/cb2 are spent and absent")
	require.Equal(t, []utxo{{spendTxid, 0, uint64(outB)}}, listUtxos(addrB), "B's only UTXO is T's payment output (idx 0)")

	// --- CHOPPING / truncation: every prior query used a max larger than the datum, so the chop branches were dead.
	// The contract: the length WORD reports the FULL length while only the CHOPPED bytes are appended, so a caller
	// detects truncation by (declared length) > (appended bytes). Drive each chop with a max SMALLER than the datum. ---

	// btcInputByTxid input 0: sigScript len 3, maxSigScriptSize=2 -> sigLen word=3, only 2 bytes appended, seq follows.
	ci, err := (&btcInputByTxid{}).Run(append(reversedHash(spendTxid), 0x00, 0x00, 0x00, 0x02), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(len(sig0)), binary.BigEndian.Uint16(ci[44:46]), "chopped input: sigLen word must report the FULL length")
	require.Equal(t, sig0[:2], ci[46:48], "chopped input: only maxSigScriptSize bytes appended (the prefix)")
	require.Equal(t, seq0, binary.BigEndian.Uint32(ci[48:52]), "chopped input: sequence follows the CHOPPED script")
	require.Len(t, ci, 2+8+32+2+2+2+4, "chopped input: total length reflects the chopped (2-byte) script")

	// btcOutputByTxid output 0: pkScript len 25 (P2PKH), maxOutScriptSize=10 -> pkLen word=25, only 10 bytes appended.
	co, err := (&btcOutputByTxid{}).Run(append(reversedHash(spendTxid), 0x00, 0x00, 0x00, 0x0A), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(len(scriptB)), binary.BigEndian.Uint16(co[8:10]), "chopped output: pkScriptLen word must report the FULL length")
	require.Equal(t, scriptB[:10], co[10:20], "chopped output: only maxOutputScriptSize bytes appended (the prefix)")
	require.Equal(t, byte(1), co[20], "chopped output: spent byte follows the CHOPPED script")
	require.Len(t, co, 8+2+10+1, "chopped output: total length reflects the chopped (10-byte) script")

	// btcTxGetInputWitness input 0 / witness 0: element len 2, maxWitnessLength=1 -> length word=2, only 1 byte appended.
	cw, err := (&btcTxGetInputWitness{}).Run(append(reversedHash(spendTxid), 0x00, 0x00, 0x00, 0x00, 0x00, 0x01), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(len(wit0[0])), binary.BigEndian.Uint16(cw[0:2]), "chopped witness: length word must report the FULL length")
	require.Equal(t, wit0[0][:1], cw[2:], "chopped witness: only maxWitnessLength bytes appended (the prefix)")

	// --- COUNT chopping: maxInputs smaller than the actual input count. txInLen word reports the FULL count (2) while
	// only maxInputs (1) entries are emitted. bitflag1=includeInputs(0x04), bitflag3=0x00 -> maxInputsExp 0 -> maxInputs 1. ---
	cc, err := (&btcTxByTxid{}).Run(append(reversedHash(spendTxid), 0x04, 0x00, 0x00, 0x00), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(2), binary.BigEndian.Uint16(cc[0:2]), "count-chop: txInLen word reports the FULL input count (2)")
	require.Len(t, cc, 2+8, "count-chop: only maxInputs(1) input entries are emitted (value only)")
	require.Equal(t, uint64(fund1), binary.BigEndian.Uint64(cc[2:10]), "count-chop: the one emitted entry is input 0")

	// --- Witness-LESS input (the coinbase cb1's input) returns (nil,nil). This pins the BEHAVIOR, not a specific guard:
	//     for an empty witness the explicit `len(Witness)==0` guard and the following `witIdx >= len(Witness)` bound
	//     both return the identical (nil,nil), so neither can be isolated by a test — deleting either still yields nil. ---
	ew, err := (&btcTxGetInputWitness{}).Run(append(reversedHash(cb1Txid), 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF), common.Hash{})
	require.NoError(t, err)
	require.Nil(t, ew, "btcTxGetInputWitness on an input with no witness must return (nil,nil)")
}

// reverseBytes returns a reversed copy of b (helper for asserting display-order hashes).
func reverseBytes(b []byte) []byte {
	out := make([]byte, len(b))
	for i, j := 0, len(b)-1; j >= 0; i, j = i+1, j-1 {
		out[i] = b[j]
	}
	return out
}

// isTBCMissingHeader is the discrimination at the heart of the missing-header fix: only a TBC
// "header not found" is the transient, deferrable condition; corruption / I/O / other faults (and the
// distinct block-body BlockNotFoundError) must not be treated as recoverable, or they would be
// laundered into an endless deferral instead of fail-stopping. This exercises that classifier
// directly, no TBC node required.
func TestIsTBCMissingHeader(t *testing.T) {
	// NotFound (transient) — must be recognized, including when %w-wrapped the way the header store's
	// BlockHeaderByHash wraps it ("block header get: %w").
	for _, err := range []error{
		database.ErrNotFound,
		database.NotFoundError("tx not found: abc"),
		fmt.Errorf("block header get: %w", database.NotFoundError("x")),
		fmt.Errorf("outer: %w", fmt.Errorf("inner: %w", database.ErrNotFound)),
	} {
		if !isTBCMissingHeader(err) {
			t.Errorf("isTBCMissingHeader(%v) = false, want true (NotFound is the deferrable case)", err)
		}
	}

	// Non-NotFound (fail-stop) — corruption / I/O / generic / nil, and the distinct BlockNotFoundError
	// (block-body read; not on the header path) must not match, so they remain fail-stop rather than
	// deferring.
	for _, err := range []error{
		nil,
		errors.New("io error"),
		fmt.Errorf("block decode data corruption: %w", errors.New("boom")),
		database.ErrBlockNotFound,
		fmt.Errorf("wrapped: %w", database.ErrBlockNotFound),
	} {
		if isTBCMissingHeader(err) {
			t.Errorf("isTBCMissingHeader(%v) = true, want false (only header NotFound is deferrable)", err)
		}
	}
}

// These tests lock in the required configuration for op-geth's embedded Bitcoin full node. The node
// must run with AutoIndex=false so its indexers are driven only to a lagging consensus target, never to
// the live P2P best tip; this is a supported-configuration invariant whose conditions must not silently
// regress.

// The full node must be constructed with AutoIndex=false. AutoIndex=true would drive the indexers to the
// live P2P best tip, which is not a supported configuration.
// validateTBCFullNodeConfig is the choke-point guard invoked by SetupTBCFullNode.
func TestValidateTBCFullNodeConfigRejectsAutoIndex(t *testing.T) {
	safe := tbc.NewDefaultConfig()
	if err := validateTBCFullNodeConfig(safe); err != nil {
		t.Fatalf("default full-node config must be accepted (AutoIndex=false), got: %v", err)
	}

	unsafe := tbc.NewDefaultConfig()
	unsafe.AutoIndex = true
	if err := validateTBCFullNodeConfig(unsafe); err == nil {
		t.Fatal("validateTBCFullNodeConfig must reject AutoIndex=true: it is not a supported configuration")
	}
}

// The required configuration assumes the embedded node's default config leaves AutoIndex off (op-geth
// never sets it on the full node) and ExternalHeaderMode off (so the full node really is a live P2P node,
// which is why the AutoIndex guard matters). If a dependency bump flips either default, this test fails
// and forces a re-audit of the configuration invariant before the change ships.
func TestTBCDefaultConfigInvariants(t *testing.T) {
	cfg := tbc.NewDefaultConfig()
	if cfg.AutoIndex {
		t.Error("the TBC dependency's NewDefaultConfig() now defaults AutoIndex=true; op-geth's required configuration relies on it being false — re-audit before bumping")
	}
	if cfg.ExternalHeaderMode {
		t.Error("the TBC dependency's NewDefaultConfig() now defaults ExternalHeaderMode=true; the full node is expected to be a live P2P node (ExternalHeaderMode=false) — re-audit the configuration invariant")
	}
}
