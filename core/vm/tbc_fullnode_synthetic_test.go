// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package vm

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

import (
	"bytes"
	"context"
	"encoding/binary"
	"errors"
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
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

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
