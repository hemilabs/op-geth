// Copyright 2024 The go-ethereum Authors
// Copyright 2026 Hemi Labs, Inc.
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

// hvm-btcattr-reconstruct reconstructs the NDJSON stream of every Bitcoin header ever committed to hVM consensus
// via a BtcAttributesDeposited tx — the input fixture to the differential-replay gate
// (core/vm/btcdiff_history_verify_test.go and core/blockchain_hvm_replay_test.go), which read it via the
// HEMI_MAINNET_VERIFY / HEMI_TESTNET3_VERIFY env vars.
//
// The committed history can be sourced two ways, both emitting the identical NDJSON schema:
//
//	--chaindata <dir>  reads an op-geth chaindata directory directly (leveldb/pebble); requires a local full node.
//	--rpc <url>        pulls blocks from an archive node over JSON-RPC (eth_getBlockByNumber), decoding the
//	                   BtcAttributesDeposited (type 0x7C) tx calldata — no local chaindata directory required.
//
// For each canonical L2 block in [start, head] whose transactions contain a BtcAttributesDeposited tx, it
// emits one line: {"blk":<L2 height>,"tip":"<canonical BTC tip hash hex>","hdrs":["<80-byte header hex>",...]}.
// The gate then asserts the committed history is clean under the network's params, so the proof is reproducible
// from the source code plus a node's chaindata (or an archive RPC). Point HEMI_MAINNET_VERIFY at the output, and
// set HEMI_HISTORY_GATE_REQUIRED=1 to make the gate fail (not skip) when the fixture is absent.
//
// Usage:
//
//	hvm-btcattr-reconstruct --chaindata <geth-datadir>/geth/chaindata [--start N] [--end H] [--out file.ndjson]
//	hvm-btcattr-reconstruct --rpc http://host:8545 [--chainid ID] [--hvm0-time UNIX] [--start N] [--end H] [--out file.ndjson]
//
// Pin --end H for a deterministic, reproducible bounded fixture (omit / 0 = chain head). The emitted NDJSON is
// network-unlabeled — the network is chosen by which env var the gate consumes it through — so keep mainnet and
// testnet3 fixtures separate.
//
// --rpc caveats: point it at a FULLY-SYNCED archive node and pin --end to a FINALIZED L2 height. An unset or
// near-head --end can yield reorg-dependent or (against a lagging node) silently-truncated output. Unlike
// --chaindata, --rpc does not read the chain config, so it applies the hVM0-activation gate only when --hvm0-time
// is given: on testnet3 (whose canonical pre-activation L2 blocks carry grandfathered BtcAttr txs the chaindata
// scan excludes) pass --hvm0-time <activation-unix> to reproduce a byte-identical fixture; mainnet needs no flag.
// --rpc is an operator-convenience source that no gate enforces; pass --chainid to assert the endpoint's network,
// and spot-check its output against a --chaindata run, before shipping it as a clean proof.
package main

import (
	"bufio"
	"context"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/ethdb/leveldb"
	"github.com/ethereum/go-ethereum/ethdb/pebble"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/rpc"
)

type ndjsonLine struct {
	Blk  uint64   `json:"blk"`
	Tip  string   `json:"tip"`
	Hdrs []string `json:"hdrs"`
}

// btcAttrTxTypeHex is the JSON-RPC "type" field of a BtcAttributesDeposited tx ("0x7c"), derived from the
// canonical type constant so it stays in sync. The RPC scanner matches on it to identify the tx, mirroring
// (*types.Transaction).IsBtcAttributesDepositedTx that the chaindata path's ExtractBtcAttrData uses.
var btcAttrTxTypeHex = hexutil.EncodeUint64(uint64(types.BtcAttributesDepositedTxType))

// Sentinel errors returned by the scanners so callers (and unit tests) can distinguish the fatal fixture-integrity
// conditions from incidental I/O errors. main() maps each to a log.Crit + output cleanup.
var (
	// errMissingBlocks: a canonical block was absent in the scanned range and --allow-gaps was not set — the
	// fixture would be incomplete (e.g. a snap-synced node lacking pre-pivot blocks).
	errMissingBlocks = errors.New("chaindata is missing canonical blocks in the scanned range")
	// errVacuousFixture: zero BtcAttr lines, or lines carrying zero actual BTC headers — useless as a proof.
	errVacuousFixture = errors.New("reconstruction produced a vacuous fixture: zero BtcAttr blocks, or lines carrying zero BTC headers")
)

// progressLogInterval is the number of emitted BtcAttr lines between reconstruction progress log lines.
const progressLogInterval = 5000

// rpcScanHeartbeat is the number of scanned blocks between RPC-path liveness log lines. The serial one-block-at-a-
// time RPC scan can traverse a long BtcAttr-sparse span with no emitted line, so it logs by scanned blocks too.
const rpcScanHeartbeat = 50000

// scanResult holds the counters the scanners accumulate while walking the canonical chain.
// The two absent-block cases are counted separately for diagnostics: hashMissing is a height with no canonical
// hash mapping at all (or, on the RPC path, a block the node returns as null), blockMissing is a height whose
// canonical hash is present but the block body is absent (the snap-synced/pruned-body case; chaindata only).
// Both feed the same errMissingBlocks gate.
type scanResult struct {
	emitted, scanned, hashMissing, blockMissing, rawHeaders int
}

// missing is the total count of canonical blocks that could not be read in the scanned range.
func (r scanResult) missing() int { return r.hashMissing + r.blockMissing }

// emitBtcAttrLine writes one NDJSON line for a decoded BtcAttributesDeposited payload and updates the counters.
// Shared by the chaindata and RPC scanners so both emit a byte-identical schema. The canonical tip is rendered in
// DISPLAY (byte-reversed) order — the form chainhash.NewHashFromStr expects, which the replay gate parses it back
// with; CanonicalTip is stored internal-order and chainhash.Hash.String() renders display order. Each 80-byte
// header is hex-encoded in order.
func emitBtcAttrLine(w io.Writer, res *scanResult, blk uint64, bad *types.BtcAttributesDepositData) error {
	hdrs := make([]string, 0, len(bad.Headers))
	for i := range bad.Headers {
		hdrs = append(hdrs, hex.EncodeToString(bad.Headers[i][:]))
	}
	ln := ndjsonLine{Blk: blk, Tip: chainhash.Hash(bad.CanonicalTip).String(), Hdrs: hdrs}
	b, err := json.Marshal(ln)
	if err != nil {
		return fmt.Errorf("marshal line at block %d: %w", blk, err)
	}
	if _, err := w.Write(append(b, '\n')); err != nil {
		return fmt.Errorf("write line: %w", err)
	}
	res.emitted++
	res.rawHeaders += len(hdrs)
	return nil
}

// scanBtcAttrHistory walks canonical L2 blocks in [start, end] from a chaindata db and writes to w one NDJSON line
// per block carrying a BtcAttributesDeposited tx (applying the IsHvm0 activation gate). It returns errors
// (errMissingBlocks / errVacuousFixture / wrapped I/O errors) instead of crashing, so the walk logic stays
// unit-testable against an in-memory db while main() owns the log.Crit + partial-output cleanup.
func scanBtcAttrHistory(db ethdb.Database, cfg *params.ChainConfig, start, end uint64, allowGaps bool, w io.Writer) (scanResult, error) {
	var res scanResult
	for n := start; n <= end; n++ {
		canon := rawdb.ReadCanonicalHash(db, n)
		if canon == (common.Hash{}) {
			res.hashMissing++
			continue
		}
		block := rawdb.ReadBlock(db, canon, n)
		if block == nil {
			res.blockMissing++
			continue
		}
		res.scanned++
		if !cfg.IsHvm0(block.Time()) {
			continue // pre-hVM0-activation block: excluded from the committed history the gate verifies
		}
		bad, err := block.Transactions().ExtractBtcAttrData()
		if err != nil {
			return res, fmt.Errorf("extract BtcAttr data at block %d: %w", n, err)
		}
		if bad == nil {
			continue // block carries no BtcAttributesDeposited tx
		}
		if err := emitBtcAttrLine(w, &res, n, bad); err != nil {
			return res, err
		}
		if res.emitted%progressLogInterval == 0 {
			log.Info("reconstructing", "L2height", n, "btcattr_lines", res.emitted)
		}
	}
	if res.missing() > 0 && !allowGaps {
		return res, errMissingBlocks
	}
	// Fail fast on a vacuous fixture: zero LINES, or lines that carry zero actual BTC headers (a BtcAttr tx with
	// no headers is valid, so an all-header-less file would pass an emitted-only check yet be useless).
	if res.emitted == 0 || res.rawHeaders == 0 {
		return res, errVacuousFixture
	}
	return res, nil
}

// rpcBlock / rpcTx are the minimal shape of an eth_getBlockByNumber (full-tx) response the RPC scanner reads: it
// only needs each tx's type (to spot the BtcAttributesDeposited tx) and input (its calldata), plus the block
// timestamp for the optional activation gate. A non-existent height returns JSON null, which decodes to a nil
// *rpcBlock.
type rpcBlock struct {
	Timestamp    string  `json:"timestamp"`
	Transactions []rpcTx `json:"transactions"`
}

type rpcTx struct {
	Type  string `json:"type"`
	Input string `json:"input"`
}

// scanBtcAttrHistoryRPC is the --rpc counterpart of scanBtcAttrHistory: it pulls each L2 block in [start, end] from
// an archive node via eth_getBlockByNumber and decodes the BtcAttributesDeposited (type 0x7C) tx calldata with the
// same types.BtcAttributesDepositData.UnmarshalBinary the apply path uses, so it emits the identical NDJSON schema.
//
// Two deliberate differences from the chaindata path:
//   - The hVM0-activation timestamp gate (chaindata: cfg.IsHvm0(block.Time())) is applied here only when the
//     caller passes a non-zero hvm0Time (the chain config is not fetched over RPC). On mainnet no canonical block
//     below activation carries a BtcAttr tx, so the two sources match with or without it. On testnet3, canonical
//     pre-activation L2 blocks DO carry grandfathered BtcAttr txs (a re-genesis artifact) that the chaindata gate
//     excludes; pass --hvm0-time <activation-unix> to reproduce that exclusion and keep the sources byte-identical.
//   - A block the node returns as null counts as a gap (hashMissing), honoring allowGaps exactly like chaindata.
//
// The "more than one BtcAttributesDeposited tx in a block" rule mirrors ExtractBtcAttrData: it is surfaced as an
// error, not silently merged.
func scanBtcAttrHistoryRPC(ctx context.Context, c *rpc.Client, start, end uint64, allowGaps bool, hvm0Time uint64, w io.Writer) (scanResult, error) {
	var res scanResult
	for n := start; n <= end; n++ {
		// Fetch into a RawMessage first (the ethclient.getBlock idiom): a non-existent height returns JSON null,
		// which unmarshals to a nil *rpcBlock (the gap signal). A genuinely empty result surfaces as ErrNoResult
		// from CallContext — a loud error, not a silent gap.
		var raw json.RawMessage
		if err := c.CallContext(ctx, &raw, "eth_getBlockByNumber", hexutil.EncodeUint64(n), true); err != nil {
			return res, fmt.Errorf("eth_getBlockByNumber %d: %w", n, err)
		}
		var blk *rpcBlock
		if err := json.Unmarshal(raw, &blk); err != nil {
			return res, fmt.Errorf("decode block %d: %w", n, err)
		}
		if blk == nil { // non-existent height (JSON null)
			res.hashMissing++
			continue
		}
		res.scanned++
		if res.scanned%rpcScanHeartbeat == 0 {
			log.Info("scanning (rpc)", "L2height", n, "scanned_blocks", res.scanned, "btcattr_lines", res.emitted)
		}
		if hvm0Time != 0 {
			// Activation gate, the RPC mirror of the chaindata path's cfg.IsHvm0(block.Time()): skip a block whose
			// timestamp is below hvm0Time. Needed on testnet3, whose canonical pre-activation L2 blocks carry
			// grandfathered BtcAttr txs the chaindata scan excludes.
			ts, err := hexutil.DecodeUint64(blk.Timestamp)
			if err != nil {
				return res, fmt.Errorf("decode block %d timestamp: %w", n, err)
			}
			if ts < hvm0Time {
				continue // pre-hVM0-activation block: excluded from the committed history the gate verifies
			}
		}
		if n > 0 && len(blk.Transactions) == 0 {
			// Every non-genesis OP-Stack block carries at least the index-0 L1-attributes deposit; a block that
			// exists but reports zero transactions means the endpoint/proxy stripped or omitted the list (a
			// hashes-only or trimmed response), which would silently drop any BtcAttr headers it committed. Fail
			// loud rather than emit a wrong fixture. (Genesis legitimately has no transactions and is exempt.)
			return res, fmt.Errorf("block %d returned with no transactions (endpoint not a full-tx eth_getBlockByNumber source?)", n)
		}
		var bad *types.BtcAttributesDepositData
		for i := range blk.Transactions {
			if !strings.EqualFold(blk.Transactions[i].Type, btcAttrTxTypeHex) {
				continue
			}
			if bad != nil {
				return res, fmt.Errorf("block %d contains more than one Bitcoin Attributes Deposited transaction", n)
			}
			raw, err := hexutil.Decode(blk.Transactions[i].Input)
			if err != nil {
				return res, fmt.Errorf("decode BtcAttr calldata at block %d: %w", n, err)
			}
			var parsed types.BtcAttributesDepositData
			if err := parsed.UnmarshalBinary(raw); err != nil {
				return res, fmt.Errorf("parse BtcAttr calldata at block %d: %w", n, err)
			}
			bad = &parsed
		}
		if bad == nil {
			continue // block carries no BtcAttributesDeposited tx
		}
		if err := emitBtcAttrLine(w, &res, n, bad); err != nil {
			return res, err
		}
		if res.emitted%progressLogInterval == 0 {
			log.Info("reconstructing (rpc)", "L2height", n, "btcattr_lines", res.emitted)
		}
	}
	if res.missing() > 0 && !allowGaps {
		return res, errMissingBlocks
	}
	if res.emitted == 0 || res.rawHeaders == 0 {
		return res, errVacuousFixture
	}
	return res, nil
}

func main() {
	chaindata := flag.String("chaindata", "", "path to the op-geth chaindata directory (e.g. <datadir>/geth/chaindata); mutually exclusive with --rpc")
	rpcURL := flag.String("rpc", "", "JSON-RPC endpoint of an archive node to read blocks from (e.g. http://host:8545); mutually exclusive with --chaindata")
	dbKind := flag.String("db", "auto", "key-value backend for --chaindata: auto (detect from disk), pebble, or leveldb (ignored for --rpc)")
	start := flag.Uint64("start", 0, "first L2 block height to scan (default 0; set to hVM0 activation to skip pre-hVM0-activation blocks)")
	end := flag.Uint64("end", 0, "last L2 block height to scan (0 = chain head; pin this for a deterministic, reproducible fixture)")
	allowGaps := flag.Bool("allow-gaps", false, "permit missing canonical blocks in the scanned range (default false: a missing block means an incomplete fixture, e.g. on a snap-synced node — fail loudly)")
	outPath := flag.String("out", "", "output NDJSON path (default: stdout)")
	chainID := flag.Uint64("chainid", 0, "if set, assert the --rpc endpoint's eth_chainId equals this before scanning (wrong-network guard; e.g. 43111 = Hemi mainnet, 743111 = testnet3); 0 = skip the check")
	hvm0Time := flag.Uint64("hvm0-time", 0, "--rpc only: if set, skip blocks whose timestamp is below this unix time, mirroring the chaindata hVM0-activation gate. REQUIRED on testnet3 (whose canonical pre-activation L2 blocks carry grandfathered BtcAttr txs the chaindata scan excludes) to reproduce a byte-identical fixture; unnecessary on mainnet. 0 = no activation gate")
	flag.Parse()

	// Exactly one source. (a == b) with both operands being emptiness tests is true iff both are empty or both set.
	if (*chaindata == "") == (*rpcURL == "") {
		fmt.Fprintln(os.Stderr, "error: exactly one of --chaindata or --rpc is required")
		flag.Usage()
		os.Exit(2)
	}

	ctx := context.Background()

	// Source setup runs BEFORE the temp output file is created below, so any setup failure (missing/mismatched db,
	// unreachable RPC, out-of-bounds --end) crits without orphaning a partial output file. Each branch resolves the
	// head and yields a scan closure that the shared output plumbing runs.
	var scan func(w io.Writer) (scanResult, error)
	var head uint64

	if *chaindata != "" {
		// Detect the on-disk engine. geth refuses to open a leveldb dir as pebble or vice-versa, and this mirrors
		// that: opening with the wrong backend can otherwise silently yield a stale/partial-but-resolvable head and
		// a plausible-but-wrong fixture.
		detected := rawdb.PreexistingDatabase(*chaindata)
		if detected == "" {
			log.Crit("no pre-existing key-value database at --chaindata (not a geth chaindata dir?)", "chaindata", *chaindata)
		}
		if *dbKind != "auto" && *dbKind != detected {
			log.Crit("requested --db conflicts with the on-disk engine; omit --db to auto-detect", "requested", *dbKind, "detected", detected)
		}
		var kv ethdb.KeyValueStore
		var err error
		switch detected {
		case "pebble":
			kv, err = pebble.New(*chaindata, 256, 0, "", true)
		case "leveldb":
			kv, err = leveldb.New(*chaindata, 256, 0, "", true)
		default:
			log.Crit("unsupported on-disk db engine", "detected", detected)
		}
		if err != nil {
			log.Crit("open key-value store", "err", err)
		}
		db, err := rawdb.Open(kv, rawdb.OpenOptions{
			Ancient:  filepath.Join(*chaindata, "ancient"),
			ReadOnly: true,
		})
		if err != nil {
			log.Crit("open chaindata", "err", err)
		}
		defer db.Close()

		headHash := rawdb.ReadHeadBlockHash(db)
		h, ok := rawdb.ReadHeaderNumber(db, headHash)
		if !ok {
			log.Crit("could not resolve head block number", "headHash", headHash)
		}
		head = h
		if *end != 0 {
			if *end > head {
				log.Crit("--end is beyond chain head", "end", *end, "head", head)
			}
			head = *end
		}

		// hVM-activation gate: the live apply path (core/state_processor.go, core/blockchain.go) difficulty-enforces
		// a block's BtcAttr batch ONLY when config.IsHvm0(header.Time). scanBtcAttrHistory mirrors that predicate (a
		// TIMESTAMP, not a height). For canonical input it is defense-in-depth — the apply path already rejects a
		// pre-activation block carrying a BtcAttr tx — not a dropper of real grandfathered batches.
		genHash := rawdb.ReadCanonicalHash(db, 0)
		cfg := rawdb.ReadChainConfig(db, genHash)
		if cfg == nil {
			log.Crit("could not read chain config (cannot apply the hVM0-activation gate)", "genesis", genHash)
		}
		if cfg.Hvm0Time == nil {
			log.Crit("chain config has no Hvm0Time: this datadir's chain never activated hVM Phase 0 (wrong network / non-hVM node?) — "+
				"reconstruction would silently emit an EMPTY fixture, so refuse rather than produce a misleading all-skipped result", "genesis", genHash)
		}
		scan = func(w io.Writer) (scanResult, error) {
			return scanBtcAttrHistory(db, cfg, *start, head, *allowGaps, w)
		}
	} else {
		c, err := rpc.DialContext(ctx, *rpcURL)
		if err != nil {
			log.Crit("dial --rpc endpoint", "rpc", *rpcURL, "err", err)
		}
		defer c.Close()

		// Network guard, the RPC counterpart of the chaindata path's missing-Hvm0Time crit: assert the endpoint's
		// chainId before scanning so a wrong-Hemi-network endpoint (e.g. a testnet3 node when mainnet was intended,
		// which also carries type-0x7C txs) fails loud instead of silently producing a mislabeled fixture. The
		// detected chainId is always logged for visibility even when --chainid is unset.
		var gotChainID hexutil.Uint64
		if err := c.CallContext(ctx, &gotChainID, "eth_chainId"); err != nil {
			log.Crit("eth_chainId (is --rpc an op-geth archive endpoint?)", "rpc", *rpcURL, "err", err)
		}
		if *chainID != 0 && uint64(gotChainID) != *chainID {
			log.Crit("--rpc endpoint chainId does not match --chainid (wrong network?)", "want", *chainID, "got", uint64(gotChainID))
		}

		var headHex hexutil.Uint64
		if err := c.CallContext(ctx, &headHex, "eth_blockNumber"); err != nil {
			log.Crit("eth_blockNumber (is --rpc an op-geth archive endpoint?)", "rpc", *rpcURL, "err", err)
		}
		head = uint64(headHex)
		if *end != 0 {
			if *end > head {
				log.Crit("--end is beyond chain head", "end", *end, "head", head)
			}
			head = *end
		}
		if *hvm0Time != 0 {
			log.Info("reconstructing from RPC (applying --hvm0-time activation gate)",
				"rpc", *rpcURL, "chainId", uint64(gotChainID), "hvm0Time", *hvm0Time, "start", *start, "end", head)
		} else {
			log.Info("reconstructing from RPC (no activation gate; pass --hvm0-time on networks with pre-activation BtcAttr commits, e.g. testnet3)",
				"rpc", *rpcURL, "chainId", uint64(gotChainID), "start", *start, "end", head)
		}
		scan = func(w io.Writer) (scanResult, error) {
			return scanBtcAttrHistoryRPC(ctx, c, *start, head, *allowGaps, *hvm0Time, w)
		}
	}

	var outFile *os.File // a sibling temp file we write to and atomically rename onto *outPath on success
	var tmpPath string
	// fatal removes the not-yet-renamed temp file, then log.Crit-exits. log.Crit calls os.Exit, which skips the
	// deferred cleanup below, so a bare log.Crit on a failure path would orphan a .btcattr-reconstruct-*.tmp in the
	// output dir (*outPath itself is never touched until the success rename). For stdout output tmpPath is "" (no-op).
	fatal := func(msg string, logCtx ...interface{}) {
		if tmpPath != "" {
			_ = outFile.Close()
			_ = os.Remove(tmpPath)
		}
		log.Crit(msg, logCtx...)
	}
	var w *bufio.Writer
	if *outPath != "" {
		// Write to a SIBLING temp file and rename onto *outPath only on the success path. Creating *outPath directly
		// would TRUNCATE a previously-good fixture before this run is known to succeed, so a later failure would have
		// already destroyed it. Temp+rename keeps the prior fixture intact on ANY failure.
		var terr error
		outFile, terr = os.CreateTemp(filepath.Dir(*outPath), ".btcattr-reconstruct-*.ndjson.tmp")
		if terr != nil {
			log.Crit("create temp output", "err", terr)
		}
		tmpPath = outFile.Name()
		defer func() { // close + remove the temp on any exit unless it was renamed into place (tmpPath cleared)
			_ = outFile.Close()
			if tmpPath != "" {
				_ = os.Remove(tmpPath)
			}
		}()
		w = bufio.NewWriter(outFile)
	} else {
		w = bufio.NewWriter(os.Stdout)
	}

	res, scanErr := scan(w)
	if scanErr == nil {
		if err := w.Flush(); err != nil {
			scanErr = fmt.Errorf("flush output: %w", err)
		}
	}
	if scanErr != nil {
		// The prior *outPath fixture is left INTACT: the deferred cleanup removes only our temp file, never *outPath.
		switch {
		case errors.Is(scanErr, errMissingBlocks):
			fatal("a source block was unavailable in the scanned range — the reconstructed fixture would be "+
				"INCOMPLETE (a --chaindata snap-synced node lacks pre-pivot blocks; a --rpc endpoint may be pruned or "+
				"behind the tip); run against a full-history / archive source. "+
				"--allow-gaps overrides this for DIAGNOSTIC runs only: a gap orphans every header after it from the gate's "+
				"genesis BFS (reported as unconnected, not difficulty-validated), and the coverage pin only catches gaps "+
				"that break connectivity to the pinned tip height — do NOT ship an --allow-gaps fixture as a clean proof",
				"hash_missing", res.hashMissing, "block_missing", res.blockMissing, "start", *start, "end", head)
		case errors.Is(scanErr, errVacuousFixture):
			fatal("reconstruction produced a vacuous fixture: zero BTC headers across the emitted BtcAttr lines "+
				"(wrong --start/--end window, a datadir whose canonical chain carries no committed BTC headers, or only "+
				"header-less BtcAttr txs) — refusing to write an empty/misleading fixture",
				"btcattr_lines", res.emitted, "raw_headers", res.rawHeaders, "scanned_blocks", res.scanned, "start", *start, "end", head)
		default:
			fatal("reconstruction failed", "err", scanErr)
		}
	}
	// Success: close the temp and atomically rename it onto --out (the prior fixture, if any, is replaced only now).
	if tmpPath != "" {
		if cerr := outFile.Close(); cerr != nil {
			fatal("close temp output", "err", cerr)
		}
		if rerr := os.Rename(tmpPath, *outPath); rerr != nil {
			fatal("rename temp output onto --out", "err", rerr)
		}
		tmpPath = "" // renamed into place; stop the deferred cleanup from removing it
	}
	log.Info("reconstruction complete", "scanned_blocks", res.scanned, "btcattr_lines", res.emitted, "raw_headers", res.rawHeaders, "hash_missing", res.hashMissing, "block_missing", res.blockMissing, "start", *start, "end", head)
}
