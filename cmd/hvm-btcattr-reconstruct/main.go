// Copyright 2024 The go-ethereum Authors
// This file is part of go-ethereum. Licensed under the GNU GPL v3.

// hvm-btcattr-reconstruct reconstructs, from an op-geth chaindata directory, the NDJSON stream of every
// Bitcoin header ever committed to hVM consensus via a BtcAttributesDeposited tx — the input fixture to the
// differential-replay gate (core/vm/btcdiff_{mainnet,testnet3}_history_verify_test.go and
// core/blockchain_hvm_mainnet_replay_test.go), which read it via the HEMI_MAINNET_VERIFY / HEMI_TESTNET3_VERIFY
// env vars.
//
// For each canonical L2 block in [start, head] whose transactions contain a BtcAttributesDeposited tx, it
// emits one line: {"blk":<L2 height>,"tip":"<canonical BTC tip hash hex>","hdrs":["<80-byte header hex>",...]}.
// The gate then asserts the committed history is clean under the network's params, so the proof is reproducible
// from the source code plus a node's chaindata. Point HEMI_MAINNET_VERIFY at the output, and set
// HEMI_HISTORY_GATE_REQUIRED=1 to make the gate fail (not skip) when the fixture is absent.
//
// Usage:
//
//	hvm-btcattr-reconstruct --chaindata <geth-datadir>/geth/chaindata [--start N] [--end H] [--out file.ndjson]
//
// Pin --end H for a deterministic, reproducible bounded fixture (omit / 0 = chain head).
package main

import (
	"bufio"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/ethdb/leveldb"
	"github.com/ethereum/go-ethereum/ethdb/pebble"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
)

type ndjsonLine struct {
	Blk  uint64   `json:"blk"`
	Tip  string   `json:"tip"`
	Hdrs []string `json:"hdrs"`
}

// Sentinel errors returned by scanBtcAttrHistory so callers (and unit tests) can distinguish the fatal
// fixture-integrity conditions from incidental I/O errors. main() maps each to a log.Crit + output cleanup.
var (
	// errMissingBlocks: a canonical block was absent in the scanned range and --allow-gaps was not set — the
	// fixture would be incomplete (e.g. a snap-synced node lacking pre-pivot blocks).
	errMissingBlocks = errors.New("chaindata is missing canonical blocks in the scanned range")
	// errVacuousFixture: zero BtcAttr lines, or lines carrying zero actual BTC headers — useless as a proof.
	errVacuousFixture = errors.New("reconstruction produced a vacuous fixture: zero BTC headers across the emitted BtcAttr lines")
)

// progressLogInterval is the number of emitted BtcAttr lines between reconstruction progress log lines.
const progressLogInterval = 5000

// scanResult holds the counters scanBtcAttrHistory accumulates while walking the canonical chain.
type scanResult struct {
	emitted, scanned, missing, rawHeaders int
}

// scanBtcAttrHistory walks canonical L2 blocks in [start, end] and writes to w one NDJSON line per block carrying
// a BtcAttributesDeposited tx (applying the IsHvm0 activation gate). It returns errors (errMissingBlocks /
// errVacuousFixture / wrapped I/O errors) instead of crashing, so the walk logic stays unit-testable against an
// in-memory db while main() owns the log.Crit + partial-output cleanup.
func scanBtcAttrHistory(db ethdb.Database, cfg *params.ChainConfig, start, end uint64, allowGaps bool, w io.Writer) (scanResult, error) {
	var res scanResult
	for n := start; n <= end; n++ {
		canon := rawdb.ReadCanonicalHash(db, n)
		if canon == (common.Hash{}) {
			res.missing++
			continue
		}
		block := rawdb.ReadBlock(db, canon, n)
		if block == nil {
			res.missing++
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
		hdrs := make([]string, 0, len(bad.Headers))
		for i := range bad.Headers {
			hdrs = append(hdrs, hex.EncodeToString(bad.Headers[i][:]))
		}
		// Emit the canonical tip in DISPLAY (byte-reversed) order — the form chainhash.NewHashFromStr expects,
		// which the replay gate (core/blockchain_hvm_mainnet_replay_test.go) uses to parse it back. CanonicalTip
		// is stored internal-order; chainhash.Hash.String() renders display order.
		ln := ndjsonLine{Blk: n, Tip: chainhash.Hash(bad.CanonicalTip).String(), Hdrs: hdrs}
		b, err := json.Marshal(ln)
		if err != nil {
			return res, fmt.Errorf("marshal line at block %d: %w", n, err)
		}
		if _, err := w.Write(append(b, '\n')); err != nil {
			return res, fmt.Errorf("write line: %w", err)
		}
		res.emitted++
		res.rawHeaders += len(hdrs)
		if res.emitted%progressLogInterval == 0 {
			log.Info("reconstructing", "L2height", n, "btcattr_lines", res.emitted)
		}
	}
	if res.missing > 0 && !allowGaps {
		return res, errMissingBlocks
	}
	// Fail fast on a vacuous fixture: zero LINES, or lines that carry zero actual BTC headers (a BtcAttr tx with
	// no headers is valid, so an all-header-less file would pass an emitted-only check yet be useless).
	if res.emitted == 0 || res.rawHeaders == 0 {
		return res, errVacuousFixture
	}
	return res, nil
}

func main() {
	chaindata := flag.String("chaindata", "", "path to the op-geth chaindata directory (e.g. <datadir>/geth/chaindata)")
	dbKind := flag.String("db", "auto", "key-value backend: auto (detect from disk), pebble, or leveldb")
	start := flag.Uint64("start", 0, "first L2 block height to scan (default 0; set to hVM Phase-0 activation to skip pre-hVM blocks)")
	end := flag.Uint64("end", 0, "last L2 block height to scan (0 = chain head; pin this for a deterministic, reproducible fixture)")
	allowGaps := flag.Bool("allow-gaps", false, "permit missing canonical blocks in the scanned range (default false: a missing block means an incomplete fixture, e.g. on a snap-synced node — fail loudly)")
	outPath := flag.String("out", "", "output NDJSON path (default: stdout)")
	flag.Parse()

	if *chaindata == "" {
		fmt.Fprintln(os.Stderr, "error: --chaindata is required")
		flag.Usage()
		os.Exit(2)
	}

	// Detect the on-disk engine. geth refuses to open a leveldb dir as pebble or vice-versa, and this mirrors that:
	// opening with the wrong backend can otherwise silently yield a stale/partial-but-resolvable head and a
	// plausible-but-wrong fixture.
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
	head, ok := rawdb.ReadHeaderNumber(db, headHash)
	if !ok {
		log.Crit("could not resolve head block number", "headHash", headHash)
	}
	if *end != 0 {
		if *end > head {
			log.Crit("--end is beyond chain head", "end", *end, "head", head)
		}
		head = *end
	}

	// hVM-activation gate: the live apply path (core/state_processor.go, core/blockchain.go) difficulty-enforces a
	// block's BtcAttr batch ONLY when config.IsHvm0(header.Time). scanBtcAttrHistory mirrors that predicate (a
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

	var outFile *os.File // a sibling temp file we write to and atomically rename onto *outPath on success
	var tmpPath string
	// fatal removes the not-yet-renamed temp file, then log.Crit-exits. log.Crit calls os.Exit, which skips the
	// deferred cleanup below, so a bare log.Crit on a failure path would orphan a .btcattr-reconstruct-*.tmp in the
	// output dir (*outPath itself is never touched until the success rename). For stdout output tmpPath is "" (no-op).
	fatal := func(msg string, ctx ...interface{}) {
		if tmpPath != "" {
			_ = outFile.Close()
			_ = os.Remove(tmpPath)
		}
		log.Crit(msg, ctx...)
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

	res, scanErr := scanBtcAttrHistory(db, cfg, *start, head, *allowGaps, w)
	if scanErr == nil {
		if err := w.Flush(); err != nil {
			scanErr = fmt.Errorf("flush output: %w", err)
		}
	}
	if scanErr != nil {
		// The prior *outPath fixture is left INTACT: the deferred cleanup removes only our temp file, never *outPath.
		switch {
		case errors.Is(scanErr, errMissingBlocks):
			fatal("chaindata is missing canonical blocks in the scanned range — the reconstructed fixture would be "+
				"INCOMPLETE (e.g. a snap-synced node lacks pre-pivot blocks); run against a full-history node. "+
				"--allow-gaps overrides this for DIAGNOSTIC runs only: a gap orphans every header after it from the gate's "+
				"genesis BFS (reported as unconnected, not difficulty-validated), and the coverage pin only catches gaps "+
				"that break connectivity to the pinned tip height — do NOT ship an --allow-gaps fixture as a clean proof",
				"missing", res.missing, "start", *start, "end", head)
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
	log.Info("reconstruction complete", "scanned_blocks", res.scanned, "btcattr_lines", res.emitted, "raw_headers", res.rawHeaders, "missing", res.missing, "start", *start, "end", head)
}
