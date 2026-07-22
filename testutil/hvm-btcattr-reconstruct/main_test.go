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

package main

import (
	"bytes"
	"context"
	"encoding/hex"
	"encoding/json"
	"io"
	"math/big"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/ethdb/leveldb"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/rpc"
	"github.com/stretchr/testify/require"
)

// hvm0TestTime is the activation timestamp the test chain config uses; blocks at or after it are hVM0-active.
const hvm0TestTime = uint64(1000)

func testCfg() *params.ChainConfig {
	cfg := *params.TestChainConfig
	t := hvm0TestTime
	cfg.Hvm0Time = &t
	return &cfg
}

// wireHdr builds a distinct, well-formed 80-byte BTC header (the content is irrelevant to the scanner — it only
// serializes and hex-encodes; distinctness via nonce keeps hashes/hex unique per header).
func wireHdr(nonce uint32) wire.BlockHeader {
	return wire.BlockHeader{Version: 1, Bits: 0x207fffff, Nonce: nonce}
}

func wireHdrTip(nonce uint32) chainhash.Hash {
	h := wireHdr(nonce)
	return h.BlockHash()
}

func serializeHdr(t *testing.T, h wire.BlockHeader) string {
	t.Helper()
	var buf bytes.Buffer
	require.NoError(t, h.Serialize(&buf))
	require.Equal(t, types.BitcoinHeaderLengthBytes, buf.Len(), "a BTC header must serialize to 80 bytes")
	return hex.EncodeToString(buf.Bytes())
}

func mkBtcAttrTx(t *testing.T, tip *chainhash.Hash, hdrs []wire.BlockHeader) *types.Transaction {
	t.Helper()
	bad, err := types.MakeBtcAttributesDepositedTx(tip, hdrs)
	require.NoError(t, err)
	return types.NewTx(bad)
}

// putCanonBlock stores a canonical L2 block (header + body + canonical-hash mapping) at num with the given time.
func putCanonBlock(t *testing.T, db ethdb.Database, num, time uint64, txs types.Transactions) {
	t.Helper()
	blk := types.NewBlockWithHeader(&types.Header{Number: new(big.Int).SetUint64(num), Time: time}).
		WithBody(types.Body{Transactions: txs})
	rawdb.WriteBlock(db, blk)
	rawdb.WriteCanonicalHash(db, blk.Hash(), num)
}

func parseLines(t *testing.T, out []byte) []ndjsonLine {
	t.Helper()
	var lines []ndjsonLine
	for _, raw := range strings.Split(strings.TrimSpace(string(out)), "\n") {
		if raw == "" {
			continue
		}
		var ln ndjsonLine
		require.NoError(t, json.Unmarshal([]byte(raw), &ln))
		lines = append(lines, ln)
	}
	return lines
}

// TestScanEmitsOnlyHvm0BtcAttrBlocks: the scanner emits exactly one line per hVM0-active block carrying a BtcAttr
// tx, in order, with the headers hex-encoded and the canonical tip rendered in display (byte-reversed) order that
// round-trips through chainhash.NewHashFromStr — the exact contract the replay gate consumes.
func TestScanEmitsOnlyHvm0BtcAttrBlocks(t *testing.T) {
	db := rawdb.NewMemoryDatabase()
	cfg := testCfg()

	tip := wireHdrTip(42)
	h0, h1 := wireHdr(1), wireHdr(2)

	putCanonBlock(t, db, 0, 500, nil)                                                                   // pre-Hvm0, no tx
	putCanonBlock(t, db, 1, 2000, nil)                                                                  // hVM0-active, no BtcAttr tx -> skipped
	putCanonBlock(t, db, 2, 2000, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{h0, h1})}) // emitted
	putCanonBlock(t, db, 3, 2000, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{h0})})     // emitted

	var out bytes.Buffer
	res, err := scanBtcAttrHistory(db, cfg, 0, 3, false, &out)
	require.NoError(t, err)
	require.Equal(t, 2, res.emitted)
	require.Equal(t, 4, res.scanned)
	require.Equal(t, 0, res.missing())
	require.Equal(t, 3, res.rawHeaders)

	lines := parseLines(t, out.Bytes())
	require.Len(t, lines, 2)
	require.Equal(t, uint64(2), lines[0].Blk)
	require.Equal(t, []string{serializeHdr(t, h0), serializeHdr(t, h1)}, lines[0].Hdrs)
	require.Equal(t, uint64(3), lines[1].Blk)
	require.Equal(t, []string{serializeHdr(t, h0)}, lines[1].Hdrs)

	// tip must be display-order and round-trip back to the stored internal-order hash.
	rt, err := chainhash.NewHashFromStr(lines[0].Tip)
	require.NoError(t, err)
	require.Equal(t, tip, *rt, "emitted tip must round-trip through chainhash.NewHashFromStr to the original")
}

// TestScanSkipsPreHvm0BtcAttr: a BtcAttr tx in a block BEFORE hVM0 activation is grandfathered out of the
// reconstructed history (the activation predicate is the block timestamp, not its height).
func TestScanSkipsPreHvm0BtcAttr(t *testing.T) {
	db := rawdb.NewMemoryDatabase()
	tip := wireHdrTip(9)
	putCanonBlock(t, db, 0, 500, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)})})  // pre-Hvm0
	putCanonBlock(t, db, 1, 2000, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(2)})}) // active

	var out bytes.Buffer
	res, err := scanBtcAttrHistory(db, testCfg(), 0, 1, false, &out)
	require.NoError(t, err)
	require.Equal(t, 1, res.emitted, "only the post-activation BtcAttr block is emitted")
	lines := parseLines(t, out.Bytes())
	require.Len(t, lines, 1)
	require.Equal(t, uint64(1), lines[0].Blk)
}

// TestScanGapWithoutAllowGapsFails: a missing canonical block in the range is a fatal incomplete-fixture
// condition (errMissingBlocks) unless --allow-gaps is set.
func TestScanGapWithoutAllowGapsFails(t *testing.T) {
	db := rawdb.NewMemoryDatabase()
	tip := wireHdrTip(9)
	putCanonBlock(t, db, 0, 2000, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)})})
	// block 1 deliberately absent
	putCanonBlock(t, db, 2, 2000, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(2)})})

	var out bytes.Buffer
	res, err := scanBtcAttrHistory(db, testCfg(), 0, 2, false, &out)
	require.ErrorIs(t, err, errMissingBlocks)
	require.Equal(t, 1, res.hashMissing, "an absent canonical-hash mapping counts as hashMissing")
	require.Equal(t, 0, res.blockMissing)
	require.Equal(t, 1, res.missing())
}

// TestScanGapWithAllowGapsSucceeds: --allow-gaps downgrades a gap to non-fatal (DIAGNOSTIC runs), so a
// non-vacuous result is returned despite the missing block.
func TestScanGapWithAllowGapsSucceeds(t *testing.T) {
	db := rawdb.NewMemoryDatabase()
	tip := wireHdrTip(9)
	putCanonBlock(t, db, 0, 2000, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)})})
	putCanonBlock(t, db, 2, 2000, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(2)})})

	var out bytes.Buffer
	res, err := scanBtcAttrHistory(db, testCfg(), 0, 2, true, &out)
	require.NoError(t, err)
	require.Equal(t, 1, res.hashMissing)
	require.Equal(t, 1, res.missing())
	require.Equal(t, 2, res.emitted)
	require.Equal(t, 2, res.scanned, "scanned counts only successfully-read blocks; the gap must NOT inflate it")
}

// TestScanVacuousNoLinesFails: a range with no BtcAttr-carrying blocks yields zero lines — fatal errVacuousFixture.
func TestScanVacuousNoLinesFails(t *testing.T) {
	db := rawdb.NewMemoryDatabase()
	putCanonBlock(t, db, 0, 2000, nil)
	putCanonBlock(t, db, 1, 2000, nil)

	var out bytes.Buffer
	res, err := scanBtcAttrHistory(db, testCfg(), 0, 1, false, &out)
	require.ErrorIs(t, err, errVacuousFixture)
	require.Equal(t, 0, res.emitted)
}

// TestScanVacuousHeaderlessLinesFails: BtcAttr txs that carry NO headers are individually valid, so emitted>0,
// but the fixture is still useless (rawHeaders==0) — must be caught as errVacuousFixture.
func TestScanVacuousHeaderlessLinesFails(t *testing.T) {
	db := rawdb.NewMemoryDatabase()
	tip := wireHdrTip(9)
	putCanonBlock(t, db, 0, 2000, types.Transactions{mkBtcAttrTx(t, &tip, nil)})
	putCanonBlock(t, db, 1, 2000, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{})})

	var out bytes.Buffer
	res, err := scanBtcAttrHistory(db, testCfg(), 0, 1, false, &out)
	require.ErrorIs(t, err, errVacuousFixture)
	require.Greater(t, res.emitted, 0, "header-less BtcAttr lines are emitted...")
	require.Equal(t, 2, res.emitted, "exactly 2 header-less BtcAttr txs must be emitted")
	require.Equal(t, 0, res.rawHeaders, "...but carry zero real headers, so the fixture is vacuous")
}

// TestScanRespectsStartEndWindow: only blocks within [start,end] are considered; BtcAttr blocks outside the
// window are neither scanned nor emitted.
func TestScanRespectsStartEndWindow(t *testing.T) {
	db := rawdb.NewMemoryDatabase()
	tip := wireHdrTip(9)
	for n := uint64(0); n <= 4; n++ {
		putCanonBlock(t, db, n, 2000, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(uint32(n + 1))})})
	}
	var out bytes.Buffer
	res, err := scanBtcAttrHistory(db, testCfg(), 1, 3, false, &out)
	require.NoError(t, err)
	require.Equal(t, 3, res.emitted)
	lines := parseLines(t, out.Bytes())
	require.Equal(t, uint64(1), lines[0].Blk)
	require.Equal(t, uint64(3), lines[len(lines)-1].Blk)
}

// TestScanExtractErrorSurfaces covers the scanBtcAttrHistory extract-error arm: a block carrying TWO
// BtcAttributesDeposited txs makes ExtractBtcAttrData fail, which the scanner must surface (block-number wrapped),
// not swallow. Skipping the error would silently drop a malformed/double-committed block.
func TestScanExtractErrorSurfaces(t *testing.T) {
	db := rawdb.NewMemoryDatabase()
	tip := wireHdrTip(9)
	// hVM0-active block with TWO BtcAttr txs -> ExtractBtcAttrData "more than one ..." error.
	putCanonBlock(t, db, 0, 2000, types.Transactions{
		mkBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)}),
		mkBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(2)}),
	})
	var out bytes.Buffer
	_, err := scanBtcAttrHistory(db, testCfg(), 0, 0, false, &out)
	require.Error(t, err)
	require.ErrorContains(t, err, "extract BtcAttr data at block 0", "the extract error must be surfaced with the block number")
	require.NotErrorIs(t, err, errMissingBlocks)
	require.NotErrorIs(t, err, errVacuousFixture)
}

// TestScanMissingBlockBodyCountsAsGap covers the second missing-block branch: a canonical hash present but the
// block BODY absent (ReadBlock==nil — the snap-synced/pruned-body case). This is distinct from the no-canonical-
// hash branch; without the nil-guard block.Time() would nil-panic.
func TestScanMissingBlockBodyCountsAsGap(t *testing.T) {
	db := rawdb.NewMemoryDatabase()
	tip := wireHdrTip(9)
	putCanonBlock(t, db, 0, 2000, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)})}) // non-vacuous
	// Height 1: write only the canonical-hash mapping, no body.
	var bogus common.Hash
	bogus[0] = 0xab
	rawdb.WriteCanonicalHash(db, bogus, 1)

	var out bytes.Buffer
	res, err := scanBtcAttrHistory(db, testCfg(), 0, 1, false, &out)
	require.ErrorIs(t, err, errMissingBlocks, "a present canonical hash with an absent body is a gap")
	require.Equal(t, 1, res.blockMissing, "a present canonical hash with an absent body counts as blockMissing, not hashMissing")
	require.Equal(t, 0, res.hashMissing)
	require.Equal(t, 1, res.missing())

	// With --allow-gaps the body-absent block is tolerated and the height-0 line is still emitted.
	out.Reset()
	res, err = scanBtcAttrHistory(db, testCfg(), 0, 1, true, &out)
	require.NoError(t, err)
	require.Equal(t, 1, res.blockMissing)
	require.Equal(t, 1, res.missing())
	require.Equal(t, 1, res.emitted)
}

const reconstructCritChildEnv = "RECONSTRUCT_MAIN_CRIT_CHILD"

// TestReconstructMainCritChild is the subprocess child for TestReconstructMainGuards. It calls main() with a
// crafted --chaindata dir (marker files only — rawdb.PreexistingDatabase is a pure file-stat check, so no real DB
// is needed) and the root logger routed to stderr, so the parent can observe the log.Crit (os.Exit) message.
func TestReconstructMainCritChild(t *testing.T) {
	mode := os.Getenv(reconstructCritChildEnv)
	if mode == "" {
		t.Skip("child-only: driven by TestReconstructMainGuards via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	dir := t.TempDir()
	writePebbleMarkers := func() {
		require.NoError(t, os.WriteFile(filepath.Join(dir, "CURRENT"), []byte("x"), 0o644))        // CURRENT => a db exists
		require.NoError(t, os.WriteFile(filepath.Join(dir, "OPTIONS-000001"), []byte("x"), 0o644)) // OPTIONS* => pebble
	}
	switch mode {
	case "no-db":
		// Empty dir: no CURRENT -> PreexistingDatabase == "" -> the no-database guard crits.
		os.Args = []string{"hvm-btcattr-reconstruct", "--chaindata", dir}
	case "conflict":
		// detected==pebble, but --db=leveldb -> the conflict guard crits before any DB open.
		writePebbleMarkers()
		os.Args = []string{"hvm-btcattr-reconstruct", "--chaindata", dir, "--db", "leveldb"}
	case "no-conflict-control":
		// detected==pebble and --db=pebble MATCHES -> the conflict guard must NOT fire (a later open-failure crit
		// is expected instead). Guards against the guard firing even when the engines agree.
		writePebbleMarkers()
		os.Args = []string{"hvm-btcattr-reconstruct", "--chaindata", dir, "--db", "pebble"}
	default:
		t.Fatalf("unknown child mode %q", mode)
	}
	main()
	t.Fatalf("main returned for mode %q; expected a log.Crit -> os.Exit before returning", mode)
}

// TestReconstructMainGuards drives main()'s db-detect + conflict guards via subprocess re-exec. The no-database
// guard and the --db-vs-detected conflict guard are the safety net against opening the wrong engine and silently
// producing a wrong fixture.
func TestReconstructMainGuards(t *testing.T) {
	cases := []struct {
		mode            string
		wantSub         string // substring the crit MUST carry (empty for the control)
		wantNotConflict bool   // the conflict crit must be ABSENT (the engines-agree control)
	}{
		{"no-db", "no pre-existing key-value database", false},
		{"conflict", "conflicts with the on-disk engine", false},
		{"no-conflict-control", "", true},
	}
	for _, tc := range cases {
		t.Run(tc.mode, func(t *testing.T) {
			cmd := exec.Command(os.Args[0], "-test.run=^TestReconstructMainCritChild$", "-test.v")
			cmd.Env = append(os.Environ(), reconstructCritChildEnv+"="+tc.mode)
			out, err := cmd.CombinedOutput()

			var ee *exec.ExitError
			require.ErrorAs(t, err, &ee, "child must exit non-zero, output:\n%s", string(out))
			require.False(t, ee.Success(), "child must report failure")
			if tc.wantSub != "" {
				require.Contains(t, string(out), tc.wantSub, "mode %q must crit with the expected guard message", tc.mode)
			}
			if tc.wantNotConflict {
				require.NotContains(t, string(out), "conflicts with the on-disk engine",
					"a matching --db must NOT trip the conflict guard")
			}
			require.NotContains(t, string(out), "main returned for mode",
				"main must os.Exit (log.Crit) before returning for mode %q", tc.mode)
		})
	}
}

// TestScanNDJSONLineGolden freezes the emitted NDJSON wire schema the replay gate consumes. The other producer
// tests route output through parseLines->json.Unmarshal into the producer's OWN struct, so a tag rename
// (blk->block, tip->canonicaltip, hdrs->headers) survives that symmetric round-trip silently while leaving the gate
// to unmarshal zero-filled garbage and verify nothing. This pins the exact key names, order, compact form, single
// trailing newline, and the DISPLAY-order (byte-reversed) tip the gate's chainhash.NewHashFromStr requires. The
// btcd-version-dependent header/tip bytes are computed at test time; the literal key-name layout is the golden.
func TestScanNDJSONLineGolden(t *testing.T) {
	db := rawdb.NewMemoryDatabase()
	tip := wireHdrTip(42)
	h1, h2 := wireHdr(1), wireHdr(2)
	putCanonBlock(t, db, 7, 2000, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{h1, h2})})

	var out bytes.Buffer
	_, err := scanBtcAttrHistory(db, testCfg(), 7, 7, false, &out)
	require.NoError(t, err)

	// Golden schema: literal key names blk/tip/hdrs, in this order, compact (no spaces), one trailing newline.
	want := `{"blk":7,"tip":"` + chainhash.Hash(tip).String() + `","hdrs":["` + serializeHdr(t, h1) + `","` + serializeHdr(t, h2) + `"]}` + "\n"
	require.Equal(t, want, out.String(), "the NDJSON wire schema (key names/order/compactness/newline) is frozen")

	// The tip MUST be display (byte-reversed) order, not the internal bytes — the gate's chainhash.NewHashFromStr
	// contract. Lock the reversal so an internal/display flip on both sides of a refactor cannot pass.
	require.Contains(t, out.String(), `"tip":"`+chainhash.Hash(tip).String()+`"`, "tip must be display order")
	require.NotContains(t, out.String(), hex.EncodeToString(tip[:]), "tip must NOT be emitted in internal byte order")
}

const reconstructSuccessChildEnv = "RECONSTRUCT_MAIN_SUCCESS_CHILD"

// seedRealLeveldbChaindata writes a minimal but REAL on-disk leveldb chaindata at dir: a pre-hVM0 genesis (block 0,
// carrying the chain config keyed by the genesis hash, exactly as geth persists it), one hVM0-active canonical block
// (block 1) bearing a BtcAttr tx with one BTC header, and the head pointer. It mirrors main.go's own open path
// (leveldb.New + rawdb.Open) so the resulting marker files are the leveldb shape PreexistingDatabase must detect.
// The store is fully closed before return so the re-exec'd child can re-open it (leveldb takes an exclusive lock).
func seedRealLeveldbChaindata(t *testing.T, dir string) {
	t.Helper()
	seedRealLeveldbChaindataWithConfig(t, dir, testCfg())
}

// seedRealLeveldbChaindataWithConfig is seedRealLeveldbChaindata with an explicit chain config (so tests can seed a
// config without Hvm0Time to exercise main()'s never-activated-hVM guard).
func seedRealLeveldbChaindataWithConfig(t *testing.T, dir string, cfg *params.ChainConfig) {
	t.Helper()
	kv, err := leveldb.New(dir, 256, 0, "", false)
	require.NoError(t, err)
	// Open with the same Ancient (freezer) path main.go uses so the empty freezer index files exist on disk; main's
	// read-only re-open fails outright if the freezer was never initialized.
	db, err := rawdb.Open(kv, rawdb.OpenOptions{Ancient: filepath.Join(dir, "ancient")})
	require.NoError(t, err)

	gen := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(0), Time: hvm0TestTime - 500}) // pre-hVM0
	rawdb.WriteBlock(db, gen)
	rawdb.WriteCanonicalHash(db, gen.Hash(), 0)
	rawdb.WriteChainConfig(db, gen.Hash(), cfg) // config is keyed by the genesis hash, like geth

	tip := wireHdrTip(7)
	b1 := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(1), Time: hvm0TestTime + 1000, ParentHash: gen.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)})}})
	rawdb.WriteBlock(db, b1)
	rawdb.WriteCanonicalHash(db, b1.Hash(), 1)
	rawdb.WriteHeadBlockHash(db, b1.Hash())

	require.NoError(t, db.Close())
}

// TestReconstructMainSuccessChild is the subprocess child for TestReconstructMainSuccess: it points main() at a
// pre-seeded leveldb chaindata (path via env) and lets it run to completion. Unlike the crit child, main() RETURNS
// normally on success (no os.Exit), so the child simply returns and the test exits 0.
func TestReconstructMainSuccessChild(t *testing.T) {
	dir := os.Getenv(reconstructSuccessChildEnv)
	if dir == "" {
		t.Skip("child-only: driven by TestReconstructMainSuccess via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	out := os.Getenv(reconstructSuccessChildEnv + "_OUT")
	// No --db: force the auto-detect path to pick leveldb from the on-disk markers. --end defaults to 1 (the seeded
	// head) for the happy path; an override drives the out-of-bounds guard.
	end := os.Getenv(reconstructSuccessChildEnv + "_END")
	if end == "" {
		end = "1"
	}
	os.Args = []string{"hvm-btcattr-reconstruct", "--chaindata", dir, "--out", out, "--end", end}
	main()
}

// TestReconstructMainSuccess exercises main()'s entire happy path end to end (the one path every other main test
// crits out of): auto-detect the on-disk engine from a REAL leveldb dir, open it read-only, resolve the head,
// read the genesis-keyed chain config, scan [0..head], and write a non-vacuous fixture — exiting 0 with the
// "reconstruction complete" summary. It pins that auto-detect selects the correct backend (no --db given) AND that
// the emitted file carries exactly the one hVM0-active BtcAttr block (block 0 is pre-hVM0 and must be skipped).
func TestReconstructMainSuccess(t *testing.T) {
	dir := t.TempDir()
	seedRealLeveldbChaindata(t, dir)
	require.Equal(t, "leveldb", rawdb.PreexistingDatabase(dir), "seeding must produce a leveldb-shaped chaindata")
	outPath := filepath.Join(t.TempDir(), "fixture.ndjson")

	cmd := exec.Command(os.Args[0], "-test.run=^TestReconstructMainSuccessChild$", "-test.v")
	cmd.Env = append(os.Environ(),
		reconstructSuccessChildEnv+"="+dir,
		reconstructSuccessChildEnv+"_OUT="+outPath)
	out, err := cmd.CombinedOutput()
	require.NoError(t, err, "main must exit 0 on the happy path, output:\n%s", string(out))
	require.Contains(t, string(out), "reconstruction complete", "the success summary must be logged")
	require.Contains(t, string(out), "btcattr_lines=1", "exactly one hVM0-active BtcAttr block must be emitted")

	data, err := os.ReadFile(outPath)
	require.NoError(t, err, "main must write the --out fixture file")
	lines := parseLines(t, data)
	require.Len(t, lines, 1, "only block 1 (hVM0-active) is emitted; block 0 is pre-hVM0 and skipped")
	require.Equal(t, uint64(1), lines[0].Blk)
	require.Len(t, lines[0].Hdrs, 1, "the emitted line must carry the one seeded BTC header")
}

// TestReconstructMainEndBeyondHead pins main()'s out-of-bounds --end guard: an --end past the chain head must crit
// ("--end is beyond chain head") BEFORE scanning, refusing to produce an incomplete/misleading fixture. Subprocess
// re-exec against a REAL seeded leveldb (head=1) with --end=999.
func TestReconstructMainEndBeyondHead(t *testing.T) {
	dir := t.TempDir()
	seedRealLeveldbChaindata(t, dir) // canonical head = block 1
	require.Equal(t, "leveldb", rawdb.PreexistingDatabase(dir))
	outPath := filepath.Join(t.TempDir(), "fixture.ndjson")

	cmd := exec.Command(os.Args[0], "-test.run=^TestReconstructMainSuccessChild$", "-test.v")
	cmd.Env = append(os.Environ(),
		reconstructSuccessChildEnv+"="+dir,
		reconstructSuccessChildEnv+"_OUT="+outPath,
		reconstructSuccessChildEnv+"_END=999") // beyond head=1
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "an out-of-bounds --end must crit (os.Exit), output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "--end is beyond chain head", "the out-of-bounds --end guard must fire")
	require.NotContains(t, string(out), "reconstruction complete", "the scan must NOT run when --end is out of bounds")
}

// TestReconstructMainMissingHvm0TimeCrits pins main()'s fixture-integrity guard: a chaindata whose chain config has
// no Hvm0Time (the chain never activated hVM Phase 0 — wrong network / non-hVM node) must crit rather than silently
// emit an EMPTY/misleading fixture. Subprocess re-exec against a real seeded leveldb whose genesis-keyed config has
// Hvm0Time == nil.
func TestReconstructMainMissingHvm0TimeCrits(t *testing.T) {
	dir := t.TempDir()
	cfg := *params.TestChainConfig // a copy; Hvm0Time is nil here (never activated hVM)
	cfg.Hvm0Time = nil
	seedRealLeveldbChaindataWithConfig(t, dir, &cfg)
	require.Equal(t, "leveldb", rawdb.PreexistingDatabase(dir))
	outPath := filepath.Join(t.TempDir(), "fixture.ndjson")

	cmd := exec.Command(os.Args[0], "-test.run=^TestReconstructMainSuccessChild$", "-test.v")
	cmd.Env = append(os.Environ(),
		reconstructSuccessChildEnv+"="+dir,
		reconstructSuccessChildEnv+"_OUT="+outPath)
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "a config without Hvm0Time must crit, output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "chain config has no Hvm0Time", "the never-activated-hVM fixture-integrity guard must fire")
	require.NotContains(t, string(out), "reconstruction complete", "the scan must NOT run when Hvm0Time is absent")
}

// --- RPC source (--rpc) tests -----------------------------------------------------------------------------------

// testRPCTx / testRPCBlock are the eth_getBlockByNumber (full-tx) JSON shapes the fake server serves. Only the
// fields scanBtcAttrHistoryRPC reads (tx type + input) are load-bearing; to/number are included for realism.
type testRPCTx struct {
	Type  string `json:"type"`
	To    string `json:"to"`
	Input string `json:"input"`
}

type testRPCBlock struct {
	Number       string      `json:"number"`
	Timestamp    string      `json:"timestamp"`
	Transactions []testRPCTx `json:"transactions"`
}

// btcAttrCalldataHex returns the hex "0x..." calldata of a BtcAttributesDeposited tx carrying tip+hdrs — the exact
// bytes an archive node serves as the tx "input", so the RPC scanner decodes the identical payload the chaindata
// path reads via tx.Data().
func btcAttrCalldataHex(t *testing.T, tip *chainhash.Hash, hdrs []wire.BlockHeader) string {
	t.Helper()
	return hexutil.Encode(mkBtcAttrTx(t, tip, hdrs).Data())
}

// rpcBtcAttrTx builds a fake-server tx row for a BtcAttributesDeposited (type 0x7C) tx.
func rpcBtcAttrTx(t *testing.T, tip *chainhash.Hash, hdrs []wire.BlockHeader) testRPCTx {
	t.Helper()
	return testRPCTx{Type: btcAttrTxTypeHex, To: types.BtcAttributesDepositedSender, Input: btcAttrCalldataHex(t, tip, hdrs)}
}

// rpcOtherTx builds a fake-server tx row for a non-BtcAttr system tx (e.g. the L1-attributes deposit), which the
// RPC scanner must ignore.
func rpcOtherTx() testRPCTx {
	return testRPCTx{Type: "0x7e", To: "0x4200000000000000000000000000000000000015", Input: "0x098999be"}
}

func rpcBlk(num uint64, txs ...testRPCTx) *testRPCBlock {
	return &testRPCBlock{Number: hexutil.EncodeUint64(num), Transactions: txs}
}

// rpcBlkTS is rpcBlk with an explicit block timestamp (unix seconds), for exercising the --hvm0-time gate.
func rpcBlkTS(num, timeSec uint64, txs ...testRPCTx) *testRPCBlock {
	b := rpcBlk(num, txs...)
	b.Timestamp = hexutil.EncodeUint64(timeSec)
	return b
}

// testFakeRPCChainID is the chainId the fake server reports via eth_chainId (Hemi mainnet's real id), so the
// --chainid wrong-network guard can be exercised.
const testFakeRPCChainID = 43111

// startFakeRPCServer serves a minimal in-memory JSON-RPC endpoint answering eth_blockNumber (=> head) and
// eth_getBlockByNumber (=> the block from blocks, or JSON null if absent), so the RPC scanner + main()'s --rpc path
// run in CI with no live node. It handles the single-call requests rpc.Client.CallContext sends.
func startFakeRPCServer(t *testing.T, head uint64, blocks map[uint64]*testRPCBlock) *httptest.Server {
	t.Helper()
	mustJSON := func(v any) json.RawMessage {
		b, err := json.Marshal(v)
		if err != nil { // goroutine-safe: t.FailNow (require) must not be called off the test goroutine
			t.Errorf("fake rpc: marshal: %v", err)
			return json.RawMessage("null")
		}
		return b
	}
	srv := httptest.NewServer(http.HandlerFunc(func(wr http.ResponseWriter, r *http.Request) {
		body, err := io.ReadAll(r.Body)
		if err != nil {
			t.Errorf("fake rpc: read body: %v", err)
			return
		}
		var req struct {
			ID     json.RawMessage   `json:"id"`
			Method string            `json:"method"`
			Params []json.RawMessage `json:"params"`
		}
		if err := json.Unmarshal(body, &req); err != nil {
			t.Errorf("fake rpc: expects a single JSON-RPC request object, got: %s", body)
			return
		}
		var result json.RawMessage
		switch req.Method {
		case "eth_blockNumber":
			result = mustJSON(hexutil.EncodeUint64(head))
		case "eth_chainId":
			result = mustJSON(hexutil.EncodeUint64(testFakeRPCChainID))
		case "eth_getBlockByNumber":
			if len(req.Params) == 0 {
				t.Errorf("fake rpc: eth_getBlockByNumber requires params")
				return
			}
			var hexNum string
			if err := json.Unmarshal(req.Params[0], &hexNum); err != nil {
				t.Errorf("fake rpc: bad block-number param %s: %v", req.Params[0], err)
				return
			}
			n, err := hexutil.DecodeUint64(hexNum)
			if err != nil {
				t.Errorf("fake rpc: bad block-number hex %q: %v", hexNum, err)
				return
			}
			if b, ok := blocks[n]; ok {
				result = mustJSON(b)
			} else {
				result = json.RawMessage("null") // non-existent height => JSON null, the RPC scanner's gap signal
			}
		default:
			t.Errorf("fake rpc: unexpected method %q", req.Method)
			result = json.RawMessage("null")
		}
		wr.Header().Set("Content-Type", "application/json")
		_, _ = wr.Write([]byte(`{"jsonrpc":"2.0","id":` + string(req.ID) + `,"result":` + string(result) + `}`))
	}))
	t.Cleanup(srv.Close)
	return srv
}

func dialFakeRPC(t *testing.T, url string) *rpc.Client {
	t.Helper()
	c, err := rpc.DialContext(context.Background(), url)
	require.NoError(t, err)
	t.Cleanup(c.Close)
	return c
}

// TestScanBtcAttrHistoryRPCEmitsBtcAttrBlocks: the RPC scanner emits one line per block carrying a
// BtcAttributesDeposited (type 0x7C) tx, ignoring other system txs, with the same hex/display-order contract the
// chaindata scanner produces. The BtcAttr tx is placed at a non-zero index to prove index independence.
func TestScanBtcAttrHistoryRPCEmitsBtcAttrBlocks(t *testing.T) {
	tip := wireHdrTip(42)
	h0, h1 := wireHdr(1), wireHdr(2)
	blocks := map[uint64]*testRPCBlock{
		5: rpcBlk(5, rpcOtherTx()),                                                    // no BtcAttr tx -> skipped
		6: rpcBlk(6, rpcOtherTx(), rpcBtcAttrTx(t, &tip, []wire.BlockHeader{h0, h1})), // emitted (BtcAttr at index 1)
		7: rpcBlk(7, rpcBtcAttrTx(t, &tip, []wire.BlockHeader{h0})),                   // emitted
	}
	c := dialFakeRPC(t, startFakeRPCServer(t, 7, blocks).URL)

	var out bytes.Buffer
	res, err := scanBtcAttrHistoryRPC(context.Background(), c, 5, 7, false, 0, &out)
	require.NoError(t, err)
	require.Equal(t, 2, res.emitted)
	require.Equal(t, 3, res.scanned)
	require.Equal(t, 3, res.rawHeaders)
	require.Equal(t, 0, res.missing())

	lines := parseLines(t, out.Bytes())
	require.Len(t, lines, 2)
	require.Equal(t, uint64(6), lines[0].Blk)
	require.Equal(t, []string{serializeHdr(t, h0), serializeHdr(t, h1)}, lines[0].Hdrs)
	require.Equal(t, uint64(7), lines[1].Blk)
	require.Equal(t, []string{serializeHdr(t, h0)}, lines[1].Hdrs)

	rt, err := chainhash.NewHashFromStr(lines[0].Tip)
	require.NoError(t, err)
	require.Equal(t, tip, *rt, "emitted tip must round-trip through chainhash.NewHashFromStr")
}

// TestScanBtcAttrHistoryRPCMatchesChaindataByteForByte is the source-equivalence proof: the SAME BtcAttr payloads
// fed through the chaindata scanner and the RPC scanner must emit byte-identical NDJSON. All blocks are hVM0-active
// so the chaindata activation gate skips none, isolating source equivalence from the gate. Together with
// TestScanNDJSONLineGolden (which freezes the chaindata schema) this pins the RPC output to the same golden schema.
func TestScanBtcAttrHistoryRPCMatchesChaindataByteForByte(t *testing.T) {
	tipA, tipB := wireHdrTip(11), wireHdrTip(22)
	type pl struct {
		n    uint64
		tip  chainhash.Hash
		hdrs []wire.BlockHeader
	}
	// BtcAttr payloads at heights 2,3,5; heights 0,1,4 carry no BtcAttr tx.
	payloads := []pl{
		{2, tipA, []wire.BlockHeader{wireHdr(1), wireHdr(2), wireHdr(3)}},
		{3, tipB, []wire.BlockHeader{wireHdr(4)}},
		{5, tipA, []wire.BlockHeader{wireHdr(5), wireHdr(6)}},
	}
	withBtcAttr := map[uint64]pl{}
	for _, p := range payloads {
		withBtcAttr[p.n] = p
	}

	db := rawdb.NewMemoryDatabase()
	rpcBlocks := map[uint64]*testRPCBlock{}
	for n := uint64(0); n <= 5; n++ {
		if p, ok := withBtcAttr[n]; ok {
			putCanonBlock(t, db, n, 2000, types.Transactions{mkBtcAttrTx(t, &p.tip, p.hdrs)})
			rpcBlocks[n] = rpcBlk(n, rpcBtcAttrTx(t, &p.tip, p.hdrs))
		} else if n == 0 {
			putCanonBlock(t, db, n, 2000, nil)
			rpcBlocks[n] = rpcBlk(n) // genesis: legitimately carries no transactions
		} else {
			putCanonBlock(t, db, n, 2000, nil)
			rpcBlocks[n] = rpcBlk(n, rpcOtherTx()) // non-genesis blocks always carry >=1 tx (the L1-attributes deposit)
		}
	}

	var outChain bytes.Buffer
	resChain, err := scanBtcAttrHistory(db, testCfg(), 0, 5, false, &outChain)
	require.NoError(t, err)

	c := dialFakeRPC(t, startFakeRPCServer(t, 5, rpcBlocks).URL)
	var outRPC bytes.Buffer
	resRPC, err := scanBtcAttrHistoryRPC(context.Background(), c, 0, 5, false, 0, &outRPC)
	require.NoError(t, err)

	require.Equal(t, outChain.String(), outRPC.String(), "chaindata and RPC sources must emit byte-identical NDJSON for the same payloads")
	require.Equal(t, 3, resRPC.emitted)
	require.Equal(t, resChain.emitted, resRPC.emitted)
	require.Equal(t, resChain.rawHeaders, resRPC.rawHeaders)
}

// TestScanBtcAttrHistoryRPCRejectsMultipleBtcAttrTxs mirrors ExtractBtcAttrData: two BtcAttr txs in one block is a
// malformed condition surfaced as an error (with the block number), not silently merged.
func TestScanBtcAttrHistoryRPCRejectsMultipleBtcAttrTxs(t *testing.T) {
	tip := wireHdrTip(9)
	blocks := map[uint64]*testRPCBlock{
		0: rpcBlk(0,
			rpcBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)}),
			rpcBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(2)}),
		),
	}
	c := dialFakeRPC(t, startFakeRPCServer(t, 0, blocks).URL)
	_, err := scanBtcAttrHistoryRPC(context.Background(), c, 0, 0, false, 0, io.Discard)
	require.Error(t, err)
	require.ErrorContains(t, err, "block 0 contains more than one Bitcoin Attributes Deposited transaction")
	require.NotErrorIs(t, err, errMissingBlocks)
	require.NotErrorIs(t, err, errVacuousFixture)
}

// TestScanBtcAttrHistoryRPCGapHandling: a block the node returns as JSON null is a gap (errMissingBlocks) unless
// --allow-gaps, exactly like the chaindata path's absent-block handling; the gap counts as hashMissing and must
// NOT inflate scanned.
func TestScanBtcAttrHistoryRPCGapHandling(t *testing.T) {
	tip := wireHdrTip(9)
	blocks := map[uint64]*testRPCBlock{
		0: rpcBlk(0, rpcBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)})),
		// height 1 absent -> the server returns JSON null
		2: rpcBlk(2, rpcBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(2)})),
	}
	c := dialFakeRPC(t, startFakeRPCServer(t, 2, blocks).URL)

	var out bytes.Buffer
	res, err := scanBtcAttrHistoryRPC(context.Background(), c, 0, 2, false, 0, &out)
	require.ErrorIs(t, err, errMissingBlocks, "a null block is a gap unless --allow-gaps")
	require.Equal(t, 1, res.hashMissing, "an RPC null block counts as hashMissing")
	require.Equal(t, 0, res.blockMissing)

	out.Reset()
	res, err = scanBtcAttrHistoryRPC(context.Background(), c, 0, 2, true, 0, &out)
	require.NoError(t, err)
	require.Equal(t, 1, res.hashMissing)
	require.Equal(t, 2, res.emitted)
	require.Equal(t, 2, res.scanned, "scanned counts only non-null blocks; the gap must NOT inflate it")
}

// TestScanBtcAttrHistoryRPCVacuous: a window with no BtcAttr-carrying blocks yields zero lines -> errVacuousFixture.
func TestScanBtcAttrHistoryRPCVacuous(t *testing.T) {
	blocks := map[uint64]*testRPCBlock{
		0: rpcBlk(0),               // no txs
		1: rpcBlk(1, rpcOtherTx()), // non-BtcAttr tx only
	}
	c := dialFakeRPC(t, startFakeRPCServer(t, 1, blocks).URL)
	res, err := scanBtcAttrHistoryRPC(context.Background(), c, 0, 1, false, 0, io.Discard)
	require.ErrorIs(t, err, errVacuousFixture)
	require.Equal(t, 0, res.emitted)
	require.Equal(t, 2, res.scanned)
}

const reconstructRPCChildEnv = "RECONSTRUCT_MAIN_RPC_CHILD"

// TestReconstructMainRPCSuccessChild is the subprocess child for TestReconstructMainRPCSuccess: it points main()'s
// --rpc at the parent's fake RPC server (URL via env) and lets it run to completion. main() RETURNS normally on
// success, so the child returns and exits 0.
func TestReconstructMainRPCSuccessChild(t *testing.T) {
	url := os.Getenv(reconstructRPCChildEnv)
	if url == "" {
		t.Skip("child-only: driven by TestReconstructMainRPCSuccess via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	out := os.Getenv(reconstructRPCChildEnv + "_OUT")
	// --chainid matches the fake server's eth_chainId, exercising the wrong-network guard's PASS path end to end.
	os.Args = []string{"hvm-btcattr-reconstruct", "--rpc", url, "--chainid", "43111", "--out", out, "--start", "0", "--end", "1"}
	main()
}

// TestReconstructMainRPCSuccess exercises main()'s entire --rpc happy path end to end: dial the endpoint, resolve
// the head via eth_blockNumber, scan [0..1], and write a non-vacuous fixture — exiting 0 with the
// "reconstruction complete" summary. The parent hosts the fake RPC server (in-process); the re-exec'd child
// reaches it over localhost, proving the --rpc flag wiring, head resolution, and output plumbing.
func TestReconstructMainRPCSuccess(t *testing.T) {
	tip := wireHdrTip(7)
	blocks := map[uint64]*testRPCBlock{
		0: rpcBlk(0),                                                        // no BtcAttr tx
		1: rpcBlk(1, rpcBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)})), // one BtcAttr block
	}
	srv := startFakeRPCServer(t, 1, blocks)
	outPath := filepath.Join(t.TempDir(), "fixture.ndjson")

	cmd := exec.Command(os.Args[0], "-test.run=^TestReconstructMainRPCSuccessChild$", "-test.v")
	cmd.Env = append(os.Environ(),
		reconstructRPCChildEnv+"="+srv.URL,
		reconstructRPCChildEnv+"_OUT="+outPath)
	out, err := cmd.CombinedOutput()
	require.NoError(t, err, "main --rpc must exit 0 on the happy path, output:\n%s", string(out))
	require.Contains(t, string(out), "reconstruction complete", "the success summary must be logged")
	require.Contains(t, string(out), "btcattr_lines=1", "exactly one BtcAttr block must be emitted")

	data, err := os.ReadFile(outPath)
	require.NoError(t, err, "main --rpc must write the --out fixture")
	lines := parseLines(t, data)
	require.Len(t, lines, 1)
	require.Equal(t, uint64(1), lines[0].Blk)
	require.Len(t, lines[0].Hdrs, 1, "the emitted line must carry the one BTC header")
}

const reconstructExclusivityChildEnv = "RECONSTRUCT_MAIN_EXCLUSIVITY_CHILD"

// TestReconstructMainSourceExclusivityChild is the subprocess child for TestReconstructMainSourceExclusivity: it
// invokes main() with neither or both of --chaindata/--rpc, which must trip the source-exclusivity guard
// (os.Exit(2)) before any db/RPC work.
func TestReconstructMainSourceExclusivityChild(t *testing.T) {
	mode := os.Getenv(reconstructExclusivityChildEnv)
	if mode == "" {
		t.Skip("child-only: driven by TestReconstructMainSourceExclusivity via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	switch mode {
	case "neither":
		os.Args = []string{"hvm-btcattr-reconstruct"}
	case "both":
		os.Args = []string{"hvm-btcattr-reconstruct", "--chaindata", t.TempDir(), "--rpc", "http://127.0.0.1:0"}
	default:
		t.Fatalf("unknown mode %q", mode)
	}
	main()
	t.Fatalf("main returned for mode %q; expected os.Exit(2) from the source-exclusivity guard", mode)
}

// TestReconstructMainSourceExclusivity drives the "exactly one of --chaindata or --rpc" guard: both neither-source
// and both-sources must exit non-zero with the guard message, before any db open or RPC dial.
func TestReconstructMainSourceExclusivity(t *testing.T) {
	for _, mode := range []string{"neither", "both"} {
		t.Run(mode, func(t *testing.T) {
			cmd := exec.Command(os.Args[0], "-test.run=^TestReconstructMainSourceExclusivityChild$", "-test.v")
			cmd.Env = append(os.Environ(), reconstructExclusivityChildEnv+"="+mode)
			out, err := cmd.CombinedOutput()

			var ee *exec.ExitError
			require.ErrorAs(t, err, &ee, "the guard must exit non-zero, output:\n%s", string(out))
			require.False(t, ee.Success(), "child must report failure")
			require.Contains(t, string(out), "exactly one of --chaindata or --rpc is required",
				"the source-exclusivity guard message must be printed for mode %q", mode)
			require.NotContains(t, string(out), "main returned for mode",
				"main must os.Exit before returning for mode %q", mode)
		})
	}
}

// TestScanBtcAttrHistoryRPCRejectsStrippedBlock: a non-genesis block that EXISTS but reports zero transactions
// (an endpoint/proxy that stripped or omitted the tx list) must FAIL LOUD, not be silently treated as a clean
// no-BtcAttr block — otherwise a block whose BtcAttr headers were dropped would vanish from the fixture with no
// gap/vacuous signal. Genesis (height 0) is exempt because it legitimately carries no transactions.
func TestScanBtcAttrHistoryRPCRejectsStrippedBlock(t *testing.T) {
	tip := wireHdrTip(9)
	blocks := map[uint64]*testRPCBlock{
		5: rpcBlk(5, rpcBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)})), // real BtcAttr block
		6: rpcBlk(6),                                                        // exists but transactions stripped
	}
	c := dialFakeRPC(t, startFakeRPCServer(t, 6, blocks).URL)
	_, err := scanBtcAttrHistoryRPC(context.Background(), c, 5, 6, false, 0, io.Discard)
	require.Error(t, err)
	require.ErrorContains(t, err, "block 6 returned with no transactions")
	require.NotErrorIs(t, err, errMissingBlocks, "a stripped block is NOT a gap (that would be silenced by --allow-gaps)")
	require.NotErrorIs(t, err, errVacuousFixture)
}

// TestReconstructMainRPCChainIdMismatchChild is the subprocess child for TestReconstructMainRPCChainIdMismatch: it
// runs main() --rpc with a --chainid that does NOT match the fake server's eth_chainId, so the wrong-network guard
// must crit before scanning.
func TestReconstructMainRPCChainIdMismatchChild(t *testing.T) {
	url := os.Getenv(reconstructRPCChildEnv)
	if url == "" {
		t.Skip("child-only: driven by TestReconstructMainRPCChainIdMismatch via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	os.Args = []string{"hvm-btcattr-reconstruct", "--rpc", url, "--chainid", "999", "--end", "1"}
	main()
	t.Fatalf("main returned; expected the chainId-mismatch wrong-network guard to crit")
}

// TestReconstructMainRPCChainIdMismatch: the RPC wrong-network guard (the counterpart of the chaindata path's
// missing-Hvm0Time crit) must fail loud when the endpoint's eth_chainId does not match --chainid.
func TestReconstructMainRPCChainIdMismatch(t *testing.T) {
	tip := wireHdrTip(7)
	blocks := map[uint64]*testRPCBlock{
		0: rpcBlk(0),
		1: rpcBlk(1, rpcBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)})),
	}
	srv := startFakeRPCServer(t, 1, blocks) // reports chainId testFakeRPCChainID (43111)

	cmd := exec.Command(os.Args[0], "-test.run=^TestReconstructMainRPCChainIdMismatchChild$", "-test.v")
	cmd.Env = append(os.Environ(), reconstructRPCChildEnv+"="+srv.URL)
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "a chainId mismatch must crit, output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "chainId does not match", "the wrong-network guard must fire")
	require.NotContains(t, string(out), "reconstruction complete", "the scan must NOT run on a chainId mismatch")
}

// TestScanBtcAttrHistoryRPCActivationGateMatchesChaindata pins the --hvm0-time gate against the chaindata
// cfg.IsHvm0(block.Time()) gate, INCLUDING the exact boundary. Three blocks carry a BtcAttr tx: one below
// activation (excluded by both), one AT exactly the activation time (both gates are inclusive — IsHvm0 is
// Hvm0Time<=time, the RPC skip is ts<hvm0Time — so it must be INCLUDED by both; this pins < vs <=), and one
// above (included). WITHOUT --hvm0-time the RPC path includes all three, the divergence --hvm0-time closes.
func TestScanBtcAttrHistoryRPCActivationGateMatchesChaindata(t *testing.T) {
	tip := wireHdrTip(9)
	preHdr, boundaryHdr, postHdr := wireHdr(1), wireHdr(2), wireHdr(3)
	const preTime = hvm0TestTime - 500   // below activation -> excluded
	const boundaryTime = hvm0TestTime    // EXACTLY at activation -> included (inclusive boundary)
	const postTime = hvm0TestTime + 1000 // above activation -> included

	// chaindata: IsHvm0 excludes only the pre-activation block; the block AT activation is included.
	db := rawdb.NewMemoryDatabase()
	putCanonBlock(t, db, 1, preTime, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{preHdr})})
	putCanonBlock(t, db, 2, boundaryTime, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{boundaryHdr})})
	putCanonBlock(t, db, 3, postTime, types.Transactions{mkBtcAttrTx(t, &tip, []wire.BlockHeader{postHdr})})
	var outChain bytes.Buffer
	resChain, err := scanBtcAttrHistory(db, testCfg(), 1, 3, false, &outChain)
	require.NoError(t, err)
	require.Equal(t, 2, resChain.emitted, "chaindata IsHvm0 excludes only the pre-activation block; the block AT activation is included")

	blocks := map[uint64]*testRPCBlock{
		1: rpcBlkTS(1, preTime, rpcBtcAttrTx(t, &tip, []wire.BlockHeader{preHdr})),
		2: rpcBlkTS(2, boundaryTime, rpcBtcAttrTx(t, &tip, []wire.BlockHeader{boundaryHdr})),
		3: rpcBlkTS(3, postTime, rpcBtcAttrTx(t, &tip, []wire.BlockHeader{postHdr})),
	}
	c := dialFakeRPC(t, startFakeRPCServer(t, 3, blocks).URL)

	// WITH --hvm0-time: byte-identical to chaindata across the activation boundary, INCLUDING the exact-boundary
	// block (a < -> <= regression would drop it here and diverge, so this pins the inclusive boundary).
	var outGated bytes.Buffer
	resGated, err := scanBtcAttrHistoryRPC(context.Background(), c, 1, 3, false, hvm0TestTime, &outGated)
	require.NoError(t, err)
	require.Equal(t, 2, resGated.emitted, "--hvm0-time includes the block AT exactly the activation time (< not <=), matching chaindata")
	require.Equal(t, outChain.String(), outGated.String(), "with --hvm0-time the RPC output is byte-identical to chaindata across activation, incl. the exact-boundary block")

	// WITHOUT the gate (hvm0Time=0): the pre-activation grandfathered block is (wrongly) included — the divergence.
	var outNoGate bytes.Buffer
	resNoGate, err := scanBtcAttrHistoryRPC(context.Background(), c, 1, 3, false, 0, &outNoGate)
	require.NoError(t, err)
	require.Equal(t, 3, resNoGate.emitted, "without --hvm0-time the pre-activation block is included (diverges from chaindata)")
}

// TestScanBtcAttrHistoryRPCSurfacesRPCError: an endpoint returning a JSON-RPC error object (not a null result)
// must surface LOUD from the scanner, not be swallowed into a short/clean fixture.
func TestScanBtcAttrHistoryRPCSurfacesRPCError(t *testing.T) {
	srv := httptest.NewServer(http.HandlerFunc(func(wr http.ResponseWriter, r *http.Request) {
		body, _ := io.ReadAll(r.Body)
		var req struct {
			ID json.RawMessage `json:"id"`
		}
		_ = json.Unmarshal(body, &req)
		wr.Header().Set("Content-Type", "application/json")
		_, _ = wr.Write([]byte(`{"jsonrpc":"2.0","id":` + string(req.ID) + `,"error":{"code":-32000,"message":"boom"}}`))
	}))
	t.Cleanup(srv.Close)
	c := dialFakeRPC(t, srv.URL)

	_, err := scanBtcAttrHistoryRPC(context.Background(), c, 0, 0, false, 0, io.Discard)
	require.Error(t, err)
	require.ErrorContains(t, err, "eth_getBlockByNumber 0", "the failing RPC call must be named")
	require.ErrorContains(t, err, "boom", "the endpoint's JSON-RPC error must be surfaced")
	require.NotErrorIs(t, err, errMissingBlocks, "an RPC error is NOT a gap")
	require.NotErrorIs(t, err, errVacuousFixture)
}

// TestScanBtcAttrHistoryRPCTimestampDecodeError: with --hvm0-time set, a block whose timestamp is absent or
// malformed must fail LOUD (the activation gate can't be applied), not silently pass through.
func TestScanBtcAttrHistoryRPCTimestampDecodeError(t *testing.T) {
	tip := wireHdrTip(9)
	blocks := map[uint64]*testRPCBlock{
		1: {
			Number:       hexutil.EncodeUint64(1),
			Timestamp:    "not-hex", // malformed -> hexutil.DecodeUint64 errors
			Transactions: []testRPCTx{rpcBtcAttrTx(t, &tip, []wire.BlockHeader{wireHdr(1)})},
		},
	}
	c := dialFakeRPC(t, startFakeRPCServer(t, 1, blocks).URL)
	_, err := scanBtcAttrHistoryRPC(context.Background(), c, 1, 1, false, hvm0TestTime, io.Discard)
	require.Error(t, err)
	require.ErrorContains(t, err, "block 1 timestamp", "a bad timestamp under --hvm0-time must be surfaced with the block number")
}
