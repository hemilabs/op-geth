// Copyright 2024 The go-ethereum Authors
// This file is part of go-ethereum.
//
// go-ethereum is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// go-ethereum is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with go-ethereum. If not, see <http://www.gnu.org/licenses/>.

package main

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"math/big"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/ethdb/leveldb"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
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
	require.Equal(t, 0, res.missing)
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
	require.Equal(t, 1, res.missing)
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
	require.Equal(t, 1, res.missing)
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
	require.Equal(t, 1, res.missing)

	// With --allow-gaps the body-absent block is tolerated and the height-0 line is still emitted.
	out.Reset()
	res, err = scanBtcAttrHistory(db, testCfg(), 0, 1, true, &out)
	require.NoError(t, err)
	require.Equal(t, 1, res.missing)
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
