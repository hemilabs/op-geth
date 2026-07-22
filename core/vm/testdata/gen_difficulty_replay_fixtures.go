//go:build ignore

// gen_difficulty_replay_fixtures.go fetches real Bitcoin block headers from blockstream.info and writes them as
// committed fixtures for the differential-replay tests.
//
// Run once (it needs network); the result is committed and the tests //go:embed it — the tests
// themselves never touch the network. The oracle is the real chain: each embedded header carries the
// difficulty (Bits) Bitcoin actually used, so the reused btcd engine must reproduce it.
//
//	cd core/vm/testdata && go run gen_difficulty_replay_fixtures.go
//
// Curated heights:
//   - mainnet non-boundary run 100000..100020 (full-validator replay; constant epoch).
//   - mainnet retarget boundaries 2016, 32256, 800352 — each with its 2016-back window start + the
//     11-ancestor MTP window + the boundary block. 2016 exercises the PowLimit cap (difficulty stayed
//     at minimum); 32256 is the first real change (0x1d00ffff -> 0x1d00d86a); 800352 is a modern
//     large-exponent boundary.
//   - testnet3 run 38304..38360 — starts at retarget boundary 38304 (=2016*19) so every
//     within-20-minute block's findPrevTestNetDifficulty walk is bounded in-fixture; a mix of real
//     ReduceMinDifficulty / 20-minute-rule min-diff blocks and the epoch difficulty, exercising the
//     restore path end-to-end. Do not regenerate into a non-boundary-aligned range — that would break
//     the in-fixture walk guarantee.
package main

import (
	"fmt"
	"io"
	"net/http"
	"os"
	"sort"
	"strings"
	"time"
)

const (
	mainnetAPI  = "https://blockstream.info/api"
	testnet3API = "https://blockstream.info/testnet/api"
)

func get(url string) (string, error) {
	var lastErr error
	for attempt := 0; attempt < 5; attempt++ {
		resp, err := http.Get(url)
		if err != nil {
			lastErr = err
			time.Sleep(time.Duration(attempt+1) * time.Second)
			continue
		}
		body, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		if resp.StatusCode != 200 {
			lastErr = fmt.Errorf("%s -> %d: %s", url, resp.StatusCode, string(body))
			time.Sleep(time.Duration(attempt+1) * time.Second)
			continue
		}
		return strings.TrimSpace(string(body)), nil
	}
	return "", lastErr
}

func headerHex(api string, height uint64) (string, error) {
	hash, err := get(fmt.Sprintf("%s/block-height/%d", api, height))
	if err != nil {
		return "", err
	}
	hdr, err := get(fmt.Sprintf("%s/block/%s/header", api, hash))
	if err != nil {
		return "", err
	}
	if len(hdr) != 160 {
		return "", fmt.Errorf("height %d: header hex len %d != 160", height, len(hdr))
	}
	return hdr, nil
}

func writeFixture(path, api string, heights []uint64) error {
	sort.Slice(heights, func(i, j int) bool { return heights[i] < heights[j] })
	var b strings.Builder
	for _, h := range heights {
		hex, err := headerHex(api, h)
		if err != nil {
			return err
		}
		fmt.Fprintf(&b, "%d %s\n", h, hex)
		fmt.Printf("  %s height %d ok\n", path, h)
		time.Sleep(350 * time.Millisecond)
	}
	return os.WriteFile(path, []byte(b.String()), 0o644)
}

func rangeHeights(lo, hi uint64) []uint64 {
	out := make([]uint64, 0, hi-lo+1)
	for h := lo; h <= hi; h++ {
		out = append(out, h)
	}
	return out
}

// boundarySet returns {H-2016} + {H-11 .. H} for a retarget boundary H.
func boundarySet(H uint64) []uint64 {
	out := []uint64{H - 2016}
	for h := H - 11; h <= H; h++ {
		out = append(out, h)
	}
	return out
}

func main() {
	var boundaries []uint64
	for _, H := range []uint64{2016, 32256, 800352} {
		boundaries = append(boundaries, boundarySet(H)...)
	}

	jobs := []struct {
		path    string
		api     string
		heights []uint64
	}{
		{"difficulty_replay_mainnet_run.txt", mainnetAPI, rangeHeights(100000, 100020)},
		{"difficulty_replay_mainnet_boundaries.txt", mainnetAPI, boundaries},
		// Start at a retarget boundary (38304 = 2016*19) so every within-20-minute block's
		// findPrevTestNetDifficulty walk is bounded by the in-fixture boundary and cannot run off the
		// fixture floor (which would falsely reject a real header).
		{"difficulty_replay_testnet3_run.txt", testnet3API, rangeHeights(38304, 38360)},
	}
	for _, j := range jobs {
		fmt.Printf("fetching %s (%d headers)...\n", j.path, len(j.heights))
		if err := writeFixture(j.path, j.api, j.heights); err != nil {
			fmt.Fprintf(os.Stderr, "FAILED %s: %v\n", j.path, err)
			os.Exit(1)
		}
	}
	fmt.Println("done")
}
