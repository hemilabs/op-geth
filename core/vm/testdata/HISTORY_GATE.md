# hVM BTC history gate — operator runbook

The **differential-replay history gate** proves that the Bitcoin header history hVM has
committed to consensus (via every `BtcAttributesDeposited` tx) is *clean* — i.e. it passes the
exact contextual-difficulty + PoW validation the apply path enforces, under the network's
params. On every push, CI runs this gate against the **committed, bounded** fixtures
(`core/vm/testdata/btcattr_{mainnet,testnet3}_history.ndjson`).

This runbook is the **live-tip** lane, run by an operator (e.g. before a release): reconstruct
the *full* history from a real full-history node and run the gate enforced against it —
coverage CI cannot provide, since it needs a full node. It supersedes the removed
`hvm-history-gate` / `hvm-history-gate-testnet3` Makefile targets.

## What it does

1. **Reconstruct** the NDJSON of every committed BTC header from a node using
   `testutil/hvm-btcattr-reconstruct` (see its package doc for flags). Pin `--end` to a
   finalized L2 height for a reproducible fixture.
2. **Run the gate tests ENFORCED.** `HEMI_HISTORY_GATE_REQUIRED=1` turns an absent/vacuous
   fixture into a hard FAIL (never a silent skip); the `EXPECT_TIP_*` pins bind the
   reconstruction to the real chain tip:
   - `TestBtcDiffValidatorAcceptsAll{Mainnet,Testnet3}CommittedHistory` (`./core/vm`) — the
     validator-only check (the contextual-difficulty / PoW math, incl. a retarget recompute).
   - `TestHvmReplaysAll{Mainnet,Testnet3}BtcAttrThroughApplyPath` (`./core`) — the full apply
     path (cumulative-work canonical-tip selection + per-block tip claim).

**testnet3 is the shipped default network** and the only one exercising `ReduceMinDifficulty`,
so gate testnet3 too — the mainnet lane cannot exercise the min-difficulty rule.

## Prerequisites

- A **full-history** node's chaindata (`<datadir>/geth/chaindata`) for the network you gate.
  A snap-synced node lacks pre-pivot blocks and the reconstruction fails loudly. (Alternatively,
  reconstruct from an archive node over JSON-RPC with `--rpc <url> --chainid <ID>` — pass `--chainid`
  (43111 for Hemi mainnet, 743111 for testnet3) as a wrong-network guard that fails loud if the
  endpoint is the wrong network; on testnet3 also add `--hvm0-time <activation-unix>` so
  pre-activation grandfathered commits are excluded, matching the chaindata scan.)
- The real BTC tip **height** and **hash** for the coverage pin (from a block explorer or the node).

## Run (mainnet)

```sh
# 1. reconstruct (pin --end to a finalized L2 height for reproducibility)
go run ./testutil/hvm-btcattr-reconstruct \
    --chaindata <datadir>/geth/chaindata [--end <L2_HEIGHT>] \
    --out /tmp/btcattr_mainnet.ndjson

# 2. validator gate (must print "--- PASS:")
env HEMI_HISTORY_GATE_REQUIRED=1 \
    HEMI_MAINNET_VERIFY=/tmp/btcattr_mainnet.ndjson \
    HEMI_MAINNET_EXPECT_TIP_HEIGHT=<real BTC tip height> \
    HEMI_MAINNET_EXPECT_TIP_HASH=<real BTC block hash at that height> \
    go test ./core/vm/ -run '^TestBtcDiffValidatorAcceptsAllMainnetCommittedHistory$' -count=1 -v

# 3. apply-path replay gate
env HEMI_HISTORY_GATE_REQUIRED=1 \
    HEMI_MAINNET_VERIFY=/tmp/btcattr_mainnet.ndjson \
    HEMI_MAINNET_EXPECT_TIP_HEIGHT=<...> HEMI_MAINNET_EXPECT_TIP_HASH=<...> \
    go test ./core/ -run '^TestHvmReplaysAllMainnetBtcAttrThroughApplyPath$' -count=1 -v
```

## Run (testnet3 — the shipped default)

Same three steps against the testnet3 chaindata, with the `HEMI_TESTNET3_*` vars:

```sh
go run ./testutil/hvm-btcattr-reconstruct \
    --chaindata <testnet3-datadir>/geth/chaindata [--end <L2_HEIGHT>] \
    --out /tmp/btcattr_testnet3.ndjson

env HEMI_HISTORY_GATE_REQUIRED=1 \
    HEMI_TESTNET3_VERIFY=/tmp/btcattr_testnet3.ndjson \
    HEMI_TESTNET3_EXPECT_TIP_HEIGHT=<...> HEMI_TESTNET3_EXPECT_TIP_HASH=<...> \
    go test ./core/vm/ -run '^TestBtcDiffValidatorAcceptsAllTestnet3CommittedHistory$' -count=1 -v

env HEMI_HISTORY_GATE_REQUIRED=1 \
    HEMI_TESTNET3_VERIFY=/tmp/btcattr_testnet3.ndjson \
    HEMI_TESTNET3_EXPECT_TIP_HEIGHT=<...> HEMI_TESTNET3_EXPECT_TIP_HASH=<...> \
    go test ./core/ -run '^TestHvmReplaysAllTestnet3BtcAttrThroughApplyPath$' -count=1 -v
```

## Bridging reconstruction gaps (optional)

If the gate reports headers as UNCONNECTED (a "does not connect" fatal, or a non-empty unconnected set), the
reconstruction is missing a canonical link — a single missing header disconnects everything downstream from the
genesis connectivity walk. Early testnet3 history has a few genuinely orphaned (reorg-link) headers where this
happens. Supply the missing ancestry with an optional file:

- `HEMI_MAINNET_EXTRA_HEADERS=<path>` / `HEMI_TESTNET3_EXTRA_HEADERS=<path>` — one 80-byte BTC header hex per
  line, explorer-recovered. Loaded as **ancestry only**: they bridge connectivity but are NOT counted as
  committed batches, so they cannot mask a real difficulty/PoW rejection.

Only an explicitly-set path is loaded — there is no default. A stale or planted default file would silently
auto-bridge a gap the run never intended to, masking an unconnected signal that the history is not yet proven
clean. Recover the headers from a block explorer, confirm they are the real canonical links, and opt in per run.

## Confirm it actually ran

A mistyped or renamed `-run` regex matches nothing and `go test` still exits 0 — a silent false
pass. **Verify each run printed a `--- PASS: <TestName>` line**, not just a zero exit code (this
is the run-and-PASS vacuity check the CI `test`-job steps also encode).
