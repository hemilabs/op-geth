# This Makefile is meant to be used by people that do not usually work
# with Go source code. If you know what GOPATH is then you probably
# don't need to bother with make.

.PHONY: geth evm all test test-short lint fmt clean devtools help hvm-history-gate hvm-history-gate-testnet3

GOBIN = ./build/bin
GO ?= latest
GORUN = go run

#? geth: Build geth.
geth:
	$(GORUN) build/ci.go install ./cmd/geth
	@echo "Done building."
	@echo "Run \"$(GOBIN)/geth\" to launch geth."

#? evm: Build evm.
evm:
	$(GORUN) build/ci.go install ./cmd/evm
	@echo "Done building."
	@echo "Run \"$(GOBIN)/evm\" to launch evm."

#? all: Build all packages and executables.
all:
	$(GORUN) build/ci.go install

#? test: Run the tests.
test: all
	$(GORUN) build/ci.go test

#? test-short: Run the tests with -short (skips the slow integration tests that carry a testing.Short() guard, for fast feedback). Does NOT run the ENFORCED hVM history gates (tip pins + HEMI_HISTORY_GATE_REQUIRED + run+PASS vacuity guard) — run those locally via `make hvm-history-gate` / `hvm-history-gate-testnet3`, or in CI as the three enforced steps of the `test` job. Plain `make test` (and the CI `test-long` job) run the gate tests against committed fixtures but WITHOUT that enforcement.
test-short: all
	$(GORUN) build/ci.go test --short

#? hvm-history-gate: Run the differential-replay gate (proves committed hVM BTC history is clean).
# Provisions the reconstructed NDJSON from CHAINDATA, then runs the gate ENFORCED (HEMI_HISTORY_GATE_REQUIRED=1)
# with the coverage + real-chain pins.
# Required vars (mainnet): CHAINDATA (a FULL-history node), MAINNET_TIP_HEIGHT (real BTC tip HEIGHT, coverage
#   pin), MAINNET_TIP_HASH (real BTC block HASH at that height, the real-chain binding).
# Optional: MAINNET_L2_END (an L2 block height to cap reconstruction for a REPRODUCIBLE fixture; note this is an
#   L2 height, a DIFFERENT unit from the BTC tip height — leave unset to scan to the L2 head).
# The shipped default node runs testnet3 (ReduceMinDifficulty); set TESTNET3_CHAINDATA + TESTNET3_TIP_HEIGHT/HASH
#   to also gate testnet3 (the only network that exercises the min-difficulty rule) — see hvm-history-gate-testnet3.
hvm-history-gate:
	@test -n "$(CHAINDATA)" || { echo "set CHAINDATA=<datadir>/geth/chaindata (a FULL-history node)"; exit 1; }
	@case '$(MAINNET_TIP_HEIGHT)' in ''|*[!0-9]*|0) echo "MAINNET_TIP_HEIGHT must be a positive integer (real BTC tip height for the coverage pin)"; exit 1;; esac
	@case '$(MAINNET_TIP_HASH)' in *[!0-9a-f]*|'') echo "MAINNET_TIP_HASH must be lowercase hex (real BTC block hash at MAINNET_TIP_HEIGHT)"; exit 1;; esac
	@test `printf %s '$(MAINNET_TIP_HASH)' | wc -c` -eq 64 || { echo "MAINNET_TIP_HASH must be exactly 64 hex chars"; exit 1; }
	rm -f /tmp/btcattr_headers.ndjson
	$(GORUN) ./testutil/hvm-btcattr-reconstruct --chaindata "$(CHAINDATA)" $(if $(MAINNET_L2_END),--end $(MAINNET_L2_END)) --out /tmp/btcattr_headers.ndjson
	@OUT=`HEMI_HISTORY_GATE_REQUIRED=1 HEMI_MAINNET_VERIFY=/tmp/btcattr_headers.ndjson \
		HEMI_MAINNET_EXPECT_TIP_HEIGHT=$(MAINNET_TIP_HEIGHT) HEMI_MAINNET_EXPECT_TIP_HASH=$(MAINNET_TIP_HASH) \
		go test ./core/vm/ -run '^TestBtcDiffValidatorAcceptsAllMainnetCommittedHistory$$' -count=1 -v 2>&1`; echo "$$OUT"; \
		echo "$$OUT" | grep -q -- '--- PASS: TestBtcDiffValidatorAcceptsAllMainnetCommittedHistory (' || { echo "GATE ERROR: mainnet validator test did not run+PASS (renamed/misfiltered? a non-matching -run exits 0)"; exit 1; }
	@OUT=`HEMI_HISTORY_GATE_REQUIRED=1 HEMI_MAINNET_VERIFY=/tmp/btcattr_headers.ndjson \
		HEMI_MAINNET_EXPECT_TIP_HEIGHT=$(MAINNET_TIP_HEIGHT) HEMI_MAINNET_EXPECT_TIP_HASH=$(MAINNET_TIP_HASH) \
		go test ./core/ -run '^TestHvmReplaysAllMainnetBtcAttrThroughApplyPath$$' -count=1 -v 2>&1`; echo "$$OUT"; \
		echo "$$OUT" | grep -q -- '--- PASS: TestHvmReplaysAllMainnetBtcAttrThroughApplyPath (' || { echo "GATE ERROR: mainnet apply-path replay test did not run+PASS"; exit 1; }
	@if [ -n "$(TESTNET3_CHAINDATA)" ]; then $(MAKE) hvm-history-gate-testnet3; \
	else echo "WARNING: testnet3 lane SKIPPED. The shipped default node runs testnet3 (ReduceMinDifficulty=true); the mainnet-only gate (ReduceMinDifficulty=false) CANNOT exercise the min-difficulty rule. Set TESTNET3_CHAINDATA + TESTNET3_TIP_HEIGHT/HASH to gate the shipped network."; fi

#? hvm-history-gate-testnet3: Run the differential-replay gate for testnet3 (the shipped default network; exercises ReduceMinDifficulty).
hvm-history-gate-testnet3:
	@test -n "$(TESTNET3_CHAINDATA)" || { echo "set TESTNET3_CHAINDATA=<datadir>/geth/chaindata (a FULL-history testnet3 node)"; exit 1; }
	@case '$(TESTNET3_TIP_HEIGHT)' in ''|*[!0-9]*|0) echo "TESTNET3_TIP_HEIGHT must be a positive integer (real testnet3 BTC tip height)"; exit 1;; esac
	@case '$(TESTNET3_TIP_HASH)' in *[!0-9a-f]*|'') echo "TESTNET3_TIP_HASH must be lowercase hex (real testnet3 BTC block hash at TESTNET3_TIP_HEIGHT)"; exit 1;; esac
	@test `printf %s '$(TESTNET3_TIP_HASH)' | wc -c` -eq 64 || { echo "TESTNET3_TIP_HASH must be exactly 64 hex chars"; exit 1; }
	rm -f /tmp/btcattr_testnet3_post.ndjson
	$(GORUN) ./testutil/hvm-btcattr-reconstruct --chaindata "$(TESTNET3_CHAINDATA)" $(if $(TESTNET3_L2_END),--end $(TESTNET3_L2_END)) --out /tmp/btcattr_testnet3_post.ndjson
	@OUT=`HEMI_HISTORY_GATE_REQUIRED=1 HEMI_TESTNET3_VERIFY=/tmp/btcattr_testnet3_post.ndjson \
		HEMI_TESTNET3_EXPECT_TIP_HEIGHT=$(TESTNET3_TIP_HEIGHT) HEMI_TESTNET3_EXPECT_TIP_HASH=$(TESTNET3_TIP_HASH) \
		go test ./core/vm/ -run '^TestBtcDiffValidatorAcceptsAllTestnet3CommittedHistory$$' -count=1 -v 2>&1`; echo "$$OUT"; \
		echo "$$OUT" | grep -q -- '--- PASS: TestBtcDiffValidatorAcceptsAllTestnet3CommittedHistory (' || { echo "GATE ERROR: testnet3 validator test did not run+PASS"; exit 1; }
	@OUT=`HEMI_HISTORY_GATE_REQUIRED=1 HEMI_TESTNET3_VERIFY=/tmp/btcattr_testnet3_post.ndjson \
		HEMI_TESTNET3_EXPECT_TIP_HEIGHT=$(TESTNET3_TIP_HEIGHT) HEMI_TESTNET3_EXPECT_TIP_HASH=$(TESTNET3_TIP_HASH) \
		go test ./core/ -run '^TestHvmReplaysAllTestnet3BtcAttrThroughApplyPath$$' -count=1 -v 2>&1`; echo "$$OUT"; \
		echo "$$OUT" | grep -q -- '--- PASS: TestHvmReplaysAllTestnet3BtcAttrThroughApplyPath (' || { echo "GATE ERROR: testnet3 apply-path replay test did not run+PASS (orphan residual? see the test header)"; exit 1; }

#? lint: Run certain pre-selected linters.
lint: ## Run linters.
	$(GORUN) build/ci.go lint

#? fmt: Ensure consistent code formatting.
fmt:
	gofmt -s -w $(shell find . -name "*.go")

#? clean: Clean go cache, built executables, and the auto generated folder.
clean:
	go clean -cache
	rm -fr build/_workspace/pkg/ $(GOBIN)/*

# The devtools target installs tools required for 'go generate'.
# You need to put $GOBIN (or $GOPATH/bin) in your PATH to use 'go generate'.

#? devtools: Install recommended developer tools.
devtools:
	env GOBIN= go install golang.org/x/tools/cmd/stringer@latest
	env GOBIN= go install github.com/fjl/gencodec@latest
	env GOBIN= go install google.golang.org/protobuf/cmd/protoc-gen-go@latest
	env GOBIN= go install ./cmd/abigen
	@type "solc" 2> /dev/null || echo 'Please install solc'
	@type "protoc" 2> /dev/null || echo 'Please install protoc'

forkdiff:
	docker run --rm \
		--mount src=$(shell pwd),target=/host-pwd,type=bind \
		protolambda/forkdiff:latest \
		-repo /host-pwd/ -fork /host-pwd/fork.yaml -out /host-pwd/forkdiff.html

#? help: Get more info on make commands.
help: Makefile
	@echo ''
	@echo 'Usage:'
	@echo '  make [target]'
	@echo ''
	@echo 'Targets:'
	@sed -n 's/^#?//p' $< | column -t -s ':' |  sort | sed -e 's/^/ /'
