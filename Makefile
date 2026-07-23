# This Makefile is meant to be used by people that do not usually work
# with Go source code. If you know what GOPATH is then you probably
# don't need to bother with make.

.PHONY: geth evm all test test-short lint fmt clean devtools help forkdiff

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
	$(GORUN) build/ci.go test -v

#? test-short: Run the tests with -short (skips the slow integration tests that carry a testing.Short() guard, for fast feedback). Does NOT run the ENFORCED hVM history gates (tip pins + HEMI_HISTORY_GATE_REQUIRED + run+PASS vacuity guard) — run those locally per core/vm/testdata/HISTORY_GATE.md, or in CI as the three enforced steps of the `test` job. Plain `make test` (and the CI `test-long` job) run the gate tests against committed fixtures but WITHOUT that enforcement.
test-short: all
	$(GORUN) build/ci.go test --short

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

#? forkdiff: Generate the fork-diff report (forkdiff.html) via the protolambda/forkdiff image.
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
