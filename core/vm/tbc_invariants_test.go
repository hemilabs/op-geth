// Copyright 2024 The go-ethereum Authors
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

package vm

import (
	"errors"
	"fmt"
	"testing"

	"github.com/hemilabs/heminetwork/database"
	"github.com/hemilabs/heminetwork/service/tbc"
)

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
