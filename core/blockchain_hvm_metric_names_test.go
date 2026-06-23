// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Metric NAME-stability tripwire. Dashboards and alerts scrape these meters and gauges by their registered NAME
// strings, an external contract a rename silently breaks. Other tests check the VALUES via the Go package variable,
// never the literal name, so a typo'd rename leaves them green while breaking the dashboard query. This pins each
// metric to its exact name and sweeps for any stray sibling under chain/hvm/.

import (
	"strings"
	"testing"

	"github.com/ethereum/go-ethereum/metrics"
	"github.com/stretchr/testify/require"
)

func TestHvmMetricNamesStable(t *testing.T) {
	meters := map[string]*metrics.Meter{
		"chain/hvm/migration/triggered":      hvmMigrationTriggeredMeter,
		"chain/hvm/migration/deferred":       hvmMigrationDeferredMeter,
		"chain/hvm/migration/completed":      hvmMigrationCompletedMeter,
		"chain/hvm/migration/failed":         hvmMigrationFailedMeter,
		"chain/hvm/migration/pow_reject":     hvmMigrationPoWRejectMeter,
		"chain/hvm/migration/btcdiff_reject": hvmMigrationBtcDiffRejectMeter,
		"chain/hvm/snap/pow_reject":          hvmSnapPoWRejectMeter,
		"chain/hvm/snap/btcdiff_reject":      hvmSnapBtcDiffRejectMeter,
		"chain/hvm/btcattr/fail":             hvmBtcAttrFailMeter,
		"chain/hvm/btcattr/diff_trunc":       hvmBtcAttrDiffTruncMeter,
		"chain/hvm/reapply/restore":          hvmReapplyRestoreMeter,
	}
	gauges := map[string]*metrics.Gauge{
		"chain/hvm/migration/in_progress": hvmMigrationInProgressGauge,
		"chain/hvm/btcattr/failing":       hvmBtcAttrFailingGauge,
		"chain/hvm/fulltbc/behind":        hvmFullTBCBehindGauge,
		"chain/hvm/snap/awaiting":         hvmSnapAwaitingGauge,
	}

	expected := make(map[string]bool)
	for name, want := range meters {
		got, ok := metrics.DefaultRegistry.Get(name).(*metrics.Meter)
		require.Truef(t, ok, "meter %q must be registered under its exact name", name)
		require.Samef(t, want, got, "meter %q must resolve to its own variable (rename/collision detector)", name)
		expected[name] = true
	}
	for name, want := range gauges {
		got, ok := metrics.DefaultRegistry.Get(name).(*metrics.Gauge)
		require.Truef(t, ok, "gauge %q must be registered under its exact name", name)
		require.Samef(t, want, got, "gauge %q must resolve to its own variable", name)
		expected[name] = true
	}

	// Prefix-exclusivity: every registered chain/hvm/ metric must be in the pinned set, so a stray or typo'd
	// sibling like chain/hvm/migraton/... cannot slip in unnoticed.
	metrics.DefaultRegistry.Each(func(name string, _ interface{}) {
		if strings.HasPrefix(name, "chain/hvm/") {
			require.Truef(t, expected[name], "unexpected chain/hvm/ metric %q — pin it here (typo, or a new metric)", name)
		}
	})
}
