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

package ethconfig

import (
	"bytes"
	"reflect"
	"strings"
	"testing"

	"github.com/naoina/toml"
	"github.com/stretchr/testify/require"
)

// gethLikeTOML mirrors cmd/geth's tomlSettings: identity field-name mapping (so keys are the Go field names,
// not snake_case) and a lenient MissingField, which is how geth actually marshals/loads its config file.
var gethLikeTOML = toml.Config{
	NormFieldName: func(_ reflect.Type, key string) string { return key },
	FieldToKey:    func(_ reflect.Type, field string) string { return field },
	MissingField:  func(_ reflect.Type, _ string) error { return nil },
}

// TestConfigTBCNetworkTOMLRoundTrip guards the gencodec TOML marshaller (gen_config.go): TBCNetwork MUST
// survive marshal+unmarshal via geth's TOML settings. A `geth --config geth.toml` node that sets
// TBCNetwork=mainnet would otherwise silently drop it (if gen_config were not regenerated) and fall back to
// testnet3 — the exact "mainnet-as-testnet3" mislabel this guard exists to kill. A future Config field added
// without regenerating gen_config.go fails this test.
func TestConfigTBCNetworkTOMLRoundTrip(t *testing.T) {
	// Base on Defaults (a valid, round-trippable Config; a bare Config{} fails on unrelated fields like the nil
	// miner gas price) and override only TBCNetwork, isolating this field's round-trip.
	in := Defaults
	in.TBCNetwork = "mainnet"

	data, err := gethLikeTOML.Marshal(&in)
	require.NoError(t, err)
	require.True(t, strings.Contains(string(data), "TBCNetwork") && strings.Contains(string(data), "mainnet"),
		"TBCNetwork must be EMITTED to TOML (gen_config.go must include the field); got:\n%s", string(data))

	var out Config
	require.NoError(t, gethLikeTOML.NewDecoder(bytes.NewReader(data)).Decode(&out))
	require.Equal(t, "mainnet", out.TBCNetwork, "TBCNetwork must round-trip through a geth-style TOML load (gen_config UnmarshalTOML)")
}

// TestConfigTBCNetworkTOMLMissingKeyInheritsDefault pins the prior-release backwards-compat path: a config.toml
// written by a release that predates the TBCNetwork field has NO TBCNetwork key. geth loads the TOML ONTO a
// Defaults-seeded Config, so a document with content but no TBCNetwork key must leave TBCNetwork at the default
// (testnet3) — never blank it (an empty network would later crit or, worse, fail open). The control assertion proves
// the decode actually ran.
func TestConfigTBCNetworkTOMLMissingKeyInheritsDefault(t *testing.T) {
	require.NotEmpty(t, Defaults.TBCNetwork, "the default TBCNetwork must be non-empty (the value a prior config inherits)")
	const doc = "NetworkId = 12345\n" // a valid TOML with content but NO TBCNetwork key (mirrors a prior-release config)
	out := Defaults                   // geth seeds cfg.Eth from Defaults before decoding the config file onto it
	require.NoError(t, gethLikeTOML.NewDecoder(strings.NewReader(doc)).Decode(&out))
	require.Equal(t, uint64(12345), out.NetworkId, "control: the decode actually applied the document")
	require.Equal(t, Defaults.TBCNetwork, out.TBCNetwork,
		"a config that omits TBCNetwork must INHERIT the default, not blank it (prior-release backwards-compat)")
}

// TestGenConfigCoversAllTomlFields guards against stale gencodec output: EVERY exported Config field that is not
// toml:"-" must appear in the gencodec MarshalTOML shadow struct. A field added to Config without re-running
// `go generate` (so gen_config.go is stale) is silently un-TOML-able in BOTH directions. This reflection guard
// fails CI on any such drift.
func TestGenConfigCoversAllTomlFields(t *testing.T) {
	enc, err := Defaults.MarshalTOML()
	require.NoError(t, err)
	encT := reflect.TypeOf(enc)
	if encT.Kind() == reflect.Ptr {
		encT = encT.Elem()
	}
	encFields := map[string]bool{}
	for i := 0; i < encT.NumField(); i++ {
		encFields[encT.Field(i).Name] = true
	}
	cfgT := reflect.TypeOf(Config{})
	for i := 0; i < cfgT.NumField(); i++ {
		f := cfgT.Field(i)
		if f.PkgPath != "" { // unexported
			continue
		}
		if tag := f.Tag.Get("toml"); tag == "-" { // intentionally TOML-excluded
			continue
		}
		require.Truef(t, encFields[f.Name],
			"ethconfig.Config.%s is not in the gen_config.go MarshalTOML shadow struct — run `go generate ./eth/ethconfig/` "+
				"so the field is not silently dropped by TOML load/dump", f.Name)
	}
}
