// Copyright 2017 The go-ethereum Authors
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

package params

import (
	"encoding/json"
	"fmt"
	"math"
	"math/big"
	"reflect"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
)

func TestCheckCompatible(t *testing.T) {
	type test struct {
		stored, new   *ChainConfig
		headBlock     uint64
		headTimestamp uint64
		wantErr       *ConfigCompatError

		genesisTimestamp *uint64
	}
	tests := []test{
		{stored: AllEthashProtocolChanges, new: AllEthashProtocolChanges, headBlock: 0, headTimestamp: 0, wantErr: nil},
		{stored: AllEthashProtocolChanges, new: AllEthashProtocolChanges, headBlock: 0, headTimestamp: uint64(time.Now().Unix()), wantErr: nil},
		{stored: AllEthashProtocolChanges, new: AllEthashProtocolChanges, headBlock: 100, wantErr: nil},
		{
			stored:    &ChainConfig{EIP150Block: big.NewInt(10)},
			new:       &ChainConfig{EIP150Block: big.NewInt(20)},
			headBlock: 9,
			wantErr:   nil,
		},
		{
			stored:    AllEthashProtocolChanges,
			new:       &ChainConfig{HomesteadBlock: nil},
			headBlock: 3,
			wantErr: &ConfigCompatError{
				What:          "Homestead fork block",
				StoredBlock:   big.NewInt(0),
				NewBlock:      nil,
				RewindToBlock: 0,
			},
		},
		{
			stored:    AllEthashProtocolChanges,
			new:       &ChainConfig{HomesteadBlock: big.NewInt(1)},
			headBlock: 3,
			wantErr: &ConfigCompatError{
				What:          "Homestead fork block",
				StoredBlock:   big.NewInt(0),
				NewBlock:      big.NewInt(1),
				RewindToBlock: 0,
			},
		},
		{
			stored:    &ChainConfig{HomesteadBlock: big.NewInt(30), EIP150Block: big.NewInt(10)},
			new:       &ChainConfig{HomesteadBlock: big.NewInt(25), EIP150Block: big.NewInt(20)},
			headBlock: 25,
			wantErr: &ConfigCompatError{
				What:          "EIP150 fork block",
				StoredBlock:   big.NewInt(10),
				NewBlock:      big.NewInt(20),
				RewindToBlock: 9,
			},
		},
		{
			stored:    &ChainConfig{ConstantinopleBlock: big.NewInt(30)},
			new:       &ChainConfig{ConstantinopleBlock: big.NewInt(30), PetersburgBlock: big.NewInt(30)},
			headBlock: 40,
			wantErr:   nil,
		},
		{
			stored:    &ChainConfig{ConstantinopleBlock: big.NewInt(30)},
			new:       &ChainConfig{ConstantinopleBlock: big.NewInt(30), PetersburgBlock: big.NewInt(31)},
			headBlock: 40,
			wantErr: &ConfigCompatError{
				What:          "Petersburg fork block",
				StoredBlock:   nil,
				NewBlock:      big.NewInt(31),
				RewindToBlock: 30,
			},
		},
		{
			stored:        &ChainConfig{ShanghaiTime: newUint64(10)},
			new:           &ChainConfig{ShanghaiTime: newUint64(20)},
			headTimestamp: 9,
			wantErr:       nil,
		},
		{
			stored:        &ChainConfig{ShanghaiTime: newUint64(10)},
			new:           &ChainConfig{ShanghaiTime: newUint64(20)},
			headTimestamp: 25,
			wantErr: &ConfigCompatError{
				What:         "Shanghai fork timestamp",
				StoredTime:   newUint64(10),
				NewTime:      newUint64(20),
				RewindToTime: 9,
			},
		},
		{
			stored:           &ChainConfig{CanyonTime: newUint64(10)},
			new:              &ChainConfig{CanyonTime: newUint64(20)},
			headTimestamp:    25,
			genesisTimestamp: newUint64(2),
			wantErr: &ConfigCompatError{
				What:         "Canyon fork timestamp",
				StoredTime:   newUint64(10),
				NewTime:      newUint64(20),
				RewindToTime: 9,
			},
		},
		{
			stored:           &ChainConfig{CanyonTime: newUint64(10)},
			new:              &ChainConfig{CanyonTime: newUint64(20)},
			headTimestamp:    25,
			genesisTimestamp: nil,
			wantErr: &ConfigCompatError{
				What:         "Canyon fork timestamp",
				StoredTime:   newUint64(10),
				NewTime:      newUint64(20),
				RewindToTime: 9,
			},
		},
		{
			stored:           &ChainConfig{CanyonTime: newUint64(10)},
			new:              &ChainConfig{CanyonTime: newUint64(20)},
			headTimestamp:    25,
			genesisTimestamp: newUint64(24),
			wantErr:          nil,
		},
		{
			stored:           &ChainConfig{HoloceneTime: newUint64(10)},
			new:              &ChainConfig{HoloceneTime: newUint64(20)},
			headTimestamp:    25,
			genesisTimestamp: newUint64(15),
			wantErr: &ConfigCompatError{
				What:         "Holocene fork timestamp",
				StoredTime:   newUint64(10),
				NewTime:      newUint64(20),
				RewindToTime: 9,
			},
		},
		{
			stored:           &ChainConfig{HoloceneTime: newUint64(10)},
			new:              &ChainConfig{HoloceneTime: newUint64(20)},
			headTimestamp:    15,
			genesisTimestamp: newUint64(5),
			wantErr: &ConfigCompatError{
				What:         "Holocene fork timestamp",
				StoredTime:   newUint64(10),
				NewTime:      newUint64(20),
				RewindToTime: 9,
			},
		},
		// hVM Phase 0 fork timestamp must be enforced by CheckCompatible (via opCheckCompatible) like every other op
		// fork: moving Hvm0Time across an already-processed head must force a protective rewind, not silently
		// re-interpret synced blocks under hVM rules. Without the opCheckCompatible guard this row would get a nil err.
		{
			stored:           &ChainConfig{Hvm0Time: newUint64(10)},
			new:              &ChainConfig{Hvm0Time: newUint64(20)},
			headTimestamp:    25,
			genesisTimestamp: newUint64(15),
			wantErr: &ConfigCompatError{
				What:         "hVM Phase 0 fork timestamp",
				StoredTime:   newUint64(10),
				NewTime:      newUint64(20),
				RewindToTime: 9,
			},
		},
		// Control: head before either Hvm0Time means no block has been processed under either schedule, so moving the
		// fork is compatible (no rewind). Pins that the guard is head-gated, not a blanket "any Hvm0Time change rewinds".
		{
			stored:           &ChainConfig{Hvm0Time: newUint64(10)},
			new:              &ChainConfig{Hvm0Time: newUint64(20)},
			headTimestamp:    5,
			genesisTimestamp: newUint64(1),
			wantErr:          nil,
		},
		// Move-EARLIER: the EXACT scenario config_op.go's guard comment names — an operator setting --override.hvm0 to
		// an EARLIER timestamp on an already-synced node. Blocks in (new,stored] were processed WITHOUT hVM and must be
		// rewound and re-processed under hVM rules. Rewind = newtime-1 (the earlier schedule).
		{
			stored:           &ChainConfig{Hvm0Time: newUint64(20)},
			new:              &ChainConfig{Hvm0Time: newUint64(10)},
			headTimestamp:    25,
			genesisTimestamp: newUint64(15),
			wantErr: &ConfigCompatError{
				What:         "hVM Phase 0 fork timestamp",
				StoredTime:   newUint64(20),
				NewTime:      newUint64(10),
				RewindToTime: 9,
			},
		},
		// nil -> set: enabling hVM (was disabled) on a node already past the new activation must rewind to newtime-1 so
		// the now-hVM-active blocks are re-processed. This is the from-scratch testnet3 enablement transition.
		{
			stored:           &ChainConfig{Hvm0Time: nil},
			new:              &ChainConfig{Hvm0Time: newUint64(10)},
			headTimestamp:    25,
			genesisTimestamp: newUint64(5),
			wantErr: &ConfigCompatError{
				What:         "hVM Phase 0 fork timestamp",
				StoredTime:   nil,
				NewTime:      newUint64(10),
				RewindToTime: 9,
			},
		},
	}

	for i, test := range tests {
		t.Run(fmt.Sprintf("case %d", i), func(t *testing.T) {
			err := test.stored.CheckCompatible(test.new, test.headBlock, test.headTimestamp, test.genesisTimestamp)
			if !reflect.DeepEqual(err, test.wantErr) {
				t.Errorf("error mismatch:\nstored: %v\nnew: %v\nheadBlock: %v\nheadTimestamp: %v\nerr: %v\nwant: %v", test.stored, test.new, test.headBlock, test.headTimestamp, err, test.wantErr)
			}
		})
	}
}

func TestConfigRules(t *testing.T) {
	c := &ChainConfig{
		LondonBlock:  new(big.Int),
		ShanghaiTime: newUint64(500),
	}
	var stamp uint64
	if r := c.Rules(big.NewInt(0), true, stamp); r.IsShanghai {
		t.Errorf("expected %v to not be shanghai", stamp)
	}
	stamp = 500
	if r := c.Rules(big.NewInt(0), true, stamp); !r.IsShanghai {
		t.Errorf("expected %v to be shanghai", stamp)
	}
	stamp = math.MaxInt64
	if r := c.Rules(big.NewInt(0), true, stamp); !r.IsShanghai {
		t.Errorf("expected %v to be shanghai", stamp)
	}
}

func TestTimestampCompatError(t *testing.T) {
	require.Equal(t, new(ConfigCompatError).Error(), "")

	errWhat := "Shanghai fork timestamp"
	require.Equal(t, newTimestampCompatError(errWhat, nil, newUint64(1681338455)).Error(),
		"mismatching Shanghai fork timestamp in database (have timestamp nil, want timestamp 1681338455, rewindto timestamp 1681338454)")

	require.Equal(t, newTimestampCompatError(errWhat, newUint64(1681338455), nil).Error(),
		"mismatching Shanghai fork timestamp in database (have timestamp 1681338455, want timestamp nil, rewindto timestamp 1681338454)")

	require.Equal(t, newTimestampCompatError(errWhat, newUint64(1681338455), newUint64(600624000)).Error(),
		"mismatching Shanghai fork timestamp in database (have timestamp 1681338455, want timestamp 600624000, rewindto timestamp 600623999)")

	require.Equal(t, newTimestampCompatError(errWhat, newUint64(0), newUint64(1681338455)).Error(),
		"mismatching Shanghai fork timestamp in database (have timestamp 0, want timestamp 1681338455, rewindto timestamp 0)")
}

func TestConfigRulesRegolith(t *testing.T) {
	c := &ChainConfig{
		RegolithTime: newUint64(500),
		LondonBlock:  new(big.Int),
		Optimism:     &OptimismConfig{},
	}
	var stamp uint64
	if r := c.Rules(big.NewInt(0), true, stamp); r.IsOptimismRegolith {
		t.Errorf("expected %v to not be regolith", stamp)
	}
	stamp = 500
	if r := c.Rules(big.NewInt(0), true, stamp); !r.IsOptimismRegolith {
		t.Errorf("expected %v to be regolith", stamp)
	}
	stamp = math.MaxInt64
	if r := c.Rules(big.NewInt(0), true, stamp); !r.IsOptimismRegolith {
		t.Errorf("expected %v to be regolith", stamp)
	}
}

func TestCheckOptimismValidity(t *testing.T) {
	validOpConfig := &OptimismConfig{
		EIP1559Denominator:       10,
		EIP1559Elasticity:        50,
		EIP1559DenominatorCanyon: newUint64(250),
	}

	tests := []struct {
		name    string
		config  *ChainConfig
		wantErr *string
	}{
		{
			name: "valid",
			config: &ChainConfig{
				Optimism:     validOpConfig,
				CanyonTime:   newUint64(100),
				ShanghaiTime: newUint64(100),
				CancunTime:   newUint64(200),
				EcotoneTime:  newUint64(200),
				PragueTime:   newUint64(300),
				IsthmusTime:  newUint64(300),
			},
			wantErr: nil,
		},
		{
			name: "zero EIP1559Denominator",
			config: &ChainConfig{
				Optimism: &OptimismConfig{
					EIP1559Denominator: 0,
					EIP1559Elasticity:  50,
				},
			},
			wantErr: ptr("zero EIP1559Denominator"),
		},
		{
			name: "zero EIP1559Elasticity",
			config: &ChainConfig{
				Optimism: &OptimismConfig{
					EIP1559Denominator: 10,
					EIP1559Elasticity:  0,
				},
			},
			wantErr: ptr("zero EIP1559Elasticity"),
		},
		{
			name: "missing EIP1559DenominatorCanyon",
			config: &ChainConfig{
				Optimism: &OptimismConfig{
					EIP1559Denominator: 10,
					EIP1559Elasticity:  50,
				},
				CanyonTime: newUint64(100),
			},
			wantErr: ptr("missing or zero EIP1559DenominatorCanyon"),
		},
		{
			name: "ShanghaiTime not equal to CanyonTime",
			config: &ChainConfig{
				Optimism:     validOpConfig,
				ShanghaiTime: newUint64(100),
				CanyonTime:   newUint64(200),
			},
			wantErr: ptr("ShanghaiTime (100) must equal CanyonTime (200)"),
		},
		{
			name: "CancunTime not equal to EcotoneTime",
			config: &ChainConfig{
				Optimism:    validOpConfig,
				CancunTime:  newUint64(200),
				EcotoneTime: newUint64(300),
			},
			wantErr: ptr("CancunTime (200) must equal EcotoneTime (300)"),
		},
		{
			name: "PragueTime not equal to IsthmusTime",
			config: &ChainConfig{
				Optimism:    validOpConfig,
				PragueTime:  newUint64(300),
				IsthmusTime: newUint64(400),
			},
			wantErr: ptr("PragueTime (300) must equal IsthmusTime (400)"),
		},
		{
			name: "nil ShanghaiTime",
			config: &ChainConfig{
				Optimism:   validOpConfig,
				CanyonTime: newUint64(200),
			},
			wantErr: ptr("ShanghaiTime (<nil>) must equal CanyonTime (200)"),
		},
		{
			name: "nil CancunTime",
			config: &ChainConfig{
				Optimism:    validOpConfig,
				EcotoneTime: newUint64(300),
			},
			wantErr: ptr("CancunTime (<nil>) must equal EcotoneTime (300)"),
		},
		{
			name: "nil PragueTime",
			config: &ChainConfig{
				Optimism: &OptimismConfig{
					EIP1559Denominator:       10,
					EIP1559Elasticity:        50,
					EIP1559DenominatorCanyon: newUint64(250),
				},
				IsthmusTime: newUint64(400),
			},
			wantErr: ptr("PragueTime (<nil>) must equal IsthmusTime (400)"),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tt.config.CheckOptimismValidity()
			if tt.wantErr != nil {
				require.EqualError(t, err, *tt.wantErr)
			} else {
				require.NoError(t, err)
			}
		})
	}
}

func ptr[T any](t T) *T {
	return &t
}

// TestConfigRulesHvm0 pins two properties of the IsHvm0 field in Rules() that no test asserts. (1) MERGE-
// INDEPENDENCE: IsHvm0 is the ONLY fork field set from a bare predicate (`IsHvm0: c.IsHvm0(timestamp)`), with no
// `isMerge &&` guard that every sibling fork (Shanghai/Cancun/all Optimism forks) carries — an intentional, fragile
// design (there is an in-code TODO). A "consistency cleanup" adding `isMerge &&` would silently disable hVM for any
// pre-London/non-merge config. (2) nil-disable: a nil Hvm0Time disables it.
func TestConfigRulesHvm0(t *testing.T) {
	// Merge-independence: NO London, NO Optimism set, isMerge=false -> IsHvm0 still activates on the timestamp.
	c := &ChainConfig{Hvm0Time: newUint64(500)}
	for _, isMerge := range []bool{false, true} {
		if r := c.Rules(big.NewInt(0), isMerge, 499); r.IsHvm0 {
			t.Errorf("isMerge=%v: IsHvm0 must be false before activation", isMerge)
		}
		if r := c.Rules(big.NewInt(0), isMerge, 500); !r.IsHvm0 {
			t.Errorf("isMerge=%v: IsHvm0 must be true at activation (independent of isMerge)", isMerge)
		}
		if r := c.Rules(big.NewInt(0), isMerge, math.MaxInt64); !r.IsHvm0 {
			t.Errorf("isMerge=%v: IsHvm0 must stay true past activation", isMerge)
		}
	}

	// Differential against a merge-GATED sibling: with isMerge=false, Shanghai stays off past its time while IsHvm0
	// is on at the same timestamp — exactly the gap an `isMerge &&` mutation on the IsHvm0 line would erase.
	cg := &ChainConfig{Hvm0Time: newUint64(500), ShanghaiTime: newUint64(500)}
	r := cg.Rules(big.NewInt(0), false, 600)
	if r.IsShanghai {
		t.Errorf("Shanghai is merge-gated: must be false when isMerge=false")
	}
	if !r.IsHvm0 {
		t.Errorf("IsHvm0 must be true regardless of isMerge — the merge-independence invariant")
	}

	// nil Hvm0Time disables hVM everywhere.
	if r := (&ChainConfig{}).Rules(big.NewInt(0), true, math.MaxInt64); r.IsHvm0 {
		t.Errorf("a nil Hvm0Time must keep IsHvm0 false")
	}
}

// TestChainConfigHvm0TimeJSONRoundTrip pins the Hvm0Time JSON serialization (struct tag "hvm0Time,omitempty";
// ChainConfig has no custom MarshalJSON). This is the genesis.json / rawdb config-persistence path
// (core/genesis.go + rawdb.WriteChainConfig/ReadChainConfig); a field-name change or a dropped value would
// silently disable hVM on a config reload. No params test marshalled/unmarshalled Hvm0Time.
func TestChainConfigHvm0TimeJSONRoundTrip(t *testing.T) {
	// Round-trip with a set value.
	c := &ChainConfig{Hvm0Time: newUint64(500)}
	b, err := json.Marshal(c)
	require.NoError(t, err)
	require.Contains(t, string(b), `"hvm0Time":500`, "the on-wire field name must be the stable hvm0Time")
	var got ChainConfig
	require.NoError(t, json.Unmarshal(b, &got))
	require.NotNil(t, got.Hvm0Time)
	require.Equal(t, uint64(500), *got.Hvm0Time)

	// nil (hVM disabled) is omitted (omitempty) and round-trips as nil.
	b2, err := json.Marshal(&ChainConfig{})
	require.NoError(t, err)
	require.NotContains(t, string(b2), "hvm0Time", "a nil Hvm0Time must be omitted")
	var got2 ChainConfig
	require.NoError(t, json.Unmarshal(b2, &got2))
	require.Nil(t, got2.Hvm0Time)

	// Deserialization direction (a hand-written genesis.json snippet) locks the read path independently.
	var got3 ChainConfig
	require.NoError(t, json.Unmarshal([]byte(`{"chainId":1,"hvm0Time":1700000000}`), &got3))
	require.NotNil(t, got3.Hvm0Time)
	require.Equal(t, uint64(1700000000), *got3.Hvm0Time)
}
