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

package beacon

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/consensus/misc/eip1559"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
	"github.com/stretchr/testify/require"
)

// extraDataHeaderReader is a minimal ChainHeaderReader: verifyHeader only calls Config() before the
// Optimism extraData check (the 2nd check), so the header-lookup methods are never reached.
type extraDataHeaderReader struct{ cfg *params.ChainConfig }

func (r extraDataHeaderReader) Config() *params.ChainConfig                 { return r.cfg }
func (r extraDataHeaderReader) CurrentHeader() *types.Header                { return nil }
func (r extraDataHeaderReader) GetHeader(common.Hash, uint64) *types.Header { return nil }
func (r extraDataHeaderReader) GetHeaderByNumber(uint64) *types.Header      { return nil }
func (r extraDataHeaderReader) GetHeaderByHash(common.Hash) *types.Header   { return nil }

// TestVerifyHeaderOptimismExtraDataElasticityBound covers the verify call site (consensus.go:
// verifyHeader -> eip1559.ValidateOptimismExtraData(chain.Config(), header.Time, header.Extra,
// header.GasLimit)) for the elasticity<=gasLimit bound, across Holocene and Jovian. It pins that
// header.GasLimit (not parent.GasLimit, header.GasUsed, or a constant) is the threaded field:
// parent.GasLimit (999) and header.GasUsed (1000) are both above the elasticity, so a reject can only
// happen if header.GasLimit (5) is used. Also pins the "invalid optimism extraData: %w" wrapper.
func TestVerifyHeaderOptimismExtraDataElasticityBound(t *testing.T) {
	zero := uint64(0)
	holoceneTime, jovianTime := uint64(100), uint64(200)
	cfg := &params.ChainConfig{
		ChainID:      big.NewInt(1),
		LondonBlock:  big.NewInt(0),
		ShanghaiTime: &zero,
		CancunTime:   &zero,
		CanyonTime:   &zero,
		HoloceneTime: &holoceneTime,
		JovianTime:   &jovianTime,
		Optimism:     &params.OptimismConfig{EIP1559Elasticity: 6, EIP1559Denominator: 50},
	}
	chain := extraDataHeaderReader{cfg: cfg}
	engine := New(ethash.NewFaker())
	parent := &types.Header{Number: big.NewInt(9), GasLimit: 999, Time: holoceneTime}
	mkHeader := func(time, gasLimit uint64, extra []byte) *types.Header {
		// GasUsed deliberately ABOVE the elasticity so a (wrong) GasUsed-based bound would NOT reject.
		return &types.Header{Number: big.NewInt(10), GasLimit: gasLimit, GasUsed: 1000, Time: time, Extra: extra}
	}

	for _, tc := range []struct {
		name       string
		header     *types.Header
		wantReject bool   // true => verifyHeader returns the wrapped extraData reject
		wantErr    string // expected exact error when wantReject
	}{
		{
			name:       "holocene elasticity above header gas limit -> wrapped reject",
			header:     mkHeader(holoceneTime, 5, eip1559.EncodeHoloceneExtraData(250, 10)),
			wantReject: true,
			wantErr:    "invalid optimism extraData: holocene extraData elasticity 10 exceeds gas limit 5",
		},
		{
			name:       "jovian elasticity above header gas limit -> wrapped reject",
			header:     mkHeader(jovianTime, 5, eip1559.EncodeJovianExtraData(250, 10, 7)),
			wantReject: true,
			wantErr:    "invalid optimism extraData: holocene extraData elasticity 10 exceeds gas limit 5",
		},
		{
			// elasticity == header.GasLimit (target 1) passes the extraData check; verifyHeader then fails a
			// LATER check, so we only assert the extraData bound did not reject it.
			name:       "holocene elasticity equals header gas limit -> extraData check passes",
			header:     mkHeader(holoceneTime, 10, eip1559.EncodeHoloceneExtraData(250, 10)),
			wantReject: false,
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			err := engine.verifyHeader(chain, tc.header, parent)
			if tc.wantReject {
				require.EqualError(t, err, tc.wantErr)
			} else if err != nil {
				require.NotContains(t, err.Error(), "exceeds gas limit", "extraData bound must not reject the e==gasLimit boundary")
				require.NotContains(t, err.Error(), "invalid optimism extraData")
			}
		})
	}
}
