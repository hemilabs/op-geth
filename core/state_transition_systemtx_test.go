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

package core

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/tracing"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/params"
	"github.com/holiman/uint256"
	"github.com/stretchr/testify/require"
)

// TestApplyMessageNoFeeForSystemTxs is the state-level proof of the state_transition.go L1-fee guard. A
// PoP payout (0x7D) and a BTC Attributes Deposited (0x7C) tx, run through ApplyMessage in both the
// Regolith and pre-Regolith eras, pay no base fee and no L1 fee — the OptimismBaseFeeRecipient and
// OptimismL1FeeRecipient balances are unchanged. A legacy user tx is the positive control (it does pay a
// base fee), proving the assertion can detect a fee. Pins the no-L1/base-fee invariant for 0x7C/0x7D
// against a refactor of the :620/:658 early-returns or the :695 guard.
func TestApplyMessageNoFeeForSystemTxs(t *testing.T) {
	// Standard go-ethereum test key; its address is funded so the positive-control user tx can pay.
	key, err := crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	require.NoError(t, err)
	userFrom := crypto.PubkeyToAddress(key.PublicKey)
	to := common.HexToAddress("0x00000000000000000000000000000000000000aa")

	popTo := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := types.NewTx(&types.PopPayoutTx{To: &popTo, Gas: 50_000, Data: []byte("pop")})
	btcHash := chainhash.Hash{0x01, 0x02, 0x03}
	btcAttrInner, err := types.MakeBtcAttributesDepositedTx(&btcHash, nil)
	require.NoError(t, err)
	btcTx := types.NewTx(btcAttrInner)

	coinbase := common.HexToAddress("0x00000000000000000000000000000000000000c0")
	const constL1Cost = 12_345 // nonzero so the positive control genuinely pays an L1 fee

	for _, era := range []struct {
		name     string
		regolith bool
	}{
		{"regolith", true},
		{"pre-regolith", false},
	} {
		t.Run(era.name, func(t *testing.T) {
			cfg := *params.OptimismTestConfig
			if era.regolith {
				zero := uint64(0)
				cfg.RegolithTime = &zero
			} else {
				future := uint64(1_000_000)
				cfg.RegolithTime = &future
			}
			signer := types.LatestSignerForChainID(cfg.ChainID)
			userTx := types.MustSignNewTx(key, signer, &types.LegacyTx{
				Nonce: 0, GasPrice: big.NewInt(1_000_000_000), Gas: 100_000, To: &to, Value: big.NewInt(0),
			})

			type feeDeltas struct{ base, l1, coinbase, sender *big.Int }

			// run applies tx against a fresh state and returns the balance deltas of the base-fee vault,
			// the L1-fee vault, the coinbase, and the sender. A constant nonzero L1CostFunc is injected so
			// the user-control tx actually pays an L1 fee (else the empty-state cost func returns 0 for the
			// control too and the system-tx l1==0 assertion would be a tautology).
			run := func(tx *types.Transaction) feeDeltas {
				statedb, err := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
				require.NoError(t, err)
				statedb.AddBalance(userFrom, uint256.NewInt(1_000_000_000_000_000_000), tracing.BalanceChangeUnspecified)

				header := &types.Header{
					Number:     big.NewInt(1),
					Time:       0,
					BaseFee:    big.NewInt(1_000),
					GasLimit:   30_000_000,
					Difficulty: big.NewInt(0),
				}
				bctx := NewEVMBlockContext(header, nil, &coinbase, &cfg, statedb)
				bctx.L1CostFunc = func(types.RollupCostData, uint64) *big.Int { return big.NewInt(constL1Cost) }
				evm := vm.NewEVM(bctx, statedb, &cfg, vm.Config{})
				msg, err := TransactionToMessage(tx, signer, header.BaseFee)
				require.NoError(t, err)
				evm.SetTxContext(NewEVMTxContext(msg))

				snap := func() (b, l, c, s *big.Int) {
					return statedb.GetBalance(params.OptimismBaseFeeRecipient).ToBig(),
						statedb.GetBalance(params.OptimismL1FeeRecipient).ToBig(),
						statedb.GetBalance(coinbase).ToBig(),
						statedb.GetBalance(msg.From).ToBig()
				}
				b0, l0, c0, s0 := snap()
				_, err = ApplyMessage(evm, msg, new(GasPool).AddGas(30_000_000))
				require.NoError(t, err)
				b1, l1, c1, s1 := snap()
				return feeDeltas{
					base:     new(big.Int).Sub(b1, b0),
					l1:       new(big.Int).Sub(l1, l0),
					coinbase: new(big.Int).Sub(c1, c0),
					sender:   new(big.Int).Sub(s1, s0),
				}
			}

			// Positive control: a normal user tx pays a base fee, an L1 fee, and a coinbase tip, and its
			// sender is charged — so the zero-deltas below are meaningful (the test can detect each fee).
			ctrl := run(userTx)
			require.Equal(t, 1, ctrl.base.Sign(), "user tx must pay a positive base fee")
			require.Equal(t, 1, ctrl.l1.Sign(), "user tx must pay a positive L1 fee")
			require.Equal(t, 1, ctrl.coinbase.Sign(), "user tx must tip the coinbase")
			require.Equal(t, -1, ctrl.sender.Sign(), "user tx sender must be charged")

			for _, sys := range []struct {
				name string
				tx   *types.Transaction
			}{
				{"pop-0x7D", popTx},
				{"btcattr-0x7C", btcTx},
			} {
				d := run(sys.tx)
				require.Zero(t, d.base.Sign(), "%s must not pay a base fee to OptimismBaseFeeRecipient", sys.name)
				require.Zero(t, d.l1.Sign(), "%s must not pay an L1 fee to OptimismL1FeeRecipient", sys.name)
				require.Zero(t, d.coinbase.Sign(), "%s must not tip the coinbase", sys.name)
				require.Zero(t, d.sender.Sign(), "%s sender balance must be unchanged (gas-free)", sys.name)
			}
		})
	}
}
