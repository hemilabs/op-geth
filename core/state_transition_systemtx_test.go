// Copyright 2024 The go-ethereum Authors
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

// TestSystemTxGasPoolReservation pins the gas-RESERVING half of the system-tx dual: the gas-exempt branch makes a
// deposit/PoP/BtcAttr gas-FREE to the sender (covered by TestApplyMessageNoFeeForSystemTxs) but RESERVES its full
// GasLimit from the block gas pool via gp.SubGas(GasLimit). Only the gas-free half was pinned; the pool reservation
// and the ErrGasLimitReached boundary were never observed.
func TestSystemTxGasPoolReservation(t *testing.T) {
	cfg := *params.OptimismTestConfig
	zero := uint64(0)
	cfg.RegolithTime = &zero
	signer := types.LatestSignerForChainID(cfg.ChainID)
	coinbase := common.HexToAddress("0x00000000000000000000000000000000000000c0")
	popTo := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := types.NewTx(&types.PopPayoutTx{To: &popTo, Gas: 50_000, Data: []byte("pop")})
	btcHash := chainhash.Hash{0x01, 0x02, 0x03}
	btcInner, err := types.MakeBtcAttributesDepositedTx(&btcHash, nil)
	require.NoError(t, err)
	btcTx := types.NewTx(btcInner) // GasLimit 1_000_000

	apply := func(tx *types.Transaction, poolGas uint64) (uint64, error) {
		statedb, err := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
		require.NoError(t, err)
		header := &types.Header{Number: big.NewInt(1), Time: 0, BaseFee: big.NewInt(1_000), GasLimit: 30_000_000, Difficulty: big.NewInt(0)}
		bctx := NewEVMBlockContext(header, nil, &coinbase, &cfg, statedb)
		bctx.L1CostFunc = func(types.RollupCostData, uint64) *big.Int { return big.NewInt(0) }
		evm := vm.NewEVM(bctx, statedb, &cfg, vm.Config{})
		msg, err := TransactionToMessage(tx, signer, header.BaseFee)
		require.NoError(t, err)
		evm.SetTxContext(NewEVMTxContext(msg))
		gp := new(GasPool).AddGas(poolGas)
		_, applyErr := ApplyMessage(evm, msg, gp)
		return gp.Gas(), applyErr
	}

	// Up-front reservation requires the FULL GasLimit (gp.SubGas(GasLimit) at preCheck), so a system tx can exhaust
	// the block gas limit EVEN THOUGH it is gas-free to the sender. The threshold tracks each tx's OWN GasLimit
	// (1M for BtcAttr, 50k for PoP) — not a constant.
	_, err = apply(btcTx, 999_999)
	require.ErrorIs(t, err, ErrGasLimitReached, "a pool below the BtcAttr's 1M GasLimit must reject up front")
	_, err = apply(btcTx, 1_000_000)
	require.NoError(t, err, "a pool of exactly the BtcAttr GasLimit reserves successfully")
	_, err = apply(popTx, 49_999)
	require.ErrorIs(t, err, ErrGasLimitReached, "the PoP's smaller 50k GasLimit has a smaller threshold")
	_, err = apply(popTx, 50_000)
	require.NoError(t, err)

	// With ample pool the tx CONSUMES block gas (it is gas-free to the sender, not to the block) but the unused
	// portion above actual usage is refunded — so the net pool draw is strictly between 0 and the full GasLimit.
	const ample = uint64(2_000_000)
	rem, err := apply(btcTx, ample)
	require.NoError(t, err)
	used := ample - rem
	require.Positive(t, used, "a system tx must consume block gas (not free to the block)")
	require.Less(t, used, uint64(1_000_000), "unused gas above actual usage must be refunded to the pool")
}

// TestApplyTransactionBtcAttrReceiptNonceHvm0 pins the consensus rule that a BtcAttr (0x7C) receipt produced by the
// block processor carries the SENDER's actual account nonce (read pre-increment under Regolith) — but ONLY when Hvm0
// is active: MakeReceipt gates receipt.BtcAttributesDepositedNonce on config.IsHvm0(evm.Context.Time)
// (state_processor.go ~218), with the value read via statedb.GetNonce(msg.From) at ~163. The receipt RLP/JSON nonce
// round-trip is covered, but no test drove the PROCESSING-time POPULATION through ApplyTransactionWithEVM. A mutant
// making the IsHvm0 gate unconditional, or reading tx.Nonce() (always 0) instead of the state nonce, survives every
// encoding test. Corpus-free (in-memory statedb + EVM).
func TestApplyTransactionBtcAttrReceiptNonceHvm0(t *testing.T) {
	signer := types.LatestSignerForChainID(big.NewInt(1))
	btcInner, err := types.MakeBtcAttributesDepositedTx(&chainhash.Hash{0x09}, nil)
	require.NoError(t, err)
	btcTx := types.NewTx(btcInner)
	coinbase := common.HexToAddress("0x00000000000000000000000000000000000000c0")

	run := func(hvm0Active bool) *types.Receipt {
		cfg := *params.OptimismTestConfig // RegolithTime=0 -> the recorded nonce is read from state
		if hvm0Active {
			z := uint64(0)
			cfg.Hvm0Time = &z
		} else {
			future := uint64(1) << 62
			cfg.Hvm0Time = &future // Hvm0 inactive at block time 0
		}
		statedb, err := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
		require.NoError(t, err)
		// The 0x7C sender account is at nonce 5; the receipt must record 5 (pre-increment) and state must become 6.
		statedb.SetNonce(types.BtcAttributesDepositedSenderAddress, 5, tracing.NonceChangeUnspecified)

		header := &types.Header{Number: big.NewInt(1), Time: 0, BaseFee: big.NewInt(1_000), GasLimit: 30_000_000, Difficulty: big.NewInt(0)}
		bctx := NewEVMBlockContext(header, nil, &coinbase, &cfg, statedb)
		evm := vm.NewEVM(bctx, statedb, &cfg, vm.Config{})
		msg, err := TransactionToMessage(btcTx, signer, header.BaseFee)
		require.NoError(t, err)
		require.Equal(t, types.BtcAttributesDepositedSenderAddress, msg.From, "the 0x7C msg.From is the hardcoded consensus sender")
		evm.SetTxContext(NewEVMTxContext(msg))

		usedGas := uint64(0)
		receipt, err := ApplyTransactionWithEVM(msg, new(GasPool).AddGas(30_000_000), statedb, header.Number, common.Hash{}, header.Time, btcTx, &usedGas, evm)
		require.NoError(t, err)
		require.Equal(t, uint64(6), statedb.GetNonce(types.BtcAttributesDepositedSenderAddress), "the system tx must increment the sender nonce 5->6")
		return receipt
	}

	// Hvm0 active: the receipt records the actual account nonce read BEFORE the increment.
	r := run(true)
	require.NotNil(t, r.BtcAttributesDepositedNonce, "an Hvm0-era BtcAttr receipt must carry the nonce")
	require.Equal(t, uint64(5), *r.BtcAttributesDepositedNonce, "the receipt nonce must be the sender's pre-increment account nonce")
	require.Equal(t, uint8(types.BtcAttributesDepositedTxType), r.Type)

	// Hvm0 inactive: the field must be nil (the IsHvm0 receipt gate is load-bearing).
	r2 := run(false)
	require.Nil(t, r2.BtcAttributesDepositedNonce, "a pre-Hvm0 BtcAttr receipt must NOT carry the nonce (IsHvm0 gate)")
}

// TestTransactionToMessageSystemTxFlags pins TransactionToMessage's per-type flag + From derivation for the three
// force-included system txs: the (IsDepositTx, IsPopPayoutTx, IsBtcAttributesDepositedTx) tuple is the switch the
// state-transition fee/gas/nonce guards branch on, and From is the hardcoded consensus identity. A mutant mis-wiring
// a flag (e.g. setting IsPopPayoutTx for a 0x7C tx) would re-route the fee logic yet survive the apply-level tests.
func TestTransactionToMessageSystemTxFlags(t *testing.T) {
	signer := types.LatestSignerForChainID(big.NewInt(1))
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	depFrom := common.HexToAddress("0x00000000000000000000000000000000000000de")

	btcInner, err := types.MakeBtcAttributesDepositedTx(&chainhash.Hash{0x01}, nil)
	require.NoError(t, err)
	btcTx := types.NewTx(btcInner)
	popTx := types.NewTx(&types.PopPayoutTx{To: &to, Gas: 50_000, Data: []byte("pop")})
	depTx := types.NewTx(&types.DepositTx{From: depFrom, To: &to, Value: big.NewInt(0), Gas: 21_000})

	for _, tc := range []struct {
		name                      string
		tx                        *types.Transaction
		wantDep, wantPop, wantBtc bool
		wantFrom                  common.Address
	}{
		{"deposit-0x7E", depTx, true, false, false, depFrom},
		{"pop-0x7D", popTx, false, true, false, types.PoPPayoutSenderAddress},
		{"btcattr-0x7C", btcTx, false, false, true, types.BtcAttributesDepositedSenderAddress},
	} {
		msg, err := TransactionToMessage(tc.tx, signer, big.NewInt(0))
		require.NoError(t, err, tc.name)
		require.Equal(t, tc.wantDep, msg.IsDepositTx, "%s IsDepositTx", tc.name)
		require.Equal(t, tc.wantPop, msg.IsPopPayoutTx, "%s IsPopPayoutTx", tc.name)
		require.Equal(t, tc.wantBtc, msg.IsBtcAttributesDepositedTx, "%s IsBtcAttributesDepositedTx", tc.name)
		require.Equal(t, tc.wantFrom, msg.From, "%s From", tc.name)
	}
}

// TestApplyTransactionDepositReceiptNonceRegolith completes the system-tx receipt-nonce-population set (BtcAttr and
// PoP are pinned; deposit is the third sibling sharing the state_transition.go:162 branch). A deposit receipt carries
// the sender's pre-increment account nonce ONLY when Regolith is active (MakeReceipt gate, state_processor.go ~201).
// A mutant dropping the Regolith gate, or reading tx.Nonce() (always 0) instead of statedb.GetNonce(msg.From),
// survives the receipt RLP/JSON tests (which use pre-built fixtures). Corpus-free (in-memory statedb + EVM).
func TestApplyTransactionDepositReceiptNonceRegolith(t *testing.T) {
	signer := types.LatestSignerForChainID(big.NewInt(1))
	depFrom := common.HexToAddress("0x00000000000000000000000000000000000000de")
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	depTx := types.NewTx(&types.DepositTx{From: depFrom, To: &to, Value: big.NewInt(0), Gas: 50_000})
	coinbase := common.HexToAddress("0x00000000000000000000000000000000000000c0")

	run := func(regolith bool) *types.Receipt {
		cfg := *params.OptimismTestConfig
		if regolith {
			z := uint64(0)
			cfg.RegolithTime = &z
		} else {
			future := uint64(1) << 62
			cfg.RegolithTime = &future // Regolith inactive at block time 0
		}
		statedb, err := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
		require.NoError(t, err)
		statedb.SetNonce(depFrom, 5, tracing.NonceChangeUnspecified)

		header := &types.Header{Number: big.NewInt(1), Time: 0, BaseFee: big.NewInt(1_000), GasLimit: 30_000_000, Difficulty: big.NewInt(0)}
		bctx := NewEVMBlockContext(header, nil, &coinbase, &cfg, statedb)
		evm := vm.NewEVM(bctx, statedb, &cfg, vm.Config{})
		msg, err := TransactionToMessage(depTx, signer, header.BaseFee)
		require.NoError(t, err)
		require.True(t, msg.IsDepositTx)
		require.Equal(t, depFrom, msg.From)
		evm.SetTxContext(NewEVMTxContext(msg))

		usedGas := uint64(0)
		receipt, err := ApplyTransactionWithEVM(msg, new(GasPool).AddGas(30_000_000), statedb, header.Number, common.Hash{}, header.Time, depTx, &usedGas, evm)
		require.NoError(t, err)
		// The deposit must INCREMENT the sender nonce (5->6) regardless of Regolith — this is what makes the
		// recorded DepositNonce a genuine "pre-increment" value rather than a coincidental read.
		require.Equal(t, uint64(6), statedb.GetNonce(depFrom), "the deposit tx must increment the sender nonce 5->6")
		return receipt
	}

	// Regolith active: the receipt records the sender's actual account nonce (read pre-increment).
	r := run(true)
	require.NotNil(t, r.DepositNonce, "a Regolith-era deposit receipt must carry the nonce")
	require.Equal(t, uint64(5), *r.DepositNonce, "the receipt nonce must be the sender's pre-increment account nonce")

	// Regolith inactive: the field must be nil (the Regolith gate is load-bearing).
	r2 := run(false)
	require.Nil(t, r2.DepositNonce, "a pre-Regolith deposit receipt must NOT carry the nonce")
}

// TestApplyTransactionTracerHooksSystemTx pins that the EVM tracer's OnTxStart receives the HARDCODED consensus
// sender as From for a system tx (not the To or zero), and OnTxEnd receives the built receipt. A regression feeding
// the wrong From (e.g. msg.To) would mis-attribute the force-included tx to tracers/indexers. The BtcAttr tx uses a
// To DISTINCT from the 0x8888 sender so the From assertion is non-vacuous. Corpus-free (in-memory EVM + statedb).
func TestApplyTransactionTracerHooksSystemTx(t *testing.T) {
	signer := types.LatestSignerForChainID(big.NewInt(1))
	coinbase := common.HexToAddress("0x00000000000000000000000000000000000000c0")
	distinctTo := common.HexToAddress("0x4200000000000000000000000000000000000015") // != the 0x8888 sender
	require.NotEqual(t, types.BtcAttributesDepositedSenderAddress, distinctTo, "anti-vacuity: To must differ from From")
	gov := common.HexToAddress("0x4200000000000000000000000000000000000042")

	for _, tc := range []struct {
		name     string
		tx       *types.Transaction
		wantFrom common.Address
		wantType uint8
	}{
		{"btcattr-0x7C", types.NewTx(&types.BtcAttributesDepositedTx{To: &distinctTo, Gas: 1_000_000, Data: []byte{0x01}}), types.BtcAttributesDepositedSenderAddress, types.BtcAttributesDepositedTxType},
		{"pop-0x7D", types.NewTx(&types.PopPayoutTx{To: &gov, Gas: 50_000, Data: []byte("pop")}), types.PoPPayoutSenderAddress, types.PopPayoutTxType},
	} {
		t.Run(tc.name, func(t *testing.T) {
			cfg := *params.OptimismTestConfig
			z := uint64(0)
			cfg.Hvm0Time = &z
			statedb, err := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
			require.NoError(t, err)

			var gotFrom common.Address
			var gotReceiptType uint8
			var sawStart, sawEnd bool
			hooks := &tracing.Hooks{
				OnTxStart: func(_ *tracing.VMContext, _ *types.Transaction, from common.Address) { gotFrom = from; sawStart = true },
				OnTxEnd: func(receipt *types.Receipt, _ error) {
					sawEnd = true
					if receipt != nil {
						gotReceiptType = receipt.Type
					}
				},
			}
			header := &types.Header{Number: big.NewInt(1), Time: 0, BaseFee: big.NewInt(1_000), GasLimit: 30_000_000, Difficulty: big.NewInt(0)}
			bctx := NewEVMBlockContext(header, nil, &coinbase, &cfg, statedb)
			evm := vm.NewEVM(bctx, statedb, &cfg, vm.Config{Tracer: hooks})
			msg, err := TransactionToMessage(tc.tx, signer, header.BaseFee)
			require.NoError(t, err)
			evm.SetTxContext(NewEVMTxContext(msg))

			usedGas := uint64(0)
			_, err = ApplyTransactionWithEVM(msg, new(GasPool).AddGas(30_000_000), statedb, header.Number, common.Hash{}, header.Time, tc.tx, &usedGas, evm)
			require.NoError(t, err)
			require.True(t, sawStart, "OnTxStart must fire")
			require.True(t, sawEnd, "OnTxEnd must fire")
			require.Equal(t, tc.wantFrom, gotFrom, "OnTxStart must receive the hardcoded consensus sender as From (not To/zero)")
			require.Equal(t, tc.wantType, gotReceiptType, "OnTxEnd receipt must carry the system-tx type")
		})
	}
}
