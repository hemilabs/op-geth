This test covers EIP-2780's contract-creation intrinsic gas (TX_BASE_COST +
CREATE_ACCESS) plus EIP-8037's runtime state-gas charges under Amsterdam: a
contract-creation transaction whose initcode deploys a small runtime contract
via CODECOPY/RETURN triggers the new-account state-gas charge
(GasNewAccountStateEIP8037) and the per-byte code-deposit state-gas charge
(GasCodeDepositStateEIP8037), both of which spill fully into execution gas
since the tx's declared gas limit is below EIP-7825's MaxTxGas (so the
EIP-8037 state-gas reservoir is zero). exp.json is the Amsterdam output
(gasUsed dominated by the state-gas charges); exp_prague.json is the same
alloc/txs/env run under Prague (legacy flat CreateDataGas-based accounting,
much lower gasUsed) for comparison.
