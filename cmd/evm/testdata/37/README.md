This test covers EIP-7778 (block gas accounting without refunds): a call
clears a previously-set storage slot to zero via SSTORE, earning a gas
refund that is still credited to the sender's ETH balance. Under Amsterdam,
receipt.gasUsed / cumulative block gas use the pre-refund peak gas
(ExecutionResult.MaxUsedGas) instead of the post-refund UsedGas, so the
receipt's gasUsed is higher than under Prague for the identical tx/state
even though the sender still receives the refund. exp.json is the Amsterdam
output; exp_prague.json is the same alloc/txs/env run under Prague for
comparison.
