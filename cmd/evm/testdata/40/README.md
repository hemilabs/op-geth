This test covers EIP-7843 (SLOTNUM opcode, 0x4b): a contract executes
SLOTNUM and stores the result at storage slot 0. Under Amsterdam the opcode
is defined (constant GasQuickStep cost) and the call succeeds; under Prague
0x4b is still an undefined instruction, so the call fails with an invalid
opcode error, consuming all the transaction's gas. exp.json is the Amsterdam
output; exp_prague.json is the same alloc/txs/env run under Prague for
comparison.
