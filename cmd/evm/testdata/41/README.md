This test covers EIP-8024 (backward-compatible SWAPN, DUPN, EXCHANGE): three
contracts each push a run of stack items (17 or 18, per opcode) and execute
DUPN/SWAPN/EXCHANGE with immediate 0x80, storing the resulting value at
storage slot 0. Under Amsterdam all three opcodes are defined and succeed,
each producing the expected stack-manipulation result (storage[0] == 1 in
every case, given how the immediate 0x80 decodes for each op); under Prague
0xe6/0xe7/0xe8 are still undefined instructions, so each call fails with an
invalid opcode error, consuming all the transaction's gas. exp.json is the
Amsterdam output; exp_prague.json is the same alloc/txs/env run under Prague
for comparison.
