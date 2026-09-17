This test covers EIP-2780 (reduced intrinsic tx gas), EIP-8038 (state-access
gas repricing) and EIP-7708 (ETH transfers emit a log) under Amsterdam: a
self-transfer (tx 0) only pays TX_BASE_COST (12000 gas) instead of the legacy
flat 21000, and a transfer to a distinct account (tx 1) emits a synthetic
ERC-20-Transfer-shaped log from the EIP-4788 system address. exp.json is the
Amsterdam output; exp_prague.json is the same alloc/txs run under Prague for
comparison (legacy 21000 gas each, no synthetic log).
