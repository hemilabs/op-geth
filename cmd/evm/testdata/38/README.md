This test covers EIP-8246 (remove SELFDESTRUCT burn) together with EIP-7708
(ETH-transfer log): a contract-creation transaction sends an endowment and
its constructor SSTOREs a slot then SELFDESTRUCTs to its own address, all
within the same transaction. Under Amsterdam the account survives the
same-tx self-destruct-to-self with its endowment intact (balance preserved,
nonce/code/storage reset), whereas under Prague (pre-EIP-8246) the account
is deleted and its balance is burned. exp.json is the Amsterdam output;
exp_prague.json is the same alloc/txs/env run under Prague for comparison.
