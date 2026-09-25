This test covers EIP-7954 (increase maximum contract size): a contract
creation transaction deploys 24577 bytes of runtime code - one byte over
the legacy EIP-170 limit (24576) but well under EIP-7954's Amsterdam limit
(65536). Under Amsterdam the deployment succeeds and the full code is
stored; under Prague the code-size check fails, which (per post-Homestead
semantics) fails the whole transaction and consumes all its gas, so no
contract is deployed. exp.json is the Amsterdam output; exp_prague.json is
the same alloc/txs/env run under Prague for comparison.
