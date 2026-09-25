# RPC reference fixtures

These cases pin JSON-RPC responses produced by the shipped `kore-rpc-booster` proxy.

`trivial-result-configuration.json` is the evaluated initial configuration of `execution/trivial-result-execution/false-ensures.pgm` (`<k> a </k>`, generated counter `0`), the state both servers return for the `execute-trivial` request.
`trivial-result-execute-configuration.json` is k-rust's answer to `execute` with `max-depth=1` from it, and `trivial-result-execute-configuration.reference.json` is the pinned `kore-rpc-booster` answer to the same request (`docs/compatibility.md#trivial-rule-results`).
