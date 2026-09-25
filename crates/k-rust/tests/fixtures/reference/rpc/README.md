# RPC reference fixtures

These cases pin JSON-RPC responses produced by the shipped `kore-rpc-booster` proxy.

`imp-implies.json` and `imp-implies.reference.json` are the two sides of the `imp` `implies` entry under `rpc.oracle-exception` in `scripts/reference-differential.toml`: the k-rust response and the pinned `kore-rpc-booster` response to the same request.
The RPC gate (normalisation N19) compares each side against its own file and requires the two files to differ, so a change on either side fails the gate.
When a pin or a k-rust change moves one side, refresh that file from the retained gate artifacts (`REFERENCE_DIFFERENTIAL_KEEP_WORK=1`, `rust-implies.json` or `reference-booster-implies.json`, stored as `jq -c .`) only after reconciling the change with the entry's `reason`.
