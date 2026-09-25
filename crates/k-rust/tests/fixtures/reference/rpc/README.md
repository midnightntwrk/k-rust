# RPC reference fixtures

These cases pin JSON-RPC responses produced by the shipped `kore-rpc-booster` proxy.

Each entry under `rpc.oracle-exception` in `scripts/reference-differential.toml` has two files here: `<case>-<response>.json`, the k-rust response, and `<case>-<response>.reference.json`, the pinned `kore-rpc-booster` response to the same request.

- `imp-implies`: the `imp` case's `implies` request (identical antecedent and consequent).
- `bounded-search-implies-consequent-universal`: an `implies` request whose consequent has a free variable the antecedent does not mention; k-rust answers `invalid`, the reference answers error code 4 ([RPC behavior](../../../../../../docs/compatibility.md#rpc-behavior)).

The RPC gate (normalisation N19) compares each side against its own file and requires the two files to differ, so a change on either side fails the gate.
When a pin or a k-rust change moves one side, refresh that file from the retained gate artifacts (`REFERENCE_DIFFERENTIAL_KEEP_WORK=1`, `rust-<response>.json` or `reference-booster-<response>.json`, stored as `jq -c .`) only after reconciling the change with the entry's `reason`.
