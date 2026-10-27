# Native claim qualification

This package exercises the native claims workflow through ordinary KRS source and `krs prove`.
Its continuation cases cover a currently false target, partial target coverage, a symbolic nonnegative countdown, a two-state infinite cycle, and a finite terminal violation.

From the repository root, with `krs` built by `cargo build -p krs-cli`:

```console
target/debug/krs prove --manifest-path krs/tests/native-claims/Cargo.toml \
  --package krs-native-claims --definition main \
  --spec-module NATIVE-CONTINUATION-SPEC \
  --claim later-target --claim partially-covered --claim countdown --claim cycle \
  --depth 5 --output json
```

Each selected claim must report `proven`.
The cycle proof uses guarded self-circularity after semantic progress; the cycle never reaches its destination.
The result establishes weak partial correctness and does not certify termination or finite reachability.
The same command with only `--claim terminal-false` must report `disproved` and exit 1.
The backend/API tests additionally check a concrete countdown without circularities, a cycle without circularities, and depth-zero rejection of an unguarded self-circularity.

The primitive portfolio uses mathematical results for repeated bit operands and separate write/read machine transitions over a symbolic map.
`store-load`, `distinct-store-load` and `overwrite` preserve the map frame; the distinct-key claim explicitly requires an existing read at the other key and key inequality.

```console
target/debug/krs prove --manifest-path krs/tests/native-claims/Cargo.toml \
  --package krs-native-claims --definition main \
  --spec-module NATIVE-PRIMITIVE-SPEC \
  --claim and-self --claim xor-self --claim store-load \
  --claim distinct-store-load --claim overwrite --depth 5 --output json
```

Each selected claim must report `proven`.
`--claim wrong-value` must not prove.
The backend tests separately check partial discarded values, typed injections, unknown aliases, scoped facts and nonfunctional/effectful operands.

The JSON leaf of `cycle` must retain its `claim_steps`, showing the applied guarded circularity.
The concrete wrong-value leaf has `certified: true`; the unresolved symbolic wrong-value leaf has no certified marker.
`trusted_claims` lists available trusted reachability assumptions when any exist, separately from the actual claim steps.
No portfolio claim in these two native qualification packages relies on a trusted claim.

`empty-antecedent` is a separate vacuity control with contradictory preconditions.
It must report `proven` with `vacuous: true`; it is not counted as a productive portfolio proof.
A vacuity marker describes the proof's basis and does not assert that every displayed predecessor state is empty.
