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
