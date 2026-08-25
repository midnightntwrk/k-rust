# M3D native Claim proof harness

The executable prototype is:

```bash
PYTHONDONTWRITEBYTECODE=1 \
  python3 draft/investigations/m3d-claim-proof-harness/verify.py
```

It proves the three pinned bridge cases and checks their frozen hashes. Source
specification parsing and native execution deliberately use different
`*-kompiled` directories.

For production KRS output, first ask the claim fixture for both artifacts:

```bash
KRS_CLAIM_K_OUT=/tmp/krs-m3d-claims.k \
KRS_CLAIM_KORE_OUT=/tmp/krs-m3d-claims.kore \
CARGO_TARGET_DIR=/dev/shm/krs-m3d-target \
  cargo run --locked \
  --manifest-path tests/m3d/rust-definition/claim-slice/Cargo.toml
```

Then run:

```bash
PYTHONDONTWRITEBYTECODE=1 \
CARGO_TARGET_DIR=/dev/shm/krs-m3d-target \
  python3 draft/investigations/m3d-claim-proof-harness/harness.py \
  --native-kore /tmp/krs-m3d-claims.kore \
  --execution-shell-source /tmp/krs-m3d-claims.k \
  --semantic-module KRS-M3D-CLAIM-SLICE \
  --syntax-module KRS-M3D-CLAIM-SLICE \
  --workspace /tmp/krs-m3d-native-proof
```

The strict default compares normalized source and native claims. During the
bounded M3-to-M4 symbol-identity transition,
`--allow-unmapped-claim-structure` defers only that comparison; native KORE is
still split, validated, executed directly, required to return exact `#Top`,
and checked against the frozen source-claim hashes.

See `REPORT.md` for the artifact flow and invariants.
