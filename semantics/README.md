# KRS semantics workspace

This workspace contains the canonical KRS-owned ports of KWasm, KEVM, and KMIR.
The definitions are reusable semantics packages; `tests/kwasm`, `tests/kevm`, and `tests/kmir` contain their pinned external acceptance gates and must not own a second copy of the semantics.

The ports are incremental and are not yet complete.
Their current coverage and remaining source shapes are recorded in `coverage.toml`.
A port may be described as complete only after its ledger covers the pinned source definition's syntax, configuration, executable rules, and selected upstream behavior and proof suites without an unrecorded adapter boundary.

The external Runtime Verification checkouts remain read-only authorities:

- KWasm: `../../inspirations/runtimeverification/wasm-semantics` at `212271bd434bd402e27c42f6416854342733386d`;
- KEVM: `../../inspirations/runtimeverification/evm-semantics` at `d818397e9b7ffa213d687e64418dc8f5293e1ce2`;
- KMIR: `../../inspirations/runtimeverification/mir-semantics` at `4d793252bcd77091ee759ca6cd1629db41ed5496`.

KRS qualifies all three packages under K 7.1.337.
The KEVM and KMIR authorities use the same release; the pinned KWasm authority uses K 7.1.329.

Run the product workspace with:

```text
cargo check --manifest-path semantics/Cargo.toml --locked --offline --workspace
cargo test --manifest-path semantics/Cargo.toml --locked --offline --workspace
```

Run the semantic acceptance gates from the repository root:

```text
python3 tests/kwasm/verify.py
python3 tests/kevm/verify.py
python3 tests/kmir/verify.py
```
