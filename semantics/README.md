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

Each gate pins the external checkout it is qualified against (revision, K release, and the digest of every cited source file), its corpus, and the outputs KRS produces: the expansion, emitted artifact, native KORE, and behavior digests, plus the normalized kompiled KORE digest under `--java-reference`.
It does not pin KRS source, and it reads K and schema versions from `Krs.lock`.
After an intended output change, run the gate with `--record` (and `--java-reference --record` for the kompiled digest); it rewrites only the output pins that run measured, and only when every step passes.
`--artifacts-only` runs preflight, the Rust checks, and repeated emission, compares every emitted artifact and the native KORE with its pin, and stops before the K-Rust behavior and Java reference comparisons with a PASS line that says they were skipped.
Use it for a change expected to leave every artifact byte-identical; any artifact difference fails and asks for the full gate, and it cannot be combined with `--record` or `--java-reference`.
Cargo targets and workspaces default to `/var/tmp`; `KRS_GATE_SCRATCH` moves them, and `KRS_<PORT>_ROOT_TARGET` or `KRS_<PORT>_FIXTURE_TARGET` moves one target.
