# KRS CLI external acceptance oracle

This directory tests the installed behavior of the real `krs` executable. The
oracle never imports or calls `krs-cli` library APIs. Its authored fixture is a
normal standalone Cargo semantics package materialized from
`fixtures/foo-bar/Cargo.toml.in`; only the absolute local path dependency on the KRS
facade is substituted. That build-only path is deliberately absent from every
accepted artifact.

Run from the repository root:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/cli/verify.py
```

The verifier builds the `krs` binary, then performs two clean runs from
different absolute paths. Each run checks all four commands against the same
`foo -> bar` theory:

- `check` validates exactly nine descriptors and one semantic module;
- `expand` produces canonical, deterministic layer-2 Rust source with three sorts, two constructors, one combined configuration, and one rule;
- `emit-k` creates the schema marker, the three IR/bundle documents, `definition.k`, `symbols.json`, and `sources.json`, and retains `ObjectTerm < KResult < KItem`, `<k> foo </k>`, and the `foo => bar` rule;
- `build` compiles the Definition IR through the structured k-rust frontend and creates exactly `.krs-artifacts`, `definition.kore`, `syntaxDefinition.kore`, and `macros.kore`.

Relocated outputs must be byte-identical and match `pins.json`. These pins are
independent of the in-tree minimal-definition oracle: this package intentionally has its own
stable Cargo name, K namespace, and source layout, all of which participate in
KRS identities. The verifier also rejects absolute paths, pointer-like values,
`TypeId`, `Self`, and Rust configuration-wrapper spellings in stable output.

Negative cases cover omitted and nonexistent facets, ambiguous Cargo package
names, an authored Cargo-check failure, and preservation of an unowned
nonempty artifact directory. If both `kompile` and `krun` are present at the
K version `Krs.lock` pins, the emitted K is compiled with the LLVM backend and
executed to prove `foo -> bar`. Missing tools are reported as unavailable;
present tools at a different version are a hard mismatch and are never used.

`pins.json` pins the fixture (an input, edited deliberately) and the artifact
digests (outputs). After an intended output change, re-record the artifact
digests by running the oracle:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/cli/verify.py --record
```

It rewrites `artifacts_sha256` only when every other check passes.
