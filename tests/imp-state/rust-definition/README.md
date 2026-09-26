# Explicit IMP state Rust definition

This standalone Cargo package is the Rust-authored counterpart of
`../fixtures/expr.k` plus `../fixtures/calc.k`. It uses only the public `k`
facade and remains ordinary rustc-valid Rust.

The package carries forward all 19 IMP expression productions and all 18
expression rules. Its calculation layer adds the post-hoc `Id` injection into
`Expr`, strict assignment, right-associative statement sequencing, and the
`stmt > seq-stmt` priority boundary. `Machine` declares the oracle's green
`k` cell and yellow `env` cell, initialized from `$PGM:Stmt` and `$ENV:Map`.
The Rust grammar identifier `seq_stmt` denotes the oracle's `seq-stmt` group;
KRS grammar-group authoring is intentionally identifier-shaped and the
emitter owns the concrete K group label.

The configuration rules deliberately use the configuration-rule signature:
term bindings are ordinary typed parameters in subject first-occurrence order,
followed by one final `k::cells!` parameter. K-sequence, map, and whole-machine
frames remain structural bindings. The Rust function names `step`, `var`, and
`assign` are the exact emitted K rule labels.

Check the standalone authored package with:

```bash
cargo fmt --check --manifest-path tests/imp-state/rust-definition/Cargo.toml
cargo check --locked --manifest-path tests/imp-state/rust-definition/Cargo.toml
cargo clippy --locked --manifest-path tests/imp-state/rust-definition/Cargo.toml --all-targets --no-deps -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --locked --manifest-path tests/imp-state/rust-definition/Cargo.toml --no-deps
```

Exercise production collection and K lowering from the repository root with:

```bash
cargo run --locked -p krs-cli --bin krs -- emit-k \
  --manifest-path tests/imp-state/rust-definition/Cargo.toml \
  --package krs-imp-state-rust-definition \
  --definition main \
  --output tests/imp-state/rust-definition/target/krs/emitted
```

The authored source contains no handwritten-K or generated-artifact fallback.
