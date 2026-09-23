# IMP expression fixture

This standalone Cargo package is the Rust-authored IMP expression slice that
`crates/krs-expand/tests/whole_file.rs` expands in
`corpus_matches_the_native_capture`. It deliberately uses only the explicit KRS
surface and a renamed dependency on the author-facing `krs` crate, and it is
not a member of the root workspace.

The object grammar contains exactly 19 productions:

- builtin `Int` and `Bool` injections into `Value`;
- `Value` injections into `KResult` and `Expr`;
- one same-sort `Expr` bracket; and
- fourteen expression operators.

The package also declares six precedence boundaries, six left-associativity
groups, exact strict/seqstrict field sequences, all 18 rewrite rules, and the
`$PGM:Expr` computation-cell initializer.

Check the ordinary Rust surface from the repository root with:

```bash
cargo +stable check --locked --offline --manifest-path crates/krs-expand/tests/fixtures/expr/Cargo.toml
cargo +stable clippy --locked --offline --manifest-path crates/krs-expand/tests/fixtures/expr/Cargo.toml --all-targets --no-deps -- -D warnings
```

The whole-file comparison itself is ignored by default; it runs with
`KRS_NATIVE_CAPTURE` naming a native capture that includes crate `m3a_expr`:

```bash
KRS_NATIVE_CAPTURE=/path/to/capture.jsonl \
  cargo +stable test -p krs-expand --test whole_file -- --ignored corpus_matches_the_native_capture
```
