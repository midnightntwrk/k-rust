# IMP expression fixture

This standalone Cargo package defines a Rust-authored IMP expression slice.
It uses only the explicit KRS surface and a renamed dependency on the author-facing `krs` crate.
It is not a member of the root workspace.

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
