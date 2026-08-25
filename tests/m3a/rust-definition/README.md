# Explicit M3A Rust definition

This standalone Cargo package is the Rust-authored counterpart of
`../fixtures/expr.k`. It deliberately uses only the explicit KRS surface and a
renamed dependency on the author-facing `krs` crate.

The object grammar contains exactly 19 productions:

- builtin `Int` and `Bool` injections into `Value`;
- `Value` injections into `KResult` and `Expr`;
- one same-sort `Expr` bracket; and
- fourteen expression operators.

The package also declares the oracle's six precedence boundaries, six
left-associativity groups, exact strict/seqstrict field sequences, all 18
rewrite rules, and the `$PGM:Expr` computation-cell initializer.

Check the ordinary Rust surface with:

```bash
cargo check --locked --manifest-path tests/m3a/rust-definition/Cargo.toml
cargo clippy --locked --manifest-path tests/m3a/rust-definition/Cargo.toml --all-targets --no-deps -- -D warnings
```

Run the Rust-to-K acceptance path from the KRS repository root with:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/m3a/verify_rust_definition.py
```

That verifier owns K emission, reference compilation, parsing, and execution
checks. This source must not fall back to or copy the handwritten semantic
definition during collection.
