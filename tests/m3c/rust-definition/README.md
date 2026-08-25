# Explicit M3C Rust definition

This standalone Cargo package is the Rust-authored counterpart of
`../fixtures/imp.k` plus the inherited M3B expression and calculation theory.
It uses only the public dependency facade `k` and is ordinary rustc-valid
Rust.

The package carries forward the complete M3B surface, then adds exactly five
control-flow productions: `if` with and without `else`, deliberately
non-strict `while`, and nonempty/empty blocks. The else-bearing constructor is
`strict(1)` and `avoid`; the exact escaped-space format gap is documented
below. The six state rules preserve the oracle rewrites for branch selection,
no-else normalization, loop unfolding, and block sequencing/removal.

The inherited Rust grammar identifier `seq_stmt` denotes the oracle group
`seq-stmt`. Rust-valid function names are independent of K spelling: all six
control rules use explicit `#[k::rule(label = "...")]` metadata, including
the hyphenated branch labels and reserved K label `while`.

The exact else-bearing format contains K's `% ` escaped-space control. The
current structured-format parser rejects that control, so the constructor
uses an ordinary literal space at the same location and marks the exact source
gap inline. The minimal rejected exact attribute is:

```rust
#[k::constructor(
    sort = Stmt,
    syntax = "if ({condition}) {then_branch} else {else_branch}",
    format = "%1 %2%3%4% %5 %6 %7",
)]
```

It reports `` `%` must be followed by `%`, `n`, `i`, `d`, or a one-based item
position ``. This is the first remaining unsupported authored surface; it
affects exact unparse metadata, not the operational control-flow rules.

Production `emit-k` succeeds, pinned K 7.1.337 compiles the result, and all
eight accepted programs match the frozen rewrite counts and final maps. The
nested `_` branch patterns remain exact subject wildcards throughout lowering.

Check the authored package with:

```bash
cargo fmt --check --manifest-path tests/m3c/rust-definition/Cargo.toml
cargo check --locked --manifest-path tests/m3c/rust-definition/Cargo.toml
cargo clippy --locked --manifest-path tests/m3c/rust-definition/Cargo.toml --all-targets --no-deps -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --locked --manifest-path tests/m3c/rust-definition/Cargo.toml --no-deps
cargo test --locked --manifest-path tests/m3c/rust-definition/Cargo.toml
```

Exercise production lowering with:

```bash
cargo run --locked -p krs-cli --bin krs -- emit-k \
  --manifest-path tests/m3c/rust-definition/Cargo.toml \
  --package krs-m3c-rust-definition \
  --definition main \
  --output tests/m3c/rust-definition/target/krs/emitted
```

The authored source contains no handwritten-K or generated-artifact fallback.
