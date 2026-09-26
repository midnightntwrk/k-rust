# M3D Rust-authored preflight

This directory stages the Rust-authored M3D surface without weakening it to
features implemented by the current facade.

The root package is intentionally cargo-green. Its crate root, `src/m3c.rs`,
is a byte-identical copy of the closed M3C authored definition. Keeping that
baseline buildable distinguishes regressions in the existing facade from the
new M3D compiler work.

The nested `surface` package is intentionally compile-fail. It repeats the
M3C baseline as a module and adds the intended function/equation, alias,
context-alias, selected-context strictness, simplification, and reachability
claim declarations. These declarations are neither configuration-disabled nor
replaced by handwritten K. The first current diagnostic is at `add_one`:
because the absent `k::equation` collector does not consume its `term!` subject,
the ordinary term placeholder reaches rustc in pattern position and reports
`this macro call doesn't expand to a pattern`. The facade also has no public
`function`, `alias`, `context_alias`, `simplification`, or `claim` macro.

`AUTHORED-SURFACE.md` is the sentence and binder ledger. It records which
oracle forms are represented in Rust, which exact notation remains unsettled,
and the compiler schema/lowering work requested by this preflight.

Check the green baseline with:

```bash
cargo fmt --check --manifest-path tests/m3d/rust-definition/Cargo.toml
cargo check --locked --manifest-path tests/m3d/rust-definition/Cargo.toml
cargo clippy --locked --manifest-path tests/m3d/rust-definition/Cargo.toml --all-targets --no-deps -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --locked --manifest-path tests/m3d/rust-definition/Cargo.toml --no-deps
cargo test --locked --manifest-path tests/m3d/rust-definition/Cargo.toml
```

Check the authored frontier with:

```bash
cargo fmt --check --manifest-path tests/m3d/rust-definition/surface/Cargo.toml
cargo check --locked --manifest-path tests/m3d/rust-definition/surface/Cargo.toml
```

The second command must fail until the M3D sentence kinds are implemented; a
successful check would mean the frontier needs to be re-audited and advanced.
