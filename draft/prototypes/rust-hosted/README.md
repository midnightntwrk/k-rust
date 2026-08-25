# Rust-hosted KRS architecture prototype

This disposable workspace supplies the executable evidence for
[R12](../../investigations/r12-rust-host-architecture.md). It is deliberately a
small descriptor model, not the first implementation of the complete KRS IR.

## Positive gates

From this directory:

```console
cargo check --workspace
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
cargo run -p semantics-app
cargo check -p semantics-app --target wasm32-unknown-unknown
cargo expand -p semantics-lib
python3 tools/lsp_probe.py
```

`semantics-app` collects root, nested-module, and dependency-crate descriptors,
checks the open-sort diamond, then sends structured sentences through the
portable `k-rust` frontend to reparsable KORE.

The LSP probe starts the installed rust-analyzer server and checks
go-to-definition through ordinary Rust, attribute inputs, refutable rule
inputs/bodies, and function-like macro payloads, plus ordinary completion.

## Expected failures

These fixtures are separate workspaces so their intentional errors do not
break the positive workspace:

```console
cargo check --manifest-path fixtures/invalid-rule/Cargo.toml
cargo check --manifest-path fixtures/coherence-diamond/Cargo.toml
```

The first must point at the wildcard rule pattern. The second must report
E0119 because blanket Rust impls for both paths of a subsort diamond overlap.

## Non-production mechanisms

`inventory` proves cross-crate host collection without rustc-private APIs; the
production design may instead generate an explicit collector. The native
adapter recognizes only the sample constructors/rule and retains R11's parsed
bootstrap configuration because `k-rust` v0.3 has no public structured
Definition preparation entry point.
