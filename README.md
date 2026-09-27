# k-in-k2

k-in-k2 provides execution pattern matching and semantic mutation testing for K definitions.
It is built on k-rust,
which the workspace consumes as a path dependency.
The intended source is the on-disk checkout at `../inspirations/midnightntwrk/k-rust`, tracking k-rust main.
The workspace builds against a read-only snapshot of k-rust commit `74f1356e0331e4337cd0043acf59913388ab7978` at `../k-rust-74f1356e`,
exported with `git -C ../inspirations/midnightntwrk/k-rust archive 74f1356e0331e4337cd0043acf59913388ab7978 | tar -x -C ../k-rust-74f1356e`.
Moving back to the live checkout means changing the two paths in `Cargo.toml` `[workspace.dependencies]` and adapting to the new k-rust.
The work is intended to be merged into k-rust together with KRS.

## Crates

| Crate | Purpose |
|---|---|
| [`kink-pattern`](crates/kink-pattern) | Execution pattern plans evaluated over paths whose payloads are KORE patterns. |
| [`kink-patch`](crates/kink-patch) | Patches over a loaded k-rust `Definition`, mutation sites and candidate selection. |
| [`kink-native`](crates/kink-native) | Mutant validation and execution adapters over the k-rust backend, and the bridge to kink-pattern paths. |
| [`kink-campaign`](crates/kink-campaign) | Campaign runner, typed oracle comparison, mutant classification and scoring. |

## Upstream requests

Requests this project makes of k-rust and KRS are recorded in the ledgers under [`upstream/`](upstream/README.md).

## Gate

Every commit must pass:

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

This workspace build is the no-Z3 solver profile.
`kink-native` has a `z3` feature for the Z3 profile
(it enables k-rust `z3-inference` and k-rust-backend `z3`; no other crate enables it).
Z3 comes from the machine wrapper `with-z3-static-4.16.0`,
which points the `z3-sys` build at a static Z3 4.16.0 library;
without the wrapper a `z3` build fails to link (`-lz3` missing),
and nothing is downloaded at build time.
Run the Z3 gate for every Z3-profile change and before merge:

```sh
with-z3-static-4.16.0 cargo clippy -p kink-native --all-targets --features z3 -- -D warnings
with-z3-static-4.16.0 cargo test -p kink-native --features z3
```

## Retired tooling

The earlier official-K "G-track",
its TypeScript/Bun probes and the oracle were removed from the tree.
The local tag `archive/g-track-2026-08` marks the last commit that contains them.
