# k-in-k2

k-in-k2 provides execution pattern matching and semantic mutation testing for K definitions.
It is built on k-rust,
which the workspace consumes as a path dependency.
The intended source is the on-disk checkout at `../inspirations/midnightntwrk/k-rust`, tracking k-rust main.
The workspace builds against a read-only snapshot of k-rust commit `347f693e21ae220f1844005499da262f15ca3988` at `../k-rust-347f693e`,
exported with `git -C ../inspirations/midnightntwrk/k-rust archive 347f693e21ae220f1844005499da262f15ca3988 | tar -x -C ../k-rust-347f693e`.
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

## Retired tooling

The earlier official-K "G-track",
its TypeScript/Bun probes and the oracle were removed from the tree.
The local tag `archive/g-track-2026-08` marks the last commit that contains them.
