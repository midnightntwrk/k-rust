# k-in-k2

k-in-k2 provides execution pattern matching and semantic mutation testing for K definitions.
It is built on k-rust,
which `kink-native` consumes as a path dependency on the on-disk checkout at `../inspirations/midnightntwrk/k-rust`.
The work is intended to be merged into k-rust together with KRS.

## Crates

| Crate | Purpose |
|---|---|
| [`kink-pattern`](crates/kink-pattern) | Execution pattern matching over traces. |
| [`kink-patch`](crates/kink-patch) | Mutation patch application. |
| [`kink-native`](crates/kink-native) | Adapter over the k-rust backend. |
| [`kink-campaign`](crates/kink-campaign) | Mutant classification, scoring and oracle comparison. |
| [`kink-portable`](crates/kink-portable) | Legacy portable K encoding, pending migration to k-rust types. |

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
