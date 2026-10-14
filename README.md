# k-in-k2

k-in-k2 provides execution pattern matching and semantic mutation testing for K definitions.
It is built on k-rust,
which the workspace consumes as a path dependency.
The intended source is the on-disk checkout at `../inspirations/midnightntwrk/k-rust`, tracking k-rust main.
The workspace builds against a read-only export of k-rust main commit `927b9ce6352357db340c221ff5377b294b8324e9` at `../k-rust-927b9ce6`,
exported with `git -C ../inspirations/midnightntwrk/k-rust archive 927b9ce6352357db340c221ff5377b294b8324e9 | tar -x -C ../k-rust-927b9ce6`.
That commit carries variable identity version 3: verbatim name reading, injective printing and request-unique free mints.
Moving back to the live checkout means changing the two paths in `Cargo.toml` `[workspace.dependencies]` and adapting to the new k-rust.
The work is intended to be merged into k-rust together with KRS.

## Crates

| Crate | Purpose |
|---|---|
| [`kink-pattern`](crates/kink-pattern) | Execution pattern plans evaluated over paths whose payloads are KORE patterns. |
| [`kink-patch`](crates/kink-patch) | Patches over a loaded k-rust `Definition`, mutation sites and candidate selection; SemanticInput artifacts, SHA-256 digests, sentence fingerprints that pin every patch, and the canonical patch codec. |
| [`kink-native`](crates/kink-native) | Mutant validation and execution adapters over the k-rust backend, and the bridge to kink-pattern paths. |
| [`kink-campaign`](crates/kink-campaign) | Campaign runner, typed oracle comparison, mutant classification and scoring; campaign manifests, deterministic JSON campaign reports and replay. |

## SemanticInput, manifests, reports and replay

A baseline's `SemanticInput` v1 is exactly k-rust's compact `KRUST-PROVENANCE` v7 document of the loaded definition and its source table; its digest is the SHA-256 of those bytes.
`SemanticInput::read` accepts only the canonical encoding and rebuilds the baseline without the `.k` sources.
A sentence fingerprint is a domain-separated SHA-256 of the sentence without source positions, provenance receipts or term metadata.
Candidate selection pins every patch to the fingerprints of the sentences it addresses, and `apply` refuses a stale pin as `StalePrecondition`, before any edit and so before compilation.
A fingerprint is a version check, not an identity: a sentence is identified by its module and index in one baseline.

A campaign manifest (`kink-campaign-manifest` v1) records the k-rust revision, the provenance format, the solver profile, the compile and backend options, the budget, the schedule, the operator id, version and policy, the baseline and per-mutant digests (SemanticInput, metadata-free structure, compiled KORE), the validation outcome of each mutant, and digests of the tests and the observation.
A campaign report (`kink-campaign-report` v1) embeds the manifest and adds the origins, each mutant's canonical patch, the affected sentences with old and new fingerprints, a normalized structural diff, the per-test oracle sides, the claims and the summary.
Both are canonical JSON with no wall-clock value and no absolute path, so repeated runs give identical bytes.

`replay` takes a report, the baseline artifact and the caller's declaration, including the selection code.
It checks the schema, the manifest digest, the build environment and the artifact digest, rebuilds every mutant from its canonical patch and checks its digests, then reruns selection and the campaign.
It returns `Reproduced` only when the regenerated report is byte-identical to the input; anything else is a refusal or a divergence, never a verdict.
Replay assumes the same kink build and operator code, no time bound firing in either run, and k-rust's provenance round trip and compilation determinism.

## Upstream requests

Requests this project makes of k-rust and KRS are recorded in the ledgers under [`upstream/`](upstream/README.md).

## Gate

Every commit must pass the per-commit gate, the no-Z3 workspace build and the Z3 profile:

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace --no-fail-fast
with-z3-static-4.16.0 cargo clippy -p kink-native -p kink-campaign -p kink-corpus --all-targets --features z3 -- -D warnings
with-z3-static-4.16.0 cargo test -p kink-native --features z3 --no-fail-fast
with-z3-static-4.16.0 cargo test -p kink-campaign --features z3 --no-fail-fast
with-z3-static-4.16.0 cargo test -p kink-corpus --features z3 --no-fail-fast
```

The milestone gate is the same commands with `-- --include-ignored` added to every `cargo test`.
It also runs the whole-fixture sweeps marked `#[ignore = "milestone"]`,
each of which has a smaller variant in the per-commit gate.
Run it before a merge and when a work package closes.
The external corpus measurements in `kink-corpus/tests/external.rs` are ignored for another reason;
under `--include-ignored` without `KINK_WORKSPACE` they only record a skip.

The workspace build is the no-Z3 solver profile.
`kink-native` has a `z3` feature for the Z3 profile
(it enables k-rust `z3-inference` and k-rust-backend `z3`).
`kink-campaign` and `kink-corpus` forward that feature as `z3`,
and `kink-campaign` requires its execution adapter's solver profile to match the build.
Their tests carry profile columns for outcomes that differ between no-Z3 and Z3.
Z3 comes from the machine wrapper `with-z3-static-4.16.0`,
which points the `z3-sys` build at a static Z3 4.16.0 library;
without the wrapper a `z3` build fails to link (`-lz3` missing),
and nothing is downloaded at build time.

Dependencies are built with `opt-level = 2` in the dev and test profiles (`Cargo.toml`),
because loading and compiling K definitions in k-rust dominates test time;
the workspace crates keep the plain dev profile with debug assertions and overflow checks.

## Retired tooling

The earlier official-K "G-track",
its TypeScript/Bun probes and the oracle were removed from the tree.
The local tag `archive/g-track-2026-08` marks the last commit that contains them.
