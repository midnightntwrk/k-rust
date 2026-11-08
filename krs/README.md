# KRS

KRS is a Rust-shaped language for authoring [K Framework](https://kframework.org/) semantic definitions.
A reader who knows Rust should be able to form a mostly correct mental model of a semantics without first learning K's surface language, while the definition keeps the capabilities that real K projects need.

KRS is a language for semantics authors.
It does not give ordinary Rust programs K semantics, and it is not a new rewrite engine.

A KRS definition is an ordinary Cargo crate that depends on the `krs` facade, conventionally renamed to `k`.
Its declarations are rustc-valid Rust; K-specific patterns and logic live in explicit macro islands such as `k::rules!`.
The `krs` command collects the crate's descriptors, resolves one Semantic IR and one Definition IR, and then either emits inspectable `.k` files or lowers the Definition IR natively to KORE through the `k-rust` frontend, whose crates are the rest of this repository (`../crates/`).
`krs expand` projects the readable (layer-1) surface to a deterministic, explicit (layer-2) Rust reference surface, and `krs fmt` is the canonical formatter for both.

`krs parse`, `run`, `search`, and `prove` play the roles of K's `kast`, `krun`, `krun --search`, and `kprove`: they compile the same Definition IR through `krs-exec` and the `k-rust` symbolic backend linked into krs (`prove` in a child krs process, so that a crash costs one claim), and `--output json` prints a `krs-exec` report (`krs-exec/7` for `run`, `krs-exec/1` for `search`, `krs-exec/2` for `prove`).
`krs cases` runs a batch of case documents, each case checked against its expectation as `krs run --case` checks one, with the definition loaded once per worker (each worker holds its own copy, so memory grows with `--jobs`); `--output json` prints one `krs-cases/4` record per case and a summary.
`krs compare` compares two ends of the definition, each an end document or the end of a case's run, or checks one against a case's expectation, and prints `equal` or the first difference (`--output json`: a `krs-compare/1` document).
`krs kink` runs kink's corpus loop over the package's corpus (`kink/` beside its `Cargo.toml`): the rules each case covers, the mutations of the emitted K that no case kills, patterns of interest and fuzzing; the docs-site guide "Mutation testing a KRS specification" (`../docs-site/src/pages/verification/mutation-testing.mdx`) teaches it, and `krs kink --help` lists its verbs and options.
The [native local-contract boundary](../docs/compatibility.md#native-local-state-transition-contracts) describes the supported symbolic state/helper laws, typed observation and domain premises, exhaustive input cases, weak partial correctness and unresolved proof limits.

`krs check`, `expand`, `emit-k`, `build`, and the run commands render human-readable diagnostics on stderr by default, with diagnostic codes, notes, help, and authored source snippets when the source revision matches.
Pass `--message-format=json` for machine consumption: every diagnostic is a schema-2 JSON envelope line, with a `null` authored range when no authored text is its subject; only failures without a code (a usage error, a crashed collector) are prose lines.

## Current state

- **Complete IMP.** The IMP gate (`tests/imp/`) compiles one complete Rust-authored IMP package through both the emitted-`.k` route and the native `k-rust` route.
  It compares both routes against the upstream IMP definition for source structure, parsing, concrete execution, search, and bounded proof outcomes of all 15 upstream IMP claims plus five adjunct claims.
- **Language-scale ports.** Incremental KWasm, KEVM, and KMIR ports live in `semantics/`.
  None is complete; `semantics/coverage.toml` records what each covers, what is deferred, and every adapter boundary.
  Their gates execute 32 (KWasm), 240 (KEVM), and 184 (KMIR) pinned cases natively through `k-rust`.
- **Toolchain pins.** `Krs.lock` pins K 7.1.337, the Z3 release krs links (5.3.3) and the one beside the reference K tools (4.12.5), and the IR schema versions; every gate reads them from there.
  KRS builds against the `k-rust` crates of the same commit, so there is no `k-rust` pin to move: a `k-rust` change that affects KRS updates KRS in the same commit.
  The MSRV is Rust 1.99.0, the `rust-version` every `k-rust` crate declares; the gates also qualify native-frontend helpers on any stable Rust at or above it.
- **Documentation.** The repository's Vocs site, `../docs-site/`, publishes the language tour and documents k-rust as well; its curriculum ledger is `../docs-site/plan/tour.toml`.
  `docs-plan/authoring-spec/` is the normative readable-authoring specification.
- **Browser lessons.** `browser/` contains a Web Worker that expands and compiles lessons in the browser, together with its dependency pack and release tooling.

## Repository layout

| Path | Contents |
|---|---|
| `crates/krs` | Author-facing facade (`k::sorts!`, `k::rules!`, attributes, builtins) |
| `crates/krs-macros`, `crates/krs-expand`, `crates/krs-syntax` | Procedural macros, the shared expansion core, and span-preserving parsers for macro islands |
| `crates/krs-collector` | Deterministic host descriptor collection |
| `crates/krs-compiler`, `crates/krs-ir`, `crates/krs-ir-levels` | Semantic analysis, `.k` emission, descriptor contracts, and the Semantic and Definition IR levels |
| `crates/krs-diagnostic` | Located diagnostic model and code registry shared by producers |
| `crates/krs-k-rust` | Adapter from Definition IR to the `k-rust` frontend |
| `crates/krs-exec` | Filesystem-free parse, run, search, and prove over Definition IR through the `k-rust` backend |
| `crates/krs-cli` | The `krs` command: `check`, `expand`, `emit-k`, `build`, `parse`, `run`, `search`, `cases`, `compare`, `prove`, and `fmt` |
| `crates/krs-fmt` | Canonical formatter |
| `crates/krs-expand-wasm`, `crates/krs-lesson-policy`, `crates/krs-wasm-abi` | Browser-lesson expander, editable-surface policy, and their shared Wasm ABI |
| `semantics/` | Separate Cargo workspace with the KWasm, KEVM, and KMIR ports and `coverage.toml` |
| `tests/` | IMP reference oracles, the complete IMP and precedence/associativity gates, CLI, port, tour, browser, and repository hygiene gates |
| `docs-plan/` | Tour curriculum and authoring specification; the tour itself is in the repository's `../docs-site/` |
| `browser/` | Browser-lesson worker, dependency pack, and release format |
| `Krs.lock` | External toolchain and schema pins |

## Building and testing

### Prerequisites

- Rust 1.99.0 and a current stable toolchain with Clippy and rustfmt.
  KRS has no `rust-toolchain.toml`, so pass `+stable` or `+1.99.0` explicitly.
- Z3 5.3.3, the release `Krs.lock` `[solver] linked` names, in its published build.
  Whether a query bounded by Z3's resources is decided depends on the Z3 build, so KRS's and `k-rust`'s tests and the solve budgets measured with them hold for that build; `cargo test -p krs-cli --test z3_version` fails a build that links another release, though it cannot tell two builds of one release apart.
  The default features of `krs-cli`, `krs-exec`, `krs-k-rust` and `krs-gate` (`z3-inference-gh-release`) download that build from Z3's GitHub releases at build time and link it statically, so a default build needs nothing more, whether it builds KRS's crates alone or the whole workspace.
  The download is `z3-sys`'s build script, which runs again for each new build-script output directory (a new target directory, profile or feature set) and which `--offline` does not stop, so an offline build takes the environment route.
  To link a Z3 5.3.3 the build environment provides instead (the environment route), build with `--no-default-features --features z3-inference` (`z3-inference,kink` for `krs-cli`), which `z3-sys` finds through a `pkg-config` file for it (`PKG_CONFIG_PATH`, with `Z3_STATIC=1` for a static archive), through `Z3_LIBRARY_PATH_OVERRIDE`, or on the link path.
  The Python gates, `scripts/krs-class.sh`, the browser parity scripts and the krs benchmark take the route from `KRUST_GATE_Z3`, as the repository's other gates do.
  Unset or `gh-release` is the default build, which needs no Z3 on the machine.
  `system` builds with `z3-inference`, linked to the directory `KRS_Z3_LIB` names, which may hold `libz3.so` or `libz3.a` (the linker takes the archive when no shared library is beside it); with `KRS_Z3_LIB` unset, the Python gates and `scripts/krs-class.sh` look for a `*-z3-static-5.3.3/lib` and then a `*-z3-5.3.3-lib/lib` directory under `KRS_NIX_STORE` (default `/nix/store`) and put the one they find first on the link and load paths.
  The Python gates require that library to report the linked release before they build, and each `krs` and `krs-gate` they build to link it afterwards, and `scripts/krs-class.sh` runs the `z3_version` test of the build it judges with, so another release fails on either route.
  The IMP gate's artifact probe takes `z3-inference` alone, so it needs that library on both routes.
  On a machine that holds the published build as a static archive, such as a Nix store's `z3-static-5.3.3`, `KRUST_GATE_Z3=system` with `KRS_Z3_LIB` unset, or naming that archive's directory, builds every gate's `krs` without a download.
  A Cargo command on the environment route outside the gates needs the paths exported:

  ```sh
  export LIBRARY_PATH=$KRS_Z3_LIB${LIBRARY_PATH:+:$LIBRARY_PATH}
  export LD_LIBRARY_PATH=$KRS_Z3_LIB${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
  ```

  The IMP gate requires the `z3` beside the K tools to be the release `[solver] reference` names, 4.12.5; krs does not link it.

- The pinned reference checkouts, in a directory named `inspirations/`, at the revisions that `Krs.lock`, `semantics/README.md`, and each gate's pins name.
  The gates look for it in the nearest ancestor of `krs/` that holds `inspirations/runtimeverification`, or under the directory `KRS_EXTERNAL_ROOT` names, and fail closed on a revision mismatch or a dirty checkout.
  - `inspirations/runtimeverification/{wasm-semantics,evm-semantics,mir-semantics,imp-semantics}` (port and IMP authorities);
  - `inspirations/runtimeverification/k` (K 7.1.337, for gates that need the K toolchain).
- K 7.1.337 (`kompile`, `krun`, `kprove`, `kore-exec`, `llvm-kompile`) on `PATH`, or in the directory `KRS_K_BIN` names, for the Java reference runs and every reference-cache miss.
  The complete IMP, IMP state, IMP control flow, IMP static semantics, precedence/associativity, and CLI gates replay K results from the per-user reference cache and need no K tool once it holds them.
  The KWasm, KEVM, and KMIR gates need it only with `--java-reference`.

### Workspace

KRS's crates (`crates/*`) are members of the repository's Cargo workspace, beside `k-rust`'s, so `cargo test --workspace`, `cargo clippy --workspace`, and the repository's CI build and test KRS with every `k-rust` change.
To run KRS's crates alone:

```sh
cargo +stable test -p 'krs*' --locked --offline
cargo +stable clippy -p 'krs*' --all-targets --locked --offline -- -D warnings
cargo +1.99.0 check -p 'krs*' --all-targets --locked --offline
cargo +stable test --manifest-path semantics/Cargo.toml --locked --offline --workspace
```

A workspace-wide build and `-p 'krs*'` select the same Z3, the downloaded release.
On the environment route, select one crate that links Z3 at a time, for example `cargo +stable test -p krs-cli --no-default-features --features z3-inference,kink --locked`, since `--no-default-features` over `-p 'krs*'` also turns off the default features of KRS's crates that do not link Z3.

Set `UPDATE_EXPECT=1` for a workspace test run to re-record Rust test snapshots after an intended output change.
Review the resulting golden files and inline expectations before running the tests again without it.

### Gates

Run every gate from the repository root with `PYTHONDONTWRITEBYTECODE=1 python3 tests/<gate>/verify.py`.
The KWasm, KEVM, KMIR, and IMP gates are memory heavy: run several at once only when the available memory has room for them.
`tests/imp/README.md` gives the memory-bounded recipe for IMP; other gate-specific instructions live in each gate directory's README where one exists.
`tests/gates.sh light` runs every gate but the browser and heavy ones (`../docs/testing.md`, "KRS").
Those gates build their tools, the packages they check, and the collectors `krs` generates for them in one Cargo target, the repository's `target/`, which `KRS_TOOL_TARGET` or `CARGO_TARGET_DIR` moves; the heavy gates keep their own targets under the scratch directory.
The gates format-check the standalone test packages, and `tests/gates.sh lint`, which CI runs, lints them with Clippy and checks them on the MSRV.

A gate pins what it does not control and what KRS produces, never KRS source:

- inputs: the revisions and file digests of the sibling checkouts, the toolchain and schema versions in `Krs.lock`, and the gate's corpus;
- outputs: emitted artifact, KORE, and behavior digests.

A source change that leaves every output identical passes without a pin edit.
When an output changes on purpose, re-record it by running the gate with `--record` (the KWasm, KEVM, KMIR, IMP, IMP state, IMP control flow, IMP static semantics, precedence/associativity, and CLI gates support it); the gate runs completely and, only if every step passes, rewrites exactly the output pins it measured.
Review the resulting pin diff like any other change.
`--record` never rewrites an input pin: a new checkout revision, corpus, or toolchain is a deliberate edit to the gate ledger or `Krs.lock`.
The shared pin handling lives in `tests/support`, whose unit tests run with `python3 -m unittest discover support` from `tests/`.

The repository hygiene check fails if any tracked file references one of the retired root tracking ledgers or cites a local ticket id; the repository's `scripts/repo_hygiene.py` refuses references to the local scratchpads:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tests/repo-hygiene/verify.py
```

### Reference K results

Java K 7.1.337 results are a deterministic function of the pinned K release, the upstream revisions, and the inputs, so the gates keep them in a cache instead of the repository.
The complete IMP, IMP state, IMP control flow, IMP static semantics, precedence/associativity, and CLI gates group their Java K invocations into reference snapshots (`tests/support/reference.py`).
A snapshot stores only the reduced evidence its comparators read, never a whole kompiled directory; its `manifest.toml` holds its key and the digest of every stored file.
The key covers the `Krs.lock` K version, the K tools, the argument vector of each invocation, the upstream revisions, and the digest of every input file, including any KRS-emitted `.k` file a tool reads.

Each gate pins the SHA-256 of every snapshot manifest in the `reference_sha256` table of its ledger, and a per-user cache stores the snapshot under that digest,
in `${XDG_CACHE_HOME:-~/.cache}/krs/reference-outputs/v1` or the directory `KRS_REFERENCE_CACHE_DIR` names, which must lie outside the repository.
An entry unused for `KRS_REFERENCE_CACHE_MAX_UNUSED_DAYS` (default 30) days is deleted.

- A gate replays a valid cache entry and then needs no K tool.
- On a miss (an empty cache or an entry that fails validation) it runs the pinned K tools live; a missing K tool fails closed and names `PATH` and `KRS_K_BIN`.
  The live result must reproduce the pinned digest, so a different or nondeterministic K installation fails instead of replacing the evidence, and it is stored only after every step of the gate passed.
- A cached entry whose key or invocations differ from what the gate runs fails closed.
  After an intended change to a reference input, such as what KRS emits, run the gate with `--refresh-reference --record` and the pinned K tools.
- A change to an input that leaves its meaning alone, such as a comment of an emitted `.k` file, is still a new key, and the new snapshot need not be the old one's bytes:
  Java K's KORE may list the competitors of an `owise` equation, the disjuncts its negated condition names, in another order (seen on the patterns-functions gate's `bits` and `sugar` after a comment-only edit).
  Its `reference_sha256` then moves on `--refresh-reference --record`, which is expected.
  The comparison does not move: `krs-gate kore-compare` flattens each such negated disjunction and orders its disjuncts by shape before comparing (`canonicalize_owise_competitors` in `crates/krs-gate/src/kore_compare.rs`, pinned by its `owise_competitor_order_is_normalized` test), so a pass rests on no disjunct order.

`--refresh-reference` runs Java K live whatever the cache holds; `--record` rewrites output pins, including `reference_sha256`.
CI runs none of these gates, so it needs neither K nor the cache.
`tests/imp/README.md` lists the IMP snapshots and the cost of a cold cache.

### Documentation site

```sh
bun install --cwd ../docs-site --frozen-lockfile
bun run --cwd ../docs-site build
```

The build runs the tour verifiers and several `cargo check` invocations; on the environment route it needs the Z3 exports above.

## License

KRS (everything under `krs/`) is licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT) at your option.
The rest of the repository, `k-rust`, is licensed the same way, except for the third-party material `../NOTICE` lists.
