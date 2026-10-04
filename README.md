# KRS

KRS is a Rust-shaped language for authoring [K Framework](https://kframework.org/) semantic definitions.
A reader who knows Rust should be able to form a mostly correct mental model of a semantics without first learning K's surface language, while the definition keeps the capabilities that real K projects need.

KRS is a language for semantics authors.
It does not give ordinary Rust programs K semantics, and it is not a new rewrite engine.

A KRS definition is an ordinary Cargo crate that depends on the `krs` facade, conventionally renamed to `k`.
Its declarations are rustc-valid Rust; K-specific patterns and logic live in explicit macro islands such as `k::rules!`.
The `krs` command collects the crate's descriptors, resolves one Semantic IR and one Definition IR, and then either emits inspectable `.k` files or lowers the Definition IR natively through the pinned [`k-rust`](https://github.com/midnightntwrk/k-rust) frontend to KORE.
`krs expand` projects the readable (layer-1) surface to a deterministic, explicit (layer-2) Rust reference surface, and `krs fmt` is the canonical formatter for both.

`krs check`, `expand`, `emit-k`, and `build` render human-readable diagnostics on stderr by default, with diagnostic codes, notes, and authored source snippets when the source revision matches.
Pass `--message-format=json` for machine consumption: located diagnostics use schema-1 JSON envelope lines, while unlocated diagnostics and other failures retain prose lines.

## Current state

- **Complete IMP.** The IMP gate (`tests/imp/`) compiles one complete Rust-authored IMP package through both the emitted-`.k` route and the native `k-rust` route.
  It compares both routes against the upstream IMP definition for source structure, parsing, concrete execution, search, and bounded proof outcomes of all 15 upstream IMP claims plus five adjunct claims.
- **Language-scale ports.** Incremental KWasm, KEVM, and KMIR ports live in `semantics/`.
  None is complete; `semantics/coverage.toml` records what each covers, what is deferred, and every adapter boundary.
  Their gates execute 32 (KWasm), 240 (KEVM), and 184 (KMIR) pinned cases natively through `k-rust`.
- **Toolchain pins.** `Krs.lock` pins K 7.1.337, the `k-rust` frontend commit, Z3 4.12.5, and the IR schema versions; every gate reads them from there.
  The workspace MSRV is Rust 1.88.0; the gates also qualify native-frontend helpers on any stable Rust at or above it.
- **Documentation.** `docs-plan/tour.toml` is the curriculum and feature-status ledger for a 17-chapter language tour, published by the Vocs site in `docs-site/`.
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
| `crates/krs-k-rust` | Adapter from Definition IR to the pinned `k-rust` frontend |
| `crates/krs-cli` | The `krs` command: `check`, `expand`, `emit-k`, `build`, and `fmt` |
| `crates/krs-fmt` | Canonical formatter |
| `crates/krs-expand-wasm`, `crates/krs-lesson-policy`, `crates/krs-wasm-abi` | Browser-lesson expander, editable-surface policy, and their shared Wasm ABI |
| `semantics/` | Separate Cargo workspace with the KWasm, KEVM, and KMIR ports and `coverage.toml` |
| `tests/` | IMP reference oracles, the complete IMP and precedence/associativity gates, CLI, port, tour, browser, and repository hygiene gates |
| `docs-plan/`, `docs-site/` | Tour curriculum, authoring specification, and the Vocs documentation site |
| `browser/` | Browser-lesson worker, dependency pack, and release format |
| `Krs.lock` | External toolchain and schema pins |

## Building and testing

### Prerequisites

- Rust 1.88.0 and a current stable toolchain with Clippy and rustfmt.
  The repository has no `rust-toolchain.toml`, so pass `+stable` or `+1.88.0` explicitly.
- The Z3 4.12.5 shared library on the link and load paths.
  `krs-k-rust` builds `k-rust` with the `z3-inference` feature and does not download a solver.
  Set `KRS_Z3_LIB` to the directory that contains `libz3.so`; the Python gates prepend it to both paths themselves, but Cargo needs it exported:

  ```sh
  export LIBRARY_PATH=$KRS_Z3_LIB${LIBRARY_PATH:+:$LIBRARY_PATH}
  export LD_LIBRARY_PATH=$KRS_Z3_LIB${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
  ```

- Pinned sibling checkouts, relative to the repository root, at the revisions that `Krs.lock`, `semantics/README.md`, and each gate's pins name.
  The gates fail closed on a revision mismatch or a dirty checkout.
  - `../inspirations/midnightntwrk/k-rust-krs-main` (`k-rust`, a Cargo path dependency of `krs-k-rust`);
  - `../inspirations/runtimeverification/{wasm-semantics,evm-semantics,mir-semantics,imp-semantics}` (port and IMP authorities);
  - `../inspirations/runtimeverification/k` (K 7.1.337, for gates that need the K toolchain).
- K 7.1.337 (`kompile`, `krun`, `kprove`, `kore-exec`, `llvm-kompile`) on `PATH` for the IMP reference oracles, the complete IMP gate, and the Java reference runs.
  The KWasm, KEVM, and KMIR gates need it only with `--java-reference`.

### Workspace

```sh
cargo +stable test --workspace --locked --offline
cargo +stable clippy --workspace --all-targets --locked --offline -- -D warnings
cargo +1.88.0 check --workspace --all-targets --locked --offline
cargo +stable test --manifest-path semantics/Cargo.toml --locked --offline --workspace
```

Set `UPDATE_EXPECT=1` for a workspace test run to re-record Rust test snapshots after an intended output change.
Review the resulting golden files and inline expectations before running the tests again without it.

### Gates

Run every gate from the repository root with `PYTHONDONTWRITEBYTECODE=1 python3 tests/<gate>/verify.py`.
The KWasm, KEVM, KMIR, and IMP gates are memory heavy and must run one at a time.
`tests/imp/README.md` gives the memory-bounded recipe for IMP; other gate-specific instructions live in each gate directory's README where one exists.

A gate pins what it does not control and what KRS produces, never KRS source:

- inputs: the revisions and file digests of the sibling checkouts, the toolchain and schema versions in `Krs.lock`, and the gate's corpus;
- outputs: emitted artifact, KORE, and behavior digests.

A source change that leaves every output identical passes without a pin edit.
When an output changes on purpose, re-record it by running the gate with `--record` (the KWasm, KEVM, KMIR, IMP, IMP state, IMP control flow, IMP static semantics, and CLI gates support it); the gate runs completely and, only if every step passes, rewrites exactly the output pins it measured.
Review the resulting pin diff like any other change.
`--record` never rewrites an input pin: a new checkout revision, corpus, or toolchain is a deliberate edit to the gate ledger or `Krs.lock`.
The shared pin handling lives in `tests/support`, whose unit tests run with `python3 -m unittest discover support` from `tests/`.

The repository hygiene check fails if any tracked file references the untracked, local-only notes directory or one of the retired root tracking ledgers:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tests/repo-hygiene/verify.py
```

### Documentation site

```sh
bun install --cwd docs-site --frozen-lockfile
bun run --cwd docs-site build
```

The build runs the tour verifiers and several `cargo check` invocations, so it needs the Z3 exports above.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT) at your option.
