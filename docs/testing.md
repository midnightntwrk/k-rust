# Testing contracts

The permanent regression suite must express the Rust implementation's contracts and run without another K installation.
A reference implementation helps establish an expected answer when a contract is uncertain and detects compatibility changes when its pin moves.
Live differential tests are supplementary evidence; they are not required for every new Rust test.

## Choosing a test home

| Contract | Test home | Expected answer |
|---|---|---|
| Internal algorithm, invariant, or algebraic property | The owning module's tests | A stated invariant, independent calculation, or property |
| Backend orchestration (`k_rust::backend::*`) | The module's inline tests, or CLI/RPC tests when rendering contributes | One host-independent operation plus the surface-specific rendering contract |
| Public subsystem behavior across modules | The subsystem's integration test under `crates/k-rust/tests` | A concrete contract, optionally backed by a committed reference artifact |
| CLI options, process status, RPC schema, or host binding behavior | CLI, RPC, Node, or WASM surface tests | The public surface contract |
| Compatibility requiring a running reference | The applicable `scripts/reference-*.sh` gate and `scripts/reference-differential.toml` | Output from the pinned reference toolchain |
| Broad upstream corpus exploration and acceptance tracking | `scripts/conformance/run.py` and `scripts/conformance/expectations.toml` | Upstream recipes, recorded outputs, and confirmed live oracles |

A backend semantic contract belongs with backend tests even when it was discovered through a CLI command.
Within `crates/k-rust-backend`, a contract stated through `pub` items belongs in `tests/backend/`, one that needs a `pub(crate)` entry point in `src/tests/`, and the invariant of a private helper stays inline next to the helper.
A separate CLI test is warranted when argument handling, initialization, rendering, or process status contributes to the defect.
Snapshots are an assertion format within these homes, not a separate test system.

Tests must declare the capabilities their fixtures require.
Frontend tests that load the full standard prelude or require ambiguous or parametric inference belong to the native `z3-inference` feature, even when their final assertion concerns another subsystem.
Portable tests must cover the supported subset and explicit `Z3InferenceRequired` boundary.
Use a reduced fixture when the contract can be exercised without native inference; do not require the full prelude merely for convenience.
Feature selection changes which contracts can run, not their subsystem ownership.

`scripts/conformance/subsystems.toml` is the shared registry of subsystem names, source ownership, and reference fixture homes.
The fixture validator checks the registered homes; the census uses the same mapping.
A dedicated subsystem test retains that subsystem's ownership even when it consumes a shared fixture from another directory.
For generic surface tests, a referenced fixture home supplies the semantic owner when available.
Fixture directory names and the historical `subsystem` field in fixture manifests identify storage homes; they are not an additional subsystem taxonomy.

## Turning a conformance failure into a regression

1. Reduce the failure and identify the owning subsystem and contract.
2. Establish the expected behavior from the contract and, when necessary, the pinned reference.
3. Add a focused Rust regression in the owning subsystem, including a contrasting valid or invalid case when it distinguishes the contract.
4. Preserve small reference-produced evidence under `crates/k-rust/tests/fixtures/reference` when needed, using its provenance and refresh conventions.
5. Keep the upstream case in the broad conformance expectations.
   Add a curated live case only when it protects a distinct compatibility boundary that the existing gates do not exercise.

One fixture may support multiple assertions; tests must not duplicate an entire frontend or backend pipeline merely to give the same fixture another home.
Reference attribution documents where an expectation came from.
It does not establish completeness, and the census is an inventory rather than a maturity score.

## Manual conformance acceptance

`scripts/conformance/expectations.toml` records each case's historical `baseline_verdict` and the newer `accepted_verdict` and `accepted_stage` from certification.
The acceptance metadata identifies the full certification that established the initial floor, including its measured revision and source-results digest.
Per-case `accepted_basis` records later measured increases to the acceptance floor.
These are recorded measurements, not a claim that the current checkout has been recertified.

Initialize a local log without private history or a reference installation:

```sh
scripts/conformance-ratchet.sh --seed-acceptance --label accepted --log target/conformance/ratchet.toml
```

After configuring the pinned reference tools, measure selected cases and retain their logs:

```sh
scripts/conformance-ratchet.sh --label change --cases append --log target/conformance/ratchet.toml --runs-dir target/conformance/runs
scripts/conformance-ratchet.sh --audit --log target/conformance/ratchet.toml
```

Selectors are combined as a union: `--cases NAME...` selects named cases, `--stage STAGE` selects their historical baseline stage, and `--all` selects every case.
Stage selection uses `baseline_stage`, which stays stable as the implementation progresses; inspect current per-step results to identify the affected contract.
Version-1 logs with historical ownership fields remain readable and retain their original entries, but new entries and reports contain only measurements, deltas, and exclusions.

The required rank is at least the versioned acceptance rank and the local log's first measured rank.
A fresh log or a different driver version must not lower the versioned floor.
Existing exclusions still apply; reference errors remain explicitly reported oracle changes rather than evidence of a Rust pass.
The rank is a coarse outcome ordering, not proof that every recipe or pipeline stage is covered.
Review per-step results when accepting a change.
Under the `RLIMIT_AS` fallback of `scripts/reference-memory-guard.sh`, the pinned LLVM interpreter cannot start because it reserves 2 TiB of address space; LLVM-recipe steps whose text differs therefore report `reference-error` in a sandbox and require a host-UID run under a user systemd scope for a verdict.
The pinned `kore-exec` and `kore-rpc` executables accept the threaded-runtime `GHCRTS=-N1` bound, while `kore-parser` and `kore-match-disjunction` are non-threaded and reject it.
The conformance driver therefore clears its default `GHCRTS` for parser calls and for `krun --pattern`, which delegates to `kore-match-disjunction`; an explicitly configured `GHCRTS` remains the operator's choice.

Every accepted non-`match` verdict is either justified by an exclusion category with an inline reason or is pending work with an empty exclusion and a measured reason ([compatibility.md](compatibility.md#driver-scope)).
Pending work is tracked in a local backlog outside the repository: a TOML file of `[[ticket]]` rows, each with `id`, `title`, `state` (`open` or `closed`), and `cases`, the expectation case names it covers.
`scripts/conformance-ratchet.sh --audit --backlog PATH` lists every non-excluded case whose latest measurement is not `match` and that no open ticket names, exits 3 when one exists, and lists tickets whose cases all match so that they can be closed; the wrapper passes `draft/conformance-backlog/tickets.toml` by default when that file exists.
Ticket identifiers never appear in the expectations file.

Update accepted verdicts only after inspecting the measured result and its reference evidence.
A lower floor requires a documented contract or scope change; a failing run is not sufficient reason to lower it.
Do not commit full measurement histories or temporary run output.

Expensive reference runs remain manual and selected according to the affected contract.
Changes to CI coverage, frequency, or resource budgets require a separate cost decision.

## Comparator evidence

`scripts/reference-normalisations.toml` records the permitted normalizations and exclusions.
[Compatibility decisions](compatibility.md) explain the governing semantics and reference evidence; each conformance exclusion category points to the applicable policy.
The execution comparator first compares normalized structures and may use k-rust implication in both directions to establish equivalence of remaining constraints.
That fallback is supplementary evidence: it depends on the same Rust implication implementation being tested elsewhere and cannot independently validate it.
Implication correctness must therefore have direct Rust contract tests, including variable-renaming invariance and negative controls.
The conformance driver's C8 comparison (`scripts/conformance/run.py` `compare_simplified_kore`) is supplementary evidence in the same sense: it simplifies the reference's `--output kore` result and the krust result with `krust kore-simplify` before the structural comparison, so it depends on the port's simplifier, which must have its own contract tests, and it cannot independently validate that simplifier.
A step that matches only under C8 keeps its text difference and records the C8 comparison label.
A simplification or comparison that fails or is unavailable leaves the text mismatch in place; a reference re-run that produces no result records `reference-error` with the reference's stderr, which is an oracle change and not evidence for either side.
The `oracle_confirmed` field is `true` when the reference re-run reproduces the checked-in output, `false` when a completed re-run refutes it, and `"not-run (reference crash)"` when a crash, timeout, or environmental failure prevents the re-run from producing an oracle.
The driver uses `"not-run (budget)"` when the case budget prevents the confirmation attempt.
An unavailable or inconclusive equivalence check must not be counted as a successful comparison.

## Harness recipes

These recipes hold on any host; machine-specific paths and memory-guard settings belong in local notes.

Compare a krust definition against an existing reference `definition.kore` without re-running the compile gate:

```sh
K_REFERENCE_KORE=<reference definition.kore> K_RUST_KORE=<krust definition.kore> \
  cargo test -p k-rust --test reference_differential -- \
  --ignored --exact emitted_kore_matches_the_reference_frontend --nocapture --test-threads=1
```

The `--ignored` flag is required: without it the test is skipped and the run exits 0.
A kompile-stage mismatch report names every axiom that mentions a differing generated symbol, so one differing `#lambda` or `#freezer` name hides a second difference in the same axioms; the comparator collapses multi-suffix `#lambda` families first (`scripts/reference-normalisations.toml` N23) and prints the collapsed axiom count per case, and what remains is the difference to read.

Reproduce one conformance driver step with the `krust_cmd` recorded in the run's `results.toml` rather than with a hand-written command.
Under `--io off`, both `krust krun` and the pinned `krun` read standard input to end of file into `$STDIN`, so a manual probe must redirect standard input from `/dev/null` or the step's `.in` file or it blocks with no output at any depth; the driver already supplies one of those inputs.
For every kprove recipe, the driver first compiles a separate proof-ready definition with the kompile recipe's Markdown selector and `--for-proving`, then passes the specification source unchanged through `--compiled-definition` with only the kprove recipe's Markdown selector.
This preserves the frontend boundary between definition and specification parsing; a generated source wrapper does not model that boundary.
The checked-inference probe of a regression case has the shape

```sh
KRUST_TYPE_INFERENCE_MODE=checked krust kcompile test.k --main-module TEST --backend llvm \
  --output-directory <tmp> -I . --builtin-directory <k checkout>/k-distribution/include/kframework/builtin \
  [--warnings all] [--warnings-to-errors]
```

and must run under the same memory guard as the gates.
`--backend llvm` excludes modules attributed `symbolic` and `--backend rust` excludes modules attributed `concrete` (`CompilationBackend::excluded_module_attribute`), so a checked-inference verdict may differ between the two backends.

The symbolic and MIR execution gates pass the initial pattern to the comparator through `K_DIFFERENTIAL_INITIAL_PATTERN`; every result variable that is not free in it is treated as engine-named and renamed (N4).
The conformance driver applies the same reading to kprint text: every `?Name:Sort` token is renamed by first occurrence per disjunct (C7) except the `?` variables the recipe's `--pattern` text names, and a step whose texts match only after that renaming records `renamed_existentials = true`.
A step whose texts differ but whose reference and krust KORE are equal after `krust kore-simplify` (C8) records `simplified_kore_equal = true`, the C8 comparison label, and the text difference as `text_divergence`; a step where C8 could not establish equality records why in `simplified_kore_divergence`.
`kore-exec --depth N` lists the leaves stuck within `N` steps and drops the leaves that merely reached the limit whenever a stuck leaf exists (`Kore/Exec/GraphTraversal.hs` `checkLeftUnproven`), so one-step symbolic fixtures in `scripts/reference-differential.toml` pin `depth = 2`.

A `driver-delta` label in a ratchet report marks a rank decrease that stays at or above the floor while the driver version changed (`scripts/conformance/ratchet.py`); it is not a pass, and the decrease must be diagnosed like a regression.

## Durable regression descriptions

Committed filenames, test names, fixture metadata, and comments must identify the behavior or scenario they describe.
A contributor must be able to understand an expectation without private review notes, task ledgers, or temporary run directories.
Keep upstream issue numbers and repository-defined normalization identifiers when they provide traceable evidence.
Record lasting contracts and exception rationales in tracked documentation or fixture metadata; keep work assignment, completion history, and temporary investigation narratives in development history.
A provenance record may identify a historical tool invocation, but local paths must not serve as the only explanation or as required inputs to a permanent check.

## Measurement

`k_rust_kore::measure` holds fifty-three named work counters (`Counter::ALL`) that the compiler, the parser, provenance tracking, and the backend increment at the loops whose cost they measure.
Without the `measure` Cargo feature the increments compile to nothing and `krust` behaves exactly as before; the shipped binary is feature-off.
Test builds enable the feature through each crate's dev-dependencies, so `cargo test --workspace` runs the counter ratchets (`crates/k-rust/tests/measure_ratchet.rs`, `crates/k-rust-backend/tests/measure_ratchet.rs`) without a CI change.

To read the counters from a run, build with the feature and name the output file:

```sh
cargo build --release -p k-rust --bin krust --features measure
KRUST_COUNTERS=counters.json target/release/krust kcompile examples/rewrite.k --main-module REWRITE --output-directory out
```

The file is one JSON document, `{"format": "krust-counters", "version": 5, "counters": {...}}`, with every counter in `Counter::ALL` order and zeros included, written at process exit on success and on failure.
The counters are thread-local and the one-shot subcommands do their work on the main thread; `krust kore-rpc` answers requests on connection threads, so its dump shows zeros for the backend families.
A ratchet asserts a bound on a checked-in input and a growth shape on a parameterised one; a bound that trips after a deliberate algorithm change is re-pinned in a commit that states the new measured value and why it moved.
Renaming or removing a counter changes the dump schema and bumps `version`.
