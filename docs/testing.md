# Testing contracts

The permanent regression suite must express the Rust implementation's contracts and run without another K installation.
A reference implementation helps establish an expected answer when a contract is uncertain and detects compatibility changes when its pin moves.
Live differential tests are supplementary evidence; they are not required for every new Rust test.

## Running the suites

### After a change

The workspace suite runs with `cargo test --workspace`, or, with [cargo-nextest](https://nexte.st) installed, with `cargo nextest run --workspace`, which runs every test in its own process across all CPUs instead of one test binary after another.
`.config/nextest.toml` (nextest 0.9.91 or newer) gives the tests that measure the machine a slot of their own and starts the tests that reserve several slots first.
nextest does not run doc-tests, so the loop after a change is:

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo nextest run --workspace --locked
cargo test --doc --workspace --exclude k-rust-napi --locked
```

The default features download the Z3 release into each target directory (README, "Install and build").
To link a system or otherwise preinstalled Z3 instead, give every workspace command `--exclude k-rust-napi --no-default-features --features k-rust/cli`: `k-rust-napi` always selects the downloaded release, and it has no Rust tests.
Keep the same flags on every command, including the narrower ones below, so that they share one build.

While iterating, run one crate, one test binary, or a filterset, and the whole loop once before handing the change on.
A filterset over the workspace reuses the workspace build:

```sh
cargo nextest run --workspace -E 'package(k-rust-backend)'
cargo nextest run --workspace -E 'binary_id(k-rust::inner_rules)'
cargo nextest run --workspace -E 'binary_id(k-rust::cli) & test(/kprove/)'
```

`-p k-rust --test inner_rules` builds less after a change, but Cargo resolves the features of the selected crates alone, so its first run builds a second copy of the workspace crates.

A change to code under a `cfg(feature = ...)` gate, to the backend's `z3` sites, or to the bindings also needs the portable build, which compiles the other side of those gates:

```sh
cargo nextest run -p k-rust -p k-rust-wasm -p k-rust-backend --no-default-features
```

The registry entry `build-agreement` (`scripts/build-agreement.sh`) compiles every compile case of `scripts/reference-differential.toml`, the real semantics included, through the library in both builds and fails when they compile a case differently, when a build does not compile a case expected to compile, or when the portable build's `Z3InferenceRequired` refusals differ from the set its entry records; a change to the rule grammar, the parser, or any source with a `z3-inference` cfg owes it.
CI runs the workspace suite under checked sort inference, which runs the portable and Z3 engines on every inference and fails when they disagree; reproduce it with `KRUST_TYPE_INFERENCE_MODE=checked cargo nextest run --workspace --profile ci-checked`.
The `ci-checked` profile leaves out k-rust's `measure_ratchet`, whose snapshots pin one engine's work, and `k-rust-wasm`, which ships without Z3; `scripts/measure-ratchet.sh` runs the former in the default mode.
`inner_rules` also reruns itself under checked inference in an ordinary run, so parser changes get the engine-agreement check without the whole checked run.

### In CI

| When | Workflow | Checks |
|---|---|---|
| Every push and pull request | `ci.yml` | formatting; the benchmark harness's syntax; the MSRV `cargo check`; build and clippy with Z3; the workspace suite under nextest and checked inference (`ci-checked` profile); doc-tests; `scripts/measure-ratchet.sh`; the Node-API and WebAssembly packages' builds and tests; portable clippy; the portable subset (k-rust's library tests, `inner_parser`, `definition_regex`, and `k-rust-wasm`); `k-rust-backend` without its `z3` feature; the `wasm32` build; the dependency-free regex crate; the scripts' Python unit tests (`scripts/script-unit-tests.sh`) |
| A push or pull request that changes a trigger path | `nightly.yml`, called from `ci.yml` | the full portable suite of `k-rust`, `k-rust-wasm` and `k-rust-backend`, and the system-linked Z3 acquisition check (`scripts/z3-acquisition-check.sh`), each when its own trigger paths change |
| Every night on the default branch, or on demand | `nightly.yml` | both path-triggered checks (the portable suite with its doc-tests), `scripts/backend-smoke.sh` with the release `krust` and the pinned K release's LLVM backend, and the value-contract oracle (`crates/k-rust-backend/src/tests/definedness_oracle`) at 20,000 random definitions with a date-derived seed printed in hexadecimal |
| Every week, or on demand | `differential.yml` | the reference differential gates and `scripts/lean-check.sh`, the `weekly` entries of `scripts/gates.toml` |

`scripts/ci-changed-paths.sh` defines the trigger paths and decides which path-triggered checks a push or pull request needs.
The full portable suite follows the sources and tests of `k-rust` (including the embedded prelude), `k-rust-backend` and `k-rust-wasm`, the sources of `k-rust-kore` and `k-rust-regex`, the crate manifests, the lockfile and the nextest configuration; the acquisition check follows the manifests, the lockfile, the script, `z3_acquisition.rs`, `inner_rules.rs` and `examples/z3-inference.k`; a change to the workflows or to the script triggers both.
A push is compared with the commit before it and a pull request with its merge base; a new branch, a force push, a previous commit missing from the clone, or a failing comparison runs every path-triggered check.
A check that is not needed appears as a skipped job, which GitHub counts as passing for a required check.
A failed scheduled run shows only on the repository's Actions page; `gh run list --workflow nightly.yml --limit 1` reads the latest one.

### Reference gates, the conformance ratchet, and coverage

The reference gates need the pinned reference toolchain and checkouts (README, "Compatibility evidence").
Every gate, tool and scheduled check outside `cargo test` is an entry of `scripts/gates.toml`, and `scripts/run-gates.sh --changed BASE..HEAD` runs the entries a change owes: those with a path pattern that matches a path the change touched, or whose own entry it changed (`--list` shows the selection without running it, `--touched PATH` asks about one path).
The reference-output cache (below) replays unchanged reference results, so a repeated run costs mostly the krust side.
The gates build krust and the comparator with Cargo's default features, which download the Z3 release; `KRUST_GATE_Z3=system` builds them with `--no-default-features --features cli` instead, the same features linked to the Z3 the build environment provides (for example under `with-z3-static-4.16.0`); `scripts/backend-smoke.sh` follows the same selection when it builds krust itself (without `KRUST_BIN`).
`KRUST_GATE_TARGET_DIR` and `KRUST_GATE_INVARIANT_CHECKS` (`scripts/reference-memory-guard.sh`) select the gate krust's target directory and its kompile invariant checks.

Every reference entry is owed by any change to the sources krust is built from, since kompile itself runs backend code; the entries differ in the harness each runs.
Beyond what the registry selects, run `scripts/conformance-ratchet.sh --cases` with a subsystem's cases (`scripts/conformance/subsystems.toml`) after a change to that subsystem's code, and `scripts/conformance-ratchet.sh --all` after a change to the conformance driver or before merging an integration branch.

No workflow runs the ratchet: its LLVM recipes need the pinned reference tools under a user systemd scope (see "Manual conformance acceptance"), so even `--all` is a manual run.
`scripts/reference-fixtures-refresh.sh` is for reference pin moves only.

`scripts/coverage.sh` measures which production lines the Z3 and portable suites execute, per crate, per test and per algorithm card; its header documents the options and the report.
It is a manual check, not a gate: run it before removing tests or restructuring a suite, and now and then to follow the trend.

## Choosing a test home

| Contract | Test home | Expected answer |
|---|---|---|
| Internal algorithm, invariant, or algebraic property | The owning module's tests | A stated invariant, independent calculation, or property |
| Backend orchestration (`k_rust::backend::*`) | The module's inline tests, or CLI/RPC tests when rendering contributes | One host-independent operation plus the surface-specific rendering contract |
| Public subsystem behavior across modules | The subsystem's integration test under `crates/k-rust/tests` | A concrete contract, optionally backed by a committed reference artifact |
| CLI options, process status, RPC schema, or host binding behavior | CLI, RPC, Node, or WASM surface tests | The public surface contract |
| Compatibility requiring a running reference | The applicable `scripts/reference-*.sh` gate and `scripts/reference-differential.toml` | Output from the pinned reference toolchain |
| Broad upstream corpus exploration and acceptance tracking | `scripts/conformance/run.py` and `scripts/conformance/expectations.toml` | Upstream recipes, recorded outputs, and confirmed live oracles |
| Execution and proof results of the pinned WASM semantics with the in-process backend | `scripts/wasm-execution-gate.sh` and `scripts/wasm-execution-gate.toml` | The recorded exit statuses, final configurations, proof verdicts and failed proofs' output digests; a change is a behavior change to explain |
| The load-time critical-pair check's verdict on whole definitions (FUN, SIMPLE, KOOL, WASM, IELE, the overload cases, and issue-4114 and KEVM, which withdraw claims) | `scripts/value-contract-corpus.sh` and `scripts/value-contract-corpus.toml`, on the definitions the conformance driver compiled (the ratchet runs it on the cases it measured) and on WASM and KEVM, compiled by the script | The recorded verdicts and counts; a change is a precision or cost change to explain |

A kompile stage's contract belongs in its pass module, stated on the definition the pipeline hands that stage: `kompile::stage_harness::run_to_stage` (test-only) loads a prelude-free source as `kcompile --no-prelude` does, runs the stages before the named one, and returns that stage's input and output, so the test needs no hand-built input that later drifts from what the earlier stages produce.
A backend semantic contract belongs with backend tests even when it was discovered through a CLI command.
Within `crates/k-rust-backend`, a contract stated through `pub` items belongs in `tests/backend/`, one that needs a `pub(crate)` entry point in `src/tests/`, and the invariant of a private helper stays inline next to the helper.
A separate CLI test is warranted when argument handling, initialization, rendering, or process status contributes to the defect.
Snapshots are an assertion format within these homes, not a separate test system.

Tests must declare the capabilities their fixtures require.
The embedded standard prelude is portable: it loads without Z3, under either backend's module exclusion, to the same definition as in the native build (`inner_rules::the_standard_prelude_loads_to_the_same_definition_in_both_builds`), so loading it is not by itself a reason to gate a test.
A test that runs the `krust` binary (`CARGO_BIN_EXE_krust`) needs the `cli` feature: the binary is `required-features = ["cli"]`, so a portable build defines the variable but never builds the file it names, and a binary left in the target directory by another build would not be built from the tested sources. Gate such a test, or its whole file, on `cfg(feature = "cli")`; cargo then builds `krust` before the test runs.
Frontend tests that require parametric inference, or an ambiguous forest outside the portable decision described next, belong to the native `z3-inference` feature, even when their final assertion concerns another subsystem.
An ambiguous forest is portable when every tree is monomorphic and has a greatest typing and the forest has at most `PORTABLE_AMBIGUITY_TREE_LIMIT` trees (`inner/parser/inference.rs`), unless trees of one typing instantiate formal parameters differently and do not all lower to one term; other ambiguous forests also need the native feature.
The native engine keeps every reading that some formal-parameter vector types, so `prefer`/`avoid` decides among such readings (`Encoding::admissible_parameters` in `inner/parser/z3_inference.rs`); the portable engine still leaves them to it.
Alternatives that are equal once bracket nodes are erased are one reading, whose instantiation the `K`/`KItem`/`Bag` preference picks (`LivenessGraph` reading classes); the concrete instances of one parametric production are already one production of the parsed term, since the parser gives each of them its family's production index (`Production::term_production`).
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
A case with step exclusions is ranked by its remaining steps (its logged `ranked_verdict`), and a case exclusion leaves the case unranked ([compatibility.md](compatibility.md#driver-scope)).
A run records the scale of its ranks (`ranking`); a rank logged on an earlier scale still bounds the floor, the case's first rank on the current scale bounds it too, and comparing against a run on another scale is a driver change.
The rank is a coarse outcome ordering, not proof that every recipe or pipeline stage is covered.
Review per-step results when accepting a change.
Under the `RLIMIT_AS` fallback of `scripts/reference-memory-guard.sh`, the pinned LLVM interpreter cannot start because it reserves 2 TiB of address space; LLVM-recipe steps whose text differs therefore report `reference-error` in a sandbox and require a host-UID run under a user systemd scope for a verdict.
The pinned `kore-exec` and `kore-rpc` executables accept the threaded-runtime `GHCRTS=-N1` bound, while `kore-parser` and `kore-match-disjunction` are non-threaded and reject it.
The conformance driver therefore clears `GHCRTS` for parser calls and for `krun --pattern`, which delegates to `kore-match-disjunction`, and gives the other reference calls `-N1`, or `REFERENCE_GHCRTS` when it is set.
A caller's `GHCRTS` reaches no reference call: the gates' guard removes it (README, "Compatibility evidence").

Every accepted non-`match` verdict is either justified by an exclusion category with an inline reason or is pending work with an empty exclusion and a measured reason ([compatibility.md](compatibility.md#driver-scope)).
The tracked conformance backlog is a TOML file of `[[ticket]]` rows, each with `id`, `title`, `state` (`open` or `closed`), and `cases`, the expectation case names it covers.
When the repository backlog is present, `scripts/conformance-ratchet.sh --audit` checks it by default; `--backlog PATH` or `CONFORMANCE_BACKLOG=PATH` selects a different ledger, and an empty `CONFORMANCE_BACKLOG` disables this check.
With a backlog, the audit lists every non-excluded case whose latest measurement is not `match` and that no open ticket names, exits 3 when one exists, and lists tickets whose cases all match so that they can be closed.
Ticket identifiers never appear in the expectations file.

Update accepted verdicts only after inspecting the measured result and its reference evidence.
A lower floor requires a documented contract or scope change; a failing run is not sufficient reason to lower it.
Do not commit full measurement histories or temporary run output.

Expensive reference runs remain manual and selected according to the affected contract.
Changes to CI coverage, frequency, or resource budgets require a separate cost decision.

A `step_budget` in `scripts/conformance/expectations.toml` bounds the CPU seconds of one krust program execution (`RLIMIT_CPU`), and its companion `step_wall_budget` bounds that execution's wall seconds.
The budgets exist so that one divergent program cannot consume the case budget of the programs behind it: the program's own CPU time measures divergence without depending on the other jobs on the machine, and the wall budget, set well above the program's measured cost, ends a program that stops accruing CPU time.
The case budget still bounds the wall time of the whole case, and must leave room for the rest of the case after a step that uses its whole wall budget.

### Reference-output cache

The reference gates (`scripts/reference-*.sh`, through `scripts/reference-cache.sh`) and the conformance driver replay a pinned reference tool's result when none of its inputs changed (`scripts/reference_cache.py` defines the key and the entry).
krust, every comparison, and every pin check still run; a hit restores the reference's exit status, streams, and files byte for byte from a digest-checked entry.
`REFERENCE_CACHE` selects `on` (the default), `off`, `refresh` (recompute and overwrite), or `verify` (recompute each stored result, and fail when the fresh one differs beyond the reference's run-to-run variation: line order, generated-name numbering, binary artifacts, and any difference a second fresh run does not reproduce).
The default is `off` when `CI` is true, because CI keeps no cache between runs, and always `off` under `REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED=1`.
Entries live per user under `${XDG_CACHE_HOME:-~/.cache}/k-rust/reference-outputs/v1` (`REFERENCE_CACHE_DIR`), and an entry older than `REFERENCE_CACHE_MAX_AGE_DAYS` (14) is recomputed.
The conformance ratchet runs every fourth measured `--all` run of a log in `verify` mode unless `REFERENCE_CACHE` is set.
Each gate prints its hit and miss counts; the conformance driver records each step's reference calls as `reference_cache`.
`scripts/reference-fixtures-refresh.sh` runs the reference tools directly and never reads the cache.
Three reference runs of the gates stay uncached: the MIR gate's kmir Python step, whose Python environment the manifest does not pin (the krun after it is keyed on the pattern it writes), the RPC gate's oracle server session, whose responses depend on every earlier request to the same server and which costs under two CPU seconds, and the execution gate's one-request reference simplifier session (N41).

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
No gate comparison drops a disjunct because the port's simplifier reduces it to `\bottom`: that would let the code under test remove the reference's copy of a branch the port lost.
When the reference reports branches it did not refute, an execution case may instead carry `reference-result-simplification-reason`, and the execution gate compares the port's result against the reference result as the reference's own simplifier (one `simplify` request to the Haskell backend's `kore-rpc`) rewrites it, printing the reason with the N41 label; that evidence comes from the reference, not the port.
A compile case may carry `lifted-cells`, the rule labels and cells of rules that write a cell inside a cell that does not contain it, with a written `lifted-cells-reason`; the semantic KORE comparison then compares those axioms with the port's cell replaced by the variable the reference has in its place (N45, [Cells written inside another cell](compatibility.md#cells-written-inside-another-cell)).
The manifest names those cells, not the port's own cell completion, so the code under test does not decide which of its axioms are excused.

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

## Generative compile test

`scripts/generative-compile.sh [--count N] [--seed S] [--jobs J]` is an exploratory tool, separate from `cargo test`, CI, and the gates.
It generates N small definitions from seed S (`scripts/generative/gen.py`, 1000 by default), compiles each with the release example `crates/k-rust/examples/generative-compile.rs` (built only under the `generative-harness` feature, with the kompile invariant checkers), loads every emitted `definition.kore` in the Rust backend, and triages the rows with `scripts/generative/triage.py`.
A panic, crash, timeout, or backend failure after a successful compilation, an error located in a builtin source, and a rejection that no category of `scripts/generative/expected.toml` explains as invalid input are unexpected; the script then exits 1 and keeps the corpus, and `scripts/generative/reduce.py` reduces a case.
Workers load the prelude once and compile each case against it, about 0.26 s of CPU per case, so the default run takes about 40 s with 8 jobs after a build of about a minute; `--fresh` reloads the prelude for every case (about 0.5 s per case), which is needed to see a case whose syntax changes how builtin rules parse.
The corpus is not committed, since the seed and count reproduce it.
A finding becomes a focused regression in its owning subsystem as described above; `expected.toml` holds only rejections of invalid input, each with its reason.

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
