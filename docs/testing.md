# Testing contracts

The permanent regression suite must express the Rust implementation's contracts and run without another K installation.
A reference implementation helps establish an expected answer when a contract is uncertain and detects compatibility changes when its pin moves.
Live differential tests are supplementary evidence; they are not required for every new Rust test.

## Choosing a test home

| Contract | Test home | Expected answer |
|---|---|---|
| Internal algorithm, invariant, or algebraic property | The owning module's tests | A stated invariant, independent calculation, or property |
| Public subsystem behavior across modules | The subsystem's integration test under `crates/k-rust/tests` | A concrete contract, optionally backed by a committed reference artifact |
| CLI options, process status, RPC schema, or host binding behavior | CLI, RPC, Node, or WASM surface tests | The public surface contract |
| Compatibility requiring a running reference | The applicable `scripts/reference-*.sh` gate and `scripts/reference-differential.toml` | Output from the pinned reference toolchain |
| Broad upstream corpus exploration and acceptance tracking | `scripts/conformance/run.py` and `scripts/conformance/expectations.toml` | Upstream recipes, recorded outputs, and confirmed live oracles |

A backend semantic contract belongs with backend tests even when it was discovered through a CLI command.
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
An unavailable or inconclusive equivalence check must not be counted as a successful comparison.

## Durable regression descriptions

Committed filenames, test names, fixture metadata, and comments must identify the behavior or scenario they describe.
A contributor must be able to understand an expectation without private review notes, task ledgers, or temporary run directories.
Keep upstream issue numbers and repository-defined normalization identifiers when they provide traceable evidence.
Record lasting contracts and exception rationales in tracked documentation or fixture metadata; keep work assignment, completion history, and temporary investigation narratives in development history.
A provenance record may identify a historical tool invocation, but local paths must not serve as the only explanation or as required inputs to a permanent check.
