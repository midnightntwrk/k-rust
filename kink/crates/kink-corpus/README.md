# kink-corpus

kink's admission-and-input library and kink's corpus harness.

## What this crate is

The crate has two roles.

It is the library every kink front end builds on: kink-flow, and through kink-flow the krs front end (`krs kink`, not yet built).
The library is:

- `resolver`: loading a K definition under a root, recording every file the load reads (`load_source`, `load_source_with_overlay`, `CorpusSource`, `LoadedSource`, `SourceFile`).
- `input`: assembling a program's initial configuration from its program text and its configuration variables (`InputGrammar`, `InputAssembler`, `ProgramSource`, `VariableInput`, `TestInputSpec`, `InputError`, `assemble_input`, `assemble_input_with`).
- The stage functions and records of `admission`: `check_refused_cases`, `check_loaded_refused_cases`, `check_semantic_input`, `check_loaded_semantic_input`, `compile_definition`, `compile_definition_with`, `input_backend`, `program_input`, `input_refusal`, `check_initial_state`, `below_floor_cases`, `path_names_case`, `REFUSED_CASE_STAGE`, `BELOW_FLOOR_CITATION`, `AdmissionRecord`, `AdmissionRefusal` and `KompileWarning`.
- `Store`'s atomic JSON files (`new`, `root`, `read_json`, `write_json`, `write_text`, `write_bytes`) and their error, `StoreError`.
- `runner::all_normal` (the terminal classifier both tools use), `cli::DEFINITION_STACK_BYTES` (the stack kink's commands run on), `manifest::RefusedCase` and `manifest::BELOW_FLOOR`.
- For tests only, under the `measure` feature: `input::input_grammar_builds`, which counts how often a caller builds the input grammar.

It is also kink's corpus harness: the `kink-corpus` binary over a canonical-JSON corpus manifest (schema `kink-corpus-manifest`, `src/manifest.rs`).
The harness runs campaigns of kink-patch's generated mutants over many K definitions, each definition in its own process,
keeps a digest-checked store with resume, aggregates a summary and re-derives a stored report.
`admission::admit_definition` admits one definition of such a manifest, and the rest of `manifest`, `runner`, `summary`, `cli` and `store`'s corpus layout are the harness's.

## Not a user tool

The harness serves kink's own tests and its maintainers.
To test a K specification, use kink-flow ([`../kink-flow/README.md`](../kink-flow/README.md)); for a KRS package, the krs front end (`krs kink`, not yet built).
One manifest schema, kink-flow's `FLOW.toml`, and one status set, kink-flow's (`kink_flow::search::STATUSES`), serve users.
A capability of the harness manifest reaches users only as a form of `FLOW.toml` stated in the specification's own terms: its declared inputs, its cell names, K text edits of it.

## The harness manifest and the user tool

Each capability of the harness manifest, and the user tool's form of it or why users have none:

| harness capability | user tool |
| --- | --- |
| KORE-state inputs (`kore_state = {file, sha256}`), concrete only | Typed inputs (`[[program]] inputs`), decoded by a front end that knows the specification's declared types into K terms bound to its configuration variables; at the K level, K text under `variables`. A KORE state is none of these because it bypasses the specification's initializer: a test is an input whose expected result is what the specification computes, and that computation starts at the configuration the initializer builds from the inputs. A KORE state can be a configuration no input produces, so a kill from it can be a difference only on configurations the specification never reaches, a fact about the rewrite relation rather than about the specification's behavior. It also names compiled symbols, so a corpus written that way breaks whenever the way the specification compiles changes. |
| projection `term-paths` (KORE child-index paths) | The cells compared: every cell the specification does not declare `unobservable`, narrowed by `[result] cells`, each named by its cell name. A term path names a position of the compiled configuration, not a part of the specification: child indices depend on the compiled cell layout, a path an end lacks makes the slot an error rather than a value, and a term-path slot gives no one-sided kill. A named cell is stable under compilation, defined on every configuration and compatible with one-sided kills. |
| a test's own list of oracles: any number of them, each a `whole-term`, `exit-stop`, `term-paths` or `pattern` projection (a test can compare the exit stop alone, or several projections) | Every program has the same two oracles: the exit stop, then the compared cells (the whole final configuration unless the specification declares a cell `unobservable` or `[result] cells` narrows them). The compared cells are a property of the specification, not of one program: a test's expected result is what the specification computes from its inputs, its final configuration, so comparing less for one program only lets that program miss a mutant that changes what it computes; which cells are not part of the specification's behavior is stated once, for every program (`unobservable`, `[result] cells`). |
| projection `exit-stop` with an `exit_code_cell` | None needed: the exit cell is compared as part of the final configuration (`whole-term` or `cells`), and a manifest that narrows the compared cells names it in `[result] cells` to keep it compared. |
| `campaign.classifier` (only `all-normal` is accepted) and the crash policies `compare-identity` and `distinguish` | None needed: both tools classify every end as normal (`runner::all_normal`), so no side is a crash and only `reject` is ever reached. |
| projection `pattern` (a kink-pattern plan over step events, with `observation` declarations) | `kink-flow query`, which answers whether a program reaches a pattern. In the corpus loop a pattern is a question asked of the corpus, not a kill criterion: a kill compares what the specification computes, not what an observer of its steps reports. |
| generated mutants (kink-patch operator specifications, `universe`, `max_candidates_per_spec`, `budget_mutants` sampling) | A mutation is a misunderstanding its author states as text edits of the specification (`MUTATIONS.toml`, each with its `misunderstanding`). A generated sweep states no misunderstanding, so it is not a user input; a generated candidate can be offered to a user only as such a text edit. |
| `schedule` `full` (the full kill matrix) | Not yet: `kink-flow run` is first-kill, stopping each mutation at its first killing program. |
| `schedule` `first-kill` | `kink-flow run`. |
| `selection` `prioritize` (programs ordered by compiled coverage of the edit) | `kink-flow run` orders the programs by its own witness rule, read from the edited rule's text (its README, `run` step 3). In the portable profile, while no `time_ms` bound fires, the order changes no status, only which killer is found first and the cost. |
| `budget` `time_ms` and `max_depth` (per campaign, and `max_depth` per definition) | `[budget] time_ms` and `max_depth`, with the deterministic work bounds `work_factor` and `baseline_max_work`. |
| `budget` `max_breadth` and `max_simplification_iterations` | None: kink-flow has no breadth bound, since its work bounds count the states a run visits across all its paths and so stop a wide run as deterministically as a deep one; it runs the simplifier under one fixed bound per step (`results::SIMPLIFICATION_ITERATIONS`) that no manifest sets. |
| `profiles` and a definition's `requires_profile` | None: a user's command runs in its build's solver profile (kink's `z3` feature), and its documents report the outcomes that profile decides. |
| several definitions per manifest, each with root, revision and pinned source digests (`pin`), and the manifest's `k_rust.revision`, which must equal the k-rust version kink is built from | None: a user's corpus tests one specification, `FLOW.toml`'s `[spec]`, and kink-flow's caches are keyed by content digests and kink's build (its identity's `k_rust_revision` among them), so nothing needs pinning and an outcome a different build computed is never read as this build's. |
| per-case `refused_cases` with reasons and citations | None: kink-flow refuses the below-floor conformance cases itself (stage `refused-case`); a user's specification is not a conformance case. |
| child-process isolation per definition, the store, resume, the summary and `replay-check` | None: kink-flow's cache directory keeps what a command computed, every record keyed by what derived it, and `--verify` re-derives cached outcomes. |

## Commands

The binary prints its usage on every argument error.

- `pin --workspace DIR MANIFEST`: rewrites `MANIFEST` with every definition's source files and file inputs pinned by SHA-256.
- `run --workspace DIR --store DIR MANIFEST`: runs every definition of the manifest, each in a child process (`definition`), so that a definition that aborts the process is recorded as an `error`/`process` row and the others still run; a definition whose completed report is already in the store is resumed rather than run again; then publishes the summary.
- `definition --workspace DIR --store DIR MANIFEST ID`: admits and runs one definition and writes its report and admission record into the store.
- `summary --store DIR MANIFEST_SHA256 PROFILE`: aggregates the store's reports for one manifest and solver profile.
- `replay-check --workspace DIR --store DIR MANIFEST ID`: checks one definition's stored report against the store's index and digests, then re-derives the campaign from the stored baseline artifact and fails unless the replay reproduces the report, so it can check a store another build wrote (a report whose time bound fired is not applicable).

What resume and the summary trust, and why replay is the check across builds, is stated in kink's README ([`../../README.md`](../../README.md), the "Corpus resume" paragraph and the paragraphs on what a stored verdict is bound to before it).

## The summary's tally

The summary's tally keys are a campaign report's tally keys (`summary::TALLY_KEYS`): the runner's seven mutant statuses, `killed`, `survived`, `equivalent`, `invalid`, `timeout`, `unknown` and `error`, each named as kink-flow's run document names it, then `rejected_origins`.

- The harness has no `unkillable`.
  That status is kink-flow's judgement, made at resolution, of a text edit that only weakens the specification: every model of the specification is then a model of the mutant, so no program can kill it.
  The campaign runner over generated candidates does not make that judgement; such a candidate runs, and is counted under the runner's statuses, never as `killed`.
- The harness has no `invalid-mutation`.
  A generated candidate is built from the loaded definition and always resolves to a patch; the harness's counterpart, an origin rejected at generation, is counted in `rejected_origins`, a count of origins, not of mutants.
- The score, `killed / (killed + survived)`, is the harness's and is not comparable to kink-flow's counts, which include the user tool's own statuses.

kink-flow's `tests/statuses.rs` pins this relation: each runner status has one name in kink-campaign's reports (a mutant's `status` and the tally key that counts it), this summary's `TALLY_KEYS` and kink-flow's documents, and kink-flow's statuses differ from the runner's by exactly `unkillable` and `invalid-mutation`.
