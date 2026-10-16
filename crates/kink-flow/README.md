# kink-flow

The primary usage flow of kink (`draft/tasks/flow/README.md`, section 5):
a K specification, a concrete corpus of programs an LLM writes for it,
cached results, a mutation list, a kill search and a survivor report.
The root README's "Using kink-flow" section is the walkthrough; this file is the reference.

This crate provides the corpus manifest and the `check` command (flow F-02),
the result cache with the `results` command (flow F-03),
the mutation list with its resolution into patches (flow F-04),
the kill search with its killer cache, the `run` command (flow F-05),
the survivor report with the `report` command (flow F-06),
Markdown sources (flow F-10),
the outcome cache: proved outcomes kept across commands, killer hints that survive specification edits, and `run --verify` (flow F-14),
one baseline run per program per command (flow F-12),
and report usability: named oracle slots, timings, leaf censuses in the causes of stopped runs, cheaper killers first, and the rules no mutation targets (flow F-13).

## `FLOW.toml`

```toml
[spec]
entry = "calc.k"              # relative to this file's directory
main_module = "CALC"
syntax_module = "CALC-SYNTAX" # optional
include_dirs = ["."]          # optional
md_selector = "k"             # optional

[budget]                      # optional
time_ms = 10000
max_depth = 100000

[[program]]
id = "add"
file = "programs/add.calc"    # or: text = "1 + 2"
start_sort = "Exp"            # optional
variables = { N = "42" }      # optional; configuration variable $N = 42
```

Every path is relative to the manifest's directory and must stay inside it.
Unknown keys, values of the wrong type, duplicate or empty program ids,
and a program with both or neither of `file` and `text` are errors that name the key or the program id.

Defaults:

| Key | Default | Note |
| --- | --- | --- |
| `spec.syntax_module` | none | k-rust then uses `<main_module>-SYNTAX` if it exists, else the main module (a kompile warning). |
| `spec.include_dirs` | `["."]` | The manifest's directory. |
| `spec.md_selector` | `"k"` | |
| `budget.time_ms` | `10000` | Wall-clock bound of one program run; must be positive. |
| `budget.max_depth` | `100000` | Rewrite-depth bound of one program run; must be positive. A run is never unbounded. |
| `program.start_sort` | the sort of `$PGM` | |
| `program.variables` | none | Every configuration variable other than `$PGM` must be given; streams default to empty. |

The tool supplies everything else: the k-rust revision is the build's (`kink_native::K_RUST_REVISION`, printed in every output),
and the below-floor conformance cases (kink-corpus `BELOW_FLOOR`) are refused for the entry and for every file the load reads.

## `kink-flow check FLOW.toml`

Admits the specification through kink-corpus's admission stages, with the same stage names and refusal reasons:
`manifest` (this crate: the manifest does not decode), `exclusion`, `load`, `semantic-input`, `compile`,
`representation`, `declaration-census` and `inputs`.
Then each program is admitted on its own (file read: stage `load`; parse: `inputs`/`parse`;
other assembly failures: `inputs`/`assemble`; the concrete-state check and the input gate: `inputs`/`input-gate`).
A refused specification skips the programs; a refused program never stops the others.

It prints one JSON document:

```json
{"schema": "kink-flow-check", "version": 1, "k_rust_revision": "...", "profile": "no-z3",
 "spec": {"outcome": "admitted", "stage": null, "reason": null, "detail": null,
          "files": [{"name": "calc.k", "sha256": "..."}]},
 "programs": [{"id": "add", "outcome": "ok", "stage": null, "reason": null, "detail": null}]}
```

Exit status: 0 when the specification is admitted and every program is ok;
1 when the manifest, the specification or a program is refused; 2 on a usage error (message on stderr).

## `kink-flow results FLOW.toml [--verify] [--mutations MUTATIONS.toml] [--cache DIR]`

Runs every program whose result is not cached yet and reports, per program, whether it can
kill a mutant, and, per rule of the specification, which programs reach it.

Each program runs on the baseline as its own zero-mutant campaign (kink-campaign's runner),
with two fixed oracles: the exit stop (no exit-code cell) and the whole final configuration.
A program's class is

| Class | Meaning | What to do |
| --- | --- | --- |
| `comparable` | The run ended and its final configuration is a value kink compares. | Nothing: this program can kill mutants. |
| `timeout` | The run did not end within `budget.time_ms`; `cause` gives what k-rust returned when the bound fired (see below). | Make the program terminate, or raise the budget. |
| `unknown` | The run ended without a comparable value (for example a collection with a Bytes key, `budget.max_depth` reached, an undecided step); `cause` says which. | Write a program whose final configuration kink can compare. |
| `refused` | The program was not read, parsed or assembled; `cause` is the refusal. | Fix the program. |
| `error` | The run or the runner failed. | Report it. |

Only comparable programs can kill a mutant; the others are reported and never count as covering a rule.

The cache is `.kink-flow/` next to `FLOW.toml` (or `--cache DIR`); deleting it is always safe.
One JSON record per program, `results/<spec digest>/<program digest>.json`, holds its key
(result schema version `kink-flow/result/v3`, the two digests and the budget), class and cause,
the baseline row exactly as the campaign report encodes it with the digest of its `run` part
(`run_sha256`, comparable programs only), the final configuration as KORE text, the rule
coverage, and `wall_ms`, the wall time of the program's live baseline run (outside the key and
the run digest; it orders the kill search, see `run`). The specification digest covers the k-rust revision, the solver profile, how the
specification is loaded and every source file the load reads; the program digest covers the
program's bytes, start sort and variables, never its id. A record is used only when its key is
the current key, so editing a program reruns that program, and editing the specification,
the budget or kink's result schema reruns everything.

Within one command each program's baseline runs at most once: every campaign call of the command
(the zero-mutant campaigns here, the kill search's calls in `run`) goes through one in-memory
baseline session (kink-campaign `BaselineSession`), which reuses a baseline run this command made
live for a later request with the same program, oracles, module and budget. Nothing of it is
written to disk, so every command runs the baselines it needs live again; the document's
`baseline_runs: {live, reused, diagnostic}` counts them (outside every digest and key).

When the zero-mutant campaign refuses a baseline, the class and the cause come from this command's
live run of it if that run stopped on time: the class is `timeout` and the cause continues with the
run's leaf census, read from what k-rust returned when the bound fired, for example
`the run did not finish within time_ms = 500; when the bound fired k-rust returned 1 leaf
(cancelled 1), the deepest at depth 17407; those leaves had applied 1 of the 5 rules a run can
observe` (or `k-rust returned no leaves, ...` when it returned none). Many ended leaves and a shallow
deepest leaf suggest path explosion; few leaves and a deep one non-termination. No second run is
made. For any other refusal (an `unknown` or `error` run) one diagnostic run of the initial state
supplies the class, the cause, the final states and the coverage (`diagnostic` counts them). Only
the campaign admitting a baseline makes a program `comparable`.

`--verify` reruns every program that has a current record and compares: a different class,
a different `run_sha256`, or a record whose `run_sha256` is not the digest of its own baseline
row is a mismatch. Mismatches are listed (program, record path, detail) and records are never
rewritten by `--verify`; delete a mismatching record (or the cache) to recompute it.

The document lists every program `{id, digest, class, cause, cached, verify, wall_ms}`, every authored
rule `{module, index, label, file, start_line, end_line, status, reached_by}` with status
`uncovered` (no comparable program reaches it: the next program to write) first, then
`covered`, then `not-observable` (equations: a run's trace names rewrite steps only), the
mismatches, a summary, `baseline_runs` (`results --verify` runs every program live:
`live` is the number of programs, `reused` 0) and `untargeted_rules`.

`untargeted_rules` is the mutation-side analogue of rule coverage: with `--mutations MUTATIONS.toml`,
every authored rule that no mutation of that list targets (only mutations that resolve count; an
`invalid-mutation` targets nothing), in sentence order, as `{module, index, label, file, start_line,
end_line, address, text}`: `address` is how an edit can address the rule (`{"rule": label}`, or
`{"file", "line"}` for an unlabelled rule) and `text` its K text. Without `--mutations` it is null; a
list that does not decode gives `mutation_list: {outcome: "refused", detail}` and exit 1. It is
informational only, outside every digest and key.

Exit status: 0 when the command did its job (timeouts and unknown programs included);
1 when the manifest, the specification or a program is refused, a run failed, a record could
not be written or `--verify` found a mismatch; 2 on a usage error.

## `MUTATIONS.toml`

A mutation is one or more text edits of the specification's rules, applied together or not at all
(several edits make a correlated mutation):

```toml
[[mutation]]
id = "add-becomes-sub"
note = "addition evaluates as subtraction"   # optional, free text

  [[mutation.edit]]
  file = "calc.k"            # optional when the spec reads one file, or when rule is given
  rule = "add"               # optional: a rule label, bare ("add") or module-qualified ("CALC.add")
  line = 21                  # optional: any line inside the rule
  find = "I1 +Int I2"        # exact text, exactly once in the addressed rule
  replace = "I1 -Int I2"

  [[mutation.edit]]          # a second edit of the same mutation
  rule = "CALC.mul"
  delete = true              # removes the addressed rule
```

An edit has `find` and `replace` (`find` non-empty, `replace` may be empty), or `delete = true` (which needs `rule` or `line`).
With neither `rule` nor `line`, `find` must occur exactly once in the file, inside one rule.
A label is `MODULE.x` or the bare `x` for both of K's label forms: k-rust stores `rule [x]:` as `MODULE.x`
and `[label(x)]` as the bare `x`, and either input addresses either form in module `MODULE`
(a label that matches several rules is `ambiguous-label`).
Unknown keys, values of the wrong type, duplicate or empty ids and a mutation without edits are errors naming the key.
`testdata/flow/calc/MUTATIONS.toml`, `testdata/flow/register/MUTATIONS.toml` and `testdata/flow/markdown/MUTATIONS.toml` are complete examples.

### Markdown sources: the K view

Every text an edit addresses, every occurrence count, every line and every rule text the report shows
is in the file's **K view**, the text k-rust parsed: a `.k` file's text, or for a `.md` file the extraction
of the fences `spec.md_selector` selects, in which prose and fence lines are whitespace.
Lines are the Markdown file's lines and columns on code lines are its columns, so `line` is the line an editor shows;
a `find` that occurs only in prose is `find-not-found`, and `before`/`after` are K text.
kink-flow never edits the Markdown file: the edits apply to the K view, and the edited view is loaded as a new
Markdown text with one fence around it (the envelope), which k-rust's extractor must turn back into the edited view.
`testdata/flow/markdown/spec.md` is a literate example, and `spec-view.k` beside it is its K view written as a `.k` file.

Resolution (`kink_flow::mutation::resolve`) builds the K view of each source file it touches and checks it against
the baseline's source table (the loaded definition must hold that extraction of the file), addresses every edit to one
authored rule (a rule's span is its offset attributes, which must name the same text as its location),
applies the edits to the views (a delete removes the rule's text: a one-line rule keeps its line, a rule over several lines leaves one, so later sentences move up; only their `Location` changes), loads the edited views with the
specification's load options, and checks that the edited load has the baseline's modules and sentences, in order and
with equal fingerprints, except at the addressed rules: a replaced rule is still exactly one rule sentence with the
same label, a deleted rule is gone. In every edited file each sentence must also start where the edits move it, and
end there too unless it is a replaced rule (which may end earlier by whitespace only), so an edit cannot rewrite the
text of a neighbouring sentence even into an equal one. The edited rules then become one pinned kink-patch `Patch`
(`ReplaceSentence`, `DeleteSentence`) whose digest is the mutation's identity; the mutant is always the patched
baseline, never the edited load. Only rules are editable.

A mutation that fails any check is `invalid-mutation`, with the offending edit (`edit[i]`) when one is at fault,
a reason and a detail; it is never compiled. Reasons:

| Reason | Meaning |
| --- | --- |
| `unknown-file` | `file` is not a source file of the specification. |
| `file-required` | The specification reads several files and the edit names neither `file` nor `rule`. |
| `unknown-label` | No rule has the label. |
| `ambiguous-label` | The bare label names rules of several modules; write `MODULE.label`. |
| `line-outside-rules` | No sentence covers the line. |
| `line-ambiguous` | Several rules share the line; address one by `rule`. |
| `address-mismatch` | `rule`, `line` and `file` name different rules. |
| `non-rule-sentence` | The edit addresses a syntax declaration, configuration or other non-rule sentence. |
| `find-not-found` | `find` does not occur where the edit looks. |
| `find-ambiguous` | `find` occurs more than once there; make it longer. |
| `edit-outside-rule` | `find` occurs in the file but not inside the addressed rule (or inside no rule). |
| `overlapping-edits` | Two edits of one rule overlap, or a deleted rule is also edited. |
| `source-changed` | A source file changed since the specification was loaded. |
| `source-view-mismatch` | The file's K view is not what k-rust parsed: for a `.md` file, the view under `md_selector` differs from the extraction of the same bytes under the selector the load used (for example `md_selector` changed since the load); or the loaded definition holds no such extraction of the file; or an addressed rule's spans index another one. Since k-rust 501f18b9 every extraction's offset map is the identity, so only the text comparison tells two selectors' views apart. |
| `markdown-envelope` | A Markdown file's edited K view cannot be loaded as K text: an edit makes a line a Markdown fence line (three or more backticks or tildes after at most three spaces), or the envelope does not extract to the edited view. |
| `edited-load-failed` | The edited sources do not load (parse or sort error); the detail is k-rust's message. |
| `structure-changed` | The edit changed something besides its rule: a sentence split, merged, added, removed, changed kind or changed elsewhere. |
| `span-changed` | In an edited file a sentence does not start (or, unless it is the replaced rule, end) where the edits move it: the edit's text reaches past its rule: a replacement that ends in a comment, or one that comments out a neighbouring rule and writes a copy of it. |
| `label-changed` | The edit changes the rule's label. |
| `no-change` | The edited rule equals the original up to formatting. |
| `no-usable-span`, `patch-rejected` | Defensive: a rule's offsets and location name different text of its K view, or kink-patch refused the patch; not expected on rules k-rust loaded. |

## `kink-flow run FLOW.toml MUTATIONS.toml [--only ID]... [--verify] [--order cost|corpus] [--cache DIR]`

Runs the kill search: for each mutation of the list (in file order; with `--only`, only the named ones),
is there a program of the corpus whose result the mutation changes?

1. The result cache is brought up to date first (`results` without `--verify`).
   Only `comparable` programs can kill; the others are never run.
   A program whose cached record (one read from the cache, not computed by this command) is class `timeout` and that a killer hint names
   is run once more (a timeout depends on the host's load):
   its record is replaced only when the class or the run digest changes, and the row says `"rerun": "timeout"`.
2. The mutation is resolved into one patch (see `MUTATIONS.toml`); an `invalid-mutation` stops there.
3. The programs are ordered (O): those whose cached coverage reaches an edited rule first, then the rest;
   inside each group cheapest first, by the result record's `wall_ms` (the program's baseline run time), then the manifest's order
   (`--order corpus`: the manifest's order only, F-05's order, for a reproducible search).
   Under the cost order the measured times decide, so the killer found first (and hinted) and the set of outcomes cached
   (first-kill caches nothing for the programs after the kill) can differ between hosts and runs; the content of every
   cached outcome cannot, and with `--order corpus` the outcomes and hints written are reproducible byte for byte.
   The order never changes a status: a kill outranks every other outcome under first-kill, and a mutant that fails as a whole
   fails before any program runs; it changes which killing program is found first (the reported killer and the hint) and the cost.
   Existing hints are kept; deleting `hints.json` and `outcomes/` re-runs the cold searches in the new order.
4. **Outcome cache, tier 1.** Each program of O may have a cached outcome for this mutation: `killed` (a proved difference) or `agree`.
   A cached outcome is used only when its key is exactly the current one (see "The cache directory" below) and the program's
   current result record has the baseline run digest the outcome was compared with.
   If some program has a cached `killed` outcome, the status is `killed` (its killer the first such program in O), with no compile and no run.
   Otherwise the programs with a cached `agree` outcome are not run again; if every program has one, the status is `survived`, with no run.
5. **Killer hint, tier 2.** If programs remain and the hint names one of them (by program digest, so a renamed program keeps its hint),
   the mutant runs on that program alone. If it kills, that is the verdict.
   Otherwise the mutant runs on every remaining program in the order of step 3, the hinted one included.
6. Every status is the one kink-campaign's own fold (`derive_mutant_report`, schedule first-kill) gives over the cached outcomes
   followed by the last runner call's tests. kink-flow compares no terms; only a proved difference of the exit stop or the
   whole final configuration kills, live in this command or cached under an exactly matching key.
   A cached agreement is the fold's bottom, so the status is the one a run without any cache gives.
7. Each program's baseline runs live at most once per command: the result update and every runner call share one
   in-memory baseline session, so a program the update ran, or an earlier call ran, is not run again on the baseline;
   its live run of this command is reused where the runner produces baseline evidence (`baseline_runs` counts both).
   After every runner call, each program's baseline run is checked against its cached result (`run_sha256`).
   A difference is a corpus error: the mutation gets status `error` with reason `baseline-mismatch:<program id>`
   (or `baseline-count-mismatch`), nothing is cached for it, and the run stops (exit 1). Run `results --verify`.
   A cached agreement next to a mutant that no longer compiles is the corpus error `outcome-conflict`: run `run --verify`.
   A mutant that fails as a whole for an infrastructure reason (`reason` `infrastructure`: the equivalence check or the
   mutant's backend failed while it was prepared) is not a conflict: its status is `error`, as without any cache, and its
   cached agreements are left out of the row and the counts.
8. After a verdict, every live program outcome that is `killed` or `agree` is cached; a timeout, an unknown, an error,
   a failed or skipped run, and every outcome of a call whose mutant failed as a whole are never cached.
   A `killed` mutation's first killing program becomes its hint; any other status removes it, and so does a hint that names no comparable program.
   The hints file and the run document are written after every mutation (a corpus error included), so an interrupted run keeps its finished work.

**Trust.** With identical inputs, a cached proved difference stands without being re-run in this command.
This rests on k-rust's compile and execution determinism, on the key naming every input the outcome depends on,
and on the integrity of the cache directory: whoever can write `.kink-flow/` can forge a kill, as whoever can write the kink build can.
Each record carries a digest that detects corruption and a record moved under another key, not forgery.
`run --verify` re-proves: it updates the results with `--verify`, decides nothing from tier 1 and uses no hint,
runs every program of O on each mutation, then each program that has a cached outcome and that run skipped, alone,
and compares every cached outcome (and the status the cache would have given) with the live ones.
A difference gives the mutation status `error`, reason `outcome-mismatch:<program id>`, and an entry `{mutation, program, cached, live}`
in the top-level `mismatches` (`program` null for a status difference); the run goes on and exits 1. It writes no outcome and no hint.
Known gap at the k-rust pin: a result can depend on the stack of the loading or running thread and on other threads, because a
stop for lack of stack is dismissed silently in the load's discharge of rewrite-rule definedness (k-rust KINK-06/4) and in a
run's refinement of a result (KINK-06/5), for live and cached kills alike; `--verify` does not remove it. The re-pin (RP-01)
closes it by making a comparison unknown when either run reports a nonzero `stackStops` or the load of either definition a
nonzero `discharge_counts().stack_stops` or `value_claims().counts().condition_stack_stops` (root README, "Using kink-flow").

| Status | Meaning | What to do |
| --- | --- | --- |
| `killed` | A program's result differs on the mutant; `killer` names the first such program. | Nothing. |
| `survived` | Every program ran to a comparable result and agreed. | Write a program that reaches the edited rule and whose result the edit changes (`reaching` lists the programs that reach it now). |
| `equivalent` | The mutant compiles to the baseline's executable definition. | Nothing can kill it; drop or change the mutation. |
| `invalid` | The mutant does not compile (`reason` is the runner's failure, for example `rejected`). | Fix the mutation. |
| `timeout` | No program killed it, and a program did not finish on the mutant within `budget.time_ms`. | Write a program that terminates under the mutant and shows a different result. |
| `unknown` | No program killed it, and a program's result on the mutant is not comparable. | Write a program whose result on the mutant kink can compare. |
| `error` | The runner failed for the mutant, a corpus error (`reason`: `baseline-mismatch:<id>`, `baseline-count-mismatch`, `campaign-refused`, `program-refused:<id>`, `outcome-conflict`, `no-comparable-program`), or `run --verify` found a cached outcome that differs from a live run (`outcome-mismatch:<id>`). | Report it, or fix the corpus; for `outcome-mismatch`, delete `outcomes/`. |
| `invalid-mutation` | The mutation does not resolve (`reason`, `edit`, `detail`; see the table above). | Fix the mutation. |

A kill folds above every inconclusive outcome: a mutation that one program kills is `killed` even if an earlier program timed out on it.

The document is the report (see "The report: the run document" below).

### The cache directory

Besides `results/` and `report.json` (the last run's document, also written when the specification is refused or no mutation is selected):

- `outcomes/<context digest>/<mutation identity>.json`, tier 1:
  `{schema: "kink-flow-outcomes", version: 1, context, context_sha256, mutation_identity, mutation_id, records: {<program digest>: {program_id, baseline_run_sha256, outcome, slots, mutant_run_sha256, record_sha256}}}`.
  The context is `{outcome_schema: "kink-flow/outcome/v1", result_schema, kink_build, k_rust_revision, profile, execution_digest: {kind, digest}, budget, oracles, classifier, schedule}`:
  `kink_build` is the SHA-256 of the running `kink-flow` executable, so any rebuild (debug or release) starts a new context;
  `execution_digest` is today the specification digest (kind `kink-flow/spec/v1`), so any edit of the specification, a comment included, starts a new context.
  The mutation identity hashes each edit's kind, module, the addressed rule's fingerprint, its occurrence among equal fingerprints of the module,
  and the replacement's fingerprint: positions excluded, so it is the same after an edit that only moves the rule.
  `baseline_run_sha256` is the program's result `run_sha256` when the outcome was proved, and `mutant_run_sha256` the same digest of the mutant's evidence.
  A record is used only when the file's schema, version, context and identity are the current ones, its `record_sha256` recomputes,
  its outcome agrees with its slots (`killed` exactly when a slot is `distinguish`, `agree` exactly when both are `agree`),
  and its program is comparable with that baseline run digest; anything else is ignored.
  If the executable cannot be read, tier 1 is disabled for the command (`outcome_cache.reason` says why) and every mutation runs.
- `hints.json`, tier 2: `{schema: "kink-flow-hints", version: 1, hints: {<hint key>: {program_digest, program_id, mutation_id}}}`.
  The hint key hashes the mutation's edits as written (without `line`) and the K text of each addressed rule before the edit,
  so a hint survives edits elsewhere in the specification and is lost when the addressed rule's text changes.
  A hint is a scheduling hint only: it changes which killer is found first and the cost, never a status.

Every file is written atomically; deleting any of them, or the whole directory, is always safe.
The `killers/` directory of F-05 is no longer read or written and can be deleted.

Exit status: 0 when every selected mutation got its status (survivors, timeouts and invalid mutations included);
1 when the manifest, the mutation list, the specification or a program is refused, a run failed, a cache file could not be written,
no program is comparable, a corpus error stopped the run, or `--verify` found a mismatch; 2 on a usage error (including an `--only` id that names no mutation, or `--verify` given twice).

## The report: the run document

`run` prints one document and writes the same document to `.kink-flow/report.json` (after every mutation, and once more at the end):

`{schema: "kink-flow-run", version: 3, k_rust_revision, profile, result_schema_version, spec, programs, unusable_programs, mutations, counts, survivors, stopped, outcome_cache, mismatches, baseline_runs, order, untargeted_rules}`.
Version 3 (F-13) names the oracle slots of an executed entry; `report` refuses a document of another version.

| Field | Meaning |
| --- | --- |
| `spec` | `{outcome, stage, reason, detail, digest, files}`: the specification's admission and its digest. |
| `programs` | The `results` rows `{id, digest, class, cause, cached, verify, wall_ms}`, plus `rerun` for a timeout record run again. |
| `unusable_programs` | Every program whose class is not `comparable`, once: `{id, class, cause}`. These programs are never run on a mutant. |
| `mutations` | One row per selected mutation, in the list's order (below). |
| `counts` | The number of mutations per status (all eight statuses). |
| `survivors` | The ids of the mutations whose status is `survived`, `timeout` or `unknown`: no program killed them, and a new program could. |
| `stopped` | `null`, or `{mutation, reason}` of the corpus error that stopped the run. |
| `outcome_cache` | `{context_sha256, enabled, verify, reason, mutations_from_cache, programs_from_cache, records_written}`: tier 1's context (null when disabled), whether it decided statuses, whether this is `run --verify`, why not, the mutations decided with no call, the cached program outcomes used, and the records written (one per program, also when a hinted program ran in two calls). |
| `mismatches` | `run --verify`'s differences `{mutation, program, cached, live}`; empty otherwise. |
| `baseline_runs` | `{live, reused, diagnostic}`: the baseline runs this command made live (the result update's and the calls'), at most one per program, the baseline requests of its calls answered by one of them, and the diagnostic runs of refused baselines that did not stop on time; null when the specification is refused. Outside every digest and key. |
| `order` | `cost` or `corpus`: how the programs were ordered inside each group (step 3). |
| `untargeted_rules` | The rules no resolving mutation of the whole list targets (`--only` limits the search, not this list), as in `results --mutations`. |

A mutation row is `{id, note, digest, identity, status, reason, killer, killer_source, killer_from_cache, unusable_killer, reaching, executed, calls, call_wall_ms, rules, action}`:

| Field | Meaning |
| --- | --- |
| `digest` | The patch digest; null for an `invalid-mutation`, which also has `edit` (the offending edit's index or null) and `detail`. |
| `identity` | The mutation's position-free identity (tier 1's file name); null when it has none (the mutation then always runs). |
| `status`, `reason` | The status (see the run section) and the runner's or the flow's reason. |
| `killer`, `killer_source`, `killer_from_cache` | The first killing program of a `killed` mutation; where the kill came from: `outcome-cache` (tier 1, no call), `hint` (the hinted program's one-program call) or `search` (the call over the remaining programs); `killer_from_cache` is true for the first two. Null, null and false otherwise. |
| `unusable_killer` | `{program, class, cause, source}` when a cached kill (`source` `outcome-cache`) or the hint (`hint`) names a program of the corpus that is not comparable now; else null. |
| `reaching` | The comparable programs whose cached coverage reaches an edited rule, in the order they were tried. |
| `executed` | `{program, outcome, slots | failure, cause, cached, wall_ms, baseline_ms, baseline_reused}` for every program whose outcome decided the status: first the cached ones (`cached: true`, in the order of step 3), then each program the mutant ran on in this command, in the runner's order, each listed once (a hinted program that did not kill and ran again in the next call is listed with that later run; `calls` lists every call). `outcome` is `distinguish`, `agree`, `timeout`, `unknown`, `incomparable` or `error`; `failure` names a run that produced no value (`time-limit`, `resource-limit`, `indeterminate`, `infrastructure`). `slots` is below. `cause` is null when the outcome is `agree` or `distinguish`, else what the runner's evidence says stopped the comparison, per slot (`exit-stop, whole-term: ...`), with the budget values, followed by the mutant run's leaf census for a time limit (`; when the bound fired k-rust returned ...`) or an unknown or timed-out slot (`; the mutant's run: k-rust returned 1 leaf (depth-bound 1), the deepest at depth 200`), which tells a depth bound from an undecided end. `wall_ms` is the mutant's run of the program, `baseline_ms` the program's live baseline run in this command and `baseline_reused` whether this call reused it; all three are null on a cached entry. |
| `calls` | `{programs, status}` of each runner call: `[]` when tier 1 decided, `[[hint]]` when the hinted program killed, `[[hint], [rest]]` when it did not, `[[rest]]` without a usable hint. |
| `call_wall_ms` | The wall time of each call of `calls`, in the same order (the mutant's compile and every run of the call). |
| `rules` | Null for a `killed` mutation and for an `invalid-mutation`; otherwise each edited rule, in sentence order: `{module, index, file, label, start_line, end_line, edits, before, after}`. `before` and `after` are the rule's K text before and after the mutation's edits, sliced from the file's K view by the sentence's span (`after` is null for a deleted rule); `edits` are the indices of the mutation's edits addressed to the rule. |
| `action` | Null for `killed`; otherwise one sentence saying what the status asks (write a program, fix the mutation, fix the corpus, report it). |

`slots` is an object keyed by oracle slot, `exit-stop` and `whole-term`, each `{outcome}` (`agree`, `distinguish`, `timeout`, `unknown`, `incomparable`, `error`).
A distinguishing slot also has `sides`: for `exit-stop`, each side's exit-stop kinds, for example `{"baseline": ["normal"], "mutant": ["undefined-step"]}`
(the flow's classifier makes every ended run `normal`; `undefined-step` is a rule whose result is undefined, such as a division by zero);
for `whole-term`, each side's number of final configurations, `{"baseline": {"final_configurations": 1}, "mutant": {"final_configurations": 1, "kore": [{"text", "truncated"}]}}`,
where `kore`, on the killing program's entry only, holds the mutant's final configurations as KORE text, each cut to 4000 characters (`truncated: true` when cut).
A cached entry has no evidence at hand: its distinguishing slot has `sides: null`.
No timing, census or side value enters an evidence row, a digest, a key, an outcome record or a hint.

A row may also carry `stale_killer` (the hint named a program that is not comparable; it was removed) and `cache_error`.
The cause of an `unknown` slot names the possible reasons together (a path stopped at `max_depth`, an undecided end,
or a final configuration holding a collection kink cannot compare (for example one with a Bytes key), an unevaluated function or a symbolic term),
because the runner's evidence records that the mutant's value is unknown but not which of these stopped it; the leaf census that follows
(leaves per halt class: `depth-bound`, `stuck`, `indeterminate`, ...) usually says which.

## `kink-flow report FLOW.toml [--cache DIR]`

Prints the stored run document again, byte for byte as `run` printed it.
When there is none, or it is not a version-3 run document, it prints
`{schema: "kink-flow-report", version: 1, k_rust_revision, profile, outcome: "missing" | "unreadable", path, detail}`.

Exit status: 0 when it printed a report; 1 when there is none, it is unreadable, or the manifest does not decode; 2 on a usage error.
