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
report usability: named oracle slots, timings, leaf censuses in the causes of stopped runs, cheaper killers first, and the rules no mutation targets (flow F-13),
and per-input pattern checks with the `query` command (flow F-18; "Checking a pattern" below).

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
work_factor = 4               # optional; no work budget when absent

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
| `budget.time_ms` | `10000` | Wall-clock bound of one program run; must be positive. A run whose state set kink replaces by its path set (an undefined step, a vacuous leaf or a contradicted claim) is two runs, each with this bound, so it can take up to twice as long. |
| `budget.max_depth` | `100000` | Rewrite-depth bound of one program run; must be positive. A run is never unbounded. |
| `budget.work_factor` | absent | The work budget of a mutant's run of a program: at most `work_factor * W + 10000` states visited (k-rust `max_work`), where `W` is the states the program's baseline run visited; must be positive. A mutant that runs past it is `unknown` on that program, long before `time_ms` would stop it, unless the part it ran already holds a final configuration the baseline's program never ends in: then the program kills it one-sidedly (re-pin L1-2, decision 6; the root README, "What a kill trusts"). Absent: no work budget. It never bounds a baseline run. |
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
(result schema version `kink-flow/result/v4`, kink's build identity `kink_build`, kink's semantics identity `kink`, the two digests and the budget), class and cause,
the baseline row exactly as the campaign report encodes it with the digest of its `run` part
(`run_sha256`, comparable programs only), the final configuration as KORE text, the rule
coverage, and `wall_ms`, the wall time of the program's live baseline run (outside the key and
the run digest; it orders the kill search, see `run`).
`kink_build` is the SHA-256 of the executable that wrote the record (kink-campaign `identity::kink_build`, packet CACHE-ID-fix-1), so a record another build wrote, or one without `kink_build`, is recomputed: the code that decides a result class mostly has no version constant, and only the build tells that it changed.
When the executable cannot be read, no record is read or written, and each row says so (`cache_error`).
The specification digest covers the k-rust revision, the solver profile, how the
specification is loaded and every source file the load reads; the program digest covers the
program's bytes, start sort and variables, never its id. A record is used only when its key is
the current key, so editing a program reruns that program, and editing the specification,
the budget or kink's result schema reruns everything. So does a kink build with another semantics
identity (packet CACHE-ID): the identity (kink-campaign `identity`) names every kink algorithm a
program's class can depend on (the definition exclusions, the execution request, ...), and a
record written by a build before CACHE-ID has no `kink` in its key, so it is recomputed.

Within one command each program's baseline runs at most once: every campaign call of the command
(the zero-mutant campaigns here, the kill search's calls in `run`) goes through one in-memory
baseline session (kink-campaign `BaselineSession`), which reuses a baseline run this command made
live for a later request with the same program, oracles, module and budget. Nothing of it is
written to disk, so every command runs the baselines it needs live again; the document's
`baseline_runs: {live, reused, diagnostic}` counts them (outside every digest and key).

When the zero-mutant campaign refuses a baseline, the class and the cause come from this command's
live run of it if that run stopped on time: the class is `timeout` and the cause continues with the
run's leaf census. k-rust answers a cancelled run with an error and returns no leaves (re-pin L1-1,
`cancelled_result: error`), so the census reads `the run did not finish within time_ms = 500; when
the bound fired k-rust returned no leaves, so neither the paths nor the depth reached are known`; a
census with leaves, depths and applied rules is given for runs that ended otherwise (a depth bound,
a work bound, an undecided end). No second run is
made. For any other refusal (an `unknown` or `error` run) one diagnostic run of the initial state
supplies the class, the cause, the final states and the coverage (`diagnostic` counts them). Only
the campaign admitting a baseline makes a program `comparable`.

`--verify` reruns every program that has a current record and compares: a different class,
a different `run_sha256`, or a record whose `run_sha256` is not the digest of its own baseline
row is a mismatch. Mismatches are listed (program, record path, detail) and records are never
rewritten by `--verify`; delete a mismatching record (or the cache) to recompute it.

The document (version 2 since re-pin L2-1) lists every program `{id, digest, class, cause, cached, verify, wall_ms}`, every authored
rule `{module, index, label, file, start_line, end_line, status, reached_by, fired_by}` with status
`uncovered` (no comparable program reaches it: the next program to write) first, then
`covered`, then `no-coverage-signal` (none of the rule's compiled ids can appear in a run's coverage: it
compiles to no axiom, or it is a `non-executable`, macro, alias or `smt-lemma` rule; `reason` says which), the
mismatches, a summary, `baseline_runs` (`results --verify` runs every program live:
`live` is the number of programs, `reused` 0) and `untargeted_rules`.

A rule's coverage is k-rust's run coverage of each comparable program's baseline run (kink-native
`coverage`, `kink/coverage/v2` since re-pin L2-1, v3 since L2-1-tail), rewrite rules and equations alike: `reached_by` lists the
programs that began to decide one of the rule's conditions for an instance whose left-hand side matched, or
applied it (k-rust `matched`), and `fired_by` those that applied it (`applied`: a rewrite step built a successor,
or an equation's instance gave a result). Neither is an over-approximation of what can change a result: a
higher-priority rule whose left-hand side never matched is not reached, although its failure is what lets a
lower-priority or `owise` rule fire. The record holds the reached and fired sentences (`coverage.sentences`,
`coverage.applied_sentences`).
A `non-executable` rule is one k-rust never runs (it internalizes executable axioms only), so no program can reach it:
since re-pin L2-1-tail it has status `no-coverage-signal` with reason `a non-executable rule: k-rust never runs it, so no
program can reach it`, never `uncovered`; before, it was listed `uncovered`, as a next program to write.

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
baseline, never the edited load. Only rules are editable. Every program runs on that mutant without the trusted claims
the edit leaves unbacked (re-pin R0c-fix-2; root README, "What a kill trusts"): the `total` and other claims of every
function whose equations reach an edited equation, the lemmas about them and the `preserves-definedness` of the rules
that apply them. A mutation whose edit leaves a claim no removal takes away (for example a replacement that writes a
claim, or edits a lemma or an equation's `ensures`) is `unknown` with reason `unsupported-claims`; one whose claim-free
mutant does not compile is `unknown` with reason `stripped-claim-compile-failure`. The claim-free mutant must also be a
theory with models (re-pin R0c-fix-3): a mutation that makes two equations of one function apply to one input with
different values, or whose pairs of equations k-rust's critical-pair check does not show to join, is `invalid` with
reason `inconsistent-mutant`, and its row's `inconsistent_pairs` names the pairs. The functions whose pairs are read
are those whose compiled equations the edit changes or reaches (a `#let` or `#fun` lambda included), with kink-patch's
source reading as a fail-closed cross-check (re-pin R0c-fix-4): a sentence the edit touches that compiles to an
equation of a function the source reading does not redefine makes the mutation `unknown` with reason
`unsupported-claims`, and the row's `removed_claims.unsupported` names each such equation (key `unread-equation`,
value `{head, equation}`; re-pin R0-tail).

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
| `edited-rule-too-deep` | An edited rule is too deep for kink: its patch's document would nest deeper than kink-patch `MAX_JSON_DEPTH` (two JSON levels per term level: terms about 300,000 levels deep in a release build, 64,000 in the unoptimized test build), so the mutation has no encoding and no identity. This is kink's limit, not a fault of the mutation. A patch holds each edited rule whole, so the detail gives the rule's depth as a whole and the specification's rule's: when the specification's rule alone is already past the limit, it says that no mutation that keeps the rule's deep part can be judged in this build (target other rules, or replace the deep part by a shallow one; re-pin L1-4); otherwise a mutation that keeps the whole rule within about half the limit in term levels is judged (re-pin L1-3-tail). Below the limit a rule's depth decides nothing: its typing and its patch's encoding run on a stack sized from that depth, on any thread (re-pin L1-3-fix-2; before, a rule about 230,000 terms deep aborted the whole run in typing). |
| `host-stack-refused` (status `error`) | The host refused the native stack that encoding the mutation's patch needs: the system would not map a stack segment of the size the patch's depth needs (an address-space limit such as `ulimit -v`, or memory it will not commit). It is the host's limit, neither a fault of the mutation nor a verdict, so the row is `error`, not `invalid-mutation`; rerun where the host grants the stack. Only a deep patch needs a segment: the segment is sized from the patch's own document depth (re-pin L1-3-tail; at L1-3-fix-2 every patch more than 48 term levels deep took a segment sized for `MAX_JSON_DEPTH`, 768 MB in release, and a refusal was reported as `patch-rejected`). |
| `no-usable-span`, `patch-rejected` | Defensive: a rule's offsets and location name different text of its K view, or kink-patch refused the patch for a reason other than typing (a stale pin, a patch that does not resolve); not expected on rules k-rust loaded. No typing error refuses a mutation (re-pin L2-2-fix-1): a mutant is valid when it compiles, so compilation decides, and kink-patch records the edited rules' errors in compilation's typing view (`SentenceTyper::for_compilation` with `typing_in`) as the row's `typing_diagnostics`. k-rust documents that view's errors as errors compilation stops at, but at 501f18b9 it refuses shapes compilation accepts: a local function with a variable in a cell with children (`CellCompletion`), and a rule `a(X) => b(X)` whose sorts `A` and `B` have a second common supersort in the main module (a non-unique least upper bound). |

## `kink-flow run FLOW.toml MUTATIONS.toml [--only ID]... [--verify] [--order cost|corpus] [--compile-workers N] [--no-memo] [--cache DIR]`

Runs the kill search: for each mutation of the list (in file order; with `--only`, only the named ones),
is there a program of the corpus whose result the mutation changes?

1. The result cache is brought up to date first (`results` without `--verify`).
   Only `comparable` programs can kill; the others are never run.
   A program whose cached record (one read from the cache, not computed by this command) is class `timeout` and that a killer hint names
   is run once more (a timeout depends on the host's load):
   its record is replaced only when the class or the run digest changes, and the row says `"rerun": "timeout"`.
2. The mutation is resolved into one patch (see `MUTATIONS.toml`); an `invalid-mutation` stops there.
3. The programs are ordered (O): those whose cached coverage witnesses an edited rule's edit (rewrite rule or equation) first, then the rest.
   An edit that changes the rule's `requires` is witnessed by a program that reached the rule (k-rust `matched`: it began to decide the condition); every other edit (a right-hand side, an `ensures`, a left-hand side, an attribute, a deletion) by one that fired it (`applied`), since a program that only refuted the rule's guard never runs what the rule does (re-pin L2-1-tail).
   The edit is read from the rule's text before and after it, before the mutant compiles, so this is kink-campaign's reading of a site-local edit (README.md, trust section), except that an equation edit kink-campaign leaves in manifest order (its left-hand side, an attribute, an `owise`, `smt-lemma`, `concrete` or `symbolic` equation, a deleted equation) still puts first the programs that fired the equation, or reached it for a `requires` edit, and that a rewrite rule edit changing the `requires` together with the left-hand side or an attribute is witnessed by `matched` here and by `applied` in kink-campaign (review L2-1-tail-1 D3);
   inside each group cheapest first, by the result record's `wall_ms` (the program's baseline run time), then the manifest's order
   (`--order corpus`: the manifest's order only, F-05's order, for a reproducible search).
   Under the cost order the measured times decide, so the killer found first (and hinted) and the set of outcomes cached
   (first-kill caches nothing for the programs after the kill) can differ between hosts and runs; the content of every
   cached outcome cannot, and with `--order corpus` the outcomes and hints written are reproducible byte for byte.
   In the no-Z3 profile (the default build), while no `budget.time_ms` bound fires, the order never changes a status: a kill outranks every other outcome under first-kill, and a mutant that fails as a whole
   fails before any program runs; it changes which killing program is found first (the reported killer and the hint) and the cost.
   That needs each program's outcome to be independent of the programs run before it in the same call. Under Z3 it is not: a solver query can time out, and the mutant's backend, reused for every program of a call, caches satisfiability answers, so the order can move a status between `killed`, `unknown` and `survived`: a timed-out query makes a program `unknown`, and an answer an earlier program cached can turn it into a kill or an agreement, so with no kill the status is `survived` in one order and `unknown` in the other (never a false kill: a kill is still a proved difference); tier 1 is off under Z3 for the same reason. A run near its `budget.time_ms` bound can likewise time out in one order, while caches are cold, and finish in another, in either profile; a `timeout` is host- and timing-dependent anyway (review L2-1-tail-1 D1, D2).
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

**Compile workers.** `--compile-workers N` (4 by default) compiles mutants ahead of their turn on up to N threads, capped at the host's parallelism and at half the process's memory allowance, counting for each worker one compile in flight and the at most 8 compiled mutants it keeps (kink-native `NativeValidator::compile_workers`; re-pin L1-3, L1-3-fix-1).
The mutations are taken in chunks of 4 N; for each chunk the mutants of the mutations that would make a live call given the stores at the chunk's start (each mutant and, when claims are removed, its claim-free definition) are compiled, every worker is joined, and then the chunk's mutations run exactly as with one worker, one at a time in list order, every load, consistency check and execution on the calling thread.
A worker thread runs only two steps: relinking an applied mutant and compiling it, which k-rust documents as independent of the thread; each patch is applied (and its edited rules typed, a recursion with no stack guard) on the calling thread, before the workers start (review L1-3-1 D1).
A mutant compiled ahead is the mutant its call would compile (k-rust documents relinking and compiling, and nothing after them, as independent of the thread: `docs/compatibility.md`, "Concurrency"); a refused or panicking patch or compile is not kept, so its call applies and compiles it again on the calling thread.
A guess that a mutation would call costs a compile when it does not, and the call compiles as usual when it does not guess, so no row, outcome, hint or report depends on N (`tests/compile_workers.rs`, cold and warm, 1, 2 and 4 workers).
On `examples/imp`, cold, mutant compiles are about 28 % of the run's wall time; a warm run, which tier 1 decides, compiles nothing.

**Memos (re-pin L1-4).** A run does once, or not at all, what is a function of inputs that did not change (kink-flow `memo`):
- The specification's baseline compiles once per command: program inputs are assembled with the admission's compile (kink-corpus `assemble_input_with`), where each program bound a fresh validator and compiled the baseline again (49 of the 81 baseline compiles of the flow lists cold).
- The resolution memo, `memo/resolutions/<spec digest>/<entry digest>.json`, holds per mutation the facts of its resolution a row decided by tier 1 reads: the patch digest, the edited rules (texts, lines, label, whether the `requires` changed), the tier-1 mutation identity, the typing diagnostics and the claims the edit leaves unbacked. A mutation whose record has exactly the current key and that tier 1 decides with no call (a valid `killed` record, or a valid `agree` for every program of O, or no comparable program) is not resolved: its row is built from the facts by the code that builds it from a live resolution. Every other mutation is resolved live and its facts are written, so every mutation that compiles or runs anything was resolved in this command; the record holds no patch (the patch's canonical JSON does not carry k-rust's term metadata, so a decoded patch would not be the one resolution builds). The key names every input resolution reads: the specification digest (the k-rust revision, the profile, how the specification is loaded and every source file's name and SHA-256: resolution reads the admitted load, each touched file's bytes checked against that SHA-256, and an edited load of the same files under the same options), the mutation's edits in order with every field (`file`, `rule`, `line`, `find`/`replace` or `delete`; the id only names the row and the note is never read), `kink_build` and `kink`. Records are read only while every source file still has the SHA-256 the admission recorded. A typing diagnostic that says a rule was not typed (a refused stack segment) depends on the host, so facts that carry one are never written.
- The census memo, `memo/census/<spec digest>.json`, holds the declaration census of the admission (the VI-T13 gate), a function of the compiled baseline and of kink's build (its reference prelude and hooks), keyed on the specification digest, `kink_build` and `kink`.

The premises are those the result cache and tier 1 already rest on: k-rust's load and compile are deterministic (the same files under the same options give the same definition, C-12), and the key names every input (`tests/memo.rs` pins each field of a mutation's edits: a key differs when any one field differs, it decodes back to the edits, and two mutations that differ in one field never share a record; it builds both keys member by member, the version, kink's build and semantics identity, the specification digest and the edits, and requires them equal to `memo`'s, and `tests/results.rs` requires the specification digest to change with each `[spec]` field, so a key that drops an input fails a test; re-pin L1-4-tail). Before any resolution record is read, every source file must still have the SHA-256 the admission recorded, so a file changed between the admission and resolution reads no record (`tests/memo.rs` changes one there). One premise is new, the host premise: a record exists only because resolution succeeded on the host that wrote it, and success can depend on the host (the native stack segment of the patch's encoding, which live gives `host-stack-refused`; the heap and address space of the edited load, which live aborts the process when exhausted; and the native stack segment each edited rule is typed on, which a host can refuse while it grants the encoding's, and which live gives a typing diagnostic saying the rule was not typed, with the row's status unchanged). The key does not name the host's capacity: a memo hit returns the tier-1-decided row that a host which could resolve the mutation computed for the same mutant identity, where live resolution on a smaller host would end `host-stack-refused`, abort, or give the same row with a typing diagnostic saying the rule was not typed where the memo gives the writer's typing diagnostics (re-pin L1-4-tail). That cannot make a false kill or hide a survivor (the mutant is judged where the host grants the stack, as this README recommends for `host-stack-refused`, and typing diagnostics decide nothing), but before L1-4 every resolution was recomputed in every command. So run documents with and without memos are equal on hosts that grant the stack and heap resolution needs. The memos are off where tier 1 is (the Z3 profile, an unreadable executable) and with `--no-memo`. `run --verify` decides nothing from a memo: it resolves every mutation and runs the census live, compares each record that has the current key, reports one that differs (the row's status `error`, reason `resolution-mismatch`, and an entry `{mutation, program: null, cached: {resolution}, live: {resolution}}` in `mismatches`, also for a mutation `--only` does not select or that a corpus error left unsearched, which has no row; a census, `{mutation: null, program: null, cached: {census}, live: {census}}`, also when the live census refuses the specification, so a stored census that admits a specification the live census refuses is reported in the refused document) and writes no memo. A memo never enters the run document, an outcome record or a hint: on such a host a run with and without memos writes the same ones (`tests/memo.rs`, cold and warm, with every status and a Markdown source; each key input changed, a forged record under the current key used and reported by `--verify`, in both directions for the census). A memo that cannot be written only means a later recomputation, so it is not reported.

### Cost model

Where a run's wall time goes (release build, `--order corpus`, 4 compile workers; re-pin L1-3 and L1-4 measurements, shared 32-core host at load 15-35):

| Stage | Cost | Cold | Warm (tier 1 decides) |
| --- | --- | --- | --- |
| Admission: load | one load of the specification and the prelude, about 0.12 s on `examples/imp` | once | once |
| Admission: baseline compile | about 0.22 s on `examples/imp` | once per command (before L1-4: once more per program run live) | once |
| Admission: declaration census | 0.52 s, of which its reference prelude's compile 0.22 s | once | read from the census memo |
| Resolution | one full load per mutation (0.11-0.15 s on `examples/imp`: the definition's every rule bubble is parsed again) | every mutation | only mutations tier 1 does not decide; the rest read the resolution memo |
| Result update | each new or changed program's baseline run | new programs | nothing |
| Kill search | per live call: the mutant's compile (compiled ahead on the workers), its backend, the consistency check and every program run | every mutation | nothing, or the mutations tier 1 does not decide |

On `examples/imp` (21 mutations, 7 programs) a warm run took 3.8-7.2 s before L1-4 (median 5.1 s over 7 interleaved rounds), 70-75 % of it resolution and 20-25 % admission, and takes 0.4-1.9 s since (median 0.5 s), nearly all of it the admission's load and compile. A cold run saves about 1.5 s, the 7 baseline compiles of its program inputs, which is within run-to-run noise on a shared host (medians 18.0 s before and 16.3 s since over the same 7 rounds). The 16 flow lists warm take 30-40 s before L1-4 and 10-14 s since; cold, the 49 program-input compiles they no longer make cost about 12 s of 47.3-93.3 s (the sum of the 16 lists' walls, over every cold run of main and of L1-4 with memos; single runs on a loaded host), again of the order of the host's noise (L1-4 and L1-4-fix-1 handoffs and both L1-4 reviews). A mutation the LLM adds, or one whose programs changed, costs its own resolution and calls only: a cold mutation still pays one full load.

**Trust.** With identical inputs, a cached proved difference stands without being re-run in this command.
This rests on k-rust's compile and execution determinism, on the key naming every input the outcome depends on,
and on the integrity of the cache directory: whoever can write `.kink-flow/` can forge a kill, as whoever can write the kink build can.
Each record carries a digest that detects corruption and a record moved under another key, not forgery.
`run --verify` re-proves: it updates the results with `--verify`, decides nothing from tier 1 or the memos and uses no hint,
runs every program of O on each mutation, then each program that has a cached outcome and that run skipped, alone,
and compares every cached outcome (and the status the cache would have given) with the live ones.
A difference gives the mutation status `error`, reason `outcome-mismatch:<program id>`, and an entry `{mutation, program, cached, live}`
in the top-level `mismatches` (`program` null for a status difference); the run goes on and exits 1. It writes no outcome and no hint.
The Execute promise of k-rust (`docs/compatibility.md`, "Execute") is what makes an outcome a function of its key, and it
excludes some runs; each is excluded for the whole program (both sides, both slots) before a record could be written: a
cancelled run is a timeout; kink sets no step timeout; a run with a nonzero `stackStops`, a run on a definition whose load
counted a stack stop (`discharge_counts().stack_stops`, `value_claims().counts().condition_stack_stops`) and a run with a Bytes
hook refused for the memory allowance are `unknown` (failure `stack-stop`, `load-stack-stop`, `allowance-refusal`; on the
baseline the program is not comparable); and in a build with the Z3 profile tier 1 is off (`outcome_cache.enabled` false, with
the reason: a solver query can time out and k-rust gives no per-run signal that one did). Each record carries
`allowance_bytes`, the writing process's memory allowance, for diagnosis only: it is in neither the key nor the record digest.
This closes the stack dependence of k-rust KINK-06/4 and KINK-06/5 for every comparison through `execute`, live and cached.
What remains is kink's verdict-path calls outside `execute` (`definition_facts`, `BackendRelations` unification, the bridge's
internalization; re-pin finding B-13(a)), which decide nothing for ground programs, and the Z3 profile, where tier 1 is off.
A mutation whose specification uses a hook for which k-rust chooses a value the definition leaves open (`choice`, the order of
`keys_list`, `values` or `Set2List`, mixed-format or NaN-sign Float, and the hooks whose value k-rust's builtin files leave to
the backend, the implementation or the environment, such as `String2Bytes`, `Bytes2String`, `Base2String` and substitution's
renamed variables, and the `KRYPTO`, `HASH` and `SECP256K1` hooks no builtin file documents), or whose condition or rule
result depends on whether `andBool`, `orBool` or `#if` skip an operand that may be undefined, or that has a rule or
equation condition equating two terms (`{ A #Equals B }`, a gap of k-rust's answers), is `unknown` with reason
`implementation-chosen-hook`, `short-circuit-reading` or `equals-condition`. A program whose run takes an undefined step that falsifies a
`total` or `preserves-definedness` claim the mutant still carries (a baseline claim its edit does not reach: the claims the
edit leaves unbacked are removed from the mutant, above), or an undefined step through such an operator, is `unknown` for
that mutation (failure `contradicted-claim` or `short-circuit-reading`), and a kill by another program, whose runs are clean,
stands (root README, "What a kill trusts"; decision 2 is per program). On the baseline a contradicted program is not
comparable.

| Status | Meaning | What to do |
| --- | --- | --- |
| `killed` | A program's result differs on the mutant; `killer` names the first such program. | Nothing. |
| `survived` | Every program ran to a comparable result and agreed. | Write a program that reaches the edited rule and whose result the edit changes (`reaching` lists the programs whose coverage witnesses the edit now: they fired the rule, or reached it for an edit of its `requires`). |
| `equivalent` | The mutant compiles to the baseline's executable definition. | Nothing can kill it; drop or change the mutation. |
| `invalid` | The mutant does not compile (`reason` is the runner's failure, for example `rejected`). | Fix the mutation. |
| `timeout` | No program killed it, and a program did not finish on the mutant within `budget.time_ms`. | Write a program that terminates under the mutant and shows a different result. |
| `unknown` | No program killed it, and a program's result on the mutant is not comparable. | Write a program whose result on the mutant kink can compare. |
| `error` | The runner failed for the mutant, a corpus error (`reason`: `baseline-mismatch:<id>`, `baseline-count-mismatch`, `campaign-refused`, `program-refused:<id>`, `outcome-conflict`, `no-comparable-program`), `run --verify` found a cached outcome that differs from a live run (`outcome-mismatch:<id>`) or a memo of the mutation's resolution that differs from its live resolution (`resolution-mismatch`, re-pin L1-4), or the host refused the stack the mutation's patch needs (`host-stack-refused`, see the reason table). | Report it, or fix the corpus; for `outcome-mismatch`, delete `outcomes/`; for `resolution-mismatch`, delete `memo/`; for `host-stack-refused`, rerun where the host grants more address space. |
| `invalid-mutation` | The mutation does not resolve (`reason`, `edit`, `detail`; see the table above). | Fix the mutation. |

A kill folds above every inconclusive outcome: a mutation that one program kills is `killed` even if an earlier program timed out on it.

The document is the report (see "The report: the run document" below).

### The cache directory

Besides `results/` and `report.json` (the last run's document, also written when the specification is refused or no mutation is selected):

- `outcomes/<context digest>/<mutation identity>.json`, tier 1:
  `{schema: "kink-flow-outcomes", version: 1, context, context_sha256, mutation_identity, mutation_id, removed_claims, records: {<program digest>: {program_id, baseline_run_sha256, outcome, slots, mutant_run_sha256, allowance_bytes, record_sha256}}}`.
  `removed_claims` is the row's (below), for the reader only: it is read back by nothing and is in no digest.
  The context is `{outcome_schema: "kink-flow/outcome/v1", kink_build, kink, profile, execution_digest: {kind, digest}, budget, oracles, classifier, schedule}` (with `work_factor` set, `budget` also holds `work: {factor, floor}`):
  `kink` is kink's semantics identity (kink-campaign `identity`, packet CACHE-ID), `{k_rust_revision, fingerprint, canonical_patch, compiled_kore, patch_admission, claim_removal, mutant_consistency, mutant_effect, definition_exclusion, execution_request, result_schema, coverage}`, the version of every kink algorithm an outcome can depend on. Among them:
  `claim_removal` is kink-patch's `CLAIM_REMOVAL_VERSION`, since the mutant every record ran on depends on the claim-removal algorithm (v2 since re-pin R0c-fix-3: the reach follows the overload and unit axioms; v3 since R0c-fix-4: a rule with configuration context is an equation of its head);
  `mutant_consistency` is kink-native's `MUTANT_CONSISTENCY_VERSION`, since a mutant runs (and a record exists) only when its equations are shown consistent (v2 since R0c-fix-4: the check's guard reads the equation and skipped-pair counts);
  `mutant_effect` is kink-native's `MUTANT_EFFECT_VERSION`, since the symbols the check reads, and the cross-check of kink-patch's source reading, come from the compiled definitions (re-pin R0c-fix-4);
  `definition_exclusion`, `patch_admission` and `execution_request` name the definition exclusions (re-pin R0-tail), the rule that no typing error refuses a patch (L2-2-fix-1) and the execution request with its state-set modality and work budget (L1-1);
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
  It is the one store outside kink's semantics identity: a hint decides no status, so a hint an older build wrote only orders the search.
  The hint key hashes the mutation's edits as written (without `line`) and the K text of each addressed rule before the edit,
  so a hint survives edits elsewhere in the specification and is lost when the addressed rule's text changes.
  A hint is a scheduling hint only: it changes which killer is found first and the cost, never a status.
- `memo/resolutions/<spec digest>/<sha256 of the mutation's edits>.json` and `memo/census/<spec digest>.json`, the warm path's memos (re-pin L1-4, **Memos** above):
  `{schema: "kink-flow-memo", key, value, record_sha256}`, where `key` is `{version: "kink-flow/resolution-memo/v1", kink_build, kink, spec, mutation}` (`mutation`: the edits, each `{file, rule, line, find, replace, delete}`) or `{version: "kink-flow/census-memo/v1", kink_build, kink, spec}`,
  `value` the facts `{digest, rules, identity, typing_diagnostics, removed_claims}` or the census (kink-native `DeclarationCensus::value`), and `record_sha256` the digest of `{key, value}` under the version.
  A record is used only when its key is exactly the current one and its digest recomputes under that key; the path only finds it.

- `patterns/<spec digest>/<pattern digest>/<program digest>.json`, the cached answers of `query` (flow F-18, "Checking a pattern" below). `run` neither reads nor writes them.

Every file is written atomically; deleting any of them, or the whole directory, is always safe.
The `killers/` directory of F-05 is no longer read or written and can be deleted.

Exit status: 0 when every selected mutation got its status (survivors, timeouts and invalid mutations included);
1 when the manifest, the mutation list, the specification or a program is refused, a run failed, a cache file could not be written,
no program is comparable, a corpus error stopped the run, or `--verify` found a mismatch; 2 on a usage error (including an `--only` id that names no mutation, or `--verify` given twice).

## The report: the run document

`run` prints one document and writes the same document to `.kink-flow/report.json` (after every mutation, and once more at the end):

`{schema: "kink-flow-run", version: 8, k_rust_revision, profile, result_schema_version, kink_build, kink, spec, programs, unusable_programs, mutations, counts, survivors, stopped, outcome_cache, mismatches, baseline_runs, order, untargeted_rules}`.
Version 3 (F-13) names the oracle slots of an executed entry, versions 4 to 6 add row fields (below), version 7 (packet CACHE-ID) adds `kink`, kink's semantics identity, and version 8 (packet CACHE-ID-fix-1) adds `kink_build`, the SHA-256 of the executable that wrote it.
`report` prints the stored statuses without re-deriving them, so it refuses (`unreadable`) a document of another version, one written by another build (or naming none), and one whose `kink` is not this build's.

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

A mutation row is `{id, note, digest, identity, removed_claims, inconsistent_pairs, typing_diagnostics, status, reason, killer, killer_source, killer_from_cache, unusable_killer, reaching, executed, calls, call_wall_ms, rules, action}` (version 4 added `removed_claims`, version 5 `inconsistent_pairs`, version 6 `typing_diagnostics`):

| Field | Meaning |
| --- | --- |
| `digest` | The patch digest; null for an `invalid-mutation`, which also has `edit` (the offending edit's index or null) and `detail`. |
| `identity` | The mutation's position-free identity (tier 1's file name); null when it has none (the mutation then always runs). |
| `removed_claims` | `{removed, unsupported}`: the trusted claims the edit leaves unbacked. `removed` are absent from the mutant every program ran on (a `simplification` claim is a deleted lemma); `unsupported` are those no removal takes away, which make the mutation `unknown` (`unsupported-claims`), and each compiled equation the source reading does not explain (key `unread-equation`). Each is `{module, index, label, key, value}` (`label` null for a production) or `{inserted, key, value}` for a sentence the edit inserts. The row reads them from the deciding call's plan when it records claims (since re-pin R0-tail; the cross-check's `unread-equation` claims are known only there), and otherwise from kink-patch's withdrawal of the mutation's patch, which gives the same claims. Absent on an `invalid-mutation`. |
| `inconsistent_pairs` | `[{first, second, position, reason}]`: the pairs of equations (each named by its rule label, written position or id; `position` the overlap's argument path, empty for the root) that k-rust's critical-pair check does not show to join, which make the mutation `invalid` (`inconsistent-mutant`); empty otherwise. Absent on an `invalid-mutation`. |
| `typing_diagnostics` | `[{module, index, label, message}]` (or `{inserted, message}`): the edited rules' errors in compilation's typing view (kink-patch `Mutant::typing_diagnostics`), empty when each types. A diagnostic only: compilation decides whether the mutant is valid, and a mutant with a typing error that compiles is run like any other. Absent on an `invalid-mutation`. |
| `status`, `reason` | The status (see the run section) and the runner's or the flow's reason. |
| `killer`, `killer_source`, `killer_from_cache` | The first killing program of a `killed` mutation; where the kill came from: `outcome-cache` (tier 1, no call), `hint` (the hinted program's one-program call) or `search` (the call over the remaining programs); `killer_from_cache` is true for the first two. Null, null and false otherwise. |
| `unusable_killer` | `{program, class, cause, source}` when a cached kill (`source` `outcome-cache`) or the hint (`hint`) names a program of the corpus that is not comparable now; else null. |
| `reaching` | The comparable programs whose cached coverage witnesses an edited rule's edit (step 3: reached for an edit of the rule's `requires`, fired for any other edit), in the order they were tried. |
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
A cached entry has no evidence at hand: its distinguishing slot has `sides: null`. So has a one-sided kill (the mutant's run reached its work budget, `budget.work_factor`), whose mutant side is `unknown`, not a value.
No timing, census or side value enters an evidence row, a digest, a key, an outcome record or a hint.

A row may also carry `stale_killer` (the hint named a program that is not comparable; it was removed) and `cache_error`.
The cause of an `unknown` slot names the possible reasons together (a path stopped at `max_depth`, an undecided end,
or a final configuration holding a collection kink cannot compare (for example one with a Bytes key), an unevaluated function or a symbolic term),
because the runner's evidence records that the mutant's value is unknown but not which of these stopped it; the leaf census that follows
(leaves per halt class: `depth-bound`, `stuck`, `indeterminate`, ...) usually says which.

## `kink-flow report FLOW.toml [--cache DIR]`

Prints the stored run document again, byte for byte as `run` printed it.
When there is none, or it is not a run document of the current version, it prints
`{schema: "kink-flow-report", version: 1, k_rust_revision, profile, outcome: "missing" | "unreadable", path, detail}`.

Exit status: 0 when it printed a report; 1 when there is none, it is unreadable, or the manifest does not decode; 2 on a usage error.

## Checking a pattern: `kink-flow query FLOW.toml PATTERNS.toml [--only ID]... [--verify] [--cache DIR]`

A pattern check asks, for one program of the corpus: does some run of this program, from its input, reach a configuration that matches this pattern?
The initial configuration, every configuration a run reaches and the final ones all count.
Use it to check a claim before relying on it: when you write a program meant to exercise a situation (a division by zero, a thread that writes before another reads, a loop that runs twice), write the situation as a pattern and claim the program hits it.
kink-flow runs the program and confirms or refutes the claim, so a test whose purpose was imagined rather than reached is caught.
"Every run hits" is not asked: when a program has several runs (thread interleavings, the evaluation order of `strict` operators), the answer is about some run.

### `PATTERNS.toml`

```toml
[[pattern]]
id = "result-three"                  # unique, non-empty
pattern = "<k> 3 </k>"               # K text, as the left-hand side of a rule is written
programs = ["add", "sub"]            # optional: the programs you claim hit it
note = "the result 3 is reached"     # optional, free text

[[pattern]]
id = "result-above-five"
pattern = "<k> I:Int </k> requires I >Int 5"
```

- `pattern` is parsed by the specification's own grammar, as the content of a rule in the main module: write a configuration fragment, with `...` and omitted cells completed as in a rule (`<k> 1 / 0 ~> _ </k>`, `<state> ... X |-> 3 ... </state>`), variables (`I:Int`, `_`) and an optional `requires` condition over them. A rewrite (`=>`) in a pattern denotes its left side. An `ensures` is refused, and so is a variable that occurs only on a rewrite's right side.
- A `requires` that is undefined at a state (`10 /Int (I -Int 3) >Int 0` where `I` is 3) does not hold there, as for a rule's condition: that state does not match. So a pattern whose only matches make its condition undefined gets a `no`, and a claim of it is refuted, although the program does reach the configuration you meant; write the condition so that it is defined at every state it is matched against. A condition whose definedness k-rust cannot decide (a partial function with no equation for its argument) gives `unknown`.
- `programs` lists the corpus programs you claim hit the pattern (the per-input claims). Without it, every program of the corpus is asked ("which programs already hit it?").
- An unknown key, a value of the wrong type, a duplicate or empty id, an empty or duplicated `programs` entry, and a claimed program the manifest does not have are errors that name the key; the command then runs nothing and exits 1.

`testdata/flow/calc/PATTERNS.toml` and `testdata/flow/loop/PATTERNS.toml` are complete examples.

### Answers

The command prints one document, `{schema: "kink-flow-query", version: 1, k_rust_revision, profile, kink_build, kink, spec, programs, patterns, rows, counts, refuted_claims, mismatches, pattern_cache, baseline_runs}`:
`programs` are the `results` rows (the result cache is brought up to date first),
`patterns` one entry per selected pattern `{id, note, pattern, outcome: valid | invalid-pattern, detail, digest, kore, asked: claimed | corpus}` (`kore` is the compiled target),
and `rows` one row per (pattern, program asked) `{pattern, program, claimed, answer, cause, witness, cached, wall_ms, claim}`.

| `answer` | Meaning | What to do |
| --- | --- | --- |
| `hit` | A run reaches a configuration that matches the pattern; `witness` shows it. | Nothing: the claim holds. |
| `no` | No run reaches one: the whole state space of the program was explored, within the budget, on a definition where nothing is left to the implementation. | The program does not do what you meant: change the program, or the pattern. |
| `unknown` | No definitive answer; `cause` says why (below). | Read the cause; usually make the program terminate within the budget, or accept that the definition leaves the question open. |
| `invalid-pattern` | The pattern does not parse, sort or compile; `cause` is k-rust's message. It never runs. | Fix the pattern. |
| `error` | The program is not admitted, k-rust refused the search, or its result lacks the `matches` or `incomplete` list kink reads (never read as empty); `cause` says which. | Fix the program, or report it. |

`claim` is null for a program the corpus form asked; for a claimed program it is `confirmed` (`hit`), `refuted` (`no`) or `unconfirmed` (anything else).
**A refuted claim** (also listed in `refuted_claims`) means the program, run exactly as kink runs it, never reaches the situation you said it tests: the purpose you gave the test is not what it does.
An `unconfirmed` claim is neither confirmed nor refuted.

The witness of a hit is `{depth, state: {kore, truncated}, bindings, rules, rendering, note}`:
the matching configuration as KORE text (cut to 4000 characters) and the number of rewrite steps to it, the values of the variables you wrote (`[{variable, value}]`; the variables k-rust generates to complete cells are left out, and so is every variable spelled as k-rust spells a generated one, `_Gen<n>` or `_DotVar<n>`, so a variable of your own with such a name is not shown: the witness is for display only, and no answer reads it),
and `rules`, the rewrite steps of one run from the initial configuration to it, each named by its label, else by the file and line of the rule written for it, else by its compiled id.
k-rust 501f18b9 has no unparser from KORE back to the specification's syntax, so `rendering` is `kore`.

**Why a no can be unknown.** A `no` is a claim about every run, so it needs more than a `hit`:
- the exploration completed: no path stopped at `budget.max_depth` (`a path reached max_depth = N`), the search finished within `budget.time_ms`, and k-rust decided every step and every match (an undecided step, an undecided match, a state stopped for lack of native stack each make it incomplete);
- the program's baseline run (its `results` row) is `comparable`: complete, with no stack stop and nothing else that makes a run no evidence (a contradicted claim, an allowance refusal, ...);
- the definition leaves nothing to the implementation: no rule depends on a hook whose value the definition leaves open and k-rust chooses (`implementation-chosen-hook`, decision 1's census: `keys_list`, `choice`, `String2Bytes`, ...), or on whether `andBool`, `orBool` or `#if` skip an undefined operand (`short-circuit-reading`), and neither does the program's initial configuration; with such a value another implementation could reach the pattern, so the exploration of k-rust's choice says nothing about it;
- the build is not the Z3 profile (a solver query can time out silently).

A `hit` needs none of these. It is a run k-rust found to a configuration that exists, and k-rust's choice of an open value is one model of the definition. A hit is found even in a program that never ends, or that the budget stops: the search stops at the first match.
That choice includes the short-circuit reading. K leaves it open: `domains.md` says `andBool` and `orBool` "may be short-circuited in concrete backends", and that `#if` "does not short-circuit on symbolic backends". k-rust reads them strictly: a condition with an undefined operand is undefined, so its rule does not apply. That is one reading K allows, so a `short-circuit-reading` flag on the definition or on the initial configuration makes a `no` unknown but leaves a `hit` standing.
The consequence: a hit may be on a configuration that only the strict reading reaches. For example, an `owise` rule fires because another rule's condition was undefined, and a short-circuiting backend might not reach that configuration. The census (`implementation-chosen-hook`) is treated the same way: a hit stands, a `no` does not.
Two conditions make every answer unknown: the definition's load counted a stop for lack of native stack (`load-stack-stop`), or a rule or equation has a condition equating two terms (`equals-condition`, a gap of k-rust's own answers).
A match is a hit only when it is decided, and the search stops at its first match, so otherwise the answer is unknown. A match is not decided when any of these holds:
- it holds only under a condition k-rust did not decide;
- its path emitted a backend diagnostic;
- its configuration's term is not shown defined (`undefined-state`).

The last case is a configuration holding an application of a function the definition does not declare `total` that no equation reduced, such as `f(3)` for a function with an equation for `f(0)` only, or `1 /Int 0`. Wherever that application is undefined, such a configuration denotes nothing: there is no run to it, although k-rust's search lists it and its match carries no condition. kink therefore requires the matched configuration, and with it every binding, to be defined by construction (k-rust's `ceil_free`). Every application must be of a constructor or of a function declared total, and every map or set must have keys k-rust shows distinct by their shape.
Constructors, functions declared total (a `total` helper with no equation for its argument included), lists, and maps or sets over domain values such as IMP's `<state>` and IMP++'s `<store>` pass. A configuration holding a partial function's unevaluated call does not, and neither does a map whose keys k-rust cannot show apart by their shape. Then the claim is `unconfirmed`, never confirmed; usually the program calls a function outside the cases its equations cover.

### How it runs, and what it costs

Each pattern is compiled once, by k-rust's own compiler of search patterns (`kompile::compile_search_pattern`, the one `krun --pattern` uses), against the compiled definition the programs run on.
Each (pattern, program) is one k-rust `search_pattern` from the program's initial configuration: search type all (every reachable configuration, the initial one included), state set (each distinct configuration of a depth once), at most one result, the manifest's `max_depth`, under a watchdog of `time_ms`.
k-rust's search has no work budget yet (a k-rust request, KINK-24, would make a bounded answer reproducible), so `time_ms` is what stops a program that does not end.
A check costs about one plain run of the program (release build, shared host at load 9-24; flow F-18 handoff): where the search explores every configuration it took 1.0-2.3 times the program's baseline run (`examples/imp` sum 6 ms against 3, primes 12 against 8, collatz 20 against 10; IMP++ primes 98 against 43, collatz 93 against 48, spawn 2.5-2.9 s against 2.5 s), and much less when the hit comes early (an interleaving of IMP++ spawn found at depth 39 in 0.32 s, against 2.5 s for the run).
The search keeps every configuration it reached with the trace of one run to it, which added at most 45 MiB to the process's peak (IMP++ primes 153 MiB against 109 MiB).
The admission of the specification (about 1 s per command on IMP) costs more than most checks, and a cached answer costs no search.

### The cache, `--verify` and trust

Only a `hit` and a `no` are cached, one record per (pattern, program), `patterns/<spec digest>/<pattern digest>/<program digest>.json` in the cache directory:
`{schema: "kink-flow-pattern", key, pattern_id, program_id, answer, witness, baseline_run_sha256, record_sha256}`.
The key is `{schema_version: "kink-flow/pattern-answer/v1", lowering: "kink-flow/pattern-lowering/v1", k_rust_revision, kink_build, kink, spec, program, pattern, budget, modality}`:
the specification digest (every source file, a comment included), the program digest (its text, start sort and variables), the pattern digest (its compiled KORE target, not its id or its text's layout), the budget as the result key holds it, the search's modality, kink's build (any rebuild misses) and its semantics identity.
A record is used only when its key is exactly the current one and its `record_sha256` recomputes; a cached `no` also only while the program's current result is `comparable` with the baseline run digest the `no` was given against.
A used record is judged again with the current command's facts (the definition's exclusions on this command's load, the initial configuration's, the baseline class, the profile), so it never answers more than a live search would.
Editing the specification, the program, the budget or the pattern, or rebuilding kink, recomputes the answer; an `unknown` is recomputed every time.

A cached answer stands without a search. It rests on the integrity of the cache directory (whoever can write it can forge an answer, as for every kink cache) and on the key naming every input; not on k-rust's determinism: a `hit` and a `no` are facts about the definition and the program, which a later search can fail to re-derive (an unknown) but cannot contradict.
`--verify` searches every selected (pattern, program) live, compares each with the stored record a command without `--verify` would use, lists every difference in `mismatches` (`{pattern, program, record, cached, live}`; the row's `verify` is `match` or `mismatch`), writes no pattern record, and exits 1 on a difference; it also updates the results with `--verify` (which writes a result record for a program that has none).
Each live answer is judged with the program's live baseline run, not with a stored result record that `--verify` found different, so the printed answers are those of this command's own runs; a stale result record shows as a mismatch of the results, and the command exits 1.
The cache is off under the Z3 profile, as tier 1 is, and when the executable cannot be read (`pattern_cache.enabled` false, with the reason).

What every answer trusts, besides the cache:
- k-rust's search is sound and exact for "some reachable configuration matches" under the state set (re-pin M-2 found the same distinct states and hits by stepping on IMP and IMP++; `tests/query.rs` walks every fixture program's states one step at a time and requires the same answers);
- k-rust's parser and pattern compiler decide what a pattern denotes;
- the baseline's own claims (`total`, `preserves-definedness`, lemmas) are trusted, as for every baseline run. A contradiction k-rust detects ends its path (the undefined step has no successor), so a witness's run passes through none;
- k-rust's `ceil_free` decides that a matched configuration's term is defined (by construction; k-rust proves it in Lean, `ceilFree_sound`), and the definition's `total` attributes are among the trusted claims above;
- a search does not count the stops for lack of native stack it dismisses while it only refines a result (k-rust `docs/compatibility.md`, "Execute"). k-rust states at every such site a search reaches that the kept result is sound (a definedness condition left unsimplified, a fold forgone), so such a stop can leave a step or a match undecided (an unknown) but cannot make a decided match or a completed exploration false: whether an answer is definitive can depend on the host's stack, its truth cannot. A `no` also requires the baseline run's own count to be zero.

**Answers never decide a mutation.** No answer enters a result record, an outcome record, a hint or a run document, and `run` does not read the pattern cache: a kill needs the final configurations to differ, and a pattern-only difference stays unknown by design.

Exit status: 0 when every selected (pattern, program) got its answer (`hit`, `no`, `unknown`, `invalid-pattern`; refuted claims included);
1 when the manifest, the pattern list, the specification or a program is refused, a search failed, a record could not be written, or `--verify` found a difference;
2 on a usage error (an `--only` id that names no pattern, an option given twice).
