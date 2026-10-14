# kink-flow

The primary usage flow of kink (`draft/tasks/flow/README.md`, section 5):
a K specification, a concrete corpus of programs an LLM writes for it,
and, in later packets, cached results, a mutation list, a kill search and a survivor report.

This crate currently provides the corpus manifest and the `check` command (flow F-02),
the result cache with the `results` command (flow F-03),
the mutation list with its resolution into patches (flow F-04),
and the kill search with its killer cache, the `run` command (flow F-05).

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

## `kink-flow results FLOW.toml [--verify] [--cache DIR]`

Runs every program whose result is not cached yet and reports, per program, whether it can
kill a mutant, and, per rule of the specification, which programs reach it.

Each program runs on the baseline as its own zero-mutant campaign (kink-campaign's runner),
with two fixed oracles: the exit stop (no exit-code cell) and the whole final configuration.
A program's class is

| Class | Meaning | What to do |
| --- | --- | --- |
| `comparable` | The run ended and its final configuration is a value kink compares. | Nothing: this program can kill mutants. |
| `timeout` | The run did not end within `budget.time_ms`. | Make the program terminate, or raise the budget. |
| `unknown` | The run ended without a comparable value (for example a Map in the final configuration, `budget.max_depth` reached, an undecided step); `cause` says which. | Write a program whose final configuration kink can compare. |
| `refused` | The program was not read, parsed or assembled; `cause` is the refusal. | Fix the program. |
| `error` | The run or the runner failed. | Report it. |

Only comparable programs can kill a mutant; the others are reported and never count as covering a rule.

The cache is `.kink-flow/` next to `FLOW.toml` (or `--cache DIR`); deleting it is always safe.
One JSON record per program, `results/<spec digest>/<program digest>.json`, holds its key
(result schema version `kink-flow/result/v1`, the two digests and the budget), class and cause,
the baseline row exactly as the campaign report encodes it with the digest of its `run` part
(`run_sha256`, comparable programs only), the final configuration as KORE text, and the rule
coverage. The specification digest covers the k-rust revision, the solver profile, how the
specification is loaded and every source file the load reads; the program digest covers the
program's bytes, start sort and variables, never its id. A record is used only when its key is
the current key, so editing a program reruns that program, and editing the specification,
the budget or kink's result schema reruns everything.

`--verify` reruns every program that has a current record and compares: a different class,
a different `run_sha256`, or a record whose `run_sha256` is not the digest of its own baseline
row is a mismatch. Mismatches are listed (program, record path, detail) and records are never
rewritten by `--verify`; delete a mismatching record (or the cache) to recompute it.

The document lists every program `{id, digest, class, cause, cached, verify}`, every authored
rule `{module, index, label, file, start_line, end_line, status, reached_by}` with status
`uncovered` (no comparable program reaches it: the next program to write) first, then
`covered`, then `not-observable` (equations: a run's trace names rewrite steps only), the
mismatches and a summary.

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
Unknown keys, values of the wrong type, duplicate or empty ids and a mutation without edits are errors naming the key.
`testdata/flow/calc/MUTATIONS.toml` and `testdata/flow/register/MUTATIONS.toml` are complete examples.

Resolution (`kink_flow::mutation::resolve`) addresses every edit to one authored rule, applies the edits
to in-memory copies of the source files (a delete removes the rule's text and keeps its line), loads the
edited sources with the specification's load options, and checks that the edited load has the baseline's
modules and sentences, in order and with equal fingerprints, except at the addressed rules: a replaced rule
is still exactly one rule sentence with the same label, a deleted rule is gone. The edited rules then become
one pinned kink-patch `Patch` (`ReplaceSentence`, `DeleteSentence`) whose digest is the mutation's identity;
the mutant is always the patched baseline, never the edited load. Only rules are editable.

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
| `edited-load-failed` | The edited sources do not load (parse or sort error); the detail is k-rust's message. |
| `structure-changed` | The edit changed something besides its rule: a sentence split, merged, added, removed, changed kind or changed elsewhere. |
| `label-changed` | The edit changes the rule's label. |
| `no-change` | The edited rule equals the original up to formatting. |
| `no-usable-span`, `patch-rejected` | Defensive; not expected on rules written in `.k` sources. |

## `kink-flow run FLOW.toml MUTATIONS.toml [--only ID]... [--cache DIR]`

Runs the kill search: for each mutation of the list (in file order; with `--only`, only the named ones),
is there a program of the corpus whose result the mutation changes?

1. The result cache is brought up to date first (`results` without `--verify`).
   Only `comparable` programs can kill; the others are never run.
2. The mutation is resolved into one patch (see `MUTATIONS.toml`); an `invalid-mutation` stops there.
3. The programs are ordered: those whose cached coverage reaches an edited rule first, then the rest, each group in the manifest's order.
4. If the killer cache names a program that killed this mutation before, and that program is still comparable with the same digest,
   the mutant runs on that program alone. If it kills, that is the verdict.
   Otherwise the entry is removed and the mutant runs on every program in the order of step 3,
   exactly as without the entry: a wrong or stale entry costs one more run, never a different status.
5. Every status is the one kink-campaign's runner derives for the mutant (schedule first-kill: the mutant stops at its first killing program).
   kink-flow compares no terms; only a proved difference of the exit stop or the whole final configuration kills.
6. After every runner call, each program's baseline run is checked against its cached result (`run_sha256`).
   A difference is a corpus error: the mutation gets status `error` with reason `baseline-mismatch:<program id>`,
   nothing is written to the killer cache for it, and the run stops (exit 1). Run `results --verify`.
7. A `killed` mutation's first killing program becomes its cached killer; any other status removes the entry.
   The killer cache and the run document are written after every mutation, so an interrupted run keeps its finished work.

| Status | Meaning | What to do |
| --- | --- | --- |
| `killed` | A program's result differs on the mutant; `killer` names the first such program. | Nothing. |
| `survived` | Every program ran to a comparable result and agreed. | Write a program that reaches the edited rule and whose result the edit changes (`reaching` lists the programs that reach it now). |
| `equivalent` | The mutant compiles to the baseline's executable definition. | Nothing can kill it; drop or change the mutation. |
| `invalid` | The mutant does not compile (`reason` is the runner's failure, for example `rejected`). | Fix the mutation. |
| `timeout` | No program killed it, and a program did not finish on the mutant within `budget.time_ms`. | Write a program that terminates under the mutant and shows a different result. |
| `unknown` | No program killed it, and a program's result on the mutant is not comparable. | Write a program whose result on the mutant kink can compare. |
| `error` | The runner failed for the mutant, or a corpus error (`reason`: `baseline-mismatch:<id>`, `campaign-refused`, `program-refused:<id>`, `no-comparable-program`). | Report it, or fix the corpus. |
| `invalid-mutation` | The mutation does not resolve (`reason`, `edit`, `detail`; see the table above). | Fix the mutation. |

A kill folds above every inconclusive outcome: a mutation that one program kills is `killed` even if an earlier program timed out on it.

The document is `{schema: "kink-flow-run", version: 1, k_rust_revision, profile, result_schema_version, spec, programs, mutations, counts, stopped}`:
`programs` are the `results` rows; `stopped` is `null` or `{mutation, reason}` of the corpus error that stopped the run;
`counts` counts every status. Each mutation row is
`{id, note, digest, status, reason, killer, killer_from_cache, reaching, executed, calls}`:
`digest` is the patch digest (null for an `invalid-mutation`, which also has `edit` and `detail`),
`executed` lists `{program, outcome, slots | failure}` for every program the mutant ran on, in the runner's order
(`outcome` is `distinguish`, `agree`, `timeout`, `unknown`, `incomparable` or `error`; `slots` gives the exit-stop and whole-term outcomes),
and `calls` lists the programs of each runner call (`[[killer]]` with a warm cache, `[[killer], [all]]` when the cached killer no longer kills).
A row may also carry `stale_killer` (an entry naming a program that is gone, changed or no longer comparable; it was removed) and `cache_error`.

The cache directory gains `killers/<spec digest>.json`,
`{schema: "kink-flow-killers", version: 1, spec, killers: {<mutation digest>: {mutation_id, program_id, program_digest}}}`,
and `report.json`, the last run document.
A killer entry is a scheduling hint only; a file that does not parse is treated as empty.

Exit status: 0 when every selected mutation got its status (survivors, timeouts and invalid mutations included);
1 when the manifest, the mutation list, the specification or a program is refused, a run failed, a cache file could not be written,
no program is comparable, or a corpus error stopped the run; 2 on a usage error (including an `--only` id that names no mutation).
