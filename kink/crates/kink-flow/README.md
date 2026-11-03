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
per-input pattern checks with the `query` command (flow F-18; "Checking a pattern" below),
the `fuzz` command: hole values of a template program that kill a mutation, reach a rule or hit a pattern, found by k-rust-fuzz on kink's own sides (fz26 P7-KINKFLOW T3a and T5; "Killing a survivor with `fuzz`" below),
the mutations directory, anchors by a suffix of a label's components and the required `misunderstanding` (CF-13; `MUTATIONS.toml` below),
the resolve-only check of a mutation list, `check --mutations` (CF-18; "Checking mutations" below),
the definition exclusions read at admission, each named with its causes by one formatter for every command, with `check` failing when a fact known before any mutant runs makes a verdict impossible (CF-02; "When `check` fails" below),
the compared cells: the specification's unobservable cells left out of every comparison, a manifest's narrowing, and every document naming the cells compared ("Which cells are compared" below),
and the library for both front ends, kink-flow's command line and the krs front end (`krs kink <verb>`, not yet built): one manifest schema with a K or a KRS `[spec]`, one command layer, and the deterministic `--output verdicts` rendering (CF-40; "Front ends" and "Verdicts" below).

## Building

Build the portable (no-Z3) profile for the LLM loop, from the root of k-rust's checkout:

```sh
cargo build --release -p kink-flow --no-default-features
```

The executable is `target/release/kink-flow`.
kink-flow's default features are the Z3 solver profile, as k-rust's and the other kink crates' are (the root README, "Gate"), and k-rust's own workspace build and test run use it.
Under Z3 tier 1 of the outcome cache (with the warm-path memos) and the pattern cache are off, so every mutation and every query runs live,
and a complete exploration with no match is `unknown`, not `no` (`query`, "Answers"): a solver query can time out and k-rust's search responses carry no count of undecided answers to show that none did.
That lasts until kink adopts k-rust's counts (adoption A-5) and k-rust adds the count to search responses (KINK-28).

## `FLOW.toml`

```toml
[spec]
entry = "calc.k"              # relative to this file's directory
main_module = "CALC"
syntax_module = "CALC-SYNTAX" # optional
include_dirs = ["."]          # optional
md_selector = "k"             # optional
assume_joined = ["spec.k:7:3,spec.k:8:3@root"]   # optional; findings named as premises

[budget]                      # optional
time_ms = 10000
max_depth = 100000
work_factor = 4               # optional; no work budget when absent

[result]                      # optional
cells = ["k", "regs"]         # compare only these cells; default: every observable cell

[[program]]
id = "add"
file = "programs/add.calc"    # or: text = "1 + 2"; neither on a definition without $PGM
start_sort = "Exp"            # optional; only with file or text
variables = { N = "42" }      # optional; configuration variable $N = 42
```

A KRS corpus declares its specification as the K a KRS package emits, which the krs front end (`krs kink <verb>`, not yet built) binds:

```toml
[spec]
krs = { definition = "main" }  # the package's definition facet (krs --definition)
assume_joined = []             # optional, as above
```

With `krs`, `[spec]` takes no other key but `assume_joined`: `entry`, `main_module`, `syntax_module`, `include_dirs` and `md_selector` are each the error `spec.<key>: not allowed with spec.krs: the krs front end supplies it`, and `krs` takes exactly the key `definition`.
Every other table is the same for both kinds of corpus.
kink-flow refuses a KRS corpus (``spec.krs: a KRS corpus: run `krs kink <command>` in the package``, stage `manifest`); the krs front end is to refuse a K corpus.

Every path is relative to the manifest's directory and must stay inside it.
Unknown keys, values of the wrong type, duplicate or empty program ids,
a program with both `file` and `text`, and a `start_sort` on a program with neither are errors that name the key or the program id.

A program is a case: an assignment of a value to each configuration variable of the definition.
`file` or `text` is the program text bound to `$PGM`; every other variable is bound by name.
A definition without `$PGM` takes no program text: its case gives neither `file` nor `text` and binds every variable under `variables`,
and a program text given to it is refused (stage `inputs`, reason `stray-program`, naming `$PGM` and every declared variable with its sort), since it would bind nothing.
A case of a definition that declares `$PGM` without a program text is refused as missing it (`inputs`/`assemble`).

A program may also have `inputs`, a table of typed inputs by input name (`inputs = { rom = { "$file" = "rom.bin" } }`): documents of an encoding derived from the specification's declared types, which only a front end that knows those types reads (the krs front end, `krs kink`).
kink-flow keeps them as written and never reads them; a front end sets its decoder on the manifest it decoded (`FlowManifest::with_input_decoder`, the `InputDecoder` trait), which gives for each input the configuration variable it binds and the K term it denotes, reading the files a document names inside the manifest's directory.
kink binds the term as it binds a parsed value: it types the term in the definition's grammar and refuses it when its sort is not at most the variable's.
A manifest read at the K level has no decoder, so a program with `inputs` is refused (`inputs`/`typed-inputs`): at the K level, bind K text under `variables`.
A typed input may bind `$PGM` on a program without `file` or `text`: kink binds the term as a program built without the parser.
A document the decoder refuses, or a variable bound twice (by both `variables` and `inputs`, by two inputs, or `$PGM` by an input and the program's `file` or `text`), is refused (`inputs`/`input-value`, with the decoder's message or the two bindings).
A file a document names is read as a program file is: its path is relative to the manifest's directory (or, for a file a decoder reads from another, to that file's directory), resolved by the operating system, links included, and an absolute path or one that resolves outside the manifest's directory is refused.
`fuzz` refuses a template of a program with typed inputs: it varies and replays K text only.

Defaults:

| Key | Default | Note |
| --- | --- | --- |
| `spec.syntax_module` | none | k-rust then uses `<main_module>-SYNTAX` if it exists, else the main module (a kompile warning). |
| `spec.include_dirs` | `["."]` | The manifest's directory. |
| `spec.md_selector` | `"k"` | |
| `spec.assume_joined` | none | The findings of the definition's full critical-pair check you accept as premises (fz26 KINK-BASELINE-FINDINGS; root README, "What a kill trusts"), each by the name `results` prints in `data.findings` (k-rust-backend `data_term::names`: k-rust-fuzz's `definition-findings` name, byte for byte). A name must name exactly one finding, and not a decided one, or the specification is refused (stage `assume-joined`, reason `name-refused`). With a finding left unnamed, no end of the definition is data: every mutation is `unknown` (`baseline-findings`), no comparable program can kill, and no query `no` is given. The list is in the specification digest (when not empty) and every document prints it (`data.assume_joined`). |
| `budget.time_ms` | `10000` | Wall-clock bound of one program run; must be positive. |
| `budget.max_depth` | `100000` | Rewrite-depth bound of one program run; must be positive. A run is never unbounded. |
| `budget.work_factor` | absent | The work budget of a mutant's run of a program: at most `work_factor * W + 10000` states visited (k-rust `max_work`), where `W` is the states the program's baseline run visited; must be positive. A mutant that runs past it is `unknown` on that program, long before `time_ms` would stop it, unless the part it ran already holds a final configuration the baseline's program never ends in: then the program kills it one-sidedly (re-pin L1-2, decision 6; the root README, "What a kill trusts"). Absent: no work budget. It never bounds a baseline run. |
| `program.start_sort` | the sort of `$PGM` | |
| `program.variables` | none | Every configuration variable other than `$PGM` must be given, here or under `inputs`; streams default to empty (`$IO` to `"off"`, `$STDIN` to `""`). A variable's text is read as krs-exec reads it (k-rust `variable_reading_modules`): with the syntax module's grammar first wherever that module has the variable's sort, then with the main module's, so one text denotes one term in both tools. krun's `-c`, and so a `fuzz` campaign, reads it with the main module's grammar alone; `fuzz` refuses a template that the two readings read differently (`variable-reading-differs`, below). On a definition with stream cells a program may not bind `$IO` (refused at `inputs`, reason `stream-mode`): with IO off the stream cells hold the text printed and the input not yet read, so a final configuration states the program's output. |
| `program.inputs` | none | Typed inputs, read only by a front end's decoder (above). |
| `result.cells` | absent | The cells the programs' second slot compares, by K name (below, "Which cells are compared"); a nonempty array of distinct nonempty names. Absent: every cell the specification does not declare `unobservable`. In the specification digest when present. |

### Which cells are compared

A program's run is compared by two oracle slots: the exit stop (no exit-code cell), then its final configurations.
A cell declared `unobservable` (`<w unobservable=""> 0 </w>`; KRS does not accept its spelling `#[k::cell(unobservable)]` yet) holds state no use of the definition may observe, so no kill may rest on its content.
The second slot therefore compares every cell except the unobservable ones:
it is `cells`, the final configuration with the content of each cell left out replaced by `\top` of its sort (kink-campaign `StateProjection::Cells`), exactly when some cell is left out,
and `whole-term`, the whole final configuration, otherwise.
Either way `<generatedCounter>`'s content is erased, as before.
Two final configurations agree under `cells` exactly when they are equal outside the cells left out, so a kill is a difference some compared cell shows, and a survivor survives relative to the cells compared: every document names them (`result`, below).
A cell wrongly declared unobservable can hide kills, never make one.
The projection is defined on every configuration, so the one-sided kill applies to a `cells` slot as to `whole-term` (root README, "What a kill trusts").
Whether an end is data is still judged on the whole end: an unobservable cell holding a non-value makes the slot `unknown`.

`[result] cells` narrows the compared cells to the cells named and the cells inside them.
Every other cell is left out, except the cells that enclose a named one; an unobservable cell inside a named cell is left out too.
A manifest can narrow the compared cells, never widen them past the specification's statement.

A cell is left out only where every end has it at one argument position, which holds when every cell enclosing it has multiplicity `1`; the cell itself may be `?` or `*` (the whole optional cell or collection is left out).
The specification is refused at stage `result`, naming the cell, when
an unobservable cell lies inside a `?` or `*` cell that `[result] cells` does not leave out (`unobservable-cell-position`: mark the enclosing cell unobservable, or move the cell out of it),
an unobservable cell production is placed by no configuration (`unobservable-cell-outside-configuration`),
`[result] cells` names no cell of the configuration (`result-cell-unknown`; `<generatedTop>` and `<generatedCounter>` are compilation's, not the specification's),
names an unobservable cell or one inside an unobservable cell (`result-cell-unobservable`),
or names a cell inside a `?` or `*` cell (`result-cell-position`: name the enclosing cell);
`cell-layout` (the configuration's cells cannot be placed in its KORE terms) is a k-rust defect to report.
The layout is a premise only of leaving a cell out, so a specification that declares no unobservable cell and names no `[result] cells` is never refused with `cell-layout`: its slot is `whole-term`, and `compared` is null when its cells cannot be placed.

The `check`, `results` and `run` documents (and so `report`) carry `result`, `{slots, compared, not_compared, unobservable}`, null when the specification is refused:
`slots` the slot names (`["exit-stop", "whole-term"]` or `["exit-stop", "cells"]`),
`compared` the outermost cells compared (the named cells when the manifest narrows them; a cell listed is compared except for the cells of `not_compared` inside it; null for a `whole-term` slot whose cells cannot be placed),
`not_compared` the cells left out, and `unobservable` every cell the specification declares unobservable, each in configuration order.
Where the slot is `cells`, a program's recorded final configurations and ends are the projected ones.
A mutation that only adds or removes `unobservable` compiles to the same KORE and is `equivalent`.

The tool supplies everything else: the k-rust revision is the build's (every output's `k_rust_revision` is k-rust's build identity, `k_rust::build_identity`: the version of the in-repo k-rust kink is built with and a digest of its sources; the semantics identity and the cache keys name the version, `kink_native::K_RUST_REVISION`, beside the executable's digest),
and the below-floor conformance cases (kink-corpus `BELOW_FLOOR`) are refused for the entry and for every file the load reads (stage `refused-case`).

## `kink-flow check FLOW.toml [--mutations MUTATIONS] [--cache DIR]`

Admits the specification through kink-corpus's admission stages, with the same stage names and refusal reasons:
`manifest` (this crate: the manifest does not decode), `refused-case` (a below-floor conformance case), `load`, `semantic-input`, `compile`,
`representation`, `declaration-census`, `result` (this crate: the compared cells, above under "Which cells are compared") and `inputs`, then `assume-joined` (this crate: the definition's full
critical-pair check on the input backend, against `[spec] assume_joined`).
The declaration census passes a hooked symbol whose hook its reference declares with the same argument and result sorts (rule H), or one whose hook the reference does not declare and k-rust has no evaluator for (inert); any other hooked symbol is refused (`vi-t13`).
The reference is k-rust's embedded builtin files and blockchain-k-plugin's `plugin/krypto.md` at `651a2db5` (kink-native `census::KRYPTO_REFERENCE_TEXT`, pinned by digest), so a declaration of one of the plugin's `KRYPTO` hooks with its documented sorts is admitted whichever file or symbol declares it, and one with other sorts is refused, also for a hook k-rust does not evaluate (`KRYPTO.sha512`).
Sorts are compared by name: a builtin sort's name is backed by its sort hook, but the point sorts `G1Point` and `G2Point` are not, so the BN128 hooks are admitted on any sort of that name, and their value is k-rust's reading of the point constructor (the definition's only constructor of that sort with two, or four, `Int` arguments; `docs/compatibility.md` "Cryptographic hooks", which states k-rust's contract for these hooks against this revision of `krypto.md` and is pinned by kink-native's `the_krypto_reference_is_k_rusts_crypto_contract`).
Admission is not a verdict: until k-rust records the values `krypto.md` leaves open on each run, every hook k-rust evaluates stays in the exclusion census, so a definition that declares one has no kill and no `no` (`implementation-chosen-hook`), and `fuzz` refuses it at `exclusions`; a query's `hit` through such a hook stands (query "Answers" below), and rests on k-rust's evaluation as that contract states it (lowercase hex, the ECDSA failure values, the point constructor by signature).
Then each program is admitted on its own (file read: stage `load`; typed inputs: `inputs`/`typed-inputs` or `inputs`/`input-value`; parse: `inputs`/`parse`;
a program text on a definition without `$PGM`: `inputs`/`stray-program`; other assembly failures: `inputs`/`assemble`; the concrete-state check and the input gate: `inputs`/`input-gate`;
an initial configuration with no value: `inputs`/`initial-undefined`).
A refused specification skips the programs; a refused program never stops the others.

A test's expected result is what the specification computes from its inputs.
When the baseline's initial configuration has no value (an input divides by zero, directly or through a function), the specification computes no start, so the case has no expected result: a kill by it would be false.
Admission runs each program's initial configuration on the baseline to depth 0, bounded by `budget.time_ms`, and refuses it (`initial-undefined`, listing the case's inputs) when that run ends in vacuous leaves only, whether the inputs are text or typed.
The bound is part of the rule: admission runs no step of a program, and a case whose start has a value and whose later step has none is admitted, since that step is the program's behavior, which its run reports.
The refusal needs the run to be evidence: where the initial configuration is excluded (below) or the depth-0 run is (a contradicted `total` claim, ...), whether the start has a value depends on what the definition leaves open, and the program is admitted and reported as excluded instead.
An input whose definedness the definition leaves open (a partial function applied outside its equations) is not refused either: its run reports what it finds.

Beside the data facts, admission reads the definition exclusions of the input backend's load, the facts the campaign runner reads for every run (kink-native `DefinitionExclusions`; root README, "What a kill trusts"),
and decides for each admitted program whether every run of it on the baseline is excluded before it runs:
by the definition exclusion, which excludes every run on the specification, or by the exclusion of the program's initial configuration (it applies a hook whose value the definition leaves open, or a function or operator whose value depends on the short-circuit reading).
Neither refuses anything: `results` still runs such a program and gives it no comparable class; its cause says this exclusion as `check` says it, unless a reason only the run shows comes first (a timeout, or a run that contradicts a claim).

**When `check` fails.** `check` fails when a fact known before any mutant runs makes a verdict impossible.
`check` is the compile step of the loop: passing it and then reporting no verdict is the outcome it exists to prevent.
Two kinds of fact are known then, and each is an instance of the rule, not a special case:

- A program that cannot be judged on the baseline takes part in no verdict: no run of it can kill a mutant or show that one survives.
  A program is judged on the baseline when `results` can give it a class from its baseline run, and it cannot be when the specification is refused, when the program is refused, or when every run of it is excluded.
  A definition exclusion makes every program `excluded`.
- A baseline with no data gives no mutation a verdict but `unknown`.
  When the baseline's full critical-pair check has a finding that `[spec] assume_joined` leaves unnamed, or did not read the whole definition, no end of the definition is data (root README, "What a kill trusts"): every mutation with a program to run is `unknown` (`baseline-findings`), no comparable program can kill, and no query answers `no`.
  The programs are still judged (`results` gives each its class and marks it `unable_to_kill`), so they stay `ok`; `spec.baseline_findings` names each finding with what to do about it.

What only a run shows (a timeout, a final configuration kink does not compare, an exclusion a run's own lists give) is `results`' class, not `check`'s: `check` runs no program.

It prints one JSON document:

```json
{"schema": "kink-flow-check", "version": 5, "k_rust_revision": "...", "profile": "no-z3",
 "spec": {"outcome": "admitted", "stage": null, "reason": null, "detail": null,
          "files": [{"name": "calc.k", "sha256": "..."}], "exclusion": null,
          "baseline_findings": null},
 "programs": [{"id": "add", "outcome": "ok", "stage": null, "reason": null, "detail": null}],
 "data": {"assume_joined": [], "has_data": true, "incomplete": null, "findings": []},
 "result": {"slots": ["exit-stop", "whole-term"], "compared": ["k"], "not_compared": [],
            "unobservable": []},
 "mutation_list": null, "mutations": null, "coverage": null}
```

A program's `outcome` is `ok`; `refused`, with the stage, reason and detail of the refusal; or `excluded`: admitted, but every run of it on the baseline is excluded, with stage `definition` (the definition exclusion) or `initial-state` (its initial configuration's), the exclusion's name as `reason` (`short-circuit-reading`, `implementation-chosen-hook`, `equals-condition`, `load-stack-stop`) and why as `detail`.

`spec.exclusion` is the definition exclusion, null when there is none (or the specification is refused): `{exclusion, detail, causes}`.
`detail` says what makes it hold, naming each sentence with its position (`file:start_line:start_column-end_line:end_column`, the file as the load named it; a builtin's is `krust-builtin://...`), at most eight causes; `causes` lists every one.
For `short-circuit-reading`, each cause is one rule's chain `{rule, effect, part, links}`:
`effect` is `applicability` (whether the rule applies can differ between a backend that evaluates every operand and one that skips an operand a short-circuit operator does not need) or `result` (its result can be undefined in k-rust's reading where a skipping backend gives a value);
`part` is where in the rule the first link sits (`{part: "condition", leaf}` or `{part: "right-side"}`);
and `links` go from the rule to the operator, each `{link: "function", function, dependence, equation, part}`, a function applied there with the equation (and the part of it) through which it depends on the reading (`dependence` `valued` or `undefined`),
or `{link: "operator", operator, position, operand, term, term_symbol}`, the short-circuit operator, the position of the operand a backend may skip, the operand, and the application in it that may be undefined.
A sentence is `{name, module, label, id, source, location, authors}` (`id` its compiled `UNIQUE_ID`, `module` its KORE module), where `authors` lists the baseline sentences it was compiled from, each named as `results` names a rule (`{module, index, label, file, start_line, end_line}`), and is empty for a sentence a compiler pass generated; a symbol `{id, module, label, hook, source, location}` (`id` its KORE name), and a term (`leaf`, `operand`, `term`) is printed as kill evidence prints a value (`{text, rendering, truncated}`, below under "Kill evidence").
For `implementation-chosen-hook` a cause is `{sentence, symbol, hook}`, for `equals-condition` `{sentence}`; a `load-stack-stop` has none (`detail` gives the count).
`results` and `run` print the definition exclusion with the same formatter (kink-flow `exclusion`), and `fuzz` its `detail`.

`data` is the baseline's full critical-pair check under `[spec] assume_joined`, as the run, `results` and `query` documents print it (`{assume_joined, has_data, incomplete, findings}`, below under `run`); null when the specification is refused.
`spec.baseline_findings` is null when the baseline has data (or the specification is refused), else `{detail, findings, incomplete}`:
`findings` lists each finding no name assumes, `{name, verdict, description, next}`, with `next` saying what to do about it by its verdict;
`incomplete` is null, or `{detail, next}` when the check did not read the whole definition;
and `detail` says both in one text, naming at most eight findings.
A name assumes a finding away, so naming one is right only where the definition is right and the checker could not show it:
for an `undecided` finding, review it: name it in `[spec] assume_joined` if it does not hold of the definition (the pair joins; for an equation, it agrees with its hook or applies as written; for a precondition, it is met), or else fix the definition;
a `genuine` finding is a pair a ground input of which has two normal forms, so fix the definition (a name is accepted, but every verdict then rests on a premise known to be false);
a `decided` finding, or one with no name, cannot be named, so fix the definition;
and no name can assume what the check did not read, so an incomplete check is a limit of k-rust's checker to report.

Version 2 (CF-18) adds `mutation_list`, `mutations` and `coverage`, which are null without `--mutations`.
Version 3 (CF-02) adds `spec.exclusion` and the program outcome `excluded`, and `check` exits 1 when a program cannot be judged on the baseline; before, a definition with a definition exclusion passed `check` with every program `ok`.
Version 4 adds `data` and `spec.baseline_findings`, and `check` exits 1 when the baseline has no data under `[spec] assume_joined`; before, such a specification passed `check`, and `run` then reported every mutation `unknown`.
Version 5 adds `result`, the slots and the cells compared (above), and the stage `result`.

Exit status: 0 when every program is `ok` (so the specification is admitted), `spec.baseline_findings` is null and, with `--mutations`, the list decodes and no mutation is refused (warnings do not count);
1 when the manifest, the specification, a program, the mutation list or a mutation is refused, a program is `excluded`, or the baseline has no data (`spec.baseline_findings`); 2 on a usage error (message on stderr).

### Checking mutations

`check FLOW.toml --mutations MUTATIONS` resolves every mutation of the list against the current specification, exactly as `run` resolves it, and runs no program: no mutant is compiled and nothing is written.
It is the compile step of an author's loop: run it after every edit of the list or of the specification, before `run`.
`MUTATIONS` is a `MUTATIONS.toml` or a mutations directory (`MUTATIONS.toml` below).
The check compiles no mutant, so `ok` means that the mutation resolves, not that `run` will judge it:
a mutant that kink does not compile (a replacement with an unbound variable, say) or whose equations may have no model (`inconsistent-mutant`) is found only by `run`, which gives it the status `invalid` and exits 1.

The command is library code in two steps, so that a front end can add findings of its own between them and print the document `kink-flow check` prints:
`kink_flow::cli::check_corpus_mutations` admits the specification and the programs, reads the cached coverage and checks every mutation, returning all of it as data (each mutation's resolution and findings: `kink_flow::check::MutationCheck`);
`kink_flow::cli::check_mutations_document` renders the document and decides the exit status.
A finding a front end adds with `refusal: true` refuses its mutation as a resolution failure does.
A resolved mutation gives each edit as it was applied (`ResolvedMutation::edits`: the edit's byte range in the file's K view, its replacement, and where the replacement lies in the edited view), beside each edited rule's before and after, which merge the edits of one rule.

The document is the check document above, with:

- `mutation_list`: `{outcome: "ok" | "refused", detail}`; a list that does not decode is refused with the key at fault, and `mutations` is then null.
- `mutations`: one row per mutation, in list order, `{id, misunderstanding, outcome, digest, rules, refusals, warnings}`.
  `outcome` is `ok`, `refused`, or `error` for a resolution the host refused (`host-stack-refused`, which is not the mutation's fault).
  `rules` are the edited rules, as in the run document: `{module, index, file, label, start_line, end_line, edits, before, after}` (null when the mutation does not resolve).
  Each refusal and warning is `{reason, edit, rule, detail, next}`: `edit` the index of the edit at fault (or null), `rule` the baseline sentence `{module, index}` it is about (or null), and `next` one sentence saying what to do.
- `coverage`: `{decides, without_record, incomplete, detail}`, what the cached results (`results`, read from `--cache DIR` or `.kink-flow/`, never written) say about which rules the corpus uses: `decides` is true when every program has a current result record and every comparable program's coverage is complete; `without_record` and `incomplete` name the programs that keep it false.

A refusal is a reason of the table below (`MUTATIONS.toml`) with its next step: a stale anchor (`unknown-label`, `find-not-found`, `line-outside-rules`, `source-changed`), overlapping edits (`overlapping-edits`), a sentence that is not a rule (`non-rule-sentence`), an edit that changes nothing (`no-change`), and the others.
A refused mutation is one `run` reports as `invalid-mutation`.

Warnings refuse nothing:

| Warning | Meaning |
| --- | --- |
| `line-anchor` | The edit addresses its rule by `line`. A line moves whenever anything above it changes; the edit then fails, or lands on whichever rule holds that line and the text. `next` names the rule's label to address it by, when it has one. |
| `text-anchor` | The edit addresses its rule by its `find` text alone. After an edit of the specification the text can occur once in another rule, and the edit then lands there. `next` as for `line-anchor`. |
| `unreached-rule` | No comparable program witnesses this rule's edit in the cached results: none reached the rule (k-rust `matched`) for an edit of its `requires`, none applied it (`applied`) for any other edit, which is `run`'s witness rule (step 3). It is given per edited rule: a mutation that edits several rules may still be killed by a program that witnesses another of them, and an edit (such as a widened left-hand side) can make a program that never used the rule use the mutant's. Given only when `coverage.decides`. |
| `no-coverage-signal` | k-rust's coverage cannot record the rule (a macro, alias, `smt-lemma` or non-executable rule, as in `results`), so no program can be shown to reach it. |

`kink-flow --version` prints `kink-flow VERSION (k-rust REVISION)`, where `REVISION` is k-rust's build identity (`k_rust::build_identity`: its version and a digest of its sources, such as `0.8.0+src.<hex>`), the value every document's `k_rust_revision` names (GUIDE-USABILITY 5, KINK-R4: within each document's version, since the field's shape did not change; before, every document but `fuzz`'s named the version alone), and exits 0.

## `kink-flow results FLOW.toml [--verify] [--mutations MUTATIONS] [--cache DIR] [--output json|verdicts]`

Runs every program whose result is not cached yet and reports, per program, whether it can
kill a mutant, and, per rule of the specification, which programs reach it.

Each program runs on the baseline as its own zero-mutant campaign (kink-campaign's runner),
with two oracles: the exit stop (no exit-code cell) and the final configuration without the cells left out (`whole-term` or `cells`, above under "Which cells are compared").
The document's `result` names the slots and the cells compared; version 5 of the document adds it, and, where the slot is `cells`, makes a program's `final_configuration` and `ends` the projected ends.
A program's class is

| Class | Meaning | What to do |
| --- | --- | --- |
| `comparable` | The run ended and its final configuration is a value kink compares. | Nothing: this program can kill mutants. |
| `timeout` | The run did not end within `budget.time_ms`; `cause` gives what k-rust returned when the bound fired (see below). | Make the program terminate, or raise the budget. |
| `unknown` | The run ended without a comparable value (for example a collection holding a `Float`, `budget.max_depth` reached, an undecided step), or the run is excluded (`cause` then names the exclusion, such as `contradicted-claim`); `cause` says which. | Write a program whose final configuration kink can compare; for a `contradicted-claim` exclusion fix the claim the row's `specification_diagnostics` names, not the program. |
| `refused` | The program was not read, parsed or assembled; `cause` is the refusal. | Fix the program. |
| `error` | The run or the runner failed. | Report it. |

Only comparable programs can kill a mutant; the others are reported and never count as covering a rule.

The cache is `.kink-flow/` next to `FLOW.toml` (or `--cache DIR`); deleting it is always safe.
One JSON record per program, `results/<spec digest>/<program digest>.json`, holds its key
(result schema version `kink-flow/result/v9`, kink's build identity `kink_build`, kink's semantics identity `kink`, the two digests and the budget), class and cause,
the baseline row exactly as the campaign report encodes it with the digest of its `run` part
(`run_sha256`, comparable programs only), the final configurations as KORE text (an undefined step's pre-step configuration is none, so a run whose every path takes an undefined step lists none, and its baseline row's exit stop holds no class for it; since v7, kink27 R1-UNDEF), the rule
coverage, `wall_ms`, the wall time of the program's live baseline run (outside the key and
the run digest; it orders the kill search, see `run`), and, since v5 (re-pin adoption A-1),
`specification_diagnostics`, the baseline run's contradicted-claim records (see `run`), and
`smt_unknowns`, its count of undecided solver answers (both outside the key and the run digest),
and, since v9 (CF-16), for a comparable program, `ends`: each final configuration's `{head, class}`, in the order of the final configurations (outside the key and the run digest).
An end's `head` is its computation head, the first item of its computation cell (or the cell's content when that is no sequence of items), printed as one line of K text (`{text, rendering, truncated}`, below under "Kill evidence"); null when the end has no computation cell.
The computation cell is the first cell, from the top, whose production has the `maincell` attribute: k-rust gives it to a cell named `k`, and a configuration may declare it on a cell of another name (`<code maincell="">`).
Its `class` is the class the exit-stop slot projects it to, `normal` for every end under the flow's classifier.
`kink_build` is the SHA-256 of the executable that wrote the record (kink-campaign `identity::kink_build`, packet CACHE-ID-fix-1), so a record another build wrote, or one without `kink_build`, is recomputed: the code that decides a result class mostly has no version constant, and only the build tells that it changed.
When the executable cannot be read, no record is read or written, and each row says so (`cache_error`).
The specification digest covers the k-rust revision, the solver profile, how the
specification is loaded and every source file the load reads; the program digest covers the
program's bytes (when it has a program text), start sort, variables and typed inputs, never its id.
A typed input enters by what it denotes: the variable's K name and the SHA-256 of the KAST JSON of
the term the decoder gave (`{name, kast_sha256}`), so editing a value in a file an input reads reruns
the program and reformatting the file does not; a program with no typed inputs has the digest it
had before typed inputs existed. A record is used only when its key is
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
supplies the class, the cause, the final states and the coverage (`diagnostic` counts them). When
the campaign named the exclusion of the baseline run, the cause says that exclusion and why it
holds, never a guess from the shape of the leaves (an excluded run's leaves can all be values); for
`contradicted-claim` it points at the row's `specification_diagnostics` and says to fix the claim,
not the program (re-pin adoption A-1b). An exclusion that holds for every run of the program, the
definition exclusion or its initial configuration's, is said as `check` says it (its program
`detail`), and the document's `spec.exclusion` is the definition exclusion with its causes, as in
the check document (null when there is none; added to version 4 without a new version, since it is
additive). When no exclusion is named and every path ended, the cause
names why a final configuration is not a value kink compares (fz26 KINK-CAUSE-SUBTERM): in the first
leaf whose state's term has no terminal value, the first node, in pre-order, that fails its own test
with its children ignored (a head that is not a free constructor, an overload application k-rust does
not judge data, a domain value without a trusted codec, a collection node, ...), its cells and
collection entries (`<T>/<store>/Map entry 1 value`), the test, and its KORE cut after 160
characters; for an overload application, also the first node inside it that fails its own test.
Naming the first subterm without a value would always name the root. The judgement is kink-native's
`ObservationDecider::first_non_value`, from the walk the runner's terminal value takes, with the
decider built as the runner builds the baseline's (collection trust, the baseline's data facts). It
judges the baseline alone: whether an end is data under a mutant's definition is decided for each
pair by the runner, never in this cause. Only the campaign admitting a baseline makes a program
`comparable`.

`--verify` reruns every program that has a current record and compares: a different class,
a different `run_sha256`, or a record whose `run_sha256` is not the digest of its own baseline
row is a mismatch. Mismatches are listed (program, record path, detail) and records are never
rewritten by `--verify`; delete a mismatching record (or the cache) to recompute it.

The document (version 4 since CF-16, when a program's row came to carry `ends`; version 3 since KINK-R4, when a rewrite rule's `fired_by` came to list only programs a path of whose run takes the rule's step, k-rust `committed`, a field's meaning changing although its shape did not; version 2 since re-pin L2-1; the row field `unable_to_kill` and the member `data`, fz26 KINK-BASELINE-FINDINGS, were added to version 2 without a new version, since they are additive and no command reads a `results` document back) lists every program `{id, digest, class, cause, cached, verify, wall_ms, specification_diagnostics, smt_unknowns, ends}` (`ends` from the result record, null unless comparable; the two before it from the result record since re-pin adoption A-1, so absent on a `refused` row, which has none; a `comparable` row also has `unable_to_kill: "baseline-findings"` while the baseline has a finding `[spec] assume_joined` leaves unnamed, its class and coverage being facts of the run k-rust made), the baseline's findings (`data`, see "The report: the run document"), every authored
rule `{module, index, label, file, start_line, end_line, status, reached_by, fired_by}` with status
`uncovered` (no comparable program reaches it: the next program to write) first, then
`covered`, then `no-coverage-signal` (none of the rule's compiled ids can appear in a run's coverage: it
compiles to no axiom, or it is a `non-executable`, macro, alias or `smt-lemma` rule; `reason` says which), the
mismatches, a summary, `baseline_runs` (`results --verify` runs every program live:
`live` is the number of programs, `reused` 0) and `untargeted_rules`.

A rule's coverage is k-rust's run coverage of each comparable program's baseline run (kink-native
`coverage`, `kink/coverage/v2` since re-pin L2-1, v3 since L2-1-tail), rewrite rules and equations alike: `reached_by` lists the
programs that began to decide one of the rule's conditions for an instance whose left-hand side matched, or
applied it (k-rust `matched`), and `fired_by` those that fired it: for a rewrite rule, some path of the run takes its
step (`committed`: a step built a successor of the rule that its own normalization showed defined), and for an
equation, an instance gave a result (`applied`). Since result schema v6 (KINK-R4) a rewrite rule's `fired_by` no longer
lists a program whose candidate of it was rolled back because its successor was undefined, or whose step by it was
undefined (both are in `applied`, and no path takes either): it reads the predicate `fuzz --fired` targets (k-rust
`committed`, which `--fired` calls `covered`), so a program `fuzz --fired` confirms is one `fired_by` lists, although
`fuzz` offers one program, found under its own budget, not every program `fired_by` lists.
Neither is an over-approximation of what can change a result: a
higher-priority rule whose left-hand side never matched is not reached, although its failure is what lets a
lower-priority or `owise` rule fire. The record holds the reached, applied and fired sentences (`coverage.sentences`,
`coverage.applied_sentences`, which orders `run`'s programs, and `coverage.fired_sentences`).
A `non-executable` rule is one k-rust never runs (it internalizes executable axioms only), so no program can reach it:
since re-pin L2-1-tail it has status `no-coverage-signal` with reason `a non-executable rule: k-rust never runs it, so no
program can reach it`, never `uncovered`; before, it was listed `uncovered`, as a next program to write.
What coverage is meant to cover, what it is not and why, and what is not built yet are stated once in [kink's README](../../README.md#what-coverage-covers), "What coverage covers":
an `uncovered` row can be a simplification, `symbolic` or ceil equation, which is out of scope and needs no program,
and no field shows a `requires` that was reached and did not apply.

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
(several edits make a correlated mutation), and the plausible misunderstanding of the specification it writes:

```toml
[[mutation]]
id = "add-becomes-sub"
misunderstanding = "addition evaluates as subtraction"   # required prose; `note` is its alias

  [[mutation.edit]]
  file = "calc.k"            # optional when the spec reads one file, or when rule is given
  rule = "add"               # optional: a rule label ("add", "CALC.add"), or a unique suffix of its components
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
and `[label(x)]` as the bare `x`, and either input addresses either form in module `MODULE`.
The anchor also addresses a label it is a suffix of, in whole components, components being separated by `.` or `--` (the separator of KRS's labels):
`plus_zero` addresses `nat--plus_zero` (and `NAT.nat--plus_zero`), `mul--plus_zero` addresses `nat--mul--plus_zero`, and `zero` addresses neither.
The anchor must address exactly one label, whether as the label itself or as a suffix of it: no label takes precedence over another.
A mutation is stored and replayed after every edit of the specification, so a precedence would move an anchor silently: `plus_succ` addressing `nat--plus_succ` would move to a rule that later comes to be labelled `plus_succ`; instead the anchor is refused there, as a stale anchor is.
(`krs prove --claim` lets the whole label win, which suits a filter typed once.)
An anchor that several labels match is `ambiguous-label`, naming each with its module-qualified label (`NAT.plus_succ`, `NAT.nat--plus_succ`), the fullest anchor a label has; one that matches none is `unknown-label`, naming the labels that contain its last component.

`misunderstanding` says, in prose, which mistake an author could make that the mutation writes down: a mutation is meant to be one, a reviewer judges it by what it says, and the next program for a survivor follows from it.
It is required (`note`, its former name, is accepted as an alias; giving both is an error), and it enters no digest, key or hint; the run document's row keeps it under `note`.
Unknown keys, values of the wrong type, duplicate or empty ids, a mutation without edits and one without its misunderstanding are errors naming the key.
`testdata/flow/calc/MUTATIONS.toml`, `testdata/flow/register/MUTATIONS.toml` and `testdata/flow/markdown/MUTATIONS.toml` are complete examples.

### A mutations directory

Every command that reads a mutation list (`check --mutations`, `results --mutations`, `run`, `fuzz --mutations`) takes a file or a directory.
A directory, such as a KRS package's `kink/mutations/`, holds one `<topic>.toml` per topic, each with one or more `[[mutation]]` in the format above:

```text
kink/mutations/add-carry.toml    [[mutation]] id = "ge" ...   -> mutation add-carry/ge
kink/mutations/add-carry.toml    [[mutation]] id = "gt" ...   -> mutation add-carry/gt
kink/mutations/sub-borrow.toml   [[mutation]] id = "lt" ...   -> mutation sub-borrow/lt
```

Every regular file directly in the directory whose name ends in `.toml` and does not start with `.` is read, in byte order of the names; subdirectories and other files are not.
A mutation's id is qualified by its file's stem, `<stem>/<id>`, so that ids are unique across files (a stem holds no `/`) and agents adding mutations to separate files never conflict; `--only` and `--kill` take the qualified id.
An error names the file (`add-carry.toml: mutation "ge".edit[0]: ...`).
The id only names the row: a mutation resolves, is cached and is hinted the same under either id.

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
reason `inconsistent-mutant`, and its row's `inconsistent_pairs` names the pairs. A mutation that only weakens the
specification is `unkillable` before either check and builds no mutant (README.md, trust section). The functions whose pairs are read
are those whose compiled equations the edit changes or reaches (a `#let` or `#fun` lambda included), with kink-patch's
source reading as a fail-closed cross-check (re-pin R0c-fix-4): a sentence the edit touches that compiles to an
equation of a function the source reading does not redefine makes the mutation `unknown` with reason
`unsupported-claims`, and the row's `removed_claims.unsupported` names each such equation (key `unread-equation`,
value `{head, equation}`; re-pin R0-tail).

A mutation that fails any check is `invalid-mutation`, with the offending edit (`edit[i]`) when one is at fault,
a reason and a detail; it is never compiled. `check --mutations` gives each reason's next step (`InvalidReason::next_step`). Reasons:

| Reason | Meaning |
| --- | --- |
| `unknown-file` | `file` is not a source file of the specification. |
| `file-required` | The specification reads several files and the edit names neither `file` nor `rule`. |
| `unknown-label` | No rule has the label, and no label ends with it as whole components: the rule was renamed or removed (a stale anchor), or the anchor is misspelt. |
| `ambiguous-label` | The anchor names several rules, as their label or as a suffix of their labels' components; write more of the label: more of its components, or the module-qualified label the detail gives for each. |
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
| `no-change` | The edited rule equals the original up to formatting, or an edit's `replace` is its `find`: the edit changes nothing. |
| `edited-rule-too-deep` | An edited rule is too deep for kink: its patch's document would nest deeper than kink-patch `MAX_JSON_DEPTH` (two JSON levels per term level: terms about 300,000 levels deep in a release build, 64,000 in the unoptimized test build), so the mutation has no encoding and no identity. This is kink's limit, not a fault of the mutation. A patch holds each edited rule whole, so the detail gives the rule's depth as a whole and the specification's rule's: when the specification's rule alone is already past the limit, it says that no mutation that keeps the rule's deep part can be judged in this build (target other rules, or replace the deep part by a shallow one; re-pin L1-4); otherwise a mutation that keeps the whole rule within about half the limit in term levels is judged (re-pin L1-3-tail). Below the limit a rule's depth decides nothing: its typing and its patch's encoding run on a stack sized from that depth, on any thread (re-pin L1-3-fix-2; before, a rule about 230,000 terms deep aborted the whole run in typing). |
| `host-stack-refused` (status `error`) | The host refused the native stack that encoding the mutation's patch needs: the system would not map a stack segment of the size the patch's depth needs (an address-space limit such as `ulimit -v`, or memory it will not commit). It is the host's limit, neither a fault of the mutation nor a verdict, so the row is `error`, not `invalid-mutation`; rerun where the host grants the stack. Only a deep patch needs a segment: the segment is sized from the patch's own document depth (re-pin L1-3-tail; at L1-3-fix-2 every patch more than 48 term levels deep took a segment sized for `MAX_JSON_DEPTH`, 768 MB in release, and a refusal was reported as `patch-rejected`). |
| `no-usable-span`, `patch-rejected` | Defensive: a rule's offsets and location name different text of its K view, or kink-patch refused the patch for a reason other than typing (a stale pin, a patch that does not resolve); not expected on rules k-rust loaded. No typing error refuses a mutation (re-pin L2-2-fix-1): a mutant is valid when it compiles, so compilation decides, and kink-patch records the edited rules' errors in compilation's typing view (`SentenceTyper::for_compilation` with `typing_in`) as the row's `typing_diagnostics`. k-rust documents that view's errors as errors compilation stops at, but at 501f18b9 it refuses shapes compilation accepts: a local function with a variable in a cell with children (`CellCompletion`), and a rule `a(X) => b(X)` whose sorts `A` and `B` have a second common supersort in the main module (a non-unique least upper bound). At the pin 8f8ad57c5 that view types the second shape (k-rust KINK-21/1), so its rows carry no typing diagnostic; the first remains. |

## `kink-flow run FLOW.toml MUTATIONS [--only ID]... [--verify] [--order cost|corpus] [--compile-workers N] [--no-memo] [--cache DIR] [--output json|verdicts]`

Runs the kill search: for each mutation of the list (in file order; with `--only`, only the named ones),
is there a program of the corpus whose result the mutation changes?

1. The result cache is brought up to date first (`results` without `--verify`).
   Only `comparable` programs can kill; the others are never run.
   A program whose cached record (one read from the cache, not computed by this command) is class `timeout` and that a killer hint names
   is run once more (a timeout depends on the host's load):
   its record is replaced only when the class or the run digest changes, and the row says `"rerun": "timeout"`.
2. The mutation is resolved into one patch (see `MUTATIONS.toml`); an `invalid-mutation` stops there.
   A mutation whose edit only weakens the specification is `unkillable` and stops there too (README.md, trust section), unless a program is in O (step 3) and the baseline has a finding `[spec] assume_joined` leaves unnamed: then it is `unknown` with reason `baseline-findings`, as every such mutation is, since the weakening argument reads the baseline's normal forms as a model of the specification, which such a finding puts in doubt, and fixing the specification comes first.
3. The programs are ordered (O): those whose cached coverage witnesses an edited rule's edit (rewrite rule or equation) first, then the rest.
   An edit that changes the rule's `requires` is witnessed by a program that reached the rule (k-rust `matched`: it began to decide the condition); every other edit (a right-hand side, an `ensures`, a left-hand side, an attribute, a deletion) by one that applied it (`applied`: a step built a candidate of it, defined or rolled back; wider than `results`' `fired_by`, since an edit can make a rolled-back candidate defined), since a program that only refuted the rule's guard never runs what the rule does (re-pin L2-1-tail).
   The edit is read from the rule's text before and after it, before the mutant compiles, so this is kink-campaign's reading of a site-local edit (README.md, trust section), except that an equation edit kink-campaign leaves in manifest order (its left-hand side, an attribute, an `owise`, `smt-lemma`, `concrete` or `symbolic` equation, a deleted equation) still puts first the programs that applied the equation, or reached it for a `requires` edit, and that a rewrite rule edit changing the `requires` together with the left-hand side or an attribute is witnessed by `matched` here and by `applied` in kink-campaign (review L2-1-tail-1 D3);
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
   final configuration without the cells left out kills, live in this command or cached under an exactly matching key.
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
- The specification's input grammar (kink-corpus `InputGrammar`: the program grammar with its macro-expansion definition, the declared variables, the start sort, whether the definition has stream cells) and one configuration assembler are built once per command, on the first program it assembles, and serve every later program (`InputSession`, R5-INPUT-COST); before, each program rebuilt them, about three whole-definition resolutions and two parser constructions per program, and its derived views once per configuration value. Each is a function of the specification alone and the assembler is cleared before each program, so every initial configuration and refusal is the one a fresh assembly gives (`tests/check.rs` `programs_share_one_input_grammar`, kink-corpus `tests/input.rs` `one_assembler_assembles_what_assemble_input_does`). A session is opened with its specification (`ProgramInputs::session(&spec)`), and the inputs accept only the specification admitted beside them, so no program is assembled with another specification's grammar.
- The resolution memo, `memo/resolutions/<spec digest>/<entry digest>.json`, holds per mutation the facts of its resolution a row decided by tier 1 reads: the patch digest, the edited rules (texts, lines, label, whether the `requires` changed), the tier-1 mutation identity, the typing diagnostics and the claims the edit leaves unbacked. A mutation whose record has exactly the current key and that tier 1 decides with no call (a valid `killed` record, or a valid `agree` for every program of O, or no comparable program) is not resolved: its row is built from the facts by the code that builds it from a live resolution. Every other mutation is resolved live and its facts are written, so every mutation that compiles or runs anything was resolved in this command; the record holds no patch (the patch's canonical JSON does not carry k-rust's term metadata, so a decoded patch would not be the one resolution builds). The key names every input resolution reads: the specification digest (the k-rust revision, the profile, how the specification is loaded and every source file's name and SHA-256: resolution reads the admitted load, each touched file's bytes checked against that SHA-256, and an edited load of the same files under the same options), the mutation's edits in order with every field (`file`, `rule`, `line`, `find`/`replace` or `delete`; the id only names the row and the misunderstanding is never read), `kink_build` and `kink`. Records are read only while every source file still has the SHA-256 the admission recorded. A typing diagnostic that says a rule was not typed (a refused stack segment) depends on the host, so facts that carry one are never written.
- The census memo, `memo/census/<spec digest>.json`, holds the declaration census of the admission (the VI-T13 gate), a function of the compiled baseline and of kink's build (its reference: the builtin files, the pinned `krypto.md`, and the hooks k-rust implements), keyed on the specification digest, `kink_build` and `kink`.

The premises are those the result cache and tier 1 already rest on: k-rust's load and compile are deterministic (the same files under the same options give the same definition, C-12), and the key names every input (`tests/memo.rs` pins each field of a mutation's edits: a key differs when any one field differs, it decodes back to the edits, and two mutations that differ in one field never share a record; it builds both keys member by member, the version, kink's build and semantics identity, the specification digest and the edits, and requires them equal to `memo`'s, and `tests/results.rs` requires the specification digest to change with each `[spec]` field, so a key that drops an input fails a test; re-pin L1-4-tail). Before any resolution record is read, every source file must still have the SHA-256 the admission recorded, so a file changed between the admission and resolution reads no record (`tests/memo.rs` changes one there). One premise is new, the host premise: a record exists only because resolution succeeded on the host that wrote it, and success can depend on the host (the native stack segment of the patch's encoding, which live gives `host-stack-refused`; the heap and address space of the edited load, which live aborts the process when exhausted; and the native stack segment each edited rule is typed on, which a host can refuse while it grants the encoding's, and which live gives a typing diagnostic saying the rule was not typed, with the row's status unchanged). The key does not name the host's capacity: a memo hit returns the tier-1-decided row that a host which could resolve the mutation computed for the same mutant identity, where live resolution on a smaller host would end `host-stack-refused`, abort, or give the same row with a typing diagnostic saying the rule was not typed where the memo gives the writer's typing diagnostics (re-pin L1-4-tail). That cannot make a false kill or hide a survivor (the mutant is judged where the host grants the stack, as this README recommends for `host-stack-refused`, and typing diagnostics decide nothing), but before L1-4 every resolution was recomputed in every command. So run documents with and without memos are equal on hosts that grant the stack and heap resolution needs. The memos are off where tier 1 is (the Z3 profile, an unreadable executable) and with `--no-memo`. `run --verify` decides nothing from a memo: it resolves every mutation and runs the census live, compares each record that has the current key, reports one that differs (the row's status `error`, reason `resolution-mismatch`, and an entry `{mutation, program: null, cached: {resolution}, live: {resolution}}` in `mismatches`, also for a mutation `--only` does not select or that a corpus error left unsearched, which has no row; a census, `{mutation: null, program: null, cached: {census}, live: {census}}`, also when the live census refuses the specification, so a stored census that admits a specification the live census refuses is reported in the refused document) and writes no memo. A memo never enters the run document, an outcome record or a hint: on such a host a run with and without memos writes the same ones (`tests/memo.rs`, cold and warm, with every status and a Markdown source; each key input changed, a forged record under the current key used and reported by `--verify`, in both directions for the census). A memo that cannot be written only means a later recomputation, so it is not reported.

### Cost model

Where a run's wall time goes (release build, `--order corpus`, 4 compile workers; re-pin L1-3 and L1-4 measurements, shared 32-core host at load 15-35):

| Stage | Cost | Cold | Warm (tier 1 decides) |
| --- | --- | --- | --- |
| Admission: load | one load of the specification and the prelude, about 0.12 s on `examples/imp` | once | once |
| Admission: baseline compile | about 0.22 s on `examples/imp` | once per command (before L1-4: once more per program run live) | once |
| Admission: declaration census | 0.52 s, of which its reference prelude's compile 0.22 s (measured before kink27 GK-3 added `krypto.md` to the reference) | once | read from the census memo |
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
hook refused for the memory allowance, on a leaf or on k-rust's `allowanceRefusals` list of the run or its load (re-pin adoption
A-1: a refusal in a passed-over equation or an undone attempt leaves no diagnostic), are `unknown` (failure `stack-stop`,
`load-stack-stop`, `allowance-refusal`; on the baseline the program is not comparable); and in a build with the Z3 profile tier 1
is off (`outcome_cache.enabled` false, with the reason: a solver query can time out). k-rust now counts a run's undecided solver
answers (`smtUnknowns`); kink reports the count (`smt_unknowns` in a program's row and, when nonzero, in an executed entry) and
never reads it as an exclusion (decision D-7 (a1)). Each record carries
`allowance_bytes`, the writing process's memory allowance, for diagnosis only: it is in neither the key nor the record digest.
This closes the stack dependence of k-rust KINK-06/4 and KINK-06/5 for every comparison through `execute`, live and cached.
What remains is kink's verdict-path calls outside `execute` (`definition_facts`, `BackendRelations` unification, the bridge's
internalization; re-pin finding B-13(a)), which decide nothing for ground programs, and the Z3 profile, where tier 1 is off.
A mutation whose specification uses a hook for which k-rust chooses a value the definition leaves open with no run-level record
of it (`String2Bytes` and `Bytes2String`, whose encoding `domains.md` does not name and k-rust's amendment AM-1 states as one
byte per code point, kept by kink's own choice until GK-1/GK-2, and the `KRYPTO`, `HASH`
and `SECP256K1` hooks no builtin file documents; k-rust's own classes, such as `choice`, the order of `keys_list`, `values` or
`Set2List`, mixed-format or NaN-sign Float, `Base2String`'s letter case and substitution's renamed variables, are judged per run
through `implementationChosenValues` below since kink27 R3-CENSUS-RUNLEVEL; an open hook k-rust cannot
evaluate in an execute request, a console operation such as `#getc` or `#write` or one without an evaluator such as
`Float2String`, is judged per run through `unsupportedHooks` below instead, so stock SIMPLE's stream cells exclude nothing), or whose condition or rule
result depends on whether `andBool`, `orBool` or `#if` skip an operand that may be undefined, or that has a rule or
equation condition equating two terms (`{ A #Equals B }`, a gap of k-rust's answers), is `unknown` with reason
`implementation-chosen-hook`, `short-circuit-reading` or `equals-condition` when the exclusion is the mutant's. One of the
baseline excludes every baseline run instead: each program's result is `unknown` with the exclusion as its cause, no program
is comparable, and every mutation gets the status `error`, reason `no-comparable-program`. Since re-pin adoption A-1 a program whose run reads
such a value of one of k-rust's own classes (k-rust's `implementationChosenValues` list, wherever the run reads it: a rule, an
equation, a condition, the initial state) is `unknown` for that mutation (failure `implementation-chosen-value`), and so is one whose run or definition's load left an application unevaluated as an
unsupported hook (k-rust's `unsupportedHooks` list; failure `unsupported-hook`); on the baseline the program is not comparable. A program whose run takes an undefined step that falsifies a
`total` or `preserves-definedness` claim the mutant still carries (a baseline claim its edit does not reach: the claims the
edit leaves unbacked are removed from the mutant, above), or an undefined step through such an operator, is `unknown` for
that mutation (failure `contradicted-claim` or `short-circuit-reading`), and a kill by another program, whose runs are clean,
stands (root README, "What a kill trusts"; decision 2 is per program). Since re-pin adoption A-1 so is a program whose run
lists any record on k-rust's `contradictedClaims` list, observed by the run (a candidate a defined sibling covered, an arrival
a state set absorbed, a condition decided through the contradiction) or by the load of the definition (`observedIn: load`, on
every run's list, so no program of that definition is comparable). On the baseline a contradicted program is not
comparable. Every record is reported as a specification diagnostic, `specification_diagnostics`: in a program's row (from its
result record, the baseline run's records) and in a mutant's executed entry, each `{claim, symbol, k_label, rule_id,
rule_label, application, undefined, observing_rule_id, observing_rule_label, ground, observed_in, says}`, where `says` states,
for a ground record, that the claim is false at the application ("the `total` claim of `td` is false at ..."), which the
author can act on.

| Status | Meaning | What to do |
| --- | --- | --- |
| `killed` | A program's result differs on the mutant; `killer` names the first such program. | Nothing. |
| `survived` | Every program ran to a comparable result and agreed. | Write a program that reaches the edited rule and whose result the edit changes (`reaching` lists the programs whose coverage witnesses the edit now: they applied the rule, k-rust `applied`: a step built a candidate of it, defined or not, or reached it for an edit of its `requires`. `applied` is wider than `results`' `fired_by`, which lists only steps a path takes: a candidate rolled back because its result was undefined is a site an edit can make defined). |
| `equivalent` | The mutant compiles to the baseline's executable definition. | Nothing can kill it; drop or change the mutation. |
| `unkillable` | The edit only deletes equations of functions or narrows their `requires` (reason `weakening`; `weakening` names each edited equation): every model of the specification is a model of the mutant, so no program can kill it. Decided at resolution, after the `baseline-findings` check (run step 2); no program runs. | Change a right-hand side or a rewrite rule, or drop the mutation. |
| `invalid` | The mutant does not compile (`reason` is the runner's failure, for example `rejected`). | Fix the mutation. |
| `timeout` | No program killed it, and a program did not finish on the mutant within `budget.time_ms`. | Write a program that terminates under the mutant and shows a different result. |
| `unknown` | No program killed it, and a program's result on the mutant is not comparable; or, with reason `baseline-findings`, the baseline's full critical-pair check has a finding `[spec] assume_joined` does not name (`findings` lists each with its name and verdict; no call is made and no store is read), or, with reason `mutant-findings`, the claim-free mutant's findings outside the heads its edit can change differ from the baseline's. | Write a program whose result on the mutant kink can compare; for `baseline-findings`, fix the specification or name the findings you accept as premises. |
| `error` | The runner failed for the mutant, a corpus error (`reason`: `baseline-mismatch:<id>`, `baseline-count-mismatch`, `campaign-refused`, `program-refused:<id>`, `outcome-conflict`, `no-comparable-program`), `run --verify` found a cached outcome that differs from a live run (`outcome-mismatch:<id>`) or a memo of the mutation's resolution that differs from its live resolution (`resolution-mismatch`, re-pin L1-4), or the host refused the stack the mutation's patch needs (`host-stack-refused`, see the reason table). | Report it, or fix the corpus; for `outcome-mismatch`, delete `outcomes/`; for `resolution-mismatch`, delete `memo/`; for `host-stack-refused`, rerun where the host grants more address space. |
| `invalid-mutation` | The mutation does not resolve (`reason`, `edit`, `detail`; see the table above). | Fix the mutation. |

A kill folds above every inconclusive outcome: a mutation that one program kills is `killed` even if an earlier program timed out on it.

The document is the report (see "The report: the run document" below).

### The cache directory

Besides `results/` and `report.json` (the last run's document, also written when the specification is refused or no mutation is selected):

- `outcomes/<context digest>/<mutation identity>.json`, tier 1:
  `{schema: "kink-flow-outcomes", version: 2, context, context_sha256, mutation_identity, mutation_id, removed_claims, records: {<program digest>: {program_id, baseline_run_sha256, outcome, slots, mutant_run_sha256, difference, allowance_bytes, record_sha256}}}`.
  `difference` is a `killed` record's kill evidence (below, "Kill evidence"), null on an `agree` record: outside the key, which names every input it is a function of, and inside `record_sha256` (domain `kink-flow/outcome-record/v2`), so a record whose evidence was altered is ignored; no status is read from it.
  A version 1 file, which has no evidence, is not current: its records are ignored and recomputed.
  `removed_claims` is the row's (below), for the reader only: it is read back by nothing and is in no digest.
  The context is `{outcome_schema: "kink-flow/outcome/v1", kink_build, kink, profile, execution_digest: {kind, digest}, budget, oracles, classifier, schedule}` (with `work_factor` set, `budget` also holds `work: {factor, floor}`; `oracles` names the slots, and where the second is `cells` the context also holds `not_compared`, the cells left out, since the `unobservable` attribute is not in the compiled KORE an execution digest may be read from):
  `kink` is kink's semantics identity (kink-campaign `identity`, packet CACHE-ID), `{k_rust_revision, fingerprint, canonical_patch, compiled_kore, patch_admission, claim_removal, mutant_consistency, mutant_effect, weakening, data_facts, terminal_value, definition_exclusion, execution_request, result_schema, coverage, one_sided}`, the version of every kink algorithm an outcome can depend on. Among them:
  `claim_removal` is kink-patch's `CLAIM_REMOVAL_VERSION`, since the mutant every record ran on depends on the claim-removal algorithm (v2 since re-pin R0c-fix-3: the reach follows the overload and unit axioms; v3 since R0c-fix-4: a rule with configuration context is an equation of its head);
  `mutant_consistency` is kink-native's `MUTANT_CONSISTENCY_VERSION`, since a mutant runs (and a record exists) only when its equations are shown consistent (v2 since R0c-fix-4: the check's guard reads the equation and skipped-pair counts; v3 since k-rust FZ-CONFLUENCE: k-rust pairs the equations at evaluated hooks with the hooks' written meanings and refutes more overlaps; v4 since fz26 phase 8: k-rust refutes still more overlaps and splits residuals, joins pairs over sorts with no normal form through the witness equations it adopts, whose adoption can flip between a baseline and its mutant, and the gate reads the mutant's full check from its per-definition facts, `data_facts` below, with their completeness guard);
  `mutant_effect` is kink-native's `MUTANT_EFFECT_VERSION`, since the symbols the check reads, and the cross-check of kink-patch's source reading, come from the compiled definitions (re-pin R0c-fix-4; v2 since fz26 KINK-WITNESS: a head whose adopted witness equations differ from the baseline's counts as changed, a witness reaches the symbols it applies as an equation of its head does, and a flip of the adopted witness pass checks every head);
  `weakening` is kink-patch's `WEAKENING_VERSION`, since whether a mutation is `unkillable`, and so runs nothing, is that test's verdict (v1 since kink27 R5-WEAKENING; v2 since its fix round 1: a label is a conjunction only when it denotes conjunction in every model, so a macro production hooked `BOOL.and` no longer makes an edit a narrowing);
  `data_facts` is kink-native's `DATA_FACTS_VERSION`, since what kink refuses on each definition's full critical-pair check decides whether a mutation can be killed at all (v1 since fz26 KINK-BASELINE-FINDINGS: a mutation is `unknown` with reason `baseline-findings` while the baseline has a finding no `[spec] assume_joined` name assumes, and with reason `mutant-findings` when the claim-free mutant's findings outside the heads its edit can change differ from the baseline's);
  `terminal_value` is kink-native's `TERMINAL_VALUE_VERSION`, since which ends a slot compares depends on it (v1 since fz26 KINK-OVERLOAD-VALUE: an instance-normal overload application is admitted where k-rust's `is_data` holds, and every compared end is judged under both definitions; v2 since fz26 KRUST-ANYWHERE-HEAD: k-rust's data heads also take an `anywhere` head with plain equations declared total or `value-production`, such as SIMPLE's `_[_]`, and drop an overload head declared neither; v3 since kink27 R5-BYTES-ENDS: a `Bytes` domain value, its payload in its sort's stored form, has a trusted injective codec, so an end holding one is compared);
  `definition_exclusion`, `patch_admission` and `execution_request` name the definition exclusions (re-pin R0-tail; v2 since re-pin adoption A-1, which reads k-rust's run-level lists; v3 since fz26 KS-PIN-SCDEF and KINK-CENSUS-RUNLIST: a short-circuit operator is flagged only when a term its skipped operand may leave undefined is not one another operand must evaluate, and the definition-level census reads only the open hooks k-rust evaluates without a record, the others being judged per run through `unsupportedHooks`; v4 since kink27 R3-CENSUS-RUNLEVEL: k-rust's classes leave the census and the initial-state check, a run that reads one being excluded by its `implementationChosenValues` list; each only narrows what is excluded), the rule that no typing error refuses a patch (L2-2-fix-1) and the execution request with its state-set modality and work budget (L1-1);
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
  `{schema: "kink-flow-memo", key, value, record_sha256}`, where `key` is `{version: "kink-flow/resolution-memo/v2", kink_build, kink, spec, mutation}` (`mutation`: the edits, each `{file, rule, line, find, replace, delete}`) or `{version: "kink-flow/census-memo/v1", kink_build, kink, spec}`,
  `value` the facts `{digest, rules, identity, typing_diagnostics, removed_claims, weakening}` (v2 since kink27 R5-WEAKENING added `weakening`) or the census (kink-native `DeclarationCensus::value`), and `record_sha256` the digest of `{key, value}` under the version.
  A record is used only when its key is exactly the current one and its digest recomputes under that key; the path only finds it.

- `patterns/<spec digest>/<pattern digest>/<program digest>.json`, the cached answers of `query` (flow F-18, "Checking a pattern" below). `run` neither reads nor writes them.

Every file is written atomically; deleting any of them, or the whole directory, is always safe.
The `killers/` directory of F-05 is no longer read or written and can be deleted.

Exit status: 0 when every selected mutation got its status (survivors and timeouts included) and none is invalid;
1 when the manifest, the mutation list, the specification or a program is refused, a selected mutation is `invalid-mutation` or `invalid` (its author must fix it before it is judged: it does not resolve, or its mutant does not compile or may have no model), a run failed, a cache file could not be written,
no program is comparable, a corpus error stopped the run, or `--verify` found a mismatch; 2 on a usage error (including an `--only` id that names no mutation, or `--verify` given twice).
The document is the same either way: the exit status is how a script or an agent's loop notices an invalid mutation, and `check --mutations` finds the unresolved ones without running anything.

## The report: the run document

`run` prints one document and writes the same document to `.kink-flow/report.json` (after every mutation, and once more at the end):

`{schema: "kink-flow-run", version: 14, k_rust_revision, profile, result_schema_version, kink_build, kink, spec, programs, unusable_programs, mutations, counts, survivors, result, stopped, outcome_cache, mismatches, baseline_runs, order, untargeted_rules, data}`; `data` (fz26 KINK-BASELINE-FINDINGS, also in the `results` and `query` documents; null in the run and `results` documents when the specification is refused, absent from a refused `query` document) is `{assume_joined, has_data, findings: [{name, verdict, assumed, description}]}`, the baseline's full critical-pair check under the premises.
Version 3 (F-13) names the oracle slots of an executed entry, versions 4 to 6 add row fields (below), version 7 (packet CACHE-ID) adds `kink`, kink's semantics identity, version 8 (packet CACHE-ID-fix-1) adds `kink_build`, the SHA-256 of the executable that wrote it, version 9 (re-pin adoption A-1) adds `specification_diagnostics` and `smt_unknowns` to program rows and executed entries, version 10 (fz26 KINK-BASELINE-FINDINGS) adds `data`, the `findings` of a `baseline-findings` row and a comparable program row's `unable_to_kill`, version 11 (kink27 R5-WEAKENING) adds the status `unkillable` and each row's `weakening`, version 12 (CF-16) adds each executed entry's `difference`, the sides of a cached or one-sided kill, and each program row's `ends`, version 13 (CF-02) adds `spec.exclusion`, and version 14 adds `result` and the slot name `cells`.
`report` prints the stored statuses without re-deriving them, so it refuses (`unreadable`) a document of another version, one written by another build (or naming none), and one whose `kink` is not this build's.

| Field | Meaning |
| --- | --- |
| `spec` | `{outcome, stage, reason, detail, digest, files, exclusion}`: the specification's admission and its digest, and its definition exclusion with its causes (`exclusion`, since version 13; as in the check document, null when there is none). |
| `programs` | The `results` rows `{id, digest, class, cause, cached, verify, wall_ms, specification_diagnostics, smt_unknowns, ends}` (`ends`, each end's computation head and class, since version 12), plus `rerun` for a timeout record run again. `specification_diagnostics` (the baseline run's contradicted-claim records, above) and `smt_unknowns` (its undecided solver answers, reported only) come from the result record (absent on a `refused` row, which has none). |
| `unusable_programs` | Every program whose class is not `comparable`, once: `{id, class, cause}`. These programs are never run on a mutant. |
| `mutations` | One row per selected mutation, in the list's order (below). |
| `counts` | The number of mutations per status (all nine statuses). |
| `survivors` | The ids of the mutations whose status is `survived`, `timeout` or `unknown`: no program killed them, and a new program could. Each survives relative to the cells compared (`result`). |
| `result` | `{slots, compared, not_compared, unobservable}`: the slots and the cells the programs' second slot compares (above, "Which cells are compared"); null when the specification is refused. |
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
| `weakening` | Null, or for an `unkillable` mutation `[{module, index, label, head, kind}]`, `kind` `deleted` or `narrowed`; `head` null for a lemma. |
| `typing_diagnostics` | `[{module, index, label, message}]` (or `{inserted, message}`): the edited rules' errors in compilation's typing view (kink-patch `Mutant::typing_diagnostics`), empty when each types. A diagnostic only: compilation decides whether the mutant is valid, and a mutant with a typing error that compiles is run like any other. Absent on an `invalid-mutation`. |
| `status`, `reason` | The status (see the run section) and the runner's or the flow's reason. |
| `killer`, `killer_source`, `killer_from_cache` | The first killing program of a `killed` mutation; where the kill came from: `outcome-cache` (tier 1, no call), `hint` (the hinted program's one-program call) or `search` (the call over the remaining programs); `killer_from_cache` is true for the first two. Null, null and false otherwise. |
| `unusable_killer` | `{program, class, cause, source}` when a cached kill (`source` `outcome-cache`) or the hint (`hint`) names a program of the corpus that is not comparable now; else null. |
| `reaching` | The comparable programs whose cached coverage witnesses an edited rule's edit (step 3: reached, k-rust `matched`, for an edit of the rule's `requires`; applied, k-rust `applied`, for any other edit), in the order they were tried. `applied` holds every candidate a step built of the rule, defined or rolled back, so `reaching` can list a program that `results`' `fired_by` (k-rust `committed`, the steps a path takes) does not: an edit can make a rolled-back candidate defined, and that program can then kill. |
| `executed` | `{program, outcome, slots, difference | failure, cause, cached, wall_ms, baseline_ms, baseline_reused}` (`difference` since version 12: the kill evidence of a distinguishing program, live or cached, null on every other compared program; below), plus `specification_diagnostics` when the mutant's run lists a contradicted-claim record and `smt_unknowns` when its count of undecided solver answers is nonzero (version 9), for every program whose outcome decided the status: first the cached ones (`cached: true`, in the order of step 3), then each program the mutant ran on in this command, in the runner's order, each listed once (a hinted program that did not kill and ran again in the next call is listed with that later run; `calls` lists every call). `outcome` is `distinguish`, `agree`, `timeout`, `unknown`, `incomparable` or `error`; `failure` names a run that produced no value (`time-limit`, `resource-limit`, `indeterminate`, `infrastructure`) or one that is excluded (`stack-stop`, `load-stack-stop`, `contradicted-claim`, `implementation-chosen-hook`, `short-circuit-reading`, `allowance-refusal`, `equals-condition`, `implementation-chosen-value`, `unsupported-hook`). `slots` is below. `cause` is null when the outcome is `agree` or `distinguish`, else what the runner's evidence says stopped the comparison, per slot (`exit-stop, whole-term: ...`), with the budget values, followed by the mutant run's leaf census for a time limit (`; when the bound fired k-rust returned ...`) or an unknown or timed-out slot (`; the mutant's run: k-rust returned 1 leaf (depth-bound 1), the deepest at depth 200`), which tells a depth bound from an undecided end. `wall_ms` is the mutant's run of the program, `baseline_ms` the program's live baseline run in this command and `baseline_reused` whether this call reused it; all three are null on a cached entry. |
| `calls` | `{programs, status}` of each runner call: `[]` when tier 1 decided, `[[hint]]` when the hinted program killed, `[[hint], [rest]]` when it did not, `[[rest]]` without a usable hint. |
| `call_wall_ms` | The wall time of each call of `calls`, in the same order (the mutant's compile and every run of the call). |
| `rules` | Null for a `killed` mutation and for an `invalid-mutation`; otherwise each edited rule, in sentence order: `{module, index, file, label, start_line, end_line, edits, before, after}`. `before` and `after` are the rule's K text before and after the mutation's edits, sliced from the file's K view by the sentence's span (`after` is null for a deleted rule); `edits` are the indices of the mutation's edits addressed to the rule. |
| `action` | Null for `killed`; otherwise one sentence saying what the status asks (write a program, fix the mutation, fix the corpus, report it). |

`slots` is an object keyed by oracle slot, `exit-stop` and `whole-term` (or `cells`, which has the shape of `whole-term`), each `{outcome}` (`agree`, `distinguish`, `timeout`, `unknown`, `incomparable`, `error`).
A distinguishing slot also has `sides`: for `exit-stop`, each side's exit-stop kinds, for example `{"baseline": ["normal"], "mutant": []}`
(the flow's classifier makes every ended run `normal`; an undefined step, a rule whose result is undefined such as a division by zero, is no end and has no kind, so a side whose every path takes one has `[]`, and an undefined path beside the same ends changes no kind);
for `whole-term`, each side's number of final configurations, `{"baseline": {"final_configurations": 1}, "mutant": {"final_configurations": 1, "kore": [{"text", "truncated"}]}}`
(an undefined step's outcome is no configuration, so the configuration it is taken from is no final configuration, and a side whose every path takes one has `final_configurations: 0`; the root README, "What a kill trusts"),
where `kore`, on the killing program's entry only, holds the mutant's final configurations as KORE text, each cut to 4000 characters (`truncated: true` when cut).
A cached entry has no run at hand, and a one-sided kill (the mutant's run reached its work budget, `budget.work_factor`) has a mutant side that is `unknown`, not a value: since version 12 their distinguishing slot's `sides` are read from the entry's `difference`, in the same shape (each side's count and classes of the ends the difference compared), with `complete: false` on the `whole-term` mutant side (`mutant_complete: false` on `exit-stop`) for a one-sided kill, whose mutant ends are its run's one-sided ends (below).
No timing, census or side value enters an evidence row, a digest, a key or a hint; the difference enters only its `killed` outcome record.

#### Kill evidence

A distinguishing program's `difference` (CF-16) says where the two sides' ends differ:
`{outside, path, baseline, mutant}`, each side `{final_configurations, complete, classes, end, value}`.
It compares the second slot's sets of ends: each side's final configurations with the `<generatedCounter>` content erased, and under `cells` each cell left out replaced by `\top` of its sort, so no difference it shows lies in a cell left out.
For a one-sided kill (`complete: false`) the mutant's set is its run's one-sided ends: the clean, ground, stuck ends of explored complete paths that the one-sided rule reads (kink-campaign `TestEvidence::one_sided_ends`).
The slot distinguishes one-sidedly exactly when one of them, erased, is outside the baseline's set, so the mutant end the difference shows is one that killed; every completion of that run has it among its ends.
The run's other explored ends are not compared.
The pair of ends is chosen deterministically:
when some mutant end is not in the baseline's set, the first such end (in the sets' term order) and its nearest baseline end (`outside: "mutant"`);
otherwise, for a complete mutant side, the first baseline end the mutant's set lacks and its nearest mutant end (`outside: "baseline"`).
The nearest end is the one with the least cell distance (the number of leaf cells and concrete-map entries in which two configurations differ), the first in term order among equals.
`path` is the first differing cell path from the top: the labels of the cells both ends hold, entering at each cell the first child in which they differ while it is the same cell on both sides,
then, while both values are concrete maps or both are concrete lists, `[key]` for the first key (in term order) whose entry differs, or `[i]` for the first index (from 0) whose element differs.
Each side's `value` is its content at the path (null for a map key that side lacks, or a list index past its end), `end` its end's `{head, class}` (as in a program's `ends`), `final_configurations` the size of its set and `classes` the classes of its ends.
When a side has no end (every path an undefined step), its `end` and `value` are null, and the `path` is null too.
A value is one line of K text printed by krs-unparse as `krs run` prints a configuration, aliases not reversed and maps sorted (`rendering: "k"`), or KORE text when the printer warns or the term has more than 100,000 nodes (`rendering: "kore"`, the reason in `note`); each is cut to 2000 characters (a head or map key to 200), and `truncated` says whether it was.
The two values are cut around their first differing character, so the two texts shown differ: when they first differ at least 1000 characters in and one is longer than 2000, both show the 2000 characters from 1000 before that difference, and each value's `offset` is the number of characters cut before its `text` (0 otherwise).

A row may also carry `stale_killer` (the hint named a program that is not comparable; it was removed) and `cache_error`.
The cause of an `unknown` slot names the possible reasons together (a path stopped at `max_depth`, an undecided end,
or a final configuration holding a collection kink cannot compare (for example one holding a `Float`), an unevaluated function or a symbolic term),
because the runner's evidence records that the mutant's value is unknown but not which of these stopped it; the leaf census that follows
(leaves per halt class: `depth-bound`, `stuck`, `indeterminate`, ...) usually says which.
A mutant's run whose indeterminate leaf holds an application of a function whose equations the mutation edits (deletes, replaces, or edits a term or attribute of), which no equation of the mutant reduces, names that function and the leaf's depth: the mutant leaves its value open there (kink27 R5-WEAKENING). The clause names only an application of an edited function found in the stuck state: an application of any other function is unreduced for a reason the edit does not name (it may be irreducible in the baseline as well), and the clause is absent when the open value is only read by a rule's condition (`requires p(I)`), since no state holds it.
One case has its own cause (fz26 KINK-CAUSE-SUBTERM): a slot the runner made unknown for the pair because one side's end, which is a value of
its own definition, is not data under the other side's definition (kink-campaign `judge_across`, recorded in the mutant's evidence as
`RunNotes::across`). The cause names that side (`the baseline's run ended in a value of its own definition, but that end is not data under
the mutant's definition ...`; for a pattern slot, a binding not definition-independent under the mutant's definition, or a term its relation
decisions read not definition-independent under the other side's; a state value without ends to judge is said so), and the first node of
the end, in pre-order, that fails its own test there, as a refused baseline's cause names it (see `results`); no leaf census follows it.

## Verdicts: `--output verdicts`

`results` and `run` print, with `--output verdicts`, a TOML rendering of their document instead of the JSON, with the same exit status.
It holds what the specification, the corpus and the budget decide and nothing that depends on the host, the build, the cache or the order the work was done in,
so an unchanged corpus renders the same bytes on a cold and on a warm cache and under either `--order`.
It is meant as the format of recorded outputs and of a corpus's optional committed `verdicts.lock`, which no command writes or checks yet, so that a moved verdict shows in review.

```toml
schema = "kink-flow-verdicts"
version = 1
document = "results"          # or "run"

[spec]
outcome = "admitted"          # a refused specification adds its stage and reason, and nothing below

[[case]]                      # results: each program, in manifest order
id = "add"
class = "comparable"
fired = ["add"]               # the rules whose fired_by lists the program
matched = ["add"]             # the rules whose reached_by lists it (k-rust matched)

[[mutation]]                  # run: each mutation it judged, in list order
id = "add-becomes-sub"
status = "killed"
```

A run document of a mutation list that does not decode has no `[spec]` but `[mutation_list]` with `outcome = "refused"`;
a run that a corpus error stopped ends with `[stopped]`, the mutation and the reason (the mutations after it have no status).
A refusal's or a stop's text is not part of the rendering, since it explains a refusal rather than records a verdict: `kink-flow` prints it on stderr (`kink_flow::verdicts::refusal_details`).

A rule is named by its KRS item when a front end annotated it (`krs.item`), else by its label, else by `file:line`; the names of a case are ordered by module name, then by position in the module.
A mutation's killer and a status's reason are left out: under the first-kill search the killer is the first killing program the search reached, which depends on the order (`--order cost` reads wall times) and on the outcomes the cache holds,
and the reason of `unknown` is the first exclusion in run order.
A status does not depend on either in the no-Z3 profile while no `budget.time_ms` bound fires ("Cost model"); a `timeout` depends on the host by its nature.
The killers become part of the rendering, under a new version, once a run proves every killer of a mutation rather than the first.

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

The command prints one document, `{schema: "kink-flow-query", version: 1, k_rust_revision, profile, kink_build, kink, spec, programs, patterns, rows, counts, refuted_claims, mismatches, pattern_cache, baseline_runs, data}`:
`programs` are the `results` rows (the result cache is brought up to date first),
`data` is the baseline's full critical-pair check under the premises, as in the run document (fz26 KINK-BASELINE-FINDINGS). `data` was added to version 1 without a new version, since it is additive and no command reads a `query` document back. A refused specification prints the document without `data` (the member is absent, not null; `spec.outcome` is `refused` and `programs`, `patterns` and `rows` are empty), and a pattern list that does not decode prints only `{schema, version, k_rust_revision, profile, pattern_list}`.
`patterns` one entry per selected pattern `{id, note, pattern, outcome: valid | invalid-pattern, detail, digest, kore, asked: claimed | corpus}` (`kore` is the compiled target),
and `rows` one row per (pattern, program asked) `{pattern, program, claimed, answer, cause, witness, cached, wall_ms, claim}`.

| `answer` | Meaning | What to do |
| --- | --- | --- |
| `hit` | A run reaches a configuration that matches the pattern; `witness` shows it. | Nothing: the claim holds. |
| `no` | No run reaches one: the whole state space of the program was explored, within the budget, on a definition where nothing is left to the implementation. | The program does not do what you meant: change the program, or the pattern. |
| `unknown` | No definitive answer; `cause` says why (below). | Read the cause; usually make the program terminate within the budget, or accept that the definition leaves the question open. |
| `invalid-pattern` | The pattern does not parse, sort or compile; `cause` is k-rust's message. A position in it, `pattern:LINE:COLUMN`, is a line and column of the pattern's own text with its surrounding whitespace removed, not of the pattern list's file. It never runs. | Fix the pattern. |
| `error` | The program is not admitted, k-rust refused the search, or its result lacks the `matches` or `incomplete` list kink reads (never read as empty); `cause` says which. | Fix the program, or report it. |

`claim` is null for a program the corpus form asked; for a claimed program it is `confirmed` (`hit`), `refuted` (`no`) or `unconfirmed` (anything else).
**A refuted claim** (also listed in `refuted_claims`) means the program, run exactly as kink runs it, never reaches the situation you said it tests: the purpose you gave the test is not what it does.
An `unconfirmed` claim is neither confirmed nor refuted.

The witness of a hit is `{depth, state: {kore, truncated}, bindings, rules, rendering, note}`:
the matching configuration as KORE text (cut to 4000 characters) and the number of rewrite steps to it, the values of the variables you wrote (`[{variable, value}]`; the variables k-rust generates to complete cells are left out, and so is every variable spelled as k-rust spells a generated one, `_Gen<n>` or `_DotVar<n>`, so a variable of your own with such a name is not shown: the witness is for display only, and no answer reads it),
and `rules`, the rewrite steps of one run from the initial configuration to it, each named by its label, else by the file and line of the rule written for it, else by its compiled id.
`rendering` is `kore`: `query` does not print the witness through krs-unparse, the K-text printer kill evidence uses (above).

**Why a no can be unknown.** A `no` is a claim about every run, so it needs more than a `hit`:
- the exploration completed: no path stopped at `budget.max_depth` (`a path reached max_depth = N`), the search finished within `budget.time_ms`, k-rust decided every step and every match (an undecided step, an undecided match, a state stopped for lack of native stack each make it incomplete), and the search left no hook application unevaluated (`unsupported-hook`: its `unsupportedHooks` and `allowanceRefusals` lists are empty; KINK-R4, below, since where such a hook is undefined the step to its state has no successor, and where it is defined its value can let a rule apply, neither of which k-rust computed; this does not rely on the baseline run below meeting the same hook);
- the program's baseline run (its `results` row) is `comparable`: complete, with no stack stop and nothing else that makes a run no evidence (a contradicted claim, an allowance refusal, ...);
- the definition leaves nothing to the implementation: no rule depends on a hook whose value the definition leaves open and k-rust chooses (`implementation-chosen-hook`, decision 1's census: `String2Bytes`, `KRYPTO.keccak256`, ...; an open hook k-rust cannot evaluate, such as `#getc` or `Float2String`, is judged by the baseline run's `unsupportedHooks` instead, which the comparable baseline below requires empty), or on whether `andBool`, `orBool` or `#if` skip an undefined operand (`short-circuit-reading`), and neither does the program's initial configuration; with such a value another implementation could reach the pattern, so the exploration of k-rust's choice says nothing about it;
- the search read no value the definition leaves open (`implementation-chosen-value`: its `implementationChosenValues` list is empty; kink27 R3-CENSUS-RUNLEVEL): k-rust's own classes, such as the order of `keys_list` or a `choice`, are judged per run rather than by the census, and a search lists every class value it took, the matching of the pattern included, so with one on the list another model of that value may reach the pattern;
- the build is not the Z3 profile (a solver query can time out silently);
- the definition has data under `[spec] assume_joined` (the `data` member's `has_data`, as `run` and `results` require of an end): its full critical-pair check has no finding the names leave unnamed (`baseline-findings`, fz26 KINK-BASELINE-FINDINGS), and the check read the whole definition (no stop for lack of native stack, no skipped candidate pair, every executable equation read and every root pair classified; KINK-R4, before which only a finding refused a `no`): matching is syntactic, while a pair that does not join, or one the check did not read, can identify a reached configuration with an instance of the pattern in every model.

A `hit` needs none of these. It is a run k-rust found to a configuration that exists, and k-rust's choice of an open value is one model of the definition. A hit is found even in a program that never ends, or that the budget stops: the search stops at the first match.
That choice includes the short-circuit reading. K leaves it open: `domains.md` says `andBool` and `orBool` "may be short-circuited in concrete backends", and that `#if` "does not short-circuit on symbolic backends". k-rust reads them strictly: a condition with an undefined operand is undefined, so its rule does not apply. That is one reading K allows, so a `short-circuit-reading` flag on the definition or on the initial configuration makes a `no` unknown but leaves a `hit` standing.
The consequence: a hit may be on a configuration that only the strict reading reaches. For example, an `owise` rule fires because another rule's condition was undefined, and a short-circuiting backend might not reach that configuration. The census (`implementation-chosen-hook`) is treated the same way: a hit stands, a `no` does not.
Two conditions make every answer unknown: the definition's load counted a stop for lack of native stack (`load-stack-stop`), or a rule or equation has a condition equating two terms (`equals-condition`, a gap of k-rust's own answers).
A match is a hit only when it is decided, and the search stops at its first match, so otherwise the answer is unknown. A match is not decided when any of these holds:
- it holds only under a condition k-rust did not decide;
- its path emitted a backend diagnostic;
- its configuration's term is not shown defined (`undefined-state`);
- the search left a hook application unevaluated (`unsupported-hook`, KINK-R4): the search response's `unsupportedHooks` (a hook k-rust does not evaluate) or `allowanceRefusals` (a `Bytes` result its memory allowance refused) list is not empty. Such an application stays in the configuration as written, and `ground_defined` counts an irreducible application of a `value-production` symbol as a value from its declaration alone, hooked or not; where the hook is undefined at its arguments, the configuration denotes nothing and the step to it has no successor, which k-rust did not compute. The lists are the search's as a whole, so an entry on another branch also makes the answer unknown.

The `undefined-state` case is a configuration holding an application of a function the definition does not declare `total` that no equation reduced, such as `f(3)` for a function with an equation for `f(0)` only. Wherever that application is undefined, such a configuration denotes nothing: there is no run to it, although k-rust's search lists it; its match states the undecided `\ceil(f(3))` as a condition (k-rust `docs/compatibility.md`, "Search results"), so it is not a decided match, and kink also checks the configuration itself. kink therefore requires the matched configuration, and with it every binding, to be shown defined by k-rust's one existence predicate, `BackendDefinition::ground_defined` (since fz26 KRUST-ANYWHERE-HEAD; it was the stored `ceil_free` attribute, every configuration of which it still accepts): the configuration is ground and k-rust's definedness walk owes nothing. Every application must be of a constructor, of a function declared total, of a `value-production` symbol (a production with `anywhere` rules, such as SIMPLE's `_[_]`) that no equation of its head can reach, which that declaration makes a value of its sort (a ceil lemma decides its application first), or of a partial function whose `\ceil` k-rust shows `\top`. k-rust shows it in two ways: by an unconditional ceil equation of the definition whose condition simplifies to `\top`; or, since k-rust 68e362935 and fdb3ac1a5 (re-read at kink27 R1-TRUST), from its source-checked observation catalog, for a compiler sort projection `project:S(E[v])` of a term on its exact image and for a field `f(p)` of a sort with one constructor `c` whose one equation `f(c(X1, ..., Xn)) = Xi` covers every element (kink-native `tests/data.rs` pins both and records why each holds). A hooked map lookup or list access k-rust leaves unevaluated owes its key membership or length bound, which `ground_defined` never discharges. Every map or set must have keys k-rust shows apart. The configuration must also hold no term-level `\and`, at its root or below: `\and(a, b)` denotes a configuration only where `a` and `b` are equal, and nothing where they differ, which kink does not decide (k-rust's `ceil_free` counts a conjunction defined only when its two sides are one defined term) (no K rule writes one on a right-hand side, so this refuses no configuration known to be reached). A configuration whose definedness kink cannot read (it does not verify or internalize on the searched definition, k-rust provides no stack for it, or k-rust panics) is not a hit either: the answer is `unknown`.
A hooked partial operation that k-rust evaluates is not such a case. k-rust evaluates `7 /Int 0`, or a lookup of a key a map does not hold, to bottom, so the step to it is undefined and has no successor: the configuration is never reached, and the answer is a correct `no`.
Constructors, functions declared total (a `total` helper with no equation for its argument included), lists, and maps or sets over domain values such as IMP's `<state>` and IMP++'s `<store>` pass. So does SIMPLE's stored `a[4]`, which neither `anywhere` rule of `_[_]` matches. A configuration holding a partial function's unevaluated call does not, unless k-rust shows that call defined in one of the two ways above, nor does an application an `anywhere` rule of its head still matches, nor a map whose keys k-rust cannot show apart. Then the claim is `unconfirmed`, never confirmed; usually the program calls a function outside the cases its equations cover.

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
The key is `{schema_version: "kink-flow/pattern-answer/v5", lowering: "kink-flow/pattern-lowering/v1", k_rust_revision, kink_build, kink, spec, program, pattern, budget, modality}`:
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
- the baseline's own claims (`total`, `preserves-definedness`, lemmas) are trusted, as for every baseline run. A contradiction k-rust detects does not end its path: since k-rust KINK-18/2 a path whose decisions rest on one goes on, and carries a `contradicted-claim` record on its states and matches (k-rust `docs/compatibility.md`, "A contradicted `total` attribute is named, not repaired"); a hit needs no diagnostic on the match or its path, so a witness whose path rests on a detected contradiction is `unknown`, and a record on the baseline run, on a leaf or (since re-pin adoption A-1) only on its `contradictedClaims` list (work that ended on no leaf, the load), makes the program not comparable, so no `no` is given there. A record only on a search's `contradictedClaims` list is not read yet (re-pin adoption A-2 reads it): it rests on the baseline's claims, which are trusted;
- k-rust's `unsupportedHooks` and `allowanceRefusals` lists of a search name every hook application it left unevaluated (a hit and a no each need both empty);
- k-rust's `ground_defined` decides that a matched configuration's term is defined: its definedness walk, which skips a subterm whose stored `ceil_free` attribute holds (k-rust proves that shortcut in Lean, `ceilFree_sound`) and discharges an irreducible `value-production` application through k-rust's instance-normality scan, a partial application through an unconditional ceil equation, and a sort projection on its exact image or a one-constructor field through its observation catalog; the definition's `total` and `value-production` declarations and its ceil lemmas are among the trusted claims above, and so is a lemma that states a product field's equation;
- a search does not count the stops for lack of native stack it dismisses while it only refines a result (k-rust `docs/compatibility.md`, "Execute"). k-rust states at every such site a search reaches that the kept result is sound (a definedness condition left unsimplified, a fold forgone), so such a stop can leave a step or a match undecided (an unknown) but cannot make a decided match or a completed exploration false: whether an answer is definitive can depend on the host's stack, its truth cannot. A `no` also requires the baseline run's own count to be zero.

**Answers never decide a mutation.** No answer enters a result record, an outcome record, a hint or a run document, and `run` does not read the pattern cache: a kill needs the final configurations to differ, and a pattern-only difference stays unknown by design.

Exit status: 0 when every selected (pattern, program) got its answer (`hit`, `no`, `unknown`, `invalid-pattern`; refuted claims included);
1 when the manifest, the pattern list, the specification or a program is refused, a search failed, a record could not be written, or `--verify` found a difference;
2 on a usage error (an `--only` id that names no pattern, an option given twice).

## Killing a survivor with `fuzz`

```text
kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID (--kill MUTATION --mutations MUTATIONS.toml | --reach RULE [--fired] | --pattern ID --patterns PATTERNS.toml) [--cases N | --work W] [--seed S] [--max-work N] [--time-limit-ms T] [--assume-joined NAME]... [--one-path] [--cache DIR] [--no-confirm] [--no-filter]
```

When a mutation survives or is unknown because no corpus program tells the two definitions apart, write (or pick) a program that reaches the edited rule, mark its literals as holes, and let `fuzz` look for hole values that kill the mutation.
It runs a k-rust-fuzz campaign in process on kink's own two sides, confirms the candidate with kink's own code, and prints the program as a `[[program]]` fragment for `FLOW.toml`.
The same command can also look for a program that reaches a rule or hits a pattern ("Reaching a rule and hitting a pattern" below).
k-rust's [docs/fuzzing.md](../../../docs/fuzzing.md) is the user guide: it walks through the three jobs on `testdata/flow/fuzz/imp` and `impu`, how to choose a template, and how to read the document; this section is the reference.

### `TEMPLATES.toml`

```toml
[[template]]
id = "primes-holes"        # unique, non-empty
program = "primes"         # a [[program]] of FLOW.toml (its text, start_sort and variables), or:
# file = "templates/straight.imp"   # relative to this file's directory, inside it
# text = "int x; x = 5;"
# start_sort = "Pgm"       # with file or text; default: kink's (the program position of $PGM's sort)
# variables = { IN = "3" } # with file or text, as in [[program]]

  [[template.hole]]        # krust fuzz's [[hole]] keys (crates/k-rust-fuzz/README.md, "Hole declarations")
  name = "T"
  sort = "Int"
  find = "t = 1;"
  literal = "1"
  range = { min = 0, max = 3 }
```

- Decoding is strict, as for `FLOW.toml`: an unknown key, a value of the wrong type, a duplicate id, a template with not exactly one of `program`, `file` and `text`, or a path leaving the directory is an error naming the key.
- Each `[[template.hole]]` is decoded by k-rust-fuzz's own decoder, so a hole means what it means for `krust fuzz`; its messages are prefixed with `template "ID".hole[INDEX]`. A span hole addresses the template's text (leave `program` out); a `config-var` hole makes a whole configuration variable the hole. `program = "$NAME"` puts a span hole inside the text of the template's variable `NAME` (k-rust-fuzz's witness carries each binding as instantiated, `config-vars`, and the fragment writes it). A TOML date is refused.
- Mark every data literal: in TRIAL2 the killing value was usually one nobody would have guessed (`t = 0` in `primes`). A template is not a corpus program: it gets no record, and nothing is cached for it.
- `testdata/flow/fuzz/imp` (TRIAL2's IMP thin corpus, its survivors, their templates and a pattern) and `testdata/flow/fuzz/impu` (three uncovered rules and templates that reach them) are complete examples; the user guide runs every command it shows on them (`tests/guide.rs`).

### Reaching a rule and hitting a pattern

`--reach RULE [--fired]` and `--pattern ID --patterns PATTERNS.toml` replace `--kill`; every other option applies, and the job runs on the baseline alone (its exclusions, its assembly, its findings).

- **Reach** looks for hole values whose program `results` would list in the rule's `reached_by` (with `--fired`, `fired_by`). `RULE` is `FILE:LINE` (any line of an authored rule of `FILE`, a source of the specification, or a suffix of its path after a `/`), the rule's label (bare, or `MODULE.x` when the bare label names several rules), or a 64-hex compiled id. The rule's ids that k-rust's run coverage can name (the coverage domain `results` reads) must hold exactly one rewrite axiom, the target; equation ids of the same sentence are listed as `untargeted_ids`. Refusals before any case: `no-rule-at-line` (its detail lists the five rules of the file written nearest the line, or the files that hold rules), `unknown-label` (the labels that contain the reference or that it contains, at most five), `ambiguous-label`, `ambiguous-rule-position` (the rules named), each listed rule with its position, label and the ids a reach can target, `unknown-rule-id`, `no-authored-rule` (a compiled id that no authored rule of the specification wrote, such as a prelude rule's: `results` lists programs under authored rules only), `no-coverage-signal` (a macro, alias, smt-lemma or non-executable rule), `equation-target` (a function rule) and `several-rewrite-ids`. kink counts a program in `reached_by` only when its all-paths baseline run is comparable, so the hit's run of every path must be comparable too (k-rust-fuzz's `comparable` option: complete, clean, data ends); the program must end naturally. A definition with a finding no name assumes makes the job `not-comparable`, as for a kill.
- **Pattern** looks for hole values whose program reaches a configuration matching the pattern of `PATTERNS.toml` named `ID`, as a `query` `hit`: matched at every configuration of every path (k-rust-fuzz's `at: any-state`), with every fact on which a complete search could stop refused (`query-confirmable`). The pattern is first lowered exactly as `query` lowers it; an invalid one is refused (`invalid-pattern`, with k-rust's message) before any campaign. A pattern reads no data end, so it takes no assumed name: `--assume-joined` is a usage error, and the flow's own names are not passed.
- The action names kink's confirming command: `kink-flow results` for a reach, and for a pattern, adding the fragment's id to the pattern's `programs` and running `kink-flow query --only ID`.

### What it runs

- **Sides.** The baseline is the admitted specification's compile, with its claims. The mutant is the claim-free, consistency-checked mutant kink's runner builds for every test of the mutation (kink-campaign `claim_free_mutant`, admitted with the flow's `[spec] assume_joined`). Both run on the backend route kink runs (`Backend::from_definition`). A mutation `run` would refuse (`invalid-mutation`, `equivalent`, `invalid` with its reason and `inconsistent_pairs`, unsupported claims) ends the command with that status and reason; nothing is fuzzed.
- **Target.** The differential target on all paths (`--one-path` for one), as kink compares complete state sets: a case is a hit when the mutant reaches an end the baseline cannot or the reverse, on ends that are data.
- **Comparability is strict.** If a definition's full critical-pair check reports a finding no name assumes, the campaign is `not-comparable` and the document lists every finding (`findings`: side, name, verdict). Such a definition may identify the two ends a kill compares, so a kill there would hold in no model of it, and `run` refuses it too (`baseline-findings`). A finding is read as resolved only when you name it: the flow's `[spec] assume_joined` names are always passed, and `--assume-joined NAME` adds one for this command. A decided finding cannot be named; a genuine one can, but it is a premise known to be false, and the fragment says so.
- **Budgets.** `--cases N` (default 1000) or `--work W`, `--seed S` (default 0), the library's blind proposer. Every case runs with `[budget] max_depth`, a safety limit of `[budget] time_ms` per execution, and a work bound of `--max-work N` (default 100000). `run` bounds the mutant at `work_factor` times the baseline's work plus 10000, so a kill whose mutant needs more is `unknown` there. `--time-limit-ms T` cancels the campaign's run after `T` ms (not the admission and compiles before it); a cancelled campaign is outside the determinism contract (`stopped: time-limit`). Otherwise the same inputs and seed give the same document, but for cases a clock or the stack decided: a case that `time_ms`, a solver `unknown` or a stop for lack of stack decided is outside the determinism contract (the embedded report's `totals.outside-determinism`), and since every later case depends on the cases before it, a re-run may differ from the first such case on (`totals.first-outside-determinism`, which also counts a candidate whose confirmation the clock stopped, and which the statement in `action` names); kink's confirmation runs under `time_ms` too.
- **Definition exclusions.** Before any case, kink's definition exclusions are read on both sides as kink's runner reads them (kink-native `DefinitionExclusions::of_validated`, `definition_exclusion`). One on the mutant (an edit that brings in an implementation-chosen hook, a short-circuit reading, an equals condition, or a load stack stop) makes `run` report the mutation `unknown` with that reason; one on the baseline excludes every baseline run, so `run` finds no comparable program (`error`, `no-comparable-program`, each program's cause naming the exclusion). Either refuses the job with that status and reason (`job.refusal.stage: exclusions`, `job.exclusions`: each side's `{exclusion, detail}`, the detail as the check document's `spec.exclusion` gives it, or null); nothing is fuzzed.
- **Assembly.** kink assembles every test's input from the baseline's grammar, for both sides. The campaign binds kink's stream defaults (`$IO` to `"off"`, `$STDIN` to `""`) after the template's variables, as kink does, for each stream variable the definition declares and the template leaves unbound, since k-rust-fuzz's own default binds `$STDIN` to krun's buffered `"\n"`; the printed fragment leaves these bindings out. A run of no case gives each side's initial configuration at the holes' anchors (the fuzz report identity's `initial-configuration-digest`). When the mutant's differs from the baseline's (an edit of a `[macro]` rule, or of anything the program's parse reads), the job is refused before any case (`mutant-assembly-differs`: the mutant parses the template differently from kink's input); when the baseline's differs from kink's own assembly of the template, it is refused too (`template-assembly-differs`, a defect to report). The campaign reads a configuration variable's text as krun reads `-c`, with the main module's grammar alone, while kink reads a variable of a program sort with the syntax module's grammar first (the manifest's `program.variables`); before the campaign starts, kink assembles the template with both readings, and a template that they read as different terms, or that the campaign's reading does not parse (a `Word` token the main module's scanner reads as another token sort), is refused (`variable-reading-differs`, naming the variables kink reads with the syntax module first), since no candidate could be kink's input. Then the candidate's program is assembled by kink exactly as a `[[program]]` (start sort, variables, the concrete-state check and the input gate), and each side's `initial_configuration` in the witness, parsed as KORE, must equal it; otherwise the candidate is not offered (`stopped: assembly-mismatch`, `candidate.assembly` says which side or kink's refusal, and when the side's configuration is the program with its variables read as the campaign reads them, says that).
- **The last run.** The last `run` document (`report.json` in `--cache DIR`, default `.kink-flow`, read as `report` reads it and only when it is of the current specification) gives the template's own program class (found by its program digest) and the mutation's status and `reaching` programs, each suggested as a template (`template.last_run`). Nothing in the cache is written.
- **Warnings** (`warnings: [{kind, detail}]`): `unusable-template` (the template's program is not `comparable` in the last run, or kink refuses the template's own input), `template-not-reaching` (the template's program is not among the mutation's `reaching` programs), `no-reaching-program`, `already-killed`, `unkillable` (the last run found the mutation `unkillable`: no template helps; the detail is the row's action), `stale-run-document`, `crash` (one per crash finding of the campaign: a k-rust or k-rust-fuzz panic or internal error during a case, kept in the embedded report's `crashes`; a crash is no kill and moves no verdict), `client-refused` (kink's rules, as the filter reads them, refused candidate hits inside the campaign, counted per cause), `witness-not-terminating` (the offered witness's run of every path was cut by a bound or a clock, so as a corpus program it may not terminate; only a pattern witness can be one), and `time-limit-scope` with `--time-limit-ms` (it bounds the campaign's run, not kink's admission, the mutant's preparation, the exclusions or k-rust-fuzz's `Campaign::new`, which builds both grammars and backends and runs both definitions' full critical-pair checks).
- **Witness filter** (fz26 FZ-COMPARABLE-B; `src/fuzz_filter.rs`). kink refuses some fuzz witnesses for reasons that depend on the input: its end check (TV-01) gives a `String` domain value a value only when its bytes are ASCII, and generated strings almost never are, so a String-hole kill used to end `unconfirmed` (TRIAL3's ASCII-STRINGS). Unless `--no-filter` is given, the campaign runs with kink's own rules as a k-rust-fuzz witness filter (crates/k-rust-fuzz/README.md, "Witness filters"), built from the loads the definition exclusions were read from and the data facts of the names kink's confirmation judges under (the flow's `[spec] assume_joined`, recomputed only when `--assume-joined` adds names). Each candidate hit and shrink candidate is judged before its confirmation and after it, in the order kink's runner judges a run: the state exclusion of the baseline side's initial configuration under each side's facts (`initial-state:<exclusion>`), each side's undefined steps under its own facts (`preserves-definedness`, `short-circuit-step`), TV-01 on every `stuck` leaf under its own definition (a `trivial` leaf needs only existence, which the fuzz's clean-leaf rule already requires, kink27 R3-UNDEF-BRIDGE, witness filter v3; `domain-value-not-ascii` for a String-like domain value that is not ASCII, `domain-value` for any other, `injection`, `not-constructor`, `overload-not-data`, `collection-untrusted`, `collection-shape`, `term-kind`, `undeclared-symbol`, `arity`), for a kill each `stuck` leaf's value under the other definition too (`cross-<test>`; an undefined step's pre-step configuration is no end and is not judged across, kink27 R1-UNDEF, witness filter v2), and for a removed end under `[budget] work_factor` the mutant's work within `work_factor × W + 10000` (`work-factor`). A reach judges the baseline alone; a pattern only the state exclusion, since a query's run stops at its first match and kink's own query decides the rest. Every walk over a case's terms runs on a stack sized for them (k-rust's `with_solver_over`), and terms deeper than the largest stack the backend provides are refused `too-deep`, never an overflow of the campaign's thread. Each side's definition and solver are reached once, when the filter is built: a side that cannot be reached then, or later for any reason but stack, accepts every case for the rest of the campaign, so the judgement before a confirmation and the one after it never differ for a reason outside the case. A refused hit is no witness, and the search goes on; a hit refused only for non-ASCII String ends (every refusal of the case `domain-value-not-ascii`, so none that holds whatever the strings are) is repaired: up to two candidates replace only the non-ASCII characters of the String holes (nested ones too) by ASCII letters or digits, keeping lengths, ASCII characters and distinct strings distinct, and the first that kills the same way and passes the filter and the fuzz's confirmation becomes the witness (`repaired-from` in the embedded report). A value refused whatever it holds (a `Float` or `MInt` end) gets no candidate; a `Bytes` end is a value (kink README, R5-BYTES-ENDS). The filter is stricter than kink where its work-factor check reads the fuzz's work for kink's and kink's execution request differs (both read the state set of the same request whatever its leaves since KINK-PATHSET-FALLBACK) and where it refuses a term past the backend's depth that kink's runner, judging it on no stack sized for it, may overflow on; it is laxer on a leaf that is not one decided term, on leaf diagnostics (kink makes a diagnosed leaf incomplete), on a side it cannot reach, on the mutant's single path of a `--one-path` campaign, on an added end under `work_factor`, on a `trivial` leaf kink does not show to exist, and on everything after a pattern's first match, which kink's confirmation decides; it never makes the document claim a kill kink did not make. Its identity names its composition, the kink components it composes or assumes (`terminal_value`, `data_facts`, `definition_exclusion`, `execution_request`, `k_rust_revision`) and the flow's work budget, never `kink_build`. It keeps each side's kink load (a backend and its parsed KORE) for the whole campaign: about +90 MB of peak resident memory on TRIAL3's SIMPLE job (478 MB against 385-390 MB), not measurable on IMP. A template whose own input kink excludes is refused before any case (`initial-state-excluded`).
- Nothing is written: no cache, no hint, no file under the flow's directory.

### The document

`{schema: "kink-flow-fuzz", version: 4, k_rust_revision, profile, kink_build, kink, spec, template, job, sides, assembly, findings, assumed, attempts: [{seed, fuzz, candidate, confirmation}], program, stopped, action, warnings}`.
`k_rust_revision` is k-rust's build identity (`k_rust::build_identity`: its version and a digest of its sources), as in every kink-flow document, and the value the embedded report's `identity.k-rust-revision` records (GUIDE-USABILITY 5, within version 4); `kink.k_rust_revision`, the semantics identity's component, is the version alone, and `kink_build` pins the whole executable:
- `spec`: admitted, with the flow's `assume_joined`, whether the baseline has data under them (`has_data`) and its unnamed findings, as `run` reads them; or the refusal.
- `template`: its id, source, the start sort used and where it came from (`template`, `program` or `default`), its variables, its hole declarations and `last_run` (`{found, current, template: {program, class, cause}, mutation: {status, reason, reaching}, suggested_templates}`, or `{found: false, detail}`).
- `job`: `{kind: "kill", mutation, outcome: fuzzed | refused, path_mode, filter: {on, id}}` (`id`: the witness filter's identity, `null` with `--no-filter`), with kink's `status`, `reason`, `claims` and `inconsistent_pairs` when kink refuses the mutation, and the claims the mutant withdrew otherwise. A reach job has `kind: "reach"` and `rule: {module, index, file, start_line, label, id, mode: condition-reached | covered, untargeted_ids}`; a pattern job `kind: "pattern"` and `pattern: {id, text, kore}`. Both have `sides.baseline` only and no `mutant_anchor`.
- `sides`: each side's compiled KORE digest and the two provenance digests of its k-rust-fuzz definition.
- `assembly`: `{kink_template: {sha256} | {refused}, baseline_anchor, mutant_anchor}`, the digests the up-front check compares.
- `findings`, `assumed`: every finding of the campaign's check, and every assumed name with where it came from (`in_flow`, `from_command_line`), whether it assumed a genuine finding, and the findings it matched.
- `attempts`: one attempt, `{seed, fuzz, candidate, confirmation}`: the k-rust-fuzz report as JSON, the candidate (the shrunk witness case, else the first, with `case`), with `assembly: {status: match | mismatch | refused, ...}`), and `confirmation`: `null` with `--no-confirm`, else kink's verdict `{case, confirmed, status, reason, cause}` with the job's `killer`, `class` or `answer`. When kink refuses the shrunk case and the first is another program, the first is confirmed too; the refused verdict is then listed in `refused_confirmations` and `candidate` is the first case.
- `program`: for a witness, `{id, fragment, file, premises, confirmed}` (`confirmed`: kink confirmed it; false with `--no-confirm`); absent when kink refused every candidate. `id` is `<template>-fz-<8 hex of kink's program digest>`. `fragment` is the `[[program]]` table as TOML: the instantiated text as `text`, the template's start sort and variables (each binding as instantiated: a `config-var` hole's value, or a span hole's value inside the binding's text). `file` suggests where to write the text instead. `premises` lists every assumed name, genuine ones flagged, and whether `FLOW.toml` names it already.
- `stopped`: `null` for a witness; `budget` (no witness, and the budget was spent: kink-flow runs the blind proposer alone, which never runs out, so k-rust-fuzz's ending with every proposer exhausted does not occur; `action` advises raising `--cases` or `--work` exactly when the statement says neither that coverage stopped growing, the embedded report's `totals.coverage-last-grew` long before its last case, nor that the mutant may not terminate on some case, `totals.diverging`, which one such case among many is enough for; otherwise it points at the template and its holes, since the statement then says more cases are unlikely to reach a new rule, or that a case may never end and no bound is suggested, although more cases with other hole values may still find a witness), `domain-exhausted` (no witness, and every assignment of the holes ran, each hole having finitely many values: more cases cannot help; the embedded report's `totals.domain`), `client-refused` (no witness in the budget, kink's rules refused candidate hits inside the campaign, and no hit the filter accepted was lost to the fuzz's confirmation: none was a witness kink's rules accept, which is no sign of survival; otherwise the job stops `budget` with the warning; the warning `client-refused` counts them per cause, and the embedded report's `client-refusals` give each cause's first case), `rejected-out`, `time-limit`, `equivalent`, `assembly-mismatch` (a witness kink's assembly does not reproduce: nothing offered), `unconfirmed` (kink's own code refused every candidate: nothing offered), `not-comparable`, `aborted` (`action` names the fuzz outcome's `kind`: a failed solver prelude, a solver that did not start, or backends that did not rebuild after a crash) or `refused`.
- `action`: the next step.

**Confirmation** (fz26 KF-T4). Unless `--no-confirm` is given, each candidate whose assembly matches is confirmed by kink's own code on an overlay of the flow held in memory: its `[spec]`, with the flow's `assume_joined` and the command line's `--assume-joined` names, its `[budget]`, and the fragment as the only `[[program]]`, with a fresh scratch cache under the system's temporary directory, removed on every path. A kill is confirmed when `run` kills the mutation with the fragment as killer; a reach when `results` gives the fragment class `comparable` and lists it in the targeted rule's own `reached_by` (`fired_by`), the entry of the authored rule the job resolved (a listing under any other rule is `not-listed`). The confirmation is at the authored rule's granularity, as `results` lists programs: a reach given as a 64-hex id is confirmed when the program reaches (fires) the authored rule that wrote the id, whichever of that rule's compiled axioms it reached; a rule that compiles to several rewrite axioms is refused when named by its position or label (`several-rewrite-ids`), and given one of its ids, `confirmed: true` says that the authored rule is listed, not that this axiom was; a pattern when `query`, asked with `programs = [fragment]`, confirms the claim. Things the fuzz does not judge decide here: kink's end check (TV-01, which refuses some domain values the fuzz's data judgement accepts), `work_factor`, the exclusions kink reads on a run. There is no seed retry (`--attempts` is a usage error). Confirmation costs one kink run of the one program (a few seconds), outside `--time-limit-ms`; a kink time-out in it depends on the host.

To use a witness, add every premise `FLOW.toml` lacks to `[spec] assume_joined` and append the fragment; then `kink-flow run` (or `results`, or `query` with the program claimed) decides it again on the whole corpus, and `run` writes the hint.
In the portable (no-Z3) profile, while no `time_ms` bound fires, that command gives the verdict the confirmation gave: each program's outcome is independent of the programs run before it, and under FirstKill a kill by the fragment is a kill of the corpus (another killing program may be named the killer).
Under the Z3 profile it need not: the confirmation ran the fragment alone on a fresh mutant backend, while `run` runs it after other programs on a backend whose solver caches are warm, and a solver query can time out, so the corpus run can leave the mutation `unknown` or `survived`, or a pattern `unknown`, where the confirmation gave a verdict (`src/search.rs`, the program order). A kill or hit either gives is still sound: a kill is a proved distinction, and the confirmation's stands as kink's verdict on the fragment.
A `time_ms` bound depends on the host in every profile, so a program near it can time out in one command and finish in the other.

Exit status: 0 when the job reached a verdict (`stopped` is `null`, `budget`, `domain-exhausted`, `client-refused`, `unconfirmed`, `assembly-mismatch`, `equivalent`, `rejected-out` or `time-limit`);
1 when an input, the template or the mutation is refused (`refused`: the exclusions and the up-front assembly check included), the campaign is `not-comparable`, or it `aborted`;
2 on a usage error (a template, mutation or pattern id that names nothing, an option given twice, two jobs, `--attempts`, or `--assume-joined` with `--pattern`).
`krust fuzz` agrees on a witness (0), `not-comparable` and an aborted campaign (1) and a usage error (2); its 0 means a witness, so it exits 1 where this command exits 0 without one, and 2 for a refused campaign (docs/fuzzing.md, "`krust fuzz` on its own").

Version 3 of the document (fz26 FZ-COMPARABLE-B) adds `job.filter`, the `stopped` value `client-refused`, the warning `client-refused` and the refusal `initial-state-excluded`, and embeds fuzz reports that carry the witness filter's fields; version 2 had none of them.
Version 4 (fz26 round 4, FZ-REPLAY-WHOLE) embeds k-rust-fuzz reports of version 10: their identity records the k-rust-fuzz build (`fuzz-revision`) and the parser's diagnostic work limit, their totals the first case outside the determinism contract, the holes' finite domain, the cases in which the mutant may not terminate and the last case that reached a new rule, and every source location they name is relative to the main module's file; it adds the `stopped` value `domain-exhausted` and the warning `witness-not-terminating`. `tests/formats.rs` ties the version to the document's keys and enumerated values and to the report version it embeds.

## Front ends

kink-flow's manifest, command layer and documents are a library (`kink_flow`) for two front ends: kink-flow's own command line over a K specification, and the krs front end (`krs kink <verb>`, not yet built), which is to build a KRS package, write the K it emits next to the corpus and run kink-flow's commands over that K.
Both decode `FLOW.toml` with `ManifestFile::decode` and run the engine unchanged, so a KRS corpus has the K corpus's admission, kill definition, caches, documents and statuses.

- `ManifestFile` is a decoded `FLOW.toml` whose `[spec]` is a `SpecDecl`: `K` (as written) or `Krs`.
  `ManifestFile::bind` gives the `FlowManifest` every command runs on; a front end binds a KRS declaration to the `SpecSection` of the K it emitted (the declaration's `assume_joined` is kept), and a K declaration binds to itself.
- `FlowCommand::parse(verb, files, options)` reads a verb's options exactly as `kink-flow <verb>` does, the corpus's files given by the front end (`CommandFiles`: kink-flow's operands, or the front end's layout), and `dispatch(manifest, command, front)` runs it on the large stack kink's definitions need.
- `FrontEnd` is what a front end adds: `spelling`, how next steps spell its commands, with whatever selects its corpus (the trait `CommandSpelling`; kink-flow's own is `KinkFlowSpelling`); `refused`, the mutations its own checks refused, each with an `InvalidReason::External { name, next }`; and `annotate`, applied to every document before it is printed and, for `run`, before each write of the report.
  A refused mutation's `run` row has status `invalid-mutation`, the front end's reason, detail and next step (`action`), and nothing is resolved, compiled or run for it, so no outcome record, hint or memo record is written; `check --mutations` adds the refusal to its row, and a `fuzz` kill job of it is refused.
- `check_corpus_mutations` and `check_mutations_document` let a front end add its findings (`Finding::refused` for a refusal) and its own row keys (`MutationCheckRow::extra`, rendered after kink-flow's keys) between the check and its document.
- `visit_rules` visits every object of a document that names a sentence of the baseline (a `module` and an `index`; in `spec.exclusion`, the `authors` of each compiled sentence), with the sentence and its label, so a front end can add its own names to every rule a document names.
  A rule named only by a compiled id or as text (a specification diagnostic's `rule_id`, a query witness path's `rules`) names no baseline sentence and is not visited.
- `verdicts` is the rendering above.
