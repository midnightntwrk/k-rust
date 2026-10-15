# k-in-k2

k-in-k2 provides execution pattern matching and semantic mutation testing for K definitions.
It is built on k-rust,
which the workspace consumes as a path dependency.
The intended source is the on-disk checkout at `../inspirations/midnightntwrk/k-rust`, tracking k-rust main.
The workspace builds against a read-only export of k-rust main commit `927b9ce6352357db340c221ff5377b294b8324e9` at `../k-rust-927b9ce6`,
exported with `git -C ../inspirations/midnightntwrk/k-rust archive 927b9ce6352357db340c221ff5377b294b8324e9 | tar -x -C ../k-rust-927b9ce6`.
That commit carries variable identity version 3: verbatim name reading, injective printing and request-unique free mints.
Moving back to the live checkout means changing the two paths in `Cargo.toml` `[workspace.dependencies]` and adapting to the new k-rust.
The work is intended to be merged into k-rust together with KRS.

## Crates

| Crate | Purpose |
|---|---|
| [`kink-pattern`](crates/kink-pattern) | Execution pattern plans evaluated over paths whose payloads are KORE patterns. |
| [`kink-patch`](crates/kink-patch) | Patches over a loaded k-rust `Definition`, mutation sites and candidate selection; SemanticInput artifacts, SHA-256 digests, sentence fingerprints that pin every patch, and the canonical patch codec. |
| [`kink-native`](crates/kink-native) | Mutant validation and execution adapters over the k-rust backend, and the bridge to kink-pattern paths. |
| [`kink-campaign`](crates/kink-campaign) | Campaign runner, typed oracle comparison, mutant classification and scoring; campaign manifests, deterministic JSON campaign reports and replay. |

## Using kink-flow

`kink-flow` (crate [`kink-flow`](crates/kink-flow)) is the tool for the primary usage flow:
an LLM writes a concrete test corpus for a K specification and mutations of its rules,
and the tool reports which mutations no corpus program kills.
This section is written for the LLM that drives the loop;
[`crates/kink-flow/README.md`](crates/kink-flow/README.md) is the reference for every field and reason.

### The loop

1. **Specification.** Start from a K specification: an entry file, its main module and its syntax module.
   A literate Markdown specification (`.md`) works too: every text kink-flow addresses, searches or shows is the K text k-rust parsed from the selected fences (prose and fence lines count as whitespace, and line numbers are the file's), and kink-flow never edits the Markdown file.
2. **Corpus with cached results.** Write concrete programs for it in `FLOW.toml`.
   `kink-flow results` runs each new or changed program once on the specification,
   caches its final configuration, and lists the rules no comparable program reaches (`uncovered`).
   Write programs until no rule is uncovered.
3. **Mutation list.** Write `MUTATIONS.toml`: edits of rules that are likely to expose bugs,
   either single edits (one `+Int` becomes `-Int`) or correlated edits (several rules changed together as one mutation).
4. **Kill search with an outcome cache.** `kink-flow run` checks, for each mutation, whether some program's final configuration changes.
   It reports the survivors: mutations no program kills.
   For each survivor, write a program that kills it, or argue that the mutation is equivalent and drop it; then run again.
   Each proved outcome of a mutation on a program is cached, so a later run with the same specification, budget and kink build
   re-checks a killed mutation with no run at all, and runs a survivor only on the programs added since.
   After an edit of the specification, a killed mutation is re-proved first with the program that last killed it (its hint).

Only a proved difference kills: kink-campaign's runner compares the exit stop and the whole final configuration of the baseline and the mutant on each program.
With identical inputs, a cached proved difference stands without being re-run: this rests on k-rust's compile and execution determinism,
on the cache key naming every input of the outcome (kink's build, the k-rust revision, the specification, the mutation, the program, its baseline result and the budget),
and on the integrity of the cache directory, which is trusted like the build.
`kink-flow run --verify` re-proves every cached outcome and reports any disagreement as an error.
A killer hint or a cached result never decides a status: the hint only orders the work, and a cached result detects a corpus that changed under the cache.

### Commands

Every command prints one JSON document on stdout.
The exit status is 0 when the command did its job (survivors, timeouts and invalid mutations included),
1 when the manifest, the mutation list, the specification or a program is refused, a cache file cannot be written, or a corpus error stops a run,
and 2 on a usage error (message on stderr).

| Command | Does |
| --- | --- |
| `kink-flow check FLOW.toml` | Loads and admits the specification and parses every program; reports each refusal with its stage and reason. |
| `kink-flow results FLOW.toml [--verify]` | Fills the result cache for new or changed programs; lists every program's class and every rule's coverage; `--verify` reruns every program and compares it with its cached result. |
| `kink-flow run FLOW.toml MUTATIONS.toml [--only ID]... [--verify]` | Updates the result cache, resolves each mutation, runs the kill search, updates the outcome cache and the killer hints, and writes the report. `--verify` decides nothing from the outcome cache: it re-proves every cached outcome, reports each that differs (`mismatches`, exit 1) and writes no outcome and no hint. |
| `kink-flow report FLOW.toml` | Prints the last run's report again, byte for byte. |

`results`, `run` and `report` take `--cache DIR`; the default cache is `.kink-flow/` next to `FLOW.toml`.

### Walkthrough

The walkthrough below uses the calc specification of [`testdata/flow/calc`](testdata/flow/calc).
`crates/kink-flow/tests/report.rs` follows it literally on a fresh copy of that directory:
it reads the blocks of this section in order, writes the files, runs the commands and checks the outputs shown.

The specification, `calc.k`:

<!-- example: file calc.k -->
```k
// Flow fixture (F-02): a tiny expression language for kink-flow's tests.
// `+` and `*` are labelled rules, `-` is an unlabelled rule; strictness heats
// operands, and the result is the single Int left in the <k> cell.
module CALC-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | "(" Exp ")" [bracket]
               > left:
                 Exp "*" Exp [strict, symbol(mul)]
               > left:
                 Exp "+" Exp [strict, symbol(add)]
               | Exp "-" Exp [strict, symbol(sub)]
endmodule

module CALC
  imports CALC-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>

  syntax KResult ::= Int
  rule [add]: I1:Int + I2:Int => I1 +Int I2
  rule [mul]: I1:Int * I2:Int => I1 *Int I2
  rule I1:Int - I2:Int => I1 -Int I2
endmodule
```

A first corpus, `FLOW.toml`, with one program in a file and one written inline:

<!-- example: write FLOW.toml -->
```toml
[spec]
entry = "calc.k"              # relative to this file's directory
main_module = "CALC"
syntax_module = "CALC-SYNTAX"

[budget]                      # optional; these are the defaults
time_ms = 10000               # wall-clock bound of one program run
max_depth = 100000            # rewrite-depth bound of one program run

[[program]]
id = "add"
file = "programs/add.calc"

[[program]]
id = "square"
text = "2 * 2"
```

where `programs/add.calc` holds

<!-- example: file programs/add.calc -->
```text
1 + 2
```

Check the corpus and fill the result cache:

<!-- example: run -->
```sh
kink-flow check FLOW.toml
kink-flow results FLOW.toml
```

`results` lists the rules no comparable program reaches first.
Here the unlabelled subtraction rule on line 23 is uncovered:

<!-- example: output /rules/0 -->
```json
{"module": "CALC", "file": "calc.k", "label": null, "start_line": 23, "end_line": 23,
 "status": "uncovered", "reached_by": []}
```

Cover it with a program, `programs/sub.calc`:

<!-- example: file programs/sub.calc -->
```text
10 - 4 - 3
```

<!-- example: append FLOW.toml -->
```toml

[[program]]
id = "sub"
file = "programs/sub.calc"
```

<!-- example: run -->
```sh
kink-flow results FLOW.toml
```

Only the new program runs (`computed`); the others come from the cache, and no rule is uncovered:

<!-- example: output /summary -->
```json
{"programs": 3, "comparable": 3, "computed": 1, "uncovered": 0, "covered": 3}
```

A rule that no run can observe (an equation, such as a `[function]` rule) is listed as `not-observable`, never as uncovered.
A program whose class is not `comparable` cannot kill a mutant; `cause` says why:
`timeout` (the program did not end within `time_ms`: make it end, or raise the budget),
`unknown` (it ended without a value kink compares, for example a collection with a Bytes key or `max_depth` reached),
`refused` (it did not parse) or `error`.

Now the mutations, `MUTATIONS.toml`.
Each edit is addressed to one rule: by its label (`rule`, bare or `MODULE.label`), by any line inside it (`line`),
or by text that occurs exactly once in the file (`find` alone).
`find` must occur exactly once in the addressed rule and is replaced by `replace`; `delete = true` removes the rule.
Several edits in one mutation are applied together or not at all:

<!-- example: write MUTATIONS.toml -->
```toml
[[mutation]]
id = "add-becomes-sub"
note = "addition evaluates as subtraction"

  [[mutation.edit]]
  rule = "add"
  find = "I1 +Int I2"
  replace = "I1 -Int I2"

[[mutation]]
id = "mul-becomes-add"
note = "multiplication evaluates as addition"

  [[mutation.edit]]
  find = "I1 *Int I2"
  replace = "I1 +Int I2"

[[mutation]]
id = "no-sub"
note = "the subtraction rule is deleted"

  [[mutation.edit]]
  line = 23
  delete = true

[[mutation]]
id = "add-and-mul-swapped"
note = "correlated: + multiplies and * adds"

  [[mutation.edit]]
  rule = "CALC.add"
  find = "I1 +Int I2"
  replace = "I1 *Int I2"

  [[mutation.edit]]
  rule = "mul"
  find = "I1 *Int I2"
  replace = "I1 +Int I2"
```

Run the kill search:

<!-- example: run -->
```sh
kink-flow run FLOW.toml MUTATIONS.toml
```

Three mutations are killed; `2 * 2` equals `2 + 2`, so `mul-becomes-add` survives:

<!-- example: output /survivors -->
```json
["mul-becomes-add"]
```

<!-- example: output /counts -->
```json
{"killed": 3, "survived": 1}
```

The survivor's row says what was changed, which programs reach the changed rule, and how each program ran on the mutant:

<!-- example: output /mutations/1 -->
```json
{
  "id": "mul-becomes-add",
  "status": "survived",
  "killer": null,
  "rules": [
    {"module": "CALC", "file": "calc.k", "label": "CALC.mul", "start_line": 22, "end_line": 22,
     "before": "rule [mul]: I1:Int * I2:Int => I1 *Int I2",
     "after": "rule [mul]: I1:Int * I2:Int => I1 +Int I2"}
  ],
  "reaching": ["square"],
  "executed": [
    {"program": "square", "outcome": "agree", "cause": null},
    {"program": "add", "outcome": "agree", "cause": null},
    {"program": "sub", "outcome": "agree", "cause": null}
  ]
}
```

`kink-flow report` prints the same document again, from `.kink-flow/report.json`:

<!-- example: run -->
```sh
kink-flow report FLOW.toml
```

To kill the survivor, write a program that reaches the edited rule and whose final configuration the edit changes.
`square` reaches the rule but agrees, because `2 * 2` and `2 + 2` are both `4`; `2 * 3` is `6`, and `2 + 3` is `5`:

<!-- example: append FLOW.toml -->
```toml

[[program]]
id = "product"
text = "2 * 3"
```

<!-- example: run -->
```sh
kink-flow run FLOW.toml MUTATIONS.toml
```

<!-- example: output /survivors -->
```json
[]
```

<!-- example: output /mutations/1 -->
```json
{"id": "mul-becomes-add", "status": "killed", "killer": "product", "killer_from_cache": false}
```

The other mutations made no call: their proved kill is in the outcome cache, under the same specification, budget and kink build.
Only `mul-becomes-add` ran, on the new program alone (the others had already agreed with it):

<!-- example: output /mutations/0 -->
```json
{"id": "add-becomes-sub", "status": "killed", "killer": "add", "killer_source": "outcome-cache",
 "killer_from_cache": true, "calls": []}
```

<!-- example: output /mutations/1/calls -->
```json
[{"programs": ["product"], "status": "killed"}]
```

A survivor that no program can kill is an equivalent mutant: for example, swapping the operands of `+Int` changes no result.
Argue why, then drop it from `MUTATIONS.toml`.

### Reading the report

The report (`run`'s output and `.kink-flow/report.json`) holds the specification digest, the k-rust revision and the solver profile;
`counts` per status; `survivors`, the ids of the mutations no program killed that a new program could kill;
`unusable_programs`, every program that cannot kill (`{id, class, cause}`);
and one row per mutation, in the list's order.

A killed row names its `killer` and where the kill came from (`killer_source`):
`outcome-cache` (a proved kill cached under identical inputs; no call), `hint` (the program that last killed the mutation, run alone first) or `search` (the full scan);
`killer_from_cache` is true for the first two.
The top-level `outcome_cache` counts the mutations and programs taken from the cache and the records written.
Every other row also carries:

- `rules`: each edited rule's `file`, `start_line`, `end_line`, `label`, and its source text `before` and `after` the edit (`after` is null for a deleted rule);
- `reaching`: the comparable programs whose cached coverage reaches an edited rule;
- `executed`: each program the mutant ran on, in order, with its `outcome` (`agree`, `distinguish`, `timeout`, `unknown`, `incomparable` or `error`) and, unless it agreed or distinguished, the `cause`; `cached: true` marks an outcome taken from the outcome cache (it comes first, and only agreements and kills are cached);
- `action`: what the status asks of you.

| Status | What it asks |
| --- | --- |
| `killed` | Nothing. |
| `survived` | Every executed program agreed. Write a program that reaches an edited rule and whose final configuration the edit changes; if `reaching` is empty, first reach the rule. |
| `timeout` | A program did not end on the mutant within `time_ms`, and no program killed it. Write a program that ends under the mutant with a different final configuration; a timeout is never cached as a killer. |
| `unknown` | A program's result on the mutant is not a value kink compares (see its `cause`), and no program killed it. Write a program whose final configuration under the mutant kink can compare. |
| `equivalent` | The mutant compiles to the baseline's definition; nothing can kill it. Drop or change the mutation. |
| `invalid` | The mutant does not compile (`reason`). Fix the mutation. |
| `invalid-mutation` | The mutation does not resolve (`reason`, `edit`, `detail`). Fix the mutation. |
| `error` | The runner failed, or a corpus error stopped the run (`reason`: `baseline-mismatch:<program>`, `baseline-count-mismatch`, `campaign-refused`, `program-refused:<program>`, `no-comparable-program`). Fix the corpus; `kink-flow results FLOW.toml --verify` shows which cached result no longer holds. `outcome-conflict` (a cached agreement next to a mutant that no longer compiles) stops the run too: run `kink-flow run FLOW.toml MUTATIONS.toml --verify`. `outcome-mismatch:<program>` comes from `run --verify`: a cached outcome differs from a live run; report it and delete `outcomes/`. |

### The cache directory

`.kink-flow/` (or `--cache DIR`) holds plain JSON; deleting it, or any file in it, is always safe:

- `results/<spec digest>/<program digest>.json`: one program's cached result (class, cause, baseline evidence, final configuration, rule coverage);
- `outcomes/<context digest>/<mutation identity>.json`: one mutation's proved outcomes (`killed` or `agree`) per program, with an integrity digest per record;
  the context is kink's build, the k-rust revision, the solver profile, the specification digest, the budget and the oracles;
  a timeout, an unknown or an error is never cached;
- `hints.json`: each killed mutation's last killing program, keyed by the mutation's edits and its rules' text (no positions), a scheduling hint only;
- `report.json`: the last run's report.

The specification digest covers every source file the specification loads, so editing the specification reruns every program and every mutation, each killed one first with its hint;
the program digest covers a program's text, start sort and variables, so editing a program reruns only that program.
Rebuilding kink starts a new outcome context. The `killers/` directory of earlier versions is no longer read and can be deleted.

### A larger example: IMP

[`examples/imp`](examples/imp) runs the loop on the K tutorial's IMP (`pl-tutorial/1_k/2_imp/lesson_4`):
a corpus of seven programs that covers every rule, 21 mutations (three of them correlated), and the results of the runs.
Its README also says what IMP's `strict` operators cost and why a run needs a small `time_ms` and a memory limit.

## SemanticInput, manifests, reports and replay

A baseline's `SemanticInput` v1 is exactly k-rust's compact `KRUST-PROVENANCE` v7 document of the loaded definition and its source table; its digest is the SHA-256 of those bytes.
`SemanticInput::read` accepts only the canonical encoding and rebuilds the baseline without the `.k` sources.
A sentence fingerprint is a domain-separated SHA-256 of the sentence without source positions, provenance receipts or term metadata.
Candidate selection pins every patch to the fingerprints of the sentences it addresses, and `apply` refuses a stale pin as `StalePrecondition`, before any edit and so before compilation.
A fingerprint is a version check, not an identity: a sentence is identified by its module and index in one baseline.

A campaign manifest (`kink-campaign-manifest` v1) records the k-rust revision, the provenance format, the solver profile, the compile and backend options, the budget, the schedule, the operator id, version and policy, the baseline and per-mutant digests (SemanticInput, metadata-free structure, compiled KORE), the validation outcome of each mutant, and digests of the tests and the observation.
A campaign report (`kink-campaign-report` v1) embeds the manifest and adds the origins, each mutant's canonical patch, the affected sentences with old and new fingerprints, a normalized structural diff, the per-test oracle sides, the claims and the summary.
Both are canonical JSON with no wall-clock value and no absolute path, so repeated runs give identical bytes.

`replay` takes a report, the baseline artifact and the caller's declaration, including the selection code.
It checks the schema, the manifest digest, the build environment and the artifact digest, rebuilds every mutant from its canonical patch and checks its digests, then reruns selection and the campaign.
It returns `Reproduced` only when the regenerated report is byte-identical to the input; anything else is a refusal or a divergence, never a verdict.
Replay assumes the same kink build and operator code, no time bound firing in either run, and k-rust's provenance round trip and compilation determinism.

## Upstream requests

Requests this project makes of k-rust and KRS are recorded in the ledgers under [`upstream/`](upstream/README.md).

## Gate

Every commit must pass the per-commit gate, the no-Z3 workspace build and the Z3 profile:

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace --no-fail-fast
with-z3-static-4.16.0 cargo clippy -p kink-native -p kink-campaign -p kink-corpus --all-targets --features z3 -- -D warnings
with-z3-static-4.16.0 cargo test -p kink-native --features z3 --no-fail-fast
with-z3-static-4.16.0 cargo test -p kink-campaign --features z3 --no-fail-fast
with-z3-static-4.16.0 cargo test -p kink-corpus --features z3 --no-fail-fast
```

The milestone gate is the same commands with `-- --include-ignored` added to every `cargo test`.
It also runs the whole-fixture sweeps marked `#[ignore = "milestone"]`,
each of which has a smaller variant in the per-commit gate.
Run it before a merge and when a work package closes.
The external corpus measurements in `kink-corpus/tests/external.rs` are ignored for another reason;
under `--include-ignored` without `KINK_WORKSPACE` they only record a skip.

The workspace build is the no-Z3 solver profile.
`kink-native` has a `z3` feature for the Z3 profile
(it enables k-rust `z3-inference` and k-rust-backend `z3`).
`kink-campaign` and `kink-corpus` forward that feature as `z3`,
and `kink-campaign` requires its execution adapter's solver profile to match the build.
Their tests carry profile columns for outcomes that differ between no-Z3 and Z3.
Z3 comes from the machine wrapper `with-z3-static-4.16.0`,
which points the `z3-sys` build at a static Z3 4.16.0 library;
without the wrapper a `z3` build fails to link (`-lz3` missing),
and nothing is downloaded at build time.

Dependencies are built with `opt-level = 2` in the dev and test profiles (`Cargo.toml`),
because loading and compiling K definitions in k-rust dominates test time;
the workspace crates keep the plain dev profile with debug assertions and overflow checks.

## Retired tooling

The earlier official-K "G-track",
its TypeScript/Bun probes and the oracle were removed from the tree.
The local tag `archive/g-track-2026-08` marks the last commit that contains them.
