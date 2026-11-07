# kink (k-in-k2)

kink provides execution pattern matching and semantic mutation testing for K definitions.
It is built on k-rust and is a part of k-rust's repository: its crates (`kink/crates/*`) are members of k-rust's workspace and build against the k-rust beside them (`crates/k-rust`, `crates/k-rust-backend`), at whatever commit the checkout is.
kink was developed as the separate repository k-in-k2 and merged into k-rust under `kink/` with its history.
kink has two front ends over one engine: `kink-flow` runs the corpus loop over a K definition ("Using kink-flow", below), and `krs kink` runs the same loop over a KRS package.
What a verdict rests on (the premises of a kill, of the caches and of every stored verdict) is kink's trust document, [`trust.md`](trust.md), normative and kept beside the code.

kink's decision register, [`decisions.md`](decisions.md), collects settled design decisions with their reasons and evidence as they are recorded; a proposal to change one must answer the reasons stated there.
Among them: mutations of a KRS specification are K patches of its emitted K, not Rust edits (M1).

## Crates

| Crate | Purpose |
|---|---|
| [`kink-pattern`](crates/kink-pattern) | Execution pattern plans evaluated over paths whose payloads are KORE patterns. |
| [`kink-patch`](crates/kink-patch) | Patches over a loaded k-rust `Definition`, mutation sites and candidate selection; SemanticInput artifacts, SHA-256 digests, sentence fingerprints that pin every patch, and the canonical patch codec. |
| [`kink-native`](crates/kink-native) | Mutant validation and execution adapters over the k-rust backend, and the bridge to kink-pattern paths. |
| [`kink-campaign`](crates/kink-campaign) | Campaign runner, typed oracle comparison, mutant classification and scoring; campaign manifests, deterministic JSON campaign reports and replay. |
| [`kink-flow`](crates/kink-flow) | The user tool: the corpus loop over a K definition, and the library `krs kink` runs: manifest, statuses, caches and documents. |
| [`kink-corpus`](crates/kink-corpus) | The admission-and-input library both front ends build on, and kink's corpus harness (binary, manifest, store, summary) used by kink's tests and maintainers ([`crates/kink-corpus/README.md`](crates/kink-corpus/README.md)). |

## Using kink-flow

`kink-flow` (crate [`kink-flow`](crates/kink-flow)) is the tool for the primary usage flow:
an LLM writes a concrete test corpus for a K specification and mutations of its rules,
and the tool reports which mutations no corpus program kills.
This section is written for the LLM that drives the loop;
[`crates/kink-flow/README.md`](crates/kink-flow/README.md) is the reference for every field and reason.
Build the portable profile for the loop, from the root of k-rust's checkout: `cargo build --release -p kink-flow --no-default-features`.
The default build is the Z3 profile ("Gate", below), under which every solver query is bounded by Z3 resource units (`[budget] smt_resource_limit`) and the caches are on as in the portable build, and `kink-flow query` gives no `no` answer: every answer that would be `no` is `unknown`, until k-rust's KINK-28; the walkthrough below is written for the portable build.

For a KRS specification, `krs kink <verb>` is the same loop over a KRS package: it builds the package, keeps the K it emits as `kink/definition.k`, runs these verbs with these options over it, and names every rule a document names by its Rust item and position (`krs = {item, file, line, ..}`).
Its corpus is `<package>/kink/`, with a `FLOW.toml` whose `[spec]` is `krs = { definition = "main" }`, and mutations are K patches of the emitted rules anchored by the item's name (`rule = "plus_zero"`); KRS's workflow reference, "The corpus loop" (`docs-site/src/pages/reference/workflow.mdx`), is its reference, and the docs-site page "Mutation testing a KRS specification" (`docs-site/src/pages/verification/mutation-testing.mdx`) is its guide.

### The loop

1. **Specification.** Start from a K specification: an entry file, its main module and its syntax module.
   A literate Markdown specification (`.md`) works too: every text kink-flow addresses, searches or shows is the K text k-rust parsed from the selected fences (prose and fence lines count as whitespace, and line numbers are the file's), and kink-flow never edits the Markdown file.
2. **Corpus with cached results.** Write concrete programs for it in `FLOW.toml`.
   `kink-flow results` runs each new or changed program once on the specification,
   caches its final configuration, and lists the rules no comparable program matches (`uncovered`).
   Write programs until no rule in scope is uncovered ("What coverage covers", below).
3. **Mutation list.** Write `MUTATIONS.toml` (or one `<topic>.toml` per topic in a mutations directory): edits of rules that are likely to expose bugs,
   either single edits (one `+Int` becomes `-Int`) or correlated edits (several rules changed together as one mutation),
   each with the plausible misunderstanding of the specification it writes (`misunderstanding`).
   `kink-flow check FLOW.toml --mutations MUTATIONS.toml` resolves every mutation without compiling or running anything: it shows each edited rule before and after, and refuses a mutation that does not resolve (a stale anchor, overlapping edits, an edit of a sentence that is not a rule) with what to do next.
   A mutant kink does not compile is found only by `run` (status `not-admitted`).
   `kink-flow results FLOW.toml --mutations MUTATIONS.toml` (and every run report) lists the rules no mutation targets yet (`untargeted_rules`, with each rule's K text and how to address it).
4. **Kill search with an outcome cache.** `kink-flow run` checks, for each mutation, whether some program's final configuration changes.
   It reports the survivors: mutations no program kills.
   For each survivor, write a program that kills it, or argue that no program can and drop the mutation, or keep it with the argument in its `misunderstanding`; then run again.
   An argued survivor stays `survived`: the status `equivalent` is only that of a mutant kink shows to be the specification: one that compiles to the baseline's definition, or whose every edit only adds to an equation's `requires` a condition that holds of every value of its variables' sorts (reason `valid-condition`).
   Each proved outcome of a mutation on a program is cached, so a later run with the same specification, budget and kink build
   re-checks a killed mutation with no run at all, and runs a survivor only on the programs added since.
   After an edit of the specification, a killed mutation is re-proved first with the program that last killed it (its hint).

**Checking a pattern.** When you write a program to exercise a situation, write the situation as a K pattern in `PATTERNS.toml` (`pattern = "<k> _:Int / 0 ~> _ </k>"`, as a rule's left-hand side is written) and claim the program hits it (`programs = ["divzero"]`).
`kink-flow query FLOW.toml PATTERNS.toml` answers, per (pattern, program), whether some run reaches a configuration that matches: `hit` with the matching configuration and the rules of a run to it, `no` (the claim is refuted: the program never does what you said it tests), or `unknown` with its cause.
A `no` needs the program's whole state space explored within the budget, a comparable baseline run and a definition that leaves no value to the implementation (decision 1's census), so a bounded or open run is `unknown`, never `no`; a `hit` needs only the run it found and a matched configuration k-rust shows defined (one holding an unevaluated call of a partial function is `unknown`, unless k-rust shows that call defined: by an unconditional ceil equation, or from its observation catalog as a sort projection on its exact image or a field of a one-constructor sort), and stands under k-rust's choice of an open value and its strict reading of `andBool`, `orBool` and `#if`, one reading K allows.
Definitive answers are cached under a key that names the specification, the program, the compiled pattern, the budget and kink's build, `--verify` re-derives them, and no answer ever decides a mutation ([`crates/kink-flow/README.md`](crates/kink-flow/README.md), "Checking a pattern").

**Killing a survivor with `fuzz`.** When no program you can think of tells a survivor apart, take a program that matches the edited rule (the run report's `witnesses` lists the programs whose coverage witnesses the edit), mark its literals as holes in `TEMPLATES.toml` (k-rust-fuzz's `[[hole]]` keys), and run `kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID --kill MUTATION --mutations MUTATIONS.toml`.
It runs a k-rust-fuzz campaign in process on kink's own two sides (the admitted baseline and the claim-free mutant `run` would test), judges each candidate by kink's own rules inside the campaign (`--no-filter` turns that off), has kink's own `run` confirm the witness on the flow with the fragment as its only program (`--no-confirm` skips it), and prints the killing program as a `[[program]]` fragment; it never writes `FLOW.toml` or the cache.
The same command looks for a program that matches an uncovered rule (`--matched FILE:LINE`, as `results` lists it; `--fired` for one that fires it) or hits a pattern (`--pattern ID --patterns PATTERNS.toml`); [docs/fuzzing.md](../docs/fuzzing.md) is the user guide to the three jobs.
Append the fragment and run `kink-flow run --only MUTATION`: only `run` decides the kill, with its own oracle.
The fuzz refuses up front what `run` could not confirm: a mutation `run` refuses, a definition exclusion on either side, a mutant that parses the template differently from kink's input (a `[macro]` edit), and a definition whose full critical-pair check has a finding you have not named (`--assume-joined NAME`, then `[spec] assume_joined`; every assumed name is printed beside the fragment as a premise, genuine ones flagged).
Each candidate's input is checked against kink's own assembly of the fragment, and the document warns about a template whose program is not comparable or does not witness the mutant's edit in the last run, suggesting the witnesses as templates ([`crates/kink-flow/README.md`](crates/kink-flow/README.md), "Killing a survivor with `fuzz`").

### What a kill means

A kill is a proved difference: on some comparable program, the mutant's ends differ from the specification's in the exit stop or in the final configuration on the compared cells
(every cell but the unobservable ones, or the cells `[result] cells` names; kink-flow's README, "Which cells are compared").
It is found by a live run, or read from the outcome cache, whose key names every input of the outcome (kink's build, the k-rust revision, the specification, the mutation, the program, its baseline result and the budget).
`kink-flow run --verify` re-proves every cached outcome, and a killer hint only orders the work.
A survivor says that no program of the corpus tells the mutant apart from the specification:
it is a target for a new program, or a mutant no program can kill, to argue away, never a sign that the specification is wrong.
Nor does a survivor show that no program can kill it: "no program found" is not "no program exists".

What makes a run `unknown` instead of a verdict, each cause with the premise it protects in [`trust.md`](trust.md):

- the definition leaves a value open and k-rust chose one (`choice`, an implementation-chosen hook): ["What a kill trusts"](trust.md#what-a-kill-trusts), the bullet on k-rust's model of the definition;
- the run used the strict definedness of an operand a skipping reading of `andBool`, `orBool` or `#if` may skip (`short-circuit-reading`): the short-circuit bullet;
- a rule or equation condition `{ A #Equals B }` over terms that may be undefined: the `#Equals` bullet;
- the baseline's ends are not data: its critical-pair check has a finding `[spec] assume_joined` leaves unnamed (`baseline-findings`): the confluence bullet;
- an end is not data under one of the two definitions: the bullet "Every compared end is data under both definitions";
- a work or depth bound stopped the run before every end was found (a one-sided kill is still possible; a time bound gives `timeout`, never cached): the one-sided bullet;
- the edit leaves a trusted claim unbacked that no removal takes away (`unsupported-claims`): the claim-removal bullet;
- the run's result can depend on the host, for example a stop for lack of native stack (`stack-stop`): the host bullet and ["Stack dependence"](trust.md#stack-dependence);
- under the Z3 profile, a solver query kink asks left undecided within its resource units, which can make a comparison unknown and never a kill: "Stack dependence", its last paragraph.

The full record is [`trust.md`](trust.md).

### What coverage covers

Coverage, in `kink-flow results` and in the fuzz's rule jobs (`--matched`, `--fired`), is meant to cover the parts of the specification that compute a step, since those are what a mutation edits and a program can tell apart.
This is the boundary (kink27 R2-COVERAGE-DOCS); each item in scope says whether it is built today and which function builds it.

In scope:

- **Rewrite rules.** Built.
  `kink-flow results` lists every authored `rule` sentence (kink-flow `results::rules`) and gives it status `uncovered` when no comparable program's baseline run matched it.
  `matched_by` is k-rust's `matched` (kink-native `TestCoverage::of_run`): the run began to decide the rule's `requires` for an instance whose left-hand side matched, whatever the verdict, or applied the rule.
  `kink-flow fuzz --matched` targets one (kink-flow `resolve_rule`), as `krust fuzz --reach-rule` does (k-rust-fuzz `resolve_rule_recorded`).
- **Function equations**, `owise`, `anywhere` and the equations of an overloaded function included. Built in `results`, not built yet in the fuzz.
  `results` lists and covers an equation as it does a rewrite rule: kink-native's coverage domain (`coverage_domain`) holds every axiom of the compiled `definition.kore` but `smt-lemma` and `non-executable` ones (macro and alias rules are compiled apart, into `macros.kore`), and k-rust records an equation in `matched` and `applied` wherever a run applied it (k-rust `RunCoverageOutput`).
  Those lists also hold an equation that the load-time discharge of a matched rule's definedness used, which the run never evaluated, so `matched_by` can list a program for an equation it did not evaluate.
  That is why the fuzz does not target an equation yet: `kink-flow fuzz --matched` and `--fired` refuse one as `equation-target` (`resolve_rule`) and `krust fuzz --reach-rule` as an equation (`TargetProblem::Equation`, in `resolve_rule_recorded`; finding REACH-EQUATIONS).
  Target a rewrite rule whose step evaluates the function instead.
- **A rule's `requires`, counted as two outcomes**: the rule applied, and the rule was matched and did not apply.
  The first is built as a listing and as a fuzz target, not as a status: `fired_by` lists the programs that fired the rule (for a rewrite rule, some path takes its step, k-rust `committed`; for an equation, an instance gave a result, `applied`; kink-native `TestCoverage::of_run`), and `kink-flow fuzz --fired RULE` targets it for a rewrite rule, but the status reads `matched_by` alone, so a rule some program matched and none fired is `covered`.
  The second is not built yet: kink asks k-rust for no condition records (`collect_conditions: None`, kink-native `execution::request`), and `matched` holds a rule whatever the verdict, so no kink document tells a rule whose `requires` held on every instance a run reached from one whose `requires` also failed on some instance, and no reach mode targets a failed `requires`.
  `krust fuzz`'s summary lists the rewrite rules whose condition the campaign's cases reached but which never applied (k-rust-fuzz `write_coverage`): the rules the first outcome is missing for, not the second outcome.

- **Heating and cooling rules** that kompile generates from a `strict` or `seqstrict` production attribute or a `context` sentence. They compute steps, so they are in scope, attributed to the authored attribute or `context`, which is what a mutation of evaluation order edits. Not built yet: `results` lists `rule` sentences only, so they have no row.

Out of scope, each for its reason:

- **Simplification, `symbolic` and ceil equations.** They state facts about functions and compute no step; a mutant of one is a claim edit (claims are premises, [`trust.md`](trust.md), "What a kill trusts").
  `results` does not leave them out yet: they are in kink-native's coverage domain and k-rust records them when a run applies them, so `results` gives each a status, and an `uncovered` row can be one of them, which no program needs to reach.
- **Overload axioms kompile generates** (an equation between an overloaded symbol's application and its overload's, through an injection). They state that the overloads agree and compute no step of their own. The authored equations of an overloaded function are in scope (above).
- **Macros and aliases.** They are expanded at compile time, so their rules are the expanded ones, covered where they occur.
  `results` lists such a rule as `no-coverage-signal`, never `uncovered` (`results::rules`; k-rust's coverage never names a macro or alias rule).
- **Syntax productions.** Parsing the corpus covers them. `results` lists `rule` sentences only, so a production has no row.
- **Hooks.** They are the backend's code, not the specification's; they are no axioms, and k-rust's coverage never names one.
- **The initial configuration.** Every run uses it. The `configuration` sentence has no row.

### Commands

Every command prints one JSON document on stdout.
The exit status says what to do next ([kink-flow's README](crates/kink-flow/README.md#exit-status)):
0 when the command answered its question (survivors included),
1 for a finding (a `--verify` mismatch, a fact `check` finds that makes a verdict impossible, an unmet expectation in `results`, a refuted pattern claim),
2 when the question could not be asked (a usage error, with its message on stderr; the manifest, the mutation list, the specification, a program or a mutation refused, `run` on an `invalid-mutation` or `not-admitted` mutation; a cache file that cannot be written; a corpus error that stops a run),
and 3 for no answer (a program or a mutation that is `timeout` or `unknown`, a fuzz that ends without a witness kink accepts);
a command with several parts exits 2 when one could not be asked, else 1, else 3, else 0.
A mutation list (`MUTATIONS` below) is a `MUTATIONS.toml` or a directory of `<topic>.toml` files whose ids are qualified by the file's stem ([kink-flow's README](crates/kink-flow/README.md#a-mutations-directory)).

| Command | Does |
| --- | --- |
| `kink-flow check FLOW.toml [--mutations MUTATIONS]` | Loads and admits the specification and parses every program; reports each refusal with its stage and reason, and each program every run of which kink excludes before it runs (the definition exclusion, named with each excluded rule's cause chain and positions, or the program's initial configuration's); exits 1, a finding, when a fact known before any mutant runs makes a verdict impossible: a program that cannot be judged on the baseline, whatever the reason, or a baseline whose full critical-pair check has a finding `[spec] assume_joined` leaves unnamed (each named with what to do) or did not read the whole definition. With `--mutations`, also resolves every mutation against the current specification and runs nothing: each edited rule's before and after, label, file and lines; each refusal with its reason and next step (a stale anchor, overlapping edits, a non-rule sentence, an edit that changes nothing); warnings for `line` and `find`-only anchors and for edited rules no comparable program witnesses in the cached results. It compiles no mutant, so a mutant that does not compile is `not-admitted` only in `run`. Run it after every edit of the mutations or the specification. |
| `kink-flow results FLOW.toml [--verify] [--mutations MUTATIONS]` | Fills the result cache for new or changed programs; lists every program's class, cause and baseline wall time (`wall_ms`) and every rule's coverage; `--verify` reruns every program and compares it with its cached result; `--mutations` also lists the rules no mutation of that list targets. |
| `kink-flow run FLOW.toml MUTATIONS [--only ID]... [--verify] [--order cost\|corpus] [--full] [--compile-workers N] [--no-memo] [--progress]` | Updates the result cache, resolves each mutation, runs the kill search, updates the outcome cache and the killer hints, and writes the report. The search tries the programs whose coverage witnesses an edited rule's edit first (for an edit confined to a rule's right-hand side or `ensures`, those that applied the rule; for any other site-local edit, those that matched it; [`trust.md`](trust.md#what-a-kill-trusts), "What a kill trusts", the paragraph on coverage), each group cheapest first (`--order corpus`: in `FLOW.toml`'s order); the order changes which killer is found first and the cost, never a status. `--full` runs every comparable program on every mutation, in corpus order, instead of stopping at the first kill: each row gets `killed_by`, every killing program, and the document the per-program kill `matrix`; its outcomes are cached in the same store the first-kill search reads, and its `--output verdicts` rendering, which records every killer, is the one a `verdicts.lock` needs. `--verify` decides nothing from the outcome cache: it re-proves every cached outcome, reports each that differs (`mismatches`, exit 1, a finding) and writes no outcome and no hint. `--compile-workers N` compiles up to N mutants ahead of their turn (4 by default; 1 compiles each in its own call); it changes nothing but wall time and memory. A warm run reads the memos of what did not change (re-pin L1-4: each mutation's resolution facts, used only for a mutation tier 1 decides with no call, and the specification's declaration census, under keys that name every input, `kink_build` and `kink`); `--no-memo` reads and writes none, `--verify` re-derives and compares them. `--progress` prints a line on stderr before the baseline results, as each program gets its baseline row, before the list is resolved and as each mutation gets its row (also without the flag when stderr is a terminal); stdout stays the document. |
| `kink-flow report FLOW.toml [--output json\|verdicts]` | Prints the last run's report again, byte for byte; `--output verdicts` prints the stored report's verdicts rendering, which is what that run printed under `--output verdicts`. It runs and compiles nothing. |
| `kink-flow query FLOW.toml PATTERNS.toml [--only ID]... [--verify]` | Updates the result cache and answers each pattern on each program it claims (or on every program): `hit`, `no`, `unknown`, `invalid-pattern` or `error`, with the witness of a hit, refuted claims flagged; caches the definitive answers; `--verify` re-derives every answer and compares. |
| `kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID (--kill MUTATION --mutations MUTATIONS \| --matched RULE \| --fired RULE \| --pattern ID --patterns PATTERNS.toml) [--cases N \| --work W] [--seed S] [--max-work N] [--time-limit-ms T] [--assume-joined NAME]... [--one-path] [--no-confirm] [--no-filter]` | Looks for hole values of a template that kill the mutation (or match or fire the rule, or hit the pattern), on kink's own sides, has kink confirm the witness, and prints the program as a `[[program]]` fragment with its premises; writes nothing. Exit 2 when the job is refused up front (a mutation `run` refuses, a definition exclusion, a mutant that assembles the template otherwise, unnamed findings), 3 when the search ends without a witness kink accepts. |

`results`, `run`, `report`, `query` and `fuzz` take `--cache DIR` (`fuzz` only reads the last run document there); the default cache is `.kink-flow/` next to `FLOW.toml`.

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

`results` lists the rules no comparable program matches first.
Here the unlabelled subtraction rule on line 23 is uncovered:

<!-- example: output /rules/0 -->
```json
{"module": "CALC", "file": "calc.k", "label": null, "start_line": 23, "end_line": 23,
 "status": "uncovered", "matched_by": []}
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

Coverage covers rewrite rules and equations alike: a `[function]` rule a program evaluates is covered too.
A rule none of whose compiled forms a run's coverage can name (a macro, alias or `smt-lemma` rule) is listed as `no-coverage-signal`, never as uncovered.
A program whose class is not `comparable` cannot kill a mutant; `cause` says why:
`timeout` (the program did not end within `time_ms`: make it end, or raise the budget),
`unknown` (it ended without a value kink compares, for example a collection holding a `Float` or `max_depth` reached),
`refused` (it did not parse) or `error`.

Now the mutations, `MUTATIONS.toml`.
Each mutation says which misunderstanding of the specification it writes (`misunderstanding`, required).
Each edit is addressed to one rule: by its label (`rule`, bare, `MODULE.label`, or a unique suffix of the label's components), by any line inside it (`line`),
or by text that occurs exactly once in the file (`find` alone); only the label names the rule itself, so `kink-flow check FLOW.toml --mutations MUTATIONS.toml` warns of the other two.
`find` must occur exactly once in the addressed rule and is replaced by `replace`; `delete = true` removes the rule.
Several edits in one mutation are applied together or not at all:

<!-- example: write MUTATIONS.toml -->
```toml
[[mutation]]
id = "add-becomes-sub"
misunderstanding = "addition evaluates as subtraction"

  [[mutation.edit]]
  rule = "add"
  find = "I1 +Int I2"
  replace = "I1 -Int I2"

[[mutation]]
id = "mul-becomes-add"
misunderstanding = "multiplication evaluates as addition"

  [[mutation.edit]]
  find = "I1 *Int I2"
  replace = "I1 +Int I2"

[[mutation]]
id = "no-sub"
misunderstanding = "the subtraction rule is deleted"

  [[mutation.edit]]
  line = 23
  delete = true

[[mutation]]
id = "add-and-mul-swapped"
misunderstanding = "correlated: + multiplies and * adds"

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

The survivor's row says what was changed, which programs witness the changed rule (`witnesses`), and how each program ran on the mutant:

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
  "witnesses": ["square"]
}
```

`executed` lists every program the mutant ran on, in the order the search ran them:
first the programs whose coverage witnesses the edit (here `square`, which fired the edited rule), then the others, each group cheapest first
(by the wall time of the program's baseline run, which `results` records as `wall_ms`).
Every program agreed with the baseline on both oracle slots, the exit stop and the whole final configuration:

<!-- example: output /mutations/1/executed/0 -->
```json
{"program": "square", "outcome": "agree", "cause": null, "cached": false,
 "slots": {"exit-stop": {"outcome": "agree"}, "whole-term": {"outcome": "agree"}}}
```

`kink-flow report` prints the same document again, from `.kink-flow/report.json`:

<!-- example: run -->
```sh
kink-flow report FLOW.toml
```

To kill the survivor, write a program that matches the edited rule and whose final configuration the edit changes.
`square` matches the rule but agrees, because `2 * 2` and `2 + 2` are both `4`; `2 * 3` is `6`, and `2 + 3` is `5`:

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

The killing program's entry (after the cached agreements) names the slot that distinguished and its two sides;
for the whole final configuration it gives each side's number of final configurations and the mutant's as KORE text:

<!-- example: output /mutations/1/executed/3 -->
```json
{"program": "product", "outcome": "distinguish", "cached": false,
 "slots": {"exit-stop": {"outcome": "agree"},
           "whole-term": {"outcome": "distinguish",
                          "sides": {"baseline": {"final_configurations": 1},
                                    "mutant": {"final_configurations": 1, "kore": [{"truncated": false}]}}}}}
```

A survivor its author argues no program can kill stays `survived`: kink decides two such cases by itself, `equivalent` for a mutant it shows to be the specification (it compiles to the baseline's definition, or its edits only add conditions that hold everywhere) and `unkillable` for an edit that only weakens the specification, and an author's argument is neither.
Swapping the operands of `+Int`, for example, changes no result, yet its mutant is another definition and its edit is no weakening, so it survives every program.
Argue why, then drop it from `MUTATIONS.toml`, or keep it with the argument in its `misunderstanding`.

### Reading the report

The report (`run`'s output and `.kink-flow/report.json`, version 10) holds the specification digest, the k-rust revision and the solver profile;
`counts` per status; `survivors`, the ids of the mutations no program killed that a new program could kill;
`unusable_programs`, every program that cannot kill (`{id, class, cause}`);
`untargeted_rules`, every rule no mutation of the list targets (`{module, label, file, start_line, end_line, address, text}`, where `address` is the `rule` or `file` and `line` an edit can use);
and one row per mutation, in the list's order.

A killed row names its `killer` and where the kill came from (`killer_source`):
`outcome-cache` (a proved kill cached under identical inputs; no call), `hint` (the program that last killed the mutation, run alone first) or `search` (the full scan);
`killer_from_cache` is true for the first two.
The top-level `outcome_cache` counts the mutations and programs taken from the cache and the records written.
Every other row also carries:

- `rules`: each edited rule's `file`, `start_line`, `end_line`, `label`, and its source text `before` and `after` the edit (`after` is null for a deleted rule);
- `witnesses`: the comparable programs whose cached coverage witnesses an edited rule's edit: they applied the rule (k-rust `applied`) for an edit confined to its right-hand side or `ensures`, and matched it (`matched`) for any other site-local edit; a definedness claim kink withdraws from the mutant (`removed_claims`) adds no witness through coverage ([`trust.md`](trust.md#what-a-kill-trusts), "What a kill trusts", the paragraph on coverage); every program witnesses an edit that is not site-local, such as an edit of an equation's left-hand side, which can match terms no baseline run tried, and `witnesses_global` is then true;
- `executed`: each program the mutant ran on, in order, with its `outcome` (`agree`, `distinguish`, `timeout`, `unknown`, `incomparable` or `error`) and, unless it agreed or distinguished, the `cause`; `cached: true` marks an outcome taken from the outcome cache (it comes first, and only agreements and kills are cached);
  `slots` names each oracle slot's outcome (`exit-stop`, `whole-term`), and a distinguishing slot's `sides`:
  for the exit stop each side's kinds (for example `["normal"]` against `[]`: the mutant applies a rule whose result is undefined, such as a division by zero, where the baseline ends, and an undefined step is no end),
  for the whole final configuration each side's number of final configurations and, on the killing program, the mutant's as KORE text (cut at 4000 characters, `truncated`);
  `wall_ms` is the mutant's run of the program and `baseline_ms` the program's baseline run, in milliseconds;
  a `timeout` cause says what k-rust returned when the bound fired (how many paths had ended and how deep the deepest went: many shallow paths suggest path explosion, one deep path non-termination), and an `unknown` cause the halt of each returned leaf (a `depth-bound` leaf means `max_depth` stopped it);
- `calls` and `call_wall_ms`: the programs of each runner call and its wall time;
- `action`: what the status asks of you.

| Status | What it asks |
| --- | --- |
| `killed` | Nothing. |
| `survived` | Every executed program agreed. Write a program that matches an edited rule and whose final configuration the edit changes outside the cells `result.not_compared` lists; if `witnesses` is empty, first write one that witnesses the edit: for an edit confined to the rule's right-hand side or `ensures`, one that applies it (k-rust `applied`), since a program that only refutes the rule's guard never runs what the rule builds; for an edit of its `requires` or its left-hand side, one that matches the rule, since the edited guard, or the old guard under the edited bindings, can hold where the old one was refuted; for an attribute edit or a deletion, one that applies the rule, or, for a raised priority or a removed `owise`, one that reaches a state its left-hand side matches where a higher priority group takes the step, since where its guard is refuted a rule takes no step and blocks no lower priority group wherever it is placed ([kink-flow's README](crates/kink-flow/README.md), `run` step 3). |
| `timeout` | A program did not end on the mutant within `time_ms`, and no program killed it. Write a program that ends under the mutant with a final configuration that differs outside the cells `result.not_compared` lists; a timeout is never cached as a killer. |
| `unknown` | A program's result on the mutant is not a value kink compares (see its `cause`), and no program killed it. Write a program whose final configuration under the mutant kink can compare. |
| `equivalent` | kink shows the mutant to be the specification: it compiles to the baseline's definition, or each edit only adds to an equation's `requires` a condition that holds of every value of its variables' sorts (reason `valid-condition`); nothing can kill it. Drop or change the mutation. |
| `not-admitted` | kink did not admit the mutant for judging (`reason`): it does not compile, or k-rust's critical-pair check does not show its equations to have a model (`inconsistent-mutant`, the pairs in `inconsistent_pairs`). Fix the mutation; for `inconsistent-mutant`, rewrite the edit so that the check shows each named pair to join, for example with guards it refutes as disjoint. |
| `invalid-mutation` | The mutation does not resolve (`reason`, `edit`, `detail`). Fix the mutation. |
| `error` | The runner failed, or a corpus error stopped the run (`reason`: `baseline-mismatch:<program>`, `baseline-count-mismatch`, `campaign-refused`, `program-refused:<program>`, `no-comparable-program`). Fix the corpus; `kink-flow results FLOW.toml --verify` shows which cached result no longer holds. `outcome-conflict` (a cached agreement next to a mutant that no longer compiles) stops the run too: run `kink-flow run FLOW.toml MUTATIONS.toml --verify`. `outcome-mismatch:<program>` comes from `run --verify`: a cached outcome differs from a live run; report it and delete `outcomes/`. |

### The cache directory

`.kink-flow/` (or `--cache DIR`) holds plain JSON; deleting it, or any file in it, is always safe:

- `results/<execution digest>/<program digest>.json`: one program's cached result (class, cause, baseline evidence, final configuration, rule coverage, and `wall_ms`, which orders the search and is part of no key);
  only `comparable` and `unknown` results are cached, and of `unknown` only those whose cause is not a host event: a timeout, an error, a stack stop or an allowance refusal depends on the host, so every command runs that program again (`[budget] baseline_max_work` bounds a baseline by work instead, a cached `unknown`); under the Z3 profile the key also names the solver's units and Z3 build;
- `outcomes/<context digest>/<mutation identity>.json`: one mutation's outcomes per program that are functions of their key (`killed`, `agree`, and an `unknown` that counts work or reads the run, such as a work-bound or depth-bound mutant run, with its cause), with an integrity digest per record;
  the context is kink's build, the k-rust revision, the solver profile, the execution digest, the budget's bounds (the work budget and, under Z3, the solver's units and Z3 build included) and the oracles;
  a timeout, an error, a failed run (a host exclusion such as a stack stop or an allowance refusal among them) and an unknown whose judgement the backend refused are never cached;
- `hints.json`: each killed mutation's last killing program, keyed by the mutation's edits and its rules' text (no positions), a scheduling hint only (deleting it with `outcomes/` re-runs the searches cheapest killer first);
- `report.json`: the last run's report;
- `patterns/<execution digest>/<pattern digest>/<program digest>.json`: one cached pattern answer (`hit` with its witness, or `no`); `run` never reads it;
- `memo/`: the warm path's memos of mutation resolution and of the declaration census, keyed by the specification digest, since they cite lines and file text.

The result cache, tier 1 and the pattern cache are keyed by the execution digest, the loaded definition without positions: a comment, a blank line or any other layout edit (a rustdoc comment KRS emits as a K comment included) keeps every stored result and every cached outcome (a mutation addressed by `line` follows its line, so a shifted line moves it to another sentence or to none), while editing a rule, an attribute, the order of rules, a module, an `unobservable` declaration or `[result] cells` reruns every program and every mutation, each killed one first with its hint.
The specification digest, every byte of every source file, names the specification in the documents and keys the memos.
The program digest covers a program's text, start sort and variables, so editing a program reruns only that program.
`time_ms` is in no key: no stored value depends on it, so raising it to get past timeouts keeps every result and outcome.
Rebuilding kink starts a new outcome context. The `killers/` directory of earlier versions is no longer read and can be deleted.

### A larger example: IMP

[`examples/imp`](examples/imp) runs the loop on the K tutorial's IMP (`pl-tutorial/1_k/2_imp/lesson_4`):
a corpus of seven programs that covers every rule, 21 mutations (three of them correlated), and the results of the runs.
Its README also says what IMP's `strict` operators cost and why a run needs a small `time_ms` and a memory limit.

## SemanticInput, manifests, reports and replay

A baseline's `SemanticInput` v1 is exactly k-rust's compact `KRUST-PROVENANCE` v8 document of the loaded definition and its source table; its digest is the SHA-256 of those bytes.
`SemanticInput::read` accepts only the canonical encoding and rebuilds the baseline without the `.k` sources.
A sentence fingerprint is a domain-separated SHA-256 of the sentence without source positions, provenance receipts or term metadata.
Candidate selection pins every patch to the fingerprints of the sentences it addresses, and `apply` refuses a stale pin as `StalePrecondition`, before any edit and so before compilation.
A fingerprint is a version check, not an identity: a sentence is identified by its module and index in one baseline.

A campaign manifest (`kink-campaign-manifest` v6) records the k-rust revision, the provenance format, the solver profile, the compile and backend options (those of the campaign's runs, with `smt_resource_limit`, the first attempt's Z3 resource units: kink's runs are resource-bounded by default, kink-native `BACKEND_OPTIONS`), the budget, the schedule, the operator id, version and policy, the baseline and per-mutant digests (SemanticInput, metadata-free structure, compiled KORE), the validation outcome of each mutant, and digests of the tests and the observation.
A campaign report (`kink-campaign-report` v6) embeds the manifest and adds the origins, each mutant's canonical patch, the affected sentences with old and new fingerprints, a normalized structural diff, the per-test oracle sides (each pattern of a side as its compact KORE text, since v6), the claims and the summary.
Both are canonical JSON with no wall-clock value and no absolute path, so repeated runs give identical bytes.

`replay` takes a report, the baseline artifact and the caller's declaration, including the selection code.
It checks the schema, the manifest digest, the build environment and the artifact digest, rebuilds every mutant from its canonical patch and checks its digests, then reruns selection and the campaign.
It returns `Reproduced` only when the regenerated report is byte-identical to the input; anything else is a refusal or a divergence, never a verdict.
Replay assumes the same kink build and operator code, no time bound firing in either run, and k-rust's provenance round trip and compilation determinism.

## Premises on k-rust

kink's premises on the in-repo k-rust are stated in [`trust.md`](trust.md), with the k-rust commit at which the passages they cite are read; kink's drift pins (light-tier tests, "Gate") fail when a k-rust passage or source they rest on moves.

## Gate

The tests of the kink crates are in three tiers (`kink/.config/kink-tiers.toml`):

| tier | marked | runs | budget |
|---|---|---|---|
| light | an ordinary `#[test]` | every change; every `cargo test` and `cargo nextest run` of k-rust's workspace, so every k-rust push | 120 s wall, no test over 30 s in the tier run |
| kink | `#[ignore = "kink"]` inside a `kink_tier` module | a change to a kink crate, its test data or this gate | 600 s wall together with light |
| heavy | `#[ignore = "heavy"]` inside a `heavy` module | nightly, before an integration merge, when a work package closes | 3,600 s wall |

The light tier holds what a change outside kink can break: the protected kills, the replay rows, the k-rust drift pins, one end-to-end run per layer and the cheap contract tests.
The kink tier holds kink's own optimisation equivalences on sampled rows, the CLI and store tests and the slower review pins;
the heavy tier holds the whole-fixture sweeps and the full option matrices, each of which keeps a row in a faster tier.
A test that needs an outside checkout is `#[ignore = "external: ..."]` inside an `external` module, belongs to no tier,
and only records a skip without `KINK_WORKSPACE`.

A k-rust drift pin of a passage (kink-patch `trusted_claims_are_pinned`, kink-native `the_premise_k_rust_documents_is_pinned`, `the_passages_a1_rests_on_are_pinned` and `the_console_passage_the_run_list_rests_on_is_pinned`) locates the passage by an anchor and its opening text, not by line numbers (`testdata/k/passage.rs`): in a Markdown file the anchor is the heading of the section that holds it, in a source file the declaration of the item whose documentation or body holds it.
The pin is the SHA-256 of the passage's lines, so an edit elsewhere in the file moves no pin, while an edit of the passage, or a move out of its section, fails the test with a message naming what moved, until the passage is read again and re-pinned.
A missing or ambiguous anchor or opening is refused, never resolved by the first match.

`kink/scripts/kink-tier.py` runs a tier of the kink packages (`-p` each package of `kink/crates`) with cargo-nextest from the root of k-rust's workspace (profile `kink` of the root `.config/nextest.toml`, which holds kink's overrides),
checks the run against the tier's budget from nextest's JUnit report (`target/nextest/kink/junit.xml` under the workspace root, where nextest writes it even when `CARGO_TARGET_DIR` moves cargo's build output),
and lints the tier markings: an ignored test outside a tier module would run in no tier, and a kink override of `.config/nextest.toml` that matches no test would stop applying.
Budgets are judged on a host whose load average is under half its CPUs, and only reported on a busier one.

Every commit to a kink crate must pass the gate tier in both solver profiles. From the root of k-rust's checkout:

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
KRUST_GATE_Z3=system with-z3-static-5.3.3 kink/scripts/kink-tier.py lint
KRUST_GATE_Z3=system with-z3-static-5.3.3 kink/scripts/kink-tier.py run gate
kink/scripts/kink-tier.py clippy
kink/scripts/kink-tier.py lint --portable
kink/scripts/kink-tier.py run gate --portable
```

`kink-tier.py clippy` is the portable profile's Clippy: every kink package, and k-rust-backend and k-rust-fuzz, whose code compiled only without the backend's `z3` feature no Z3 build lints, with `--no-default-features --all-targets` and warnings denied.
The heavy gate adds `kink/scripts/kink-tier.py run heavy` in both profiles.
`scripts/run-gates.sh kink` and `scripts/run-gates.sh kink-heavy` run the two tier pairs, and `scripts/run-gates.sh no-z3-clippy` the portable Clippy, which a change to krust's sources or to k-rust-fuzz also owes (`scripts/gates.toml`).
`scripts/run-gates.sh kink-native-data` runs kink-native's `data` test in both profiles, which a change to the backend's observation catalogs or its `definedness.rs` owes, since its pins rest on them.
The tier script acquires Z3 as k-rust's gates do (k-rust `docs/testing.md`): by default its Z3 runs add k-rust's `z3-inference-gh-release`, which downloads the Z3 5.3.3 release at build time,
and `KRUST_GATE_Z3=system` links the Z3 the build environment provides instead, here the machine wrapper `with-z3-static-5.3.3`, which points the `z3-sys` build at a static Z3 5.3.3 library.
`--and EXPR` narrows a tier to the tests matching a nextest filterset, for example `--and 'package(kink-flow)'`, without judging the budget.
The Z3 profile runs every test of every kink package (`[z3]` of `kink/.config/kink-tiers.toml` says why no binary is skipped).
kink-flow's tests are profile-aware (merge packet M-1): its `z3` feature (default, forwarding to kink-native's) selects the Z3 column; a `no` that a complete exploration gives in the portable build is `unknown` under Z3. The tests of the outcome cache, the warm-path memos and the pattern cache run in both profiles, since the caches are on in both, and the Z3-only light test `kink-flow::outcomes both_caches_are_on_under_the_z3_profile` keeps the Z3 side of them in the light tier.
Under Z3 every solver query is resource-bounded, so a run order cannot move a status through a reused backend's cache; the order tests (`kink-flow::usability *_statuses_do_not_depend_on_the_order`) also check that both undecided-answer counts are reported and that no run of their fixtures takes one.
So the tier lint counts differ by profile, only by tests that exist in one profile: portable light 713, kink 613, heavy 135, external 7; Z3 light 718, kink 612, heavy 135, external 9 (three kink-tier tests whose subject is a stored or cached `no`, an answer the Z3 profile never gives, compile only in the portable build, and two, of a remainder that only a solver refutes and of the solver's units in the kill search, only under Z3; the light and external columns differ by `cfg(feature = "z3")` tests).
`cargo test --workspace` still runs the light tier, and `cargo test` of the kink packages with `-- --include-ignored` every tier.
Run the two profiles one after the other, never at the same time in one target directory:
each build replaces the other's `kink-corpus` and `kink-flow` executables, which the tests run and hash, under a running test.

The default build is the Z3 solver profile, as k-rust's is.
`kink-native` has a `z3` feature for the Z3 profile
(it enables k-rust `z3-inference`, which enables k-rust-backend `z3`), and `kink-campaign` and `kink-corpus` forward it as `z3`;
the three and `kink-flow` (which forwards it too) enable it by default, and `--no-default-features` on the kink packages is the portable (no-Z3) profile.
kink-native fails to compile when its `z3` feature and k-rust's `z3-inference` disagree (`src/execution.rs`), which a build reaches only by turning k-rust's Z3 on beside kink packages built without their `z3` feature (for example `--no-default-features --features k-rust/z3-inference`); every kink package that depends on kink-native enables `z3` by default.
`kink-campaign` requires its execution adapter's solver profile to match the build.
Their tests carry profile columns for outcomes that differ between no-Z3 and Z3.
A build that selects only kink packages with their default features takes k-rust's `z3-inference` alone, which links the Z3 the build environment provides (without `with-z3-static-5.3.3` or another provider it fails to link, `-lz3` missing);
a build that also selects k-rust with its default features (`cargo clippy --workspace`, `cargo nextest run --workspace`) takes k-rust's `z3-inference-gh-release`, which downloads the Z3 5.3.3 release into the build script's output directory once per target directory.

The dev and test profiles are k-rust's (the root `Cargo.toml`): the workspace at `opt-level = 1` with line tables only, dependencies at `opt-level = 3`;
debug assertions and overflow checks stay on for every package.
For a debugger session that shows local variables, use the `debugging` profile (`cargo test --profile debugging`).

A kink-tier test whose expected outcome comes from a deterministic bound (a work budget, `max_depth`, `max_breadth`, the fuzz's `max_work`) runs under `time_ms = 600000` (the tests' `NO_CLOCK_MS`) or the same bound as `ExecutionBudget::time`: nextest stops a test after ten minutes, so the clock decides no passing run.
A test whose purpose is the time limit gives the run it expects to time out no other bound.
A wall time is asserted only as a lower bound or compared in the serial `wall-clock` group.

## Retired tooling

The earlier official-K "G-track",
its TypeScript/Bun probes and the oracle were removed from the tree.
The local tag `archive/g-track-2026-08` marks the last commit that contains them.
