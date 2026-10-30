# Fuzzing test programs: `kink-flow fuzz` and `krust fuzz`

This guide is for an author, a person or an LLM agent, who has a K definition and a test program and wants to do one of three jobs:

- **Kill a survivor.** A mutation of the definition survives because no test program tells it apart from the definition. Find an input on which the two give different results.
- **Reach an uncovered rule.** No test program reaches some rule. Find an input whose run does.
- **Hit a pattern.** You want a program that gets into some situation (a division by zero about to run, a balance above a limit). Find an input whose run reaches a configuration matching a K pattern.

You do not hand the tool a blank page. You give it a program you already have, with some of its literals marked as *holes*, and the tool searches for hole values that do the job.
That program with its holes is called a *template*.
When the search succeeds, you get the instantiated program (the *witness*), which you add to your tests.

Two commands run these searches:

- `kink-flow fuzz` (crate `kink-flow`) works on a kink flow: a `FLOW.toml` with its programs, a `MUTATIONS.toml`, and a `TEMPLATES.toml` holding your templates. It checks every candidate with kink's own rules, has kink confirm the witness, and prints it as a `[[program]]` table to append to `FLOW.toml`. Use it whenever kink admits your definition.
- `krust fuzz` (crate `k-rust-fuzz`) works on compiled definitions and a campaign file. It runs on any definition `krust kcompile` compiles, including the ones kink does not admit (WebAssembly, KEVM), and it records a witness file you can replay.

The references for every option, field and reason are [kink-flow's README, section "Killing a survivor with `fuzz`"](../kink/crates/kink-flow/README.md#killing-a-survivor-with-fuzz) and [k-rust-fuzz's README](../crates/k-rust-fuzz/README.md).
This guide teaches the jobs and links there for details.

## What the tools do not do

- They do not write programs. Random or grammar-driven programs are nothing a person would write, and you already write the programs. The tool only chooses values for the holes you mark.
- They do not prove that no input exists. "No witness" means none was found within the budget. A mutation that keeps surviving may be equivalent to the definition, or your template may be unable to show the difference; the tool cannot tell which.
- They do not decide a mutation's status. `kink-flow run` decides it with kink's own oracle, on the program you append. The fuzz searches for a program that `run` will confirm.
- They do not change the definition or its claims.

## Before you start

Build `kink-flow` from the root of k-rust's checkout, in the portable profile recommended for kink's loop: `cargo build --release -p kink-flow --no-default-features` (kink's README, "Using kink-flow").
`krust` and `krust-fuzz` come as release archives, or from source (README, "Install and build"); `krust fuzz` runs the `krust-fuzz` built from the same sources.
Put the executables on your `PATH`.

The examples use two small flows over the IMP language of the K tutorial, kept in the repository:

- `kink/testdata/flow/fuzz/imp`: two programs (`sum`, `primes`), seven mutations of `imp.k` that no program kills, four templates, and a pattern.
- `kink/testdata/flow/fuzz/impu`: three programs that leave three rules of `imp.k` uncovered, and three templates.

Commands run from the repository root. `kink-flow run` and `kink-flow results` write a cache next to `FLOW.toml`, so copy a flow out of the repository before working in it.
Each example shows the command, then the part of its output that matters. Every command prints one JSON document; save it to a file and read it with any JSON viewer.

## Marking holes

A template is a program plus `[[template.hole]]` tables. Each hole names a literal of the program by a `find` text that occurs exactly once and the `literal` inside it, gives its sort, and optionally a range or a list of `choices`.
The hole keys are `krust fuzz`'s `[[hole]]` keys ([Hole declarations](../crates/k-rust-fuzz/README.md#hole-declarations)).
This is the `primes` program with four of its literals marked:

```toml [kink/testdata/flow/fuzz/imp/TEMPLATES.toml]
[[template]]
id = "primes-holes"
program = "primes"

  [[template.hole]]
  name = "M"
  sort = "Int"
  find = "m = 4;"
  literal = "4"
  range = { min = 0, max = 8 }

  [[template.hole]]
  name = "N"
  sort = "Int"
  find = "n = 2;"
  literal = "2"
  range = { min = 0, max = 8 }

  [[template.hole]]
  name = "I"
  sort = "Int"
  find = "i = 2;"
  literal = "2"
  range = { min = 0, max = 8 }

  [[template.hole]]
  name = "T"
  sort = "Int"
  find = "t = 1;"
  literal = "1"
  range = { min = 0, max = 3 }
```

`program = "primes"` takes the text of a `[[program]]` of `FLOW.toml`; `file = "templates/x.imp"` or `text = "..."` give a new program instead.

**Mark every data literal**, operands and initial values included, not only the ones you suspect.
In the trials behind this guide the killing value was usually in a hole the author would not have chosen: `i = 0` below, `t = 0` for another IMP mutation, the dividend `100` of a WebAssembly division.
Holes cost little when they do not matter: the first case runs the program as written (each hole at its literal, the *anchor*), and a witness is shrunk so that every hole it does not need ends at its least value.
They are not free: each one widens the space the search draws from, and a value of an extra hole can take the run off the path that reaches the edited rule (in `primes`, `m = 0` with `n = 2` as written skips the loop that holds the division).

Keep ranges small when the values have no meaning beyond their size (0 to 8 for a loop bound): when every hole has finitely many values and there are at most 4096 assignments, the campaign never repeats one, and once it has tried them all it says `Domain exhausted`.

Some limits of holes:

- A hole holds data, never program syntax. A sort in which programs are written (`AExp`, `Stmt`) is refused, and so is `Id`, since a name refers to a declaration; `allow-refused-sort = true` overrides the refusal for a value you know is data (the `sum-redeclare` template does it for an `Id`).
- Every value is printed into the program and read back. IMP's grammar has no negative literals (`-1` is the unary minus applied to `1`), so a negative value cannot be written at an `Int` hole; the campaign narrows such a hole to start at 0 and warns. Write the minus into the program (`w = -0;` in `straight.imp`) and keep the hole on the digits.
- kink compares a `String` value only when it is ASCII. Generated strings rarely are: `kink-flow fuzz` repairs a refused candidate by replacing its non-ASCII characters, and you can also give the hole ASCII `choices`.
- A value beyond 64 bits is written as a decimal string, for example a range bound `max = "115792089237316195423570985008687907853269984665640564039457584007913129639935"`.

## Kill a survivor

Copy the flow and run the mutation search, so that the fuzz can read which programs reach each mutation:

```sh
cp -r kink/testdata/flow/fuzz/imp /tmp/fuzz-imp
cd /tmp/fuzz-imp
kink-flow run FLOW.toml MUTATIONS.toml > run.json
```

```json
{
  "counts": { "killed": 0, "survived": 4, "unknown": 3 },
  "mutations": [
    { "id": "div-guard-dropped", "status": "survived", "reaching": ["primes"] }
  ]
}
```

`div-guard-dropped` deletes the guard `requires I2 =/=Int 0` of IMP's division rule, so that `I1 / 0` steps to `I1 /Int 0`, which is undefined, where the definition gets stuck.
`primes` reaches the rule, but it only ever divides by numbers from 2 up, so both definitions give the same result.
Fuzz the template built on it:

```sh
cd /tmp/fuzz-imp
kink-flow fuzz FLOW.toml TEMPLATES.toml --template primes-holes --kill div-guard-dropped --mutations MUTATIONS.toml --cases 50 > kill.json
```

```json
{
  "stopped": null,
  "program": { "id": "primes-holes-fz-b92f03bf", "confirmed": true, "premises": [] },
  "attempts": [
    {
      "candidate": {
        "case": "shrunk",
        "kill": "removed-end",
        "holes": [
          { "name": "M", "k-text": "0" },
          { "name": "N", "k-text": "0" },
          { "name": "I", "k-text": "0" },
          { "name": "T", "k-text": "0" }
        ]
      },
      "confirmation": { "confirmed": true, "status": "killed", "killer": "primes-holes-fz-b92f03bf" }
    }
  ],
  "action": "append the [[program]] fragment to FLOW.toml…"
}
```

The second case killed the mutant, and shrinking moved every hole to 0. The value that matters is `I = 0`: `q = n/i` then divides by zero.
The definition stops at `0 / 0` with no rule to apply, a final configuration; the mutant's step there is undefined, which is no final configuration. So the definition has an end the mutant lacks, a *removed end*. The other kind is an *added end*, one the mutant reaches and the definition cannot.
`confirmation` is kink's own `run`, made on the flow with this program as its only program: it killed the mutation.
`program.fragment` holds the `[[program]]` table to append (shown for the next example).

### When the template cannot show the difference

`add-becomes-sub` turns IMP's addition into a subtraction. It is `unknown`: both corpus programs reach the rule, but in each a loop counter moves by an addition (`n = n + -1;` in `sum`, `n = n+1;` in `primes`), which the mutant turns the other way, so the loop never ends and kink cannot compare the runs.
Fuzzing `sum` does not help:

```sh
cd /tmp/fuzz-imp
kink-flow fuzz FLOW.toml TEMPLATES.toml --template sum-holes --kill add-becomes-sub --mutations MUTATIONS.toml --cases 20 --max-work 2000 > sum.json
```

```json
{
  "stopped": "budget",
  "action": "…10 cases stopped at max-work 2000 on the mutant, where the baseline reached all its ends within 161 work at most: the mutant may not terminate on this program…",
  "attempts": [
    { "fuzz": { "totals": { "classes": { "baseline-incomplete": 5, "miss": 5, "work-bound": 10 } } } }
  ]
}
```

The statement in `action` says what went wrong: on 10 cases the mutant ran out of work where the definition had finished, and on 5 more the definition itself did not finish (those are `D = 0`, where `n = n + -0` never decreases, so the advice to raise `max-work` there cannot help).
Raising `--cases` or `--max-work` will not change this; the template has to change.
Write a program in which the edited rule's result goes straight to the end, without a loop:

```sh
cd /tmp/fuzz-imp
kink-flow fuzz FLOW.toml TEMPLATES.toml --template straight-holes --kill add-becomes-sub --mutations MUTATIONS.toml --cases 50 > straight.json
```

```json
{
  "stopped": null,
  "warnings": [{ "kind": "template-not-reaching" }],
  "program": {
    "id": "straight-holes-fz-602cd8b6",
    "confirmed": true,
    "fragment": "[[program]]\nid = \"straight-holes-fz-602cd8b6\"\ntext = \"\"\"\nint x, y, z, w;\nx = 5;\ny = 1;\nz = x + y;\nw = -0;\n\"\"\"\n"
  },
  "attempts": [
    {
      "candidate": {
        "kill": "added-end",
        "holes": [{ "name": "Y", "k-text": "1" }, { "name": "W", "k-text": "0" }]
      }
    }
  ]
}
```

`template-not-reaching` says that this program is not among the ones the last `run` found reaching the rule. That is expected for a new program, and harmless.

### Turning the witness into a test

Append the fragment to `FLOW.toml` and run the mutation again:

```sh
cd /tmp/fuzz-imp
cat >> FLOW.toml <<'EOF'

[[program]]
id = "straight-holes-fz-602cd8b6"
text = """
int x, y, z, w;
x = 5;
y = 1;
z = x + y;
w = -0;
"""
EOF
kink-flow run FLOW.toml MUTATIONS.toml --only add-becomes-sub > run2.json
```

```json
{
  "counts": { "killed": 1 },
  "mutations": [
    { "id": "add-becomes-sub", "status": "killed", "killer": "straight-holes-fz-602cd8b6" }
  ]
}
```

`program.file` suggests a file name if you prefer to write the text to a file and give `file = ...` instead.
When the document lists `premises` (below, [Premises](#premises-findings-you-assume)), add each to `[spec] assume_joined` first.

### Equivalent mutants

`add-commuted` swaps the operands of `+Int`, which changes nothing: no input kills it, and the fuzz ends `budget` however long it runs.
The tool cannot tell an equivalent mutant from a template that cannot show the difference. Read the edited rule: when every input that reaches it gives the same result, say so and drop the mutation.

## Reach an uncovered rule

`kink-flow results` lists every rule with the programs that reach it:

```sh
cp -r kink/testdata/flow/fuzz/impu /tmp/fuzz-impu
cd /tmp/fuzz-impu
kink-flow results FLOW.toml > results.json
```

```json
{
  "summary": { "rules": 17, "covered": 14, "uncovered": 3 },
  "rules": [
    { "file": "imp.k", "start_line": 47, "status": "uncovered" },
    { "file": "imp.k", "start_line": 50, "status": "uncovered" },
    { "file": "imp.k", "start_line": 52, "status": "uncovered" }
  ]
}
```

Name the rule by `FILE:LINE`, as `results` prints it (a label works too, but these rules have none):

```sh
cd /tmp/fuzz-impu
kink-flow fuzz FLOW.toml TEMPLATES.toml --template clamp-holes --reach imp.k:47 --cases 100 > reach47.json
```

```json
{
  "stopped": null,
  "job": { "kind": "reach", "rule": { "file": "imp.k", "start_line": 47, "mode": "condition-reached" } },
  "program": { "id": "clamp-holes-fz-0b8148cc", "confirmed": true },
  "attempts": [
    {
      "candidate": { "holes": [{ "name": "X", "k-text": "0" }, { "name": "LO", "k-text": "1" }] },
      "confirmation": { "confirmed": true, "status": "reached", "reason": "listed" }
    }
  ]
}
```

Rule 47 is `- I1 => 0 -Int I1`. `clamp` writes `r = -1;` only when `x < lo`, which its literals never made true; `X = 0, LO = 1` does.
The confirmation is kink's `results` on the fragment: the program is comparable and listed in the rule's `reached_by`.
By default the job asks for the rule to be reached (its condition tried, `condition-reached`, as `reached_by` counts); `--fired` asks for some path to take the rule's step (`covered`: a step built a successor of the rule that denotes a configuration, as `fired_by` counts; a step whose result was empty, rolled back or undefined, counts for neither).

Rule 50 is `! T => notBool T`. No hole value of `clamp` reaches it, since `clamp` has no `!`:

```sh
cd /tmp/fuzz-impu
kink-flow fuzz FLOW.toml TEMPLATES.toml --template clamp-holes --reach imp.k:50 --cases 100 > reach50.json
```

```json
{
  "stopped": "budget",
  "attempts": [{ "fuzz": { "totals": { "classes": { "miss": 100 } } } }]
}
```

The statement suggests more cases or more holes, but the template is what fails here. A three-line program with a `!` reaches the rule on its first case:

```text [kink/testdata/flow/fuzz/impu/templates/bang.imp]
// Flag x when it is not small.
int x, r;
x = 5;
if (!(x <= 3)) { r = 1; } else { r = 0; }
```

```sh
cd /tmp/fuzz-impu
kink-flow fuzz FLOW.toml TEMPLATES.toml --template bang-holes --reach imp.k:50 --cases 100 > reach50b.json
```

```json
{
  "stopped": null,
  "program": { "id": "bang-holes-fz-3feceba6", "confirmed": true },
  "attempts": [{ "fuzz": { "totals": { "cases": 1 } } }]
}
```

kink counts a program as reaching a rule only when its run on every path ends in values kink can compare, so the witness must end naturally, on every path, in data.
Only rewrite rules can be targets: a function's equation is refused before any case (`equation-target`), although `results` lists it; write a program that calls the function and target a rewrite rule that uses its result.
Which rules coverage is meant to cover, and which reach targets are not built yet, are stated in [kink's README, section "What coverage covers"](../kink/README.md#what-coverage-covers): an `uncovered` simplification, `symbolic` or ceil equation is out of scope and needs no witness.

## Hit a pattern

A pattern is written in `PATTERNS.toml` as for `kink-flow query`:

```toml [kink/testdata/flow/fuzz/imp/PATTERNS.toml]
[[pattern]]
id = "divzero"
pattern = "<k> _:Int / 0 ~> _ </k>"
```

```sh
cd /tmp/fuzz-imp
kink-flow fuzz FLOW.toml TEMPLATES.toml --template primes-holes --pattern divzero --patterns PATTERNS.toml --cases 50 > divzero.json
```

```json
{
  "stopped": null,
  "job": { "kind": "pattern" },
  "program": { "id": "primes-holes-fz-b92f03bf", "confirmed": true },
  "attempts": [
    { "confirmation": { "confirmed": true, "answer": "hit", "status": "confirmed" } }
  ]
}
```

The pattern is matched against every configuration the run reaches, on every path, not only at the end, and kink's `query` with this program claimed confirms the hit.
A configuration reached on a real path is a hit even if the program later loops or is cut by the work bound: what follows cannot unmake it.
An invalid pattern is refused before any case (`invalid-pattern`), with k-rust's parse error.

## Budgets and options

`kink-flow fuzz` takes `--cases N` (1000 by default) or `--work W`, `--seed S` (0 by default) and `--max-work N`, the work bound of each run (100000 by default); each run is also bounded by the flow's `[budget] max_depth` and `time_ms`.
The same inputs and seed give the same document, so a small budget and a fixed seed make a job cheap to repeat; the examples above take a few seconds each.
The exceptions are clocks and the stack: a case that a step's time limit (the flow's `time_ms`), a solver `unknown` or a stop for lack of stack decided is outside the determinism contract, counted in the fuzz report's `totals.outside-determinism`, and since every later case depends on the cases before it, a re-run may differ from the first such case on (`totals.first-outside-determinism`, which also counts a candidate whose confirmation the clock stopped and, with the solve proposer, the case proposed after a solve run the clock or the stack stopped; the statement in `action` says so). `--time-limit-ms` and kink's confirmation, which runs under the flow's `time_ms`, are clocks too.
`--one-path` follows one path of the mutant instead of all; `--time-limit-ms T` stops the campaign after `T` ms; `--no-confirm` skips kink's confirmation (the witness then has `confirmed: false`); `--no-filter` turns off kink's rules inside the campaign; `--assume-joined NAME` adds a premise for this command.

## Choosing a template

The template decides more than the search does.
In trials on IMP, SIMPLE, WebAssembly and KEVM, every mutation that was not equivalent, on a template whose run reached the edited rule and ended on both definitions, was killed within 1 to 25 cases of blind sampling. Every miss came from the template:

- **A loop the mutant never leaves** (`add-becomes-sub` above): the definition finishes and the mutant runs out of work. The statement says "the mutant may not terminate on this program".
- **A masking expression.** `x < y && !(x == y)` gives the same result whether `<` means `<` or `<=`. Write one comparison or connective per line.
- **A discarded value.** `++i;` as a statement throws away the value a mutation of `++` changes; `var j = ++i;` keeps it.
- **A fixed operand.** Truncating and Euclidean division agree when the dividend is a positive constant; mark the dividend as a hole too.
- **Absent syntax.** No value can add a `!` to a program that has none (rule 50 above).
- **A second event that never happens.** A mutant that keeps an exception handler too long shows only if the program throws twice.

So when a survivor survives a template that reaches its rule, read the edited rule and write a short program, three to eight lines, in which its result flows straight to the output. Do not just raise `--cases`.
Start from the programs the last `run` lists in the mutation's `reaching` (the document suggests templates built on them, `template.last_run.suggested_templates`), and avoid a template whose program kink cannot compare (`unusable-template`).

## Reading the document

`kink-flow fuzz` prints one document (version 4). The fields to read first:

- `stopped`: `null` when there is a witness; otherwise why not (table below).
- `action`: the next step, in words. For a search that found nothing it quotes the campaign's statement.
- `warnings`: `{kind, detail}` entries (list below).
- `program`: the witness as a `[[program]]` table (`fragment`), its `id`, a suggested `file`, `confirmed`, and the `premises` it rests on.
- `attempts[0]`: `candidate` (the hole values, the program, the kind of kill), `confirmation` (kink's verdict) and `fuzz`, the full k-rust-fuzz report, with its `totals` (case classes, reasons) and `outcome`.
- `job`: what was run (`kind`, the mutation, rule or pattern, `path_mode`, the witness filter's identity), or why it was refused (`job.refusal` with `stage`, `reason` and `detail`).
- `template.last_run`: what the last `run` said about this template's program and the mutation.

| `stopped` | Meaning | What to do | Exit |
| --- | --- | --- | --- |
| `null` | A witness, confirmed by kink unless `--no-confirm`. | Append `program.fragment`. | 0 |
| `budget` | No witness within the budget. Not a proof of anything. | Read the statement in `action` (below). | 0 |
| `domain-exhausted` | No witness, and every assignment of the holes ran (each hole has finitely many values), so more cases cannot help. | Mark more literals as holes, widen their ranges, or write another template. | 0 |
| `client-refused` | Candidates were found, and kink's rules refused every one of them inside the campaign. | Read the fuzz report's `client-refusals` for kink's reason and remedy; change the template or the hole ranges. | 0 |
| `unconfirmed` | A candidate passed the campaign, and kink's confirmation refused it. | Read `attempts[0].confirmation.cause`; try another seed, template or range. | 0 |
| `assembly-mismatch` | kink assembles the instantiated program to another initial configuration than the campaign ran. | Report it with the document. | 0 |
| `not-comparable` | The definition has findings you have not named, so no end of it can be compared. | See [Premises](#premises-findings-you-assume). | 1 |
| `equivalent` | The mutant compiles to the same definition. | Drop the mutation. | 0 |
| `rejected-out` | Too many hole values were refused (they do not read back, or violate their sort). | Fix the holes. | 0 |
| `time-limit` | `--time-limit-ms` stopped the campaign. | Give it more time or fewer cases. | 0 |
| `aborted` | The campaign could not go on (a solver that does not start, backends that do not rebuild after a crash). | Read `action`. | 1 |
| `refused` | The job was refused before any case. | Read `job.refusal`. | 1 |

The exit status is 0 when the job reached a verdict (a witness, none within the budget, or candidates kink refused), 1 when an input, the template or the job is refused, the definition is not comparable or the campaign aborted, and 2 on a usage error (an unknown template, mutation or pattern id included). `kink-flow --version` prints its version and k-rust's build and exits 0.

**The statement of a search that found nothing** lists why cases could not decide anything, largest first, with a remedy:

- `Domain exhausted`: every assignment of the holes ran. This template cannot do it.
- "the mutant may not terminate on this program": change the program, not the bounds.
- `baseline-incomplete` with `work-bound`: the definition itself did not finish. Raise `--max-work` only if the program terminates for those values.
- `not-ceil-free` naming a function: an end holds an application of that partial function that is not shown to be defined; avoid the construct.
- `implementation-chosen-value (hook MAP.keys_list [order] …)`: the run read a value k-rust chose where the definition leaves it open (map order, here); the hook is named. Choose values or a program whose run does not read it.
- `implementation-chosen-value (hook <64 hex digits> [fresh-association] …)`: the run applied a rule with two or more `!` variables, and which of them gets which fresh value is the compiler's choice (or a rule that sets `<generatedCounter>` in a form k-rust cannot read as an advance by zero or one, which it marks too); the hook is the rule's `UNIQUE_ID`. Choose values or a program whose run does not apply that rule.
- `client-refused`: kink's rules refused the hit; see `client-refusals`.

The reasons are counted in the fuzz report's `totals.unsupported-reasons` and `totals.baseline-incomplete-reasons`, and the hooks behind them in `totals.unsupported-hooks` and `totals.baseline-incomplete-hooks` ([Why a case is unsupported](../crates/k-rust-fuzz/README.md#why-a-case-is-unsupported)).

**Warnings** are information, not refusals:

- `template-not-reaching`, `no-reaching-program`: the last `run` did not see this template's program reach the edited rule, or saw no program reach it. Expected for a new program.
- `unusable-template`: the template's program is not comparable in the last `run`, or kink refuses its input. Choose another.
- `already-killed`, `stale-run-document`: the last `run` killed the mutation already, or was made for another specification.
- `client-refused`: kink's rules refused some candidates, counted per cause.
- `crash`: k-rust or k-rust-fuzz failed on a case (a defect to report; the case kills nothing). The fuzz report's `crashes` holds the case.
- `witness-not-terminating`: the pattern witness's run of every path was cut by `--max-work`, the depth bound or a clock. It reaches the pattern, but as a test it may never end, so every `run` and `results` runs it to the budget. Prefer hole values or a template whose run ends.
- `time-limit-scope`: `--time-limit-ms` bounds the campaign, not the setup before it.

## What kink refuses, and why

kink kills a mutation only by comparing final configurations as values that mean the same thing in every model of the definition. The fuzz refuses a candidate that `run` could not use, at three points.

Final configurations are compared without the content of the `<generatedCounter>` cell, which only counts the fresh values (`!X`) minted so far: a mutant that only mints more values is not killed, while one whose fresh values reach a cell of the configuration is. A run through a rule with two or more `!` variables rests on how the compiler numbered them, so it is no evidence (`implementation-chosen-value`, class `fresh-association`).

**Before any case** (exit 1; `stopped` is `refused` or `not-comparable`):

- The specification itself, as `kink-flow check` reports it: one whose declarations kink's census flags (stage `declaration-census`, reason `vi-t13`), and one the representation gate refuses (stage `representation`: a token-creating hook into a builtin or hooked sort, `G-T`; a String token with two readings, `G-S`; a non-canonical literal of a sort hooked `INT.Int` under another name, `G-I`). Float and MInt literals of a hooked sort are admitted: k-rust stores each such value as the canonical text of its value, so ends are compared by value. KEVM's driver is refused at `declaration-census`; use `krust fuzz` for it (below).
- A mutation `run` refuses: `invalid-mutation`, `equivalent`, `invalid` (for example a mutant whose equations give one function two values, `inconsistent-mutant`), or claims it cannot remove.
- A definition exclusion on either side (`job.refusal.stage` is `exclusions`): a construct whose result k-rust chooses or reads in one of several ways K allows (an implementation-chosen hook, a short-circuit reading, an equality condition, a stack stop in the load). The exclusion names it.
- A mutant that parses the template differently (`mutant-assembly-differs`), for example after an edit of a `[macro]` rule.
- A template whose own input kink excludes (`initial-state-excluded`).
- Findings no name assumes (`not-comparable`, below).
- For a reach, a rule that is no rewrite rule (`equation-target`, `no-coverage-signal`) or that names nothing; for a pattern, an invalid pattern.

**Inside the campaign.** Unless `--no-filter` is given, every candidate is judged by kink's own rules before it is offered: the initial state's exclusions, each side's undefined steps, kink's test of every end as a value (TV-01), and, for a removed end, whether the mutant's run fits kink's work budget (`[budget] work_factor`).
A refused candidate is no witness, and the search goes on. Each cause is counted (the warning `client-refused`) and its first case kept in the fuzz report's `client-refusals`, with kink's detail and remedy.
A candidate refused only because a `String` end is not ASCII is repaired: its non-ASCII characters are replaced by ASCII letters or digits, keeping lengths and distinctness, and the witness records the refused case it came from (`repaired-from`). A value kink refuses whatever it holds (`Bytes`, `Float`) cannot be repaired.
With `--no-filter` such candidates reach the confirmation, which refuses them, and the job stops `unconfirmed`.

**At confirmation** (`stopped: unconfirmed`). Some of kink's judgement is not repeated inside the campaign: the work budget for an added end, kink's own clocks and stack, leaf differences that come from kink's run options (`max_depth`), which match a query finds first, and per-candidate assembly. A refused candidate is never offered.

## Premises: findings you assume

To compare two ends as different values, the definition must not identify them, and an equation pair that gives one input two results identifies those results, and through them possibly other terms.
So before any case, each definition's full critical-pair check runs; a finding it reports makes no end of that definition comparable, and the job is `not-comparable`, listing every finding with its `name` and whether it is **genuine** (the check found an input with two results) or undecided.

You can name a finding to read the definition as if it did not hold: `--assume-joined NAME` for one command, `[spec] assume_joined` in `FLOW.toml` for every command. Every verdict then holds for that reading only. A genuine finding is a premise known to be false; the fragment's `premises` list it, flagged.
Fix a genuine finding in the definition when you can. A pattern job reads no compared end and takes no name.

## `krust fuzz` on its own

Use `krust fuzz` when kink does not admit the definition, when you have a mutant as a K file rather than a `MUTATIONS.toml` edit, or when you want a property checked without kink.
It needs both definitions compiled with `krust kcompile`, the program, and a campaign file holding the holes (the same keys as a template's) and, optionally, the target and options ([Command line](../crates/k-rust-fuzz/README.md#command-line)).
By default it follows one path of each run (k-rust's first applicable rule at each step; for a kill, the mutant's, while the definition always runs on all paths); `--all-paths` explores every path, as `kink-flow fuzz` does.

The fixture `crates/k-rust-fuzz/tests/data/imp-diff` holds the same IMP and the `div-guard-dropped` mutant as a K file:

```sh
cp -r crates/k-rust-fuzz/tests/data/imp-diff /tmp/fuzz-krust
cd /tmp/fuzz-krust
krust kcompile imp.k -m IMP -o imp-kompiled
krust kcompile imp-div-guard-dropped.k -m IMP -o mutant-kompiled
cat > primes.toml <<'EOF'
definition = "imp-kompiled"
program = "primes.imp"
seed = 0
cases = 100

[options]
max-work = 20000

[[hole]]
name = "M"
sort = "Int"
find = "m = 4;"
literal = "4"
range = { min = 0, max = 8 }

[[hole]]
name = "N"
sort = "Int"
find = "n = 2;"
literal = "2"
range = { min = 0, max = 8 }

[[hole]]
name = "I"
sort = "Int"
find = "i = 2;"
literal = "2"
range = { min = 0, max = 8 }

[[hole]]
name = "T"
sort = "Int"
find = "t = 1;"
literal = "1"
range = { min = 0, max = 3 }
EOF
krust fuzz --campaign primes.toml --mutant mutant-kompiled --witness witness.json
```

```text
witness found
cases: 2, work: 3254 (hit 1, miss 1)
shrunk witness:
  M = 0
  N = 0
  I = 0
  T = 0
kill: removed end (the baseline reaches an end the mutant cannot)
```

The summary goes on with the program, each side's ends as K text, and a `krust krun` line per side that re-runs it. `--json` prints the report instead, and `--report FILE` writes it.
The witness file records the campaign as resolved and the report. Replay checks that the definitions and program are the ones recorded, then re-runs the first and the shrunk witness:

```sh
cd /tmp/fuzz-krust
krust fuzz --replay witness.json
```

```text
first witness: reproduced
shrunk witness: reproduced
```

Replay compares the whole witness, the program, the krun lines and each side's work included, each crash's values, program and krun line, and the report's fields fixed before any case (the definition findings, the sort overrides, the normal end, the load records and the warnings the campaign starts with), so an edit of any of them does not reproduce.
It cannot certify what the campaign's search recorded, since it runs only the recorded cases: the totals, the statement, the other warnings, the incidental findings, each crash's phase, case, count, re-runs and shrunk values, a repaired witness's `repaired-from`, the witness filter's identity and the proposers' parameters. Its last line says so.
The identity names the k-rust-fuzz build by its sources, a comment included, so a witness kept across commits replays only with `--force` (status 3 when its cases reproduce), or is found again.

`krust fuzz` exits with 0 for a witness (with `--replay`, when every case reproduced), 1 for none: no witness within the budget, `Domain exhausted`, `equivalent`, `not comparable`, the rejection cap or an aborted campaign (with `--replay`, a case that did not reproduce), 2 on an error (a usage error, a refused campaign or replay, an unreadable input or environment variable), and 3 for a replay forced past identity mismatches (`--force`) whose cases reproduced, which confirms nothing the file claims.
The two commands agree where their meanings agree: 0 for a witness, 1 for `not-comparable` and an aborted campaign, 2 for a usage error. `kink-flow fuzz` follows kink's convention, where 0 means the job reached a verdict, so no witness is 0 there and 1 here, and a refused job is 1 there and 2 here.

The same campaign file serves the other jobs; flags override it. A pattern matched at any state:

```sh
cd /tmp/fuzz-krust
krust fuzz --campaign primes.toml --pattern '<k> _:Int / 0 ~> _ </k>' --at any-state
```

```text
witness found
cases: 2, work: 1261 (hit 1, miss 1)
```

A rule named by its position, as kink's `results` prints it:

```sh
cd /tmp/fuzz-krust
krust fuzz --campaign primes.toml --reach-rule imp.k:52 --run-to-completion
```

```text
witness found
target rule: imp.k:52 unique id aad2bcfd509bccd60d7e25b0eec1c400a385c8a8ddd49c668f15f83eeac44567
```

A rule witness becomes a test only when its program ends cleanly: `--run-to-completion` asks for a natural end, and by default also that the end be data; `--comparable` asks for every path to end in data, as kink requires.

### Not comparable, and naming findings

`crates/k-rust-fuzz/tests/data/r3-plainq` is a definition with the equations `q(_) => a` and `q(_) => bb` of a total function `q`, and a mutant that stores `bb` where the definition stores `a`:

```sh
cp -r crates/k-rust-fuzz/tests/data/r3-plainq /tmp/fuzz-pq
cd /tmp/fuzz-pq
krust kcompile b.k -m PQ -o b-kompiled
krust kcompile m.k -m PQ -o m-kompiled
cat > go.toml <<'EOF'
definition = "b-kompiled"
mutant = "m-kompiled"
program = "go.pgm"
cases = 4

[[hole]]
name = "N"
sort = "Int"
literal = "3"
EOF
krust fuzz --campaign go.toml # exit 1
```

```text
not comparable: no case can be judged
baseline critical-pair findings: 1 genuine, 0 undecided
  [genuine] b.k:16:3 and b.k:17:3
    name: b.k:16:3,b.k:17:3@root
    instance: at q ( 0 ) both equations apply; its two normal forms: a and bb
```

`q(0)` equals both `a` and `bb`, so in every model of the definition `a` and `bb` are equal, and the mutant's end `bb` is no different from the definition's `a`. The refusal is right.
Naming the finding on each side makes the campaign read both definitions as if the pair joined:

```sh
cd /tmp/fuzz-pq
krust fuzz --campaign go.toml --assume-joined 'b.k:16:3,b.k:17:3@root' --assume-joined 'm.k:16:3,m.k:17:3@root'
```

```text
witness found
kill: added end (the mutant reaches an end the baseline cannot)
warning: assume-joined: the verdicts of this campaign hold for the definitions read as if the findings `b.k:16:3,b.k:17:3@root`, `m.k:16:3,m.k:17:3@root` did not hold (each pair joined, each equation agreeing with its hook or applied as written, each precondition met), not for the definitions as written
```

This kill holds for that reading only; since the pair is genuine, the reading is false of the definition as written. On WebAssembly's `test.md` the check reports two genuine `getOrDefault` pairs (a lookup at index -1 has two results, although no WebAssembly program looks up a negative index) and two undecided ones. A kill under those names holds for the definition read as if they joined: whether that reading serves your purpose is your decision, and the report states it.

### Definitions kink does not admit

On WebAssembly and KEVM, compile the definition and the mutant with `krust kcompile` and write a campaign file over a program of the language.

- A pattern target needs no premise and works as written.
- A kill, or a rule target with `comparable`, stops `not-comparable` until you name the findings listed, and then holds for that reading only.
- Mark every literal, operands included: the WebAssembly kill of a mutant that divides with `divInt` in place of truncating division needed a hole on the dividend, since the two agree on a positive dividend.
- KEVM's test driver ends naturally only when the test's `post` block matches the final state; otherwise the run gets stuck at its `check`. A test whose expected storage is `0x2a` and whose code stores `CHAINID` is hit only at `CHAINID = 42`; the other cases are `stuck`, and the summary reports the first as an incidental stuck case.
- A case whose run reads a value k-rust chooses is `unsupported` with `implementation-chosen-value`, and the summary names the hook: a KEVM test storing several slots reads `SET.set2list [order]`.

## Checklist for an agent

1. Run `kink-flow run` (kill) or `kink-flow results` (reach) first, and pick the job from the document: a `survived` or `unknown` mutation, or an `uncovered` rule by `FILE:LINE`.
2. Template: start from a program in the mutation's `reaching` (or one near the rule). Mark every data literal, with small ranges.
3. Run with a small budget and a fixed seed: `--cases 50` to `300`, `--max-work 20000`, default `--seed 0`.
4. `stopped: null`: append `program.fragment` (and any `premises` to `[spec] assume_joined`), run `kink-flow run --only ID` or `results`, and check the status.
5. `stopped: budget` or `domain-exhausted`: read `action`. `Domain exhausted`, "may not terminate", or 100 % `miss` with no progress means: write a new three-to-eight-line program in which the edited rule's result reaches the end directly. Then consider whether the mutation is equivalent.
6. `client-refused` or `unconfirmed`: read the cause; change the template or ranges (ASCII strings), or try another seed.
7. `not-comparable`: do not name findings by reflex. Name one only if you accept it as a premise, and say so beside the test.
8. Never claim a mutation is equivalent, or a rule unreachable, because the fuzz found nothing; say what you tried.

## How this guide is checked

Every command in this guide runs as written in two tests: `kink/crates/kink-flow/tests/guide.rs` runs the `kink-flow` blocks and `crates/k-rust-fuzz/tests/cli.rs` the `krust` blocks, each in a scratch directory standing for `/tmp`.
Each JSON block after a command must be contained in the document the command printed (strings with `…` match by the text they show), each `text` block's lines must appear in its output in order, and each block titled with a file must quote lines of that file.
