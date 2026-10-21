# k-rust-fuzz

`k-rust-fuzz` crafts concrete input values for a given program under a given K specification, so that an execution of that program reaches a stated target: a named rule, a pattern, a client observer, or a difference between a baseline and a mutant definition.
It is built to steer values with the specification's state space (its rules, guards, coverage and path conditions), and it never generates programs.
Generating whole programs is out of scope: random or grammar-driven program generation produces nothing a human would write, and the author (a person or an LLM) already writes the program.
Crafting inputs that reach a target is in scope: the author marks the program's input holes beside the unmodified program (typed spans of data, such as an `Int` literal), names the target, and the crate chooses hole values, runs the program with k-rust, and reports.
The report holds either a witness that a concrete re-run confirmed (the hole values, the initial and final configurations, the outcome), or a bounded "no witness found" with the budget, the cases run, the coverage reached and the outcome counts, which is never a proof that no witness exists.

The library builds without k-rust's `cli` and Z3 features; the `z3` feature enables the solver-backed proposer.
The design is in the fz26 programme's `ARCHITECTURE.md`; the rustdoc of each item cites its section.

## Outcome classes

Every case receives exactly one `OutcomeClass` (ARCHITECTURE 5.3).

| Class | Meaning |
|---|---|
| `hit` | a clean leaf reaches the target and confirmation agrees; reported as a property failure for a negated property |
| `miss` | the run ended naturally on every leaf without reaching the target |
| `stuck` | a clean leaf is an abnormal stop (stuck, but not a natural end), and no leaf reaches the target |
| `reached-unfinished` | under `run-to-completion`, the target was reached on a leaf that is clean except for its halt, which is neither a natural end nor an unsupported halt (an abnormal stop, an undefined step, a bound, a timeout or a cancellation); and no leaf is `unsupported` |
| `depth-bound` | a `depth-bound` or `breadth-bound` halt |
| `work-bound` | a `work-bound` halt; deterministic, distinct from timeouts |
| `timeout` | a `timeout` or `cancelled` halt, a cancellation or step deadline that ended the run as an `Err`, or the per-case safety limit |
| `undefined` | a `trivial` halt: an undefined step |
| `unsupported` | `unsupported-hook`, `simplification-error`, `indeterminate`, `vacuous` after depth 0, an `Err` result other than a clock stop or a refused state, a leaf unclean for a reason other than its halt, or a target-reaching leaf that is not clean (and not `reached-unfinished`) |
| `rejected` | a hole value violates its sort or constraints, does not round-trip through the program's syntax, or the backend refuses the initial state (`vacuous` at depth 0, or an invalid state) |
| `baseline-incomplete` | differential only: the baseline's set of ends is incomplete (ARCHITECTURE 4.3) |

When a result has several leaves, the case takes the first of these that some leaf has:
`hit`, `unsupported`, `reached-unfinished`, `timeout`, `work-bound`, `depth-bound`, `undefined`, `stuck`, `miss`.
`reached-unfinished` applies only when no leaf is `unsupported`.
A leaf that is unclean for a reason other than its halt (an implementation-chosen value, a contradicted claim, remaining constraints, a term that is not ceil-free, a stack stop, an undecided solver answer, and so on) is `unsupported` whether or not it reaches the target, because it may hide a reaching state, so `miss` or `stuck` would be unsound.
`rejected` is decided before execution, and `baseline-incomplete` by the differential judge before the mutant's leaves are looked at; neither is chosen by precedence.
A stuck, truncated, timed-out, undefined or unsupported run is never reported as a pass.

## Hole declarations

A hole replaces a span of the unmodified program, addressed by `program`, an optional `line`, `find` (a text that occurs exactly once in the addressed line or program) and `literal` (the hole's literal, which occurs exactly once in `find`).
The text at the span is the hole's anchor value, the first value the explicit proposer tries.
A configuration variable (`$NAME`) can also be a hole, addressed by its name; so can a free variable of a KORE initial pattern, in the library API.
The declaration format of ARCHITECTURE 2.2, with the program `transfer.imp` unchanged:

```toml
[[hole]]
name = "AMOUNT"
sort = "Int"
program = "transfer.imp"
line = 4
find = "amount = 250;"
literal = "250"
range = { min = 0, max = 1000000 }
```

In the library, the same hole is a `HoleDecl` with a `HoleLocation::Span(SpanAddress { .. })` and its `Constraints`.

A hole is data, and `Campaign::new` enforces it (ARCHITECTURE 2.4).
It refuses a hole whose sort is `K`, `KItem`, a cell sort, or a user sort in the closure of the program start sort's productions (a sort in which programs are written, such as `AExp` or `Stmt` in IMP).
It accepts builtin and hooked sorts that have a generator (`Int`, `Bool`, `String`, `Bytes`, `MInt`), collections with declared element sorts, and user sorts outside that closure, such as transactions, events or records declared in semantic modules.
The rule applies to every sort a value of the hole's sort may contain: collection element sorts and the argument sorts of its constructors, transitively, so `List<Stmt>`, `List<K>` and a record holding an `AExp` are refused, and `KResult` and other K-internal sorts count as computation.
When the start sort is `K` or `KItem`, the closure is every non-hooked sort of the syntax module.
User token sorts such as `Id` are refused, because an identifier names a declaration of the program.
`allow_refused_sort` overrides a refusal, and the report records the override.

## Library usage

The caller compiles the definition (`CompiledDefinition::from_artifacts` takes an in-process compilation), builds a `CampaignSpec` (the definitions, the program, the holes, the target, the case options, the proposers, the seed), and runs it:

```rust
use k_rust_fuzz::{Budget, Campaign, CampaignError, CampaignSpec, FuzzReport};

fn fuzz(spec: CampaignSpec) -> Result<FuzzReport, CampaignError> {
    let mut campaign = Campaign::new(spec)?;
    Ok(campaign.run(Budget::Cases(10_000), None))
}
```

`Campaign::new` validates the spec: a mutant is given exactly for a differential target, each definition's backend is built on its route, and the holes, their generators and the target are resolved.
It assembles and round-trip-checks the program with its anchor values, and returns a `CampaignError` for every refusal (a `find` or `literal` that does not occur exactly once, overlapping spans, an anchor that does not parse back, a refused hole sort, an unknown, ambiguous or refused target, and so on).

`Campaign::run` runs cases on the calling thread until the budget (`Budget::Cases` or `Budget::Work`) is spent, a witness is confirmed and shrunk, the rejection cap is reached, or the `CancellationToken` is cancelled.
The explicit proposer tries the anchors first, then the author's assignments; the other proposers are mixed by a deterministic schedule seeded from the campaign seed.
This build provides blind generation (`ProposerKind::Blind`) and the dictionary (`ProposerKind::Dictionary`): guard harvesting, which draws each hole, with probability 1/2, from the literals of the guards and left-hand sides of the target and of the rules at most two rule-graph edges before it, of the equations their guards call, and of the higher-priority rules an `owise` rule competes with, plus or minus 1 to 3 and negated (ARCHITECTURE 8.3; the rustdoc of `proposers::dictionary`). `Campaign::new` refuses a proposer the build does not provide.
A candidate hit becomes a witness only after a confirmation on a fresh backend agrees.
Each run starts from fresh proposer state, so a second run reports exactly what a fresh campaign with the same spec and budget reports.
The `FuzzReport` (`to_canonical_json` gives its canonical bytes) is a function of the definitions, program, holes, target, options, budget, seed, the k-rust revision and `ENGINE_VERSION`.
