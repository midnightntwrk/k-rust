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
This build provides blind generation (`ProposerKind::Blind`), the dictionary (`ProposerKind::Dictionary`) and the climb (`ProposerKind::Climb`, below): guard harvesting, which draws each hole, with probability 1/2, from the literals of the guards and left-hand sides of the target and of the rules at most two rule-graph edges before it, of the equations their guards call, and of the higher-priority rules an `owise` rule competes with, plus or minus 1 to 3 and negated (ARCHITECTURE 8.3; the rustdoc of `proposers::dictionary`). `Campaign::new` refuses a proposer the build does not provide.
The default `ProposerConfig` weighs blind generation alone; a positive `dictionary` weight (in the library, the campaign file's `[proposers] weights` or the bindings' `proposers.weights`) adds the dictionary, and the report then records its parameters (`identity.dictionary`).
It also provides the climb (`ProposerKind::Climb`) for rule and observer targets: targeted hill climbing, which keeps the best-scored `miss` case and proposes typed moves of one or two of its holes (integers by `±2^e` with an exponent that grows after an improvement and shrinks after a rejection, Boolean negation, single edits of strings, byte strings and collections, constructor swaps), preferring the holes whose values the scored guard read, and spends at most half of the cases, and of the work up to its last case's work (ARCHITECTURE 6.4, 8.4; the rustdoc of `proposers::climb` and `score`).
A rule target's case is scored by its rule-graph distance to the target and the branch distance of the guard that stopped it, read from the condition records the backend reports (`collectConditions`), which only a climbing campaign requests; an observer target's case by the greatest progress (`ObserverVerdict::Progress`) its observer reported.
A positive `climb` weight needs a positive `blind` or `dictionary` weight beside it, and the report then records the climb's parameters (`identity.climb`); pattern and differential targets are refused with the climb.
A candidate hit becomes a witness only after a confirmation on a fresh backend agrees.
Each run starts from fresh proposer state, so a second run reports exactly what a fresh campaign with the same spec and budget reports.
The `FuzzReport` (`to_canonical_json` gives its canonical bytes) is a function of the definitions, program, holes, target, options, budget, seed, the k-rust revision and `ENGINE_VERSION`.

The Node-API (`k-rust-napi`) and WebAssembly (`k-rust-wasm`) packages run one campaign per call, `runFuzzCampaign`, from the specification's JSON form, and return this report; without a caller identity they record the same k-rust build identity as `krust-fuzz` (below).
Observer targets are library-only, and the WebAssembly package has neither the solve proposer nor a per-case safety limit ([k-rust-napi](../k-rust-napi/README.md#fuzzing-example), [k-rust-wasm](../k-rust-wasm/README.md#fuzzing-example)).

## Command line

The `krust-fuzz` executable runs the same campaign from a compiled directory, a program and a campaign file (ARCHITECTURE 9.4).
It needs k-rust's `cli` feature, which loads compiled directories (and implies Z3), so it is built with this crate's `cli` feature: `cargo build -p k-rust-fuzz --features cli`.
`krust fuzz ARGS` runs it, as `cargo` runs `cargo-NAME`.
krust looks for an executable `krust-fuzz` beside itself, then on `PATH`, skipping files that are not executable.
It passes the arguments after `fuzz` exactly as given (a leading `--` included) and its own k-rust build identity, and `krust-fuzz` refuses to run (exit status 2, "version skew") when it was built from other k-rust sources.
When no `krust-fuzz` is found or it cannot be started, `krust fuzz` exits with status 2, never with `krust-fuzz`'s "no witness" status 1.
Release archives ship only `krust`, so `krust fuzz` needs `krust-fuzz` built from source.

```text
krust fuzz --definition imp-kompiled --program transfer.imp --campaign holes.toml \
  --reach-rule IMP.overflow --max-work 100000 --cases 5000 --seed 0x5eed --json
krust fuzz --replay witness.json
```

A compiled directory is loaded as `krust krun --definition` loads it (`k_rust::native::load_runnable_artifact`, plus the directory's `syntaxDefinition.kore` and `macros.kore`, which printing and reading back data values need), and every backend is built on krun's route, with the compiler's rewrite order.
The program's path as written names it, as `krust krun` names a program: span holes address that name, and the program's locations carry it.
The start sort defaults to the sort of `$PGM`.

The campaign file holds the `[[hole]]` declarations of [Hole declarations](#hole-declarations) and, optionally, everything else; paths in the file are relative to its directory.
Every flag overrides the file: each switch has a negation (`--one-path`, `--no-run-to-completion`, `--no-negated-property`, `--shrink`), and a target named by flags replaces the file's target kind with its `mode` and `at`.
`--rule-mode` and `mode` are refused unless the target is a rule, `at` unless it is a pattern, and `--mutant` selects the differential target only when no other target is named (a mutant with a rule or pattern target is refused).

```toml
definition = "imp-kompiled"   # --definition; `mutant` (--mutant) names a mutant: the differential target
program = "transfer.imp"      # --program; `sort` (--sort) and `config-vars = ["N=1"]` (-c) as krun takes them
seed = "0x5eed"               # --seed; `cases` (--cases) or `work` (--work) is the budget, 1000 cases by default

[target]                      # exactly one of rule, pattern, differential (OD-2)
rule = "IMP.overflow"         # --reach-rule, by label; `mode` (--rule-mode) is fired, covered or condition-reached
# pattern = '<k> .K </k> ...' # --pattern, in krun's --pattern syntax with `requires`; `at` is final
# run-to-completion = true    # --run-to-completion; negated-property (--negated-property)

[options]                     # paths = "all-paths" (--all-paths), max-depth, max-work, normal-end-pattern,
safety-limit-seconds = 60     # shrink, smt-timeout-ms, smt-retry-limit; no-safety-limit = true (--no-safety-limit)

[[hole]]
name = "AMOUNT"
sort = "Int"
line = 4                      # `program` defaults to the program's name; `$NAME` addresses a binding's text
find = "amount = 250;"        # defaults to `literal`
literal = "250"
range = { min = 0, max = 1000000 }   # also `length`, `elements = { element = "Int" }`, `choices = [1, 2]`

[[hole]]
name = "TX"
sort = "Tx"
config-var = "TX"             # a configuration variable's whole value
```

`[bounds]` (`int-bits`, `length`, `depth`) and `[proposers]` (`anchors-first`, `weights`, `explicit = [{ AMOUNT = 7 }]`) map onto `GenerationBounds` and `ProposerConfig`.
A value is written as a TOML integer (an `Int`, or the unsigned value of an `MInt{N}` hole), boolean or string, or as a table in the library's JSON form, such as `{ int = "123456789012345678901234567890" }` or `{ list = [{ int = "1" }] }`.

Every case has a wall-clock safety limit of 60 seconds unless `--safety-limit SECONDS` or `--no-safety-limit` says otherwise (D24): `max-work` counts steps, and a step whose ground function evaluation does not terminate would otherwise never end.
A limit of 0 seconds, which would stop every case, is refused, and so is a campaign file that sets both `safety-limit-seconds` and `no-safety-limit`.
A case the limit stops is `timeout` and outside the determinism contract; the report's options record the limit.
The library sets no limit by default.
The campaign runs on a thread with a 256 MiB stack, which the report records.
The report's k-rust revision is always k-rust's build identity (`k_rust::build_identity`), which `krust-fuzz --version` also prints; no flag or campaign-file key can name another.
The identity is the k-rust version followed by `+src.` and a digest of the sources k-rust is built from: k-rust's build script hashes the non-test Rust sources of `k-rust`, `k-rust-kore`, `k-rust-backend` and `k-rust-regex` and the files they embed (`crates/k-rust/build/source_digest.rs` gives the exact rule); crates.io dependency versions, features and the profile are not part of it.
Builds whose k-rust sources differ, committed or not, have different identities, and `krust` and `krust-fuzz` built from one tree have the same one.
Outside this workspace's layout the build script cannot read those sources, the identity is the version followed by `+unverified`, and the skew check and `--replay` say when they compare such identities.
The identity covers k-rust, not this crate: two `krust-fuzz` builds that differ only in this crate's code record the same revision.

The summary goes to standard output, or the canonical report with `--json`; `--report FILE` writes the report, and `--witness FILE` writes the witness file when a witness is found and removes an existing FILE when none is, so that the file never holds an older run's witness.
Both paths are checked before the campaign runs (and must name different files), and the result is printed before they are written, so a failed write loses no result.
The exit status is 0 when a witness was found and confirmed, 1 when not (including `equivalent`, `rejected-out` and `aborted`), and 2 on an error (including a failed write after the result was printed).

A witness file (`schema: "krust-fuzz-witness"`, `version: 1`) holds the campaign as resolved (absolute paths, every option) and the report; `--replay` refuses a witness whose report is not a `krust-fuzz-report` of the `REPORT_VERSION` this build writes.
`--replay FILE` loads the recorded definitions and program, rebuilds the specification and checks that its identity is the witness's.
It compares every field of the report's identity except six: the proposers and the budget, which the replay sets itself, `options.shrink`, and the engine version and the dictionary's and the climb's parameters (`dictionary`, `climb`), which cover only the code that chooses cases.
That includes the k-rust revision, each definition's modules, execution digest, route, rewrite order, frontend, execution-definition and syntax-and-macro digests and initial configuration, the program, overlay and target digests, the options, the bounds and the solver.
On a mismatch it lists every difference by its path in the report (for example `definitions[0].syntax-definition-digest`) and refuses (exit status 2) unless `--force` is given.
A forced replay prints each mismatch and a `forced: replayed despite N identity mismatches` line; its exit status still says whether the cases reproduced.
It then runs the first and, when there is one, the shrunk witness case as the campaign's only explicit assignment, without shrinking, and a case reproduces when the replay confirms a hit whose witness case (hole values, class, initial and final configurations, reaching leaf and step count) equals the recorded one; the exit status is 0 when every case reproduced and 1 otherwise.
`--definition`, `--mutant` and `--program` relocate the recorded inputs; the identity check still applies, and the replay's revision is always this build's.
