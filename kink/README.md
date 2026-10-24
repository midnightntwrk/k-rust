# kink (k-in-k2)

kink provides execution pattern matching and semantic mutation testing for K definitions.
It is built on k-rust and is a part of k-rust's repository: its crates (`kink/crates/*`) are members of k-rust's workspace and build against the k-rust beside them (`crates/k-rust`, `crates/k-rust-backend`), at whatever commit the checkout is.
kink was developed as the separate repository k-in-k2 and merged into k-rust under `kink/` with its history.
The k-rust passages and sources cited below with line numbers are cited at k-rust `0068938b1`; kink's drift pins (light-tier tests) pin the ones kink rests on, so a k-rust change that moves one fails a kink test in k-rust's own test run, to be judged then.
The k-rust revision kink reports and keys on (`kink_native::K_RUST_REVISION`, the `k_rust_revision` and `k_rust.revision` fields of its documents) is the version of the in-repo k-rust package; every store honoured without re-deriving its verdicts also keys on the build itself (`kink_build`, below).
kink writes `collect_offered: false` in its execution requests. It reads every run-level field of an execution result, fail-closed: the lists of open values read, contradicted claims, allowance refusals and unsupported hooks each exclude a run (below, "What a kill trusts"), and the count of undecided solver answers is reported only.

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
Build the portable profile for the loop, from the root of k-rust's checkout: `cargo build --release -p kink-flow --no-default-features`.
The default build is the Z3 profile ("Gate", below), under which the outcome and pattern caches are off and some `no` answers of `kink-flow query` are `unknown`, until adoption A-5 and k-rust's KINK-28; the walkthrough below is written for the portable build.

### The loop

1. **Specification.** Start from a K specification: an entry file, its main module and its syntax module.
   A literate Markdown specification (`.md`) works too: every text kink-flow addresses, searches or shows is the K text k-rust parsed from the selected fences (prose and fence lines count as whitespace, and line numbers are the file's), and kink-flow never edits the Markdown file.
2. **Corpus with cached results.** Write concrete programs for it in `FLOW.toml`.
   `kink-flow results` runs each new or changed program once on the specification,
   caches its final configuration, and lists the rules no comparable program reaches (`uncovered`).
   Write programs until no rule is uncovered.
3. **Mutation list.** Write `MUTATIONS.toml`: edits of rules that are likely to expose bugs,
   either single edits (one `+Int` becomes `-Int`) or correlated edits (several rules changed together as one mutation).
   `kink-flow results FLOW.toml --mutations MUTATIONS.toml` (and every run report) lists the rules no mutation targets yet (`untargeted_rules`, with each rule's K text and how to address it).
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
A killer hint never decides a status: it only orders the work.
When a mutation runs live, the baseline result of each program it runs is compared with that program's cached result, which detects a corpus that changed under the cache.
A killed mutation decided by a cached outcome, or a survivor whose every outcome is cached, runs nothing and gets no such check: there the programs' cached results are trusted with the rest of the cache directory.
What a kill trusts, besides the cache premise above:
- k-rust executes the definition correctly: its rewriting, its simplifier and every hook it evaluates, the STRING and INT hooks k-rust 501f18b9 newly evaluates included (re-pin decision 3).
  This includes its state-set merge (re-pin lane 1, L1-1): a test without a pattern oracle runs as one unobserved state-set run on each side, in which k-rust merges equal final configurations and expands each distinct state of a depth once, and a complete state set has exactly the distinct final configurations of the path set of the same request, diagnostics included. A state set with an undefined step, a vacuous leaf or a contradicted claim is replaced by the path set of the same request, because under a state set such a leaf's rule is witness metadata and the exclusions below read it. The replacement is decided on each side from its own leaves, so one test can compare a state-set side with a path-set side; such a run is two runs, each under the whole time bound. A test with a pattern oracle runs as a stepped path set on both sides.
  kink compares sets of projections of the final configurations, so most comparisons are the path set's. Three routes give a kill where the path set of the same request gives none; each is a real difference between the two sides' sets of final configurations and rests on this premise alone (re-pin decision 3; the orchestrator's judgement in the decisions log, 2026-10-17, which Sebastien can override; kink-campaign `tests/state_set_routes.rs` pins each):
  1. The single-crash rule reads multiplicity: a side is a crash side only when it has exactly one terminal leaf. Two paths to one crash configuration are one leaf in a state set (a crash side) and two in a path set (`unknown`).
  2. Mixed modality: the baseline's state set stays a state set while a mutant's with an undefined step is replaced by its path set (or the reverse). With route 1 this kills where both sides as path sets refuse the baseline.
  3. An absorbed bound: an earlier stuck leaf stands for a later depth-bound or indeterminate leaf of the same configuration (k-rust `docs/backend-port.md`, "Final search depth cuts"), which then leaves no leaf, so kink reads the state set as complete where the path set of the same bounds is not. Since k-rust 58720d2e5 this is a k-rust contract (KINK-22, `docs/compatibility.md` "Search results", lines 2129-2134 at 0068938b1, pinned by kink-native `tests/run_facts.rs`): a `state-set` result in which every bound or undecided leaf was merged into an earlier stuck leaf of its configuration reports the final configurations of the same request without those bounds on those paths. kink reads that as the merge's meaning (the configuration is decided stuck by the earlier leaf), not through k-rust's coverage statement, which requires a run without depth stops.
  Also, a state set can finish within the time bound where the path set did not (IMP: `and-false-returns-rhs` is killed by `primes`, `collatz` became comparable; L1-1, confirmed by its review with a single concrete path, `crates/kink-flow/tests/imp_primes_kill.rs`).
  kink-flow `tests/modality.rs` is the safeguard: on the flow corpus, its mutants and the converging fixtures of `testdata/k/l1` (and, on demand, `examples/imp` and its mutants) it runs every program as a path set and as a state set and fails on any difference but an absorbed bound: deduplicated final configurations with their terminal classes, undefined steps, incomplete leaves, diagnostics, stack stops, the bridged state-slot inputs and coverage, and, on the flow corpus, the campaign runner's verdict for every mutant under both modalities.
  Every run carries no trace, collects k-rust's run coverage (scheduling and reports only) and answers a cancellation with an error: a timed-out run publishes no leaf.
  Coverage (kink-native `coverage`, `kink/coverage/v3` since re-pin L2-1-tail; v2 since L2-1) is every rule and equation a baseline run reached (k-rust `matched`) and fired (`applied`). It only orders: a mutant's tests (kink-campaign `selection`) and kink-flow's programs run first where the baseline's coverage witnesses the edit, and the rest after them. kink-campaign reads the edit from the compiled sides: a rewrite rule edit is witnessed by `applied`, or by `matched` when it changes the `requires` (alone or with the right-hand side); an equation edit by `matched` when it changes the `requires`, by `applied` when it changes only the right-hand side or `ensures`; every other equation edit, such as a left-hand side, an attribute, an `owise` or `smt-lemma` equation, the `requires` of a `concrete` or `symbolic` equation or a deleted equation, keeps manifest order. kink-flow reads the edit from the rule's text before the mutant compiles: an edit that changes the rule's `requires` is witnessed by `matched`, every other edit by `applied`, for rewrite rules and equations alike, so an equation edit that kink-campaign leaves in manifest order still puts first the programs that fired (or, for a `requires` edit, reached) the equation, and a rewrite rule edit of the `requires` together with the left-hand side or an attribute is witnessed by `matched` in kink-flow and by `applied` in kink-campaign (kink-flow README, `run` step 3; review L2-1-tail-1 D3). No test or program is ever left out. In the no-Z3 profile (kink's default build), while no wall-clock bound fires (kink-flow's `budget.time_ms`, kink-campaign's `ExecutionBudget::time`), no status therefore depends on coverage or on any other order: under first-kill a kill ranks above every other outcome and every test before the first kill runs, which needs each test's outcome not to depend on the tests run before it, as k-rust's Execute promise gives. That promise excludes a request the clock bounds or cancels, so a run near its time bound can time out in one order, while caches are cold, and finish in another: the order can then move a status between `timeout` and the status the run gives when it finishes (a `timeout` is host- and timing-dependent anyway; review L2-1-tail-1 D2). Under Z3 that premise fails: an SMT query can time out, and a mutant's backend and the baseline's are reused for every test in schedule order and keep a cache of satisfiability answers across requests (k-rust `docs/compatibility.md`, Execute), so the order can move a status between `killed`, `unknown` and `survived`: a solver timeout makes a test `unknown`, and a cache an earlier test warmed can answer the same query, turning that test into a kill or an agreement, so with no kill the fold gives `survived` in one order and `unknown` in the other (review L2-1-tail-1 D1). It never gives a false kill, since a kill is still a proved difference (re-pin L2-1-tail, review L2-1-1 D4). kink-flow turns its outcome cache off under Z3 for the same reason.
  A mutant's state-set run may carry a work budget calibrated from the baseline's run of the same test (kink-flow `[budget] work_factor`; kink-campaign `WorkBudget`): a run it does not stop is the unbounded run, and a run it stops ends in a `work-bound` leaf, which never completes the run, so the program is `unknown` for that mutant unless the one-sided rule below kills it. Baseline runs and stepped runs are never work-bounded.
- A work-bound mutant run can kill one-sidedly (re-pin L1-2, decision 6, finding A-15; kink-campaign `OneSided`, which kink-flow turns on). k-rust checks the work budget before it expands a state, so every leaf before the `work-bound` one is a state whose own expansion finished; since k-rust 58720d2e5 this is a k-rust contract (KINK-22, `docs/compatibility.md` "Work budget", lines 2346-2349 at 0068938b1, pinned by kink-native `tests/run_facts.rs`): every leaf finished before the `work-bound` leaf is a leaf of every run of the same request with a larger budget or none, at the same position. In a build with Z3 k-rust gives this only when neither run reports `smtUnknowns` (line 2349), a count kink carries and never reads (decision D-7 (a1), below). The rule does not rest on the contract there, and needs no such condition: it reads only a leaf that is a fact of its own path. k-rust reads an undecided answer as an over-approximation (`docs/compatibility.md` line 2504): it refutes a branch or discharges a condition only on a decided answer (for example k-rust-backend `rewrite/step.rs` `may_have_instance`, where only `unsat` refutes), so a path an undecided answer kept still carries the condition it left open in its state, or a diagnostic saying a condition was left undecided. The rule refuses both (no path predicate on the leaf, no diagnostic on any leaf of the run; kink-native `work_bound_stuck_terminals`), and the leaf's reachability and finality below follow from its own path, not from the order of exploration (the contract's further fact, that the leaf keeps its position, is one the rule does not use). When such a leaf is stuck, clean (no diagnostic, no contradicted claim) and a ground value (one term, no path predicate, no free variable, definition-independent on the mutant's own definition), its configuration is reached from the test's initial state and final in every model, so it is a final configuration of every completion of the mutant's run. If the slot's projection of it is not in the baseline's projected set, the mutant's projected set differs from the baseline's whatever the unexplored part holds: the slot distinguishes, and the mutant's side stays `unknown`. The rule needs all of: a baseline side that is a value (a complete run free of every exclusion), a ground test, a mutant run judged into sides (not an error, not timed out, no exclusion) whose only incompleteness is its last, `work-bound` leaf (no stack stop, no diagnostic on any leaf, every other leaf stuck, an undefined step or vacuous, every other path complete, no crash), a slot projecting the whole term or the exit stop without an exit-code cell (projections defined on every configuration), and a classifier that never answers crash (the caller states it: kink-flow's and kink-corpus's `all_normal`; the slot does not compare a set mixing a crash with a normal terminal, and the rule cannot see the unexplored part). Never from a cancelled or timed-out run (decision 6), never on a pattern slot (stepped runs carry no work budget). Contradicted claims are read per path (Sebastien, 2026-10-17, "Land per-path, on"). A kill must be a fact about the definition the author meant. Suppose a claim the claim-free mutant kept is false (a kept claim's support is untouched by the edit, so it is a false baseline claim, against the trusted premise above), and correct it to "true except where it fails": the definition then has models, the baseline's complete set is unchanged, and so is the killing leaf's path, unless that path itself used the claim at an input where it fails, which is the same undetected risk every two-sided kill carries (a false claim used in a condition shows in no leaf, decision 2 below). The unexplored part of the mutant's run can only add or remove other final configurations, never take the killing leaf away. So a contradiction elsewhere in the mutant's run, explored on another path or unexplored, does not void the leaf; one on the leaf's own path does, and the rule refuses it: the leaf is stuck (not an undefined step), carries no contradicted claim and is a decided value (a stuck term that is not a value, such as `f(-1)` left unevaluated under a false `total`, is no leaf). The rule also reads the explored part as decision 2's per-test rule does (an explored contradicted leaf makes the run no evidence), which is stricter than the principle needs and harmless. The rule adds no execution premise; for claims it applies the per-path principle, of which the two-sided per-test rule (decision 2 below) is a conservative over-approximation, so a work budget can kill where the unbounded run is `unknown`: the L1-2 review's probes `testdata/k/l1/l12ct.k` (k-rust names the contradicted `total` on the late branch) and `l12cs.k` (the late branch ends in a term that is not a value) are `unknown` unbounded and killed one-sidedly under budgets 14, 7 and 3 (kink-campaign `tests/one_sided.rs`, which also checks that the killing leaf is a clean leaf of the unbounded run apart from the offending one). Making the two-sided rule per path too would relax a refusal; it waits for a separate decision. A one-sided kill is deterministic under a given budget (k-rust's work count is a function of the request), so kink-flow's tier 1 records it, keyed with the budget. The rule's version (kink-campaign `ONE_SIDED_VERSION`) is a component of kink's semantics identity (below, re-pin L1-2-land), so a store or cache made without the rule or under another version of it misses or is refused, naming `one_sided`. kink-campaign `tests/one_sided.rs` pins the rule and checks, on a fixture, every budget below the mutant's work against the unbounded verdict, and on the probes, whose unbounded run does not compare, that every one-sided kill is explained: the unbounded run is `unknown` only because of a contradicted claim or a non-value terminal on a leaf other than the killing one (`testdata/k/one_sided_support.rs`); kink-flow `tests/one_sided.rs` (on demand) does the same over the flow corpus and over IMP.
- A kill is relative to the definition, not to k-rust's model of it (re-pin decision 1). Where the definition leaves a value open, k-rust chooses one: `choice` of a map or set, the order of `keys_list`, `values` and `Set2List`, the destination format of mixed binary32/binary64 Float arithmetic, the sign of a NaN, `minFloat`/`maxFloat` of `+0.0` and `-0.0`, the letter case of `Base2String`, the binder names `substOne` gives and the count of characters a `#read` returns (k-rust's own list, its classifier `builtin::chosen_value`; kink-native `exclusion::K_RUST_IMPLEMENTATION_CHOSEN_HOOKS`, pinned against it by a test), and the hooks whose value k-rust's builtin files leave to the backend, the implementation or the environment. From `domains.md`: the encoding of `String2Bytes`/`Bytes2String`, the string of `Float2String` (with or without a format), `RangeMap`'s `choice`, `keys_list` and `values`, `randInt`/`srandInt`, the deprecated String hooks, the `K-REFLECTION` hooks that read the process or its environment, and the I/O hooks. From the other builtin files: substitution's renamed variables (`SUBSTITUTION`, whose fresh suffix `substitution.md` leaves to the backend), the `UNIFICATION` hooks, `JSON2String`/`String2JSON`, the timer and the FFI hooks (kink-native `exclusion::DOMAINS_OPEN_HOOKS` and `BUILTIN_OPEN_HOOKS` list each with its file and lines; a re-pin that changes any builtin file fails a test until it is swept again). Also every hook k-rust evaluates that no builtin file it ships documents: the `KRYPTO`, `HASH` and `SECP256K1` hooks, which the user declares and no text of the definition specifies (`exclusion::UNDOCUMENTED_EVALUATED_HOOKS`; a test reads k-rust's evaluated hooks from its dispatch source and pins them, so a re-pin that adds one fails it). Of these, the census reads only the hooks k-rust evaluates without a run-level record (KINK-CENSUS-RUNLIST, fz26): its `chosen_value` hooks, the `String2Bytes`/`Bytes2String` pair and the undocumented evaluated hooks (`exclusion::census_hook`). The others are judged per run (`exclusion::RUN_LIST_HOOKS`): the console operations `#getc`, `#putc` and `#write` (`#read` has a `chosen_value` class and stays in the census) and every hook k-rust has no evaluator for (`Float2String`, `randInt`, the other I/O hooks, `RangeMap`'s three, the `K-REFLECTION`, `UNIFICATION`, `JSON`, timer and FFI hooks, `substMany`). An execute request takes no value of one: it supplies no console and has no evaluator, so an application of one on constructor-like arguments whose value the run needs is on the run's `unsupportedHooks`, wherever it sits (a right-hand side, a condition, a failing left-hand-side match, an equation passed over), and that run is no evidence (`unsupported-hook`); on symbolic arguments it stays unevaluated, so an end that holds it is no value and a branch on it is a branch the definition has. That is a k-rust contract, `docs/compatibility.md` 117, pinned by digest (kink-native `the_console_passage_the_run_list_rests_on_is_pinned`; k-rust's `unsupported_hook_positions.rs` checks every run-list hook in each position, and a kink-native test derives the list from k-rust's inventory and checks it against those cases). A definition whose own sentences or rewrite rules use a census hook (a rewrite rule counts whatever its source, so the prelude's stream rules kompile copies into a definition with stream cells count; their hooks, `#getc`, `#write` and `Float2String`, are run-list hooks, so stock SIMPLE is compared), or a test whose initial state applies any of these open hooks, is never compared: the comparison is unknown, reason `implementation-chosen-hook` (the baseline is not comparable; a mutant is unknown). A program may not bind `$IO` on a definition with stream cells (input refusal `stream-mode`): with `$IO` off, kink's binding, a stream cell holds the text printed and the input not yet read, so an end states the program's output; with it on, output would leave the configuration. The refusal keeps that meaning; soundness does not rest on it (a console operation is on the run's list either way). Beside the census, a run on whose `implementationChosenValues` list k-rust notes a value of one of its own classes (every such value its evaluator takes in a run, the initial state's normalization, a vanished candidate and an absorbed state-set arrival included; `docs/compatibility.md` 1901-1924 at 0068938b1) is no evidence either, reason `implementation-chosen-value` (re-pin adoption A-1); while the census stands this only adds a run that read such a value through an equation the census does not read. k-rust's guarantee for a run whose list is empty holds for the models that agree with its stated readings (compatibility.md 1832-1834); the readings kink relies on are listed in `draft/tasks/repin-58720d2e/ADOPTION.md`, decision D-3, pending a decision. `encodeBytes`/`decodeBytes` name their encoding and are not on the list. Fresh constants (`!X`) are not a hook: the compiled definition's `<generatedCounter>` and `freshGenerator` rules fix them, where `kast.md` promises only distinctness, so a kill may depend on them as on the compiled definition. Strings beyond the first 256 code points: `domains.md` 1681-1686 calls `String` "an implementation of Unicode strings" that "is currently incomplete and does not fully support encodings and code points beyond the initial 256 code points", with possible breaking changes later. kink reads this as a caveat about K's own implementation, not a value the definition leaves open: the specified meaning is a sequence of Unicode code points, which is how k-rust evaluates every `STRING` hook, so a kill through such a string rests on that reading as on k-rust executing the definition correctly (decision 3). No definition-level census could see it anyway, since it depends on the strings a run builds.
- The same holds for short-circuiting (re-pin decision 1, `short-circuit-reading`). `domains.md` lets a concrete backend skip an operand of `andBool`, `orBool` (and `impliesBool`) and `#if`, and calls `andThenBool` and `orElseBool` short-circuiting; k-rust evaluates the definedness of every operand, so a step through one whose skipped operand is undefined (`false andBool 10 /Int 0 >Int 0`) is an undefined step in k-rust and a value elsewhere. A definition with a rewrite rule whose right-hand side applies one of these over an operand that may be undefined (a partial function, directly or through a function's equation) is excluded as a whole, and so is one with a rule whose condition depends on it below the condition's top-level conjunction, or whose right-hand side applies a function whose equation's condition does: an undefined candidate beside a defined same-priority sibling leaves no leaf (k-rust drops it and keeps the sibling's successor), and an undefined condition just leaves the rule unapplied. A run with an undefined step (`Trivial` leaf) of such a rule, and a test whose initial state applies such a function or operator, are no evidence too. "May be undefined" is read on the definition each side runs: a mutant's after the claims its edit leaves unbacked are removed (below), so a function whose `total` was removed counts as partial there; the analysis trusts the `total` declarations a definition keeps. Cost: none on testdata, flow or examples (kink-native `sweep::heavy::every_testdata_definition_passes_every_definition_check`). A skippable operand counts only where one of its applications of a partial or reading-dependent function is evaluated by no operand that runs whenever it is skipped (KINK-SC-DEFINED, the must/may rule of kink-native `exclusion.rs`): where every one is, both readings are undefined together, so `#if pd(A) >Int 0 #then pd(A) #else 0 #fi` is not flagged and `#if A >=Int 0 #then A #else pd(A) #fi` is, whatever its guard says; no guard's truth is read. A recursive function's own calls are read as independent while its equations are checked, which rests on premise A1 (evaluation terminates). This clears the prelude's `findChar`, and so the `stdin` stream rules whose conditions apply it. Known conservative case: the prelude `owise` equation of `replace` negates `Count >Int 0 andBool findString(..) >=Int 0`, whose skippable application of `findString`, declared partial, no other operand evaluates, so a rule applying `replace` or `replaceAll` is flagged. A definition with `stdin`/`stdout` stream cells is therefore excluded neither by this rule nor by the census: the I/O hooks of kompile's copied stream rules are run-list hooks, judged per run through `unsupportedHooks` (above).
- A mutant drops the claims its edit leaves unbacked (re-pin R0c-fix-2, Sebastien 2026-10-17). A claim is the specification author's assertion about the definition they wrote: k-rust trusts it instead of checking it (kink-patch `TRUSTED_CLAIMS`, each with its k-rust citation: `total`, `functional`, `injective`, `smt-hook` and `smtlib` on a production; `preserves-definedness` and `smt-lemma` on a rule; the `simplification` lemmas; an equation's non-trivial `ensures`; a `concrete` or `symbolic` equation; a hooked symbol's equations). When a mutation edits part of the definition, every claim whose truth depends on the edited part is backed by nobody, and a mutant carrying a false one is an inconsistent theory on which any verdict follows. So kink builds every mutant without them (kink-patch `ClaimSupport::withdraw`, the one function the campaign runner, kink-corpus and kink-flow build mutants through): the edited symbols E are the heads of the edited equations (a rule written with configuration context, `rule [[ F ]] C`, is an equation of `F`'s head, as k-rust reads it; re-pin R0c-fix-4), a symbol reaches E when one of its equations (left side, right side, `requires` or `ensures`) applies a symbol of E or one that reaches E (the equations kompile generates count too: each member of an `overload(key)` family reaches every other through the overload axiom `g(inj(x)) = inj(l(x))`, and a production with `unit(u)` reaches `u`; re-pin R0c-fix-3), and kink removes the claims of every symbol in E or reaching E, every lemma that mentions one (deleted: a lemma is a claim as a whole), and the `preserves-definedness` and `smt-lemma` of every rule that is edited or applies one. An edit of a rewrite rule only removes that rule's own claims (the lambdas kompile generates for a `#let` or `#fun` in it carry no written claim: a lambda is declared `total` only by k-rust's judgement of its body on the claim-free mutant). Baseline claims are a trusted premise; mutant claims the edit can affect are removed, so k-rust executes the mutant without trusting them, and every test, ground or symbolic, runs on it. Removing claims makes the mutant's claims backed; it does not make it a consistent theory by itself (next item). Equivalence is decided on the mutant as written, with the baseline's claims, so removing claims never makes a mutant `equivalent`. A claim no removal takes away without changing the definition (one the patch writes, a lemma it edits or inserts, an equation's `ensures`, `concrete` or `symbolic` restriction or hook agreement whose support the edit touches) refuses the mutant (`unsupported-claims`), and so does a claim-free mutant k-rust does not compile (`stripped-claim-compile-failure`); both are `unknown`, never killed. The removed claims are recorded per mutant (the campaign report's `claims`, kink-flow's `removed_claims` and its outcome files), and kink-flow's tier-1 context names the removal algorithm's version. On testdata and examples, catalogue-v1 mutants with removed claims and refusals are counted in the R0c-fix-2 handoff; IMP declares no function, so nothing is removed there.
- A mutant must be a theory with models (re-pin R0c-fix-3; decisions log 2026-10-17, "inconsistent mutants"). `function` is part of a symbol and a function has at most one value per input, so an edit that makes two equations of one function apply to the same input with different values (a guard literal, a dropped `owise` or `priority`) leaves a mutant with no model, and k-rust's verdict on it is the order in which it lists the equations (the R0c-fix-2 review's `fpos` 0 -> -5 was killed and its mirror `fneg` 0 -> 5 survived). After claim removal, kink checks every pair of equations of every symbol the edit can change with k-rust's own load-time critical-pair check (kink-native `consistency`, `BackendDefinition::value_claims_in_scope(CheckScope::All)` on the claim-free mutant): root pairs of one priority group (an `owise` group is its own), self pairs of a map or set pattern, inner pairs, k-rust's reports of an equation it never applies as written, and the precondition rows that put an equation outside the check (a constructor-headed or injection-headed row refuses only when its equation is itself checked: k-rust classifies no overlap of such an equation, so one with a checked equation below the root of a checked left-hand side would be neither classified nor refused; no K source is known to give one, re-pin R0-tail). A pair the check does not show to join (the reducts differ, a condition is neither refuted nor decided, the join is refused or runs out of budget, ...) refuses the mutant as `inconsistent-mutant`, naming the pair (the campaign report's and kink-flow's `inconsistent_pairs`): it is `invalid`, like a mutant that does not compile, outside the score, never killed or survived. So is a check that cannot run: kink reads the claim-free mutant's full check (`CheckScope::All`, which has no early return for a definition that declares no equation head; before fz26 KINK-BASELINE-FINDINGS kink checked a copy with an added equation head instead), computed once on the backend the mutant runs on (`Backend::from_definition`, kink-native `data::DataFacts`), and refuses the mutant when the check did not read every executable equation, skipped a candidate pair, classified fewer pairs than the definition's root pairs, or met a stop for lack of stack (`condition_stack_stops`). k-rust reports these counts for the whole definition only, so the guard shows that the check ran on the whole definition, not that each group's root, self and inner pairs were classified. Which symbols the edit can change is read from the compiled definitions, which k-rust executes (re-pin R0c-fix-4, kink-native `consistency::admit_mutant`): every index of the claim-free mutant's function theory whose equations differ from the baseline's (compared without their unique ids, origins and the claims removal handles; an index on one side only counts; the simplification and ceil lemmas are compared alike, and a changed predicate lemma checks every head), and every index whose equations reach one over either compiled theory (an equation reaches the symbols it applies; an overload family is linked both ways), together with kink-patch's source reading (`ClaimSupport::affected`); a changed or reached index that is not a symbol checks every head. So the equations kompile generates (the `#lambda` of a `#let` or `#fun`, in a rewrite rule or a function equation) and equations whose source form kink-patch would misread are checked. An edit that changes no compiled equation still has the symbols of kink-patch's source reading checked (an equation edit that compiles equal except in what the diff ignores is checked on its head), and an unknown source reading checks every head; only an edit that changes no compiled equation and whose source reading names no symbol checks nothing (re-pin R0-tail). The source reading is a fail-closed cross-check: every compiled equation that a sentence the patch touches or inserts gives, on either side, must be headed by a symbol kink-patch reads as redefined or by a generated lambda, and no other generated `total` symbol may have changed equations; otherwise the claims the edit leaves unbacked are not known and the mutant is refused as `unsupported-claims` (key `unread-equation`). The check reads the mutant's heads only: a pair of symbols the edit cannot reach is the baseline's, normalized with the baseline's equations; kink checks that every such finding of the mutant is the baseline's, by name and by the unique ids of its equations, and refuses a difference as `mutant-findings` (`unknown`), and the baseline's own pairs are the next item's. The witness equations the full check adopts (k-rust FZ-EMPTYJOIN-WITNESS: each interprets a stuck partial application at an element of a sort with no normal form, and a pair may join only through one) are part of the edit's effect (fz26 KINK-WITNESS): they are read from the same full checks the gate reads (`DataFacts::witnesses`), a head whose witnesses differ from the baseline's counts as changed and a witness reaches the symbols it applies as an equation of its head does, and a flip of the pass the check adopts between baseline and mutant checks every head, so a mutant whose check then keeps a pair unjoined is refused as `inconsistent-mutant` before the `mutant-findings` comparison. Premise: k-rust's critical-pair checker decides joinability in `M+` correctly, and A1+ holds (the equations "have `M+` as a model when the executable equations and the witness equations the check adopts terminate innermost over the signature with the added constants (A1+), and their critical pairs join, which the backend checks", k-rust `docs/compatibility.md`, where `M+` adds a fresh constant to each sort that does not have an element in every model and agrees with `M_NF` on every term free of them; A1+ is a premise k-rust states and does not check; the passages and the checker's source are pinned by digest in kink-native's `consistency` test). The check proves nothing beyond k-rust's simplifier without a solver. Since k-rust 58720d2e5 (KINK-20/3) that simplifier also refutes the integer bounds that one-term comparisons with literals state, so two disjoint single-variable guards (`I >=Int 5` beside `I <Int 0`, `r0c/cfgf.k`'s `fpos` 0 -> 5) are refuted and the mutant is admitted (decisions log 2026-10-20, "admit mutants whose guards k-rust's KINK-20/3 refutes as disjoint"); guards that do not overlap but that k-rust neither refutes nor decides (a partial key whose definedness is a sibling conjunct, a guard beyond one term and a literal) still refuse a consistent mutant. The cost on testdata and the flow lists is in the R0c-fix-3 and R0c-fix-4 handoffs. The versions of claim removal, the consistency check, the compiled reading and the definition exclusions are components of kink's semantics identity (below), so a report or store an older build wrote at the same k-rust pin is refused by replay, by kink-corpus resume and by its summary, and missed by kink-flow's caches.
- The baseline must be shown confluent, or its findings named as premises (fz26 KINK-BASELINE-FINDINGS, finding KINK-BASELINE-TRUST). A kill compares ends as values of the definition, and k-rust's full check reads the definition by the model `M+` (its normal forms with a fresh constant in each sort that does not have an element in every model, agreeing with the normal-form model `M_NF` on every end kink compares), a model only when the critical pairs of the executable and witness equations join, under the premise A1+ (k-rust-backend `data_term`). The baseline's pairs were a trusted premise "which the backend checks", but nothing checked them, and a pair that does not join can make the compared ends equal in every model: with `q(_) => a` beside `q(_) => bb`, a mutant writing `bb` where the baseline writes `a` is equal to it, and kink-flow killed it (and six more DATAEND-review repros, `testdata/flow/findings`). An identification reaches other terms through congruence, so no reading of the compared terms rules it out. kink therefore computes each definition's full critical-pair check once per load, on the backend it runs (kink-native `data::DataFacts`, k-rust's `data_heads`), and counts a kill only when both sides' compared ends are data, each under its own side's definition (`data::data_ends`, the one function that says so: while a finding is left no end is data). A baseline with a finding the author has not named makes every mutation `unknown` with reason `baseline-findings`, before any mutant compiles and whatever a cache holds; `results` lists the findings (`data`) and marks every comparable program `unable_to_kill`, and a query `no` is `unknown` (a hit stands: k-rust reached that configuration). The author may name a finding as a premise in kink-flow's `[spec] assume_joined`, by the name `results` prints, which is k-rust-fuzz's name byte for byte (k-rust-backend `data_term::names`, the one renderer); a decided finding cannot be named, and a name must name exactly one finding. Every verdict is then relative to that premise, which every document prints; a genuine finding named is a premise known to be false of the definition as written. The version of these facts is a component of kink's semantics identity (`data_facts`), so no store made before kink read them is honoured. On WASM (4 findings since k-rust FZ-EMPTYJOIN-WITNESS joined the `#t2aStmt` pair over the empty `EmptyStmt`, 2 of them genuine) and KEVM (15 before the checker work of P7-KEVM-S2A/B/C, 5 after it at fz26 int9, 4 of them genuine) every mutation is `unknown` until the findings are fixed upstream or named.
- Every compared end is data under both definitions (fz26 KINK-OVERLOAD-VALUE; P7-SIMPLE-KINK design, (c)). A compared end must be a value no model of the definition identifies with another: built from free constructors, normal-form injections, identity-safe domain values and trusted natural collections (TV-01), and, since this ticket, instance-normal applications of an overload data head (an irreducible `_,_Exps` or `_,_Vals` list, which every SIMPLE end holding an argument list or a declaration with an initializer has), admitted where k-rust's data judgement holds under the definition's own facts (k-rust-backend `BackendDefinition::is_data` with the definition's `data_heads`, called once at each outermost such application: the evaluator's own matcher, subsort order and overload axioms decide irreducibility, so kink has no second matcher, and the fuzz uses the same judgement). Each definition reads the ends with its own theory, and a mutant can change a symbol's role: an `anywhere` attribute on the baseline rule `c(1) => d` makes the baseline's end `c(1)` and the mutant's `d` one value of the mutant, and an added overload member lowers a baseline normal form (k-rust-backend `data_term`, "Two definitions"). So each side's terminals are judged under its own definition when its run is judged, and every compared end of a pair (state-slot terminals, reused baseline runs included, one-sided terminals and pattern bindings) under the other side's definition before the pair's slots are compared (kink-campaign `runner::judge_across`); an end that is not data there makes that side's slot `unknown` for that pair (a one-sided terminal is dropped), so r2-anyw written as that attribute edit is `unknown` where it was killed. kink-native `data::data_ends` is the one function that says which ends are data; the mutant's definition is the claim-free mutant, the one it runs. Two different compared ends then differ in each definition's initial model, under premises A1+ (evaluation by the executable and witness equations terminates over the signature with `M+`'s constants, which implies A1, the termination every evaluation assumes) and A2 (`simplification` lemmas and `[symbolic]` equations are theorems of the executable equations; the baseline's claims are trusted, and a mutant's that its edit unbacks are removed). `data_term`'s module documentation, its head selection and its walk are pinned by digest (kink-native `tests/data.rs`). `a[i]` in SIMPLE leaves an application of `_[_]`, which roots `anywhere` rules that are not overload equations, so an array program stays unknown. The version of this walk is a component of kink's semantics identity (`terminal_value`).
- A rule or equation condition that equates two terms (K `{ A #Equals B }`) is a gap of k-rust's own answers when the terms may be undefined: its SMT translation has no model where both sides are undefined, so answers over the definition may wrongly be empty, `valid` or `proven` (k-rust `docs/compatibility.md`, "Two gaps remain"). A definition (baseline or mutant) with such a condition is never compared (`equals-condition`, kink-native `exclusion`). Conditions are every antecedent of an axiom, whatever its left-hand side (an application, `#Ceil` or another predicate), a rewrite rule's `requires`, and every `ensures` (re-pin R0c-fix-4), a rewrite rule's under the `\exists` kompile wraps around a right-hand side with an existential variable `?Y` included (re-pin R0-tail: every `\equals` of a rewrite rule's right-hand side is read); no testdata or example definition has one.
- A kill on an inconsistent definition says nothing (re-pin decision 2). A mutant no longer carries a claim its edit can falsify (above), so the remaining claims are the baseline's, a trusted premise, and those of a mutant's unedited part. A run whose undefined step falsifies one (k-rust names a contradicted `total`, or the step's rule carries `preserves-definedness`) is no evidence (`contradicted-claim`) for its own test. Since re-pin adoption A-1 so is a run on whose `contradictedClaims` list k-rust holds any record, ground or not, observed by the run or by the load of its definition (`docs/compatibility.md` 1653-1661 at 0068938b1): the list holds what no leaf carries, a candidate a defined sibling covered, a state-set arrival a merge absorbed and a condition decided through the contradiction, and a comparison of complete sets needs every path of each side to be a path in every model of a consistent repair of the definition. A load record (`observedIn: load`) is on every run's list, so it takes every test of its definition out of the score (decision D-6). The records are reported as specification diagnostics (kink-flow: `specification_diagnostics` in a program's row and in a mutant's executed entry), so the author learns which claim is false where. The rule is per test (Sebastien, 2026-10-17): a kill counts when the killing test's baseline and mutant runs are both complete and free of every exclusion, a contradiction included, whatever another test shows. When a claim is false only at inputs the killing test never touches, weakening the claim there gives a definition that has models, and the killing test behaves the same in all of them. A test compares its slots only when both runs gave sides, and an excluded, timed-out, stack-stopped or unbridged run gives none, so a contradicted leaf in the killing test's own runs never yields a kill. On the baseline a run whose own leaf contradicts a claim makes only its test unknown for every mutant (the campaign is not refused; in kink-flow the program is not comparable); a baseline run excluded only by a record on the list is refused, as any other excluded baseline is, because before A-1 such a run was either compared or, when its leaf carried the record, unknown and refused, and keeping it per test would relax that refusal without a decision. `FirstKill` and `Full` agree. The finding A-13 residual (a false baseline claim used in a condition, or beside a defined same-priority sibling, shows in no leaf) is closed for ground tests by reading the list. A symbolic run's empty list says nothing (k-rust trusts the claims on a symbolic state, compatibility.md 1661), so kink-campaign's symbolic tests still rest on the premise that the baseline's claims are true.
- A run whose result can depend on the host is no evidence: one that counted a stop for lack of native stack (`stack-stop`), one on a definition whose load counted one (`load-stack-stop`), one with a Bytes hook refused for the process's memory allowance (`allowance-refusal`), on a leaf or, since re-pin adoption A-1, on k-rust's `allowanceRefusals` list of the run or its load, which also holds a refusal inside an undone attempt or a passed-over equation that steered the result and left no diagnostic (`docs/compatibility.md` 92). A result whose list is empty is the result under every allowance of at least as many bytes (compatibility.md 859), so the outcome records carry no allowance key.
- A run on whose `unsupportedHooks` list k-rust holds an application left unevaluated as an unsupported hook, in the run or its load, whatever became of the work that met it, is no evidence (`unsupported-hook`, re-pin adoption A-1): such an application can steer a passed-over equation without a leaf showing it.
- A program `kink-flow fuzz` found adds nothing to trust (fz26 P7-KINKFLOW): it decides no status, and `run` proves its kill like any other program's. The fuzz is a search for such a program under stricter rules than `run`'s, so that its candidates are ones `run` can confirm: its data judgement is strict (a finding no name assumes makes the campaign `not-comparable`, and an assumed finding is only ever the author's named premise, printed beside the fragment), and it refuses a job on which `run` would compare another input than the one the campaign judged.
- A mutant is held to compilation, not to K's rule parser (decisions log 2026-10-18, STRUCT-SORT parked). kink-flow takes only text edits: k-rust's K parser parses each edited rule text before the mutant is built (`kink-flow` `mutation`), so every mutant kink-flow scores is one some K text yields. A structural edit, an edit of kink's term tree rather than of text, is held only to compilation: kink-patch's operators (`OperatorSpec` with `Action::ReplaceHead` or `Action::Wrap`, and the other operators of `catalogue_v1`), the kink-corpus manifest's `operators` form and catalogue sweeps that apply them, and any `Patch` a library caller builds from terms. k-rust's compile checks the mutant's sorts and declarations, not that some K text parses to the edited rule, so a structural edit can build a mutant no K text yields. At main such an edit fails closed when it is ill-sorted (a compile refusal, or an infrastructure `error`), and none has been found `Killed`; the decisions log reopens the question if one is, or if structural edits become an input of the flow. A catalogue proposal for the flow is rendered as K text and parsed like any other edit.

Stack dependence (k-rust KINK-06/4 and KINK-06/5): k-rust can dismiss a stop for lack of stack silently, in the load's discharge of rewrite-rule definedness and its critical-pair check and in a run's refinement of a result, so a result could depend on the stack of the thread that loads the definition or runs the program, and on other threads.
For every comparison through k-rust's `execute`, the re-pin closes this: a run that reports a nonzero `stackStops`, or whose definition's load reports a nonzero `discharge_counts().stack_stops` or `value_claims().counts().condition_stack_stops` (read through `select_definition` on the backend that runs), is no evidence, on the baseline and on the mutant, live, on a reused baseline run and before any outcome is cached. A reused baseline run is judged under the load facts of the call that produced it together with the current call's (each call loads the definition again), and a run whose own load was excluded is never kept for reuse, only its exclusion.
What remains: under the Z3 profile a solver query can time out; k-rust now counts the undecided answers of a run (`smtUnknowns`, KINK-19/1), which kink carries and reports (re-pin adoption A-1: kink-flow's program rows and executed entries) but never reads as an exclusion (decision D-7 (a1): kink re-decides every leaf's feasibility itself, so an undecided answer can make a comparison unknown, never a kill), and the outcome cache (tier 1) stays off in a Z3 build; and kink's verdict path also calls k-rust outside `execute` (`definition_facts`, the unification of `BackendRelations`, the bridge's internalization of leaf states), whose determinism no k-rust promise states (re-pin finding B-13(a)). For kink-flow's ground programs these decide nothing a kill depends on.

Threads (re-pin L1-3, L1-3-fix-1): only relinking and compiling run on several threads. kink-flow (`run --compile-workers N`, 4 by default) and kink-campaign (`CampaignOptions::compile_workers`: kink-corpus passes 1, and kink-flow passes 1 to each of its one-mutant calls because it compiles across mutations itself) compile a chunk of mutants ahead (kink-native `NativeValidator::compile_ahead`: each patch is applied on the calling thread, in order, and a worker thread only relinks and compiles the applied mutant), join every worker, then run the chunk one mutant at a time in list (candidate) order on the calling thread, exactly as with one worker. Relinking and compiling are the only steps k-rust documents as independent of the thread: they read only their arguments and no process-wide input, several threads may run them at once on one shared loaded definition with each call returning what it returns alone, and every compile stage runs on a stack sized from the definition (k-rust `docs/compatibility.md`, "Concurrency"; `crates/k-rust/tests/compile_concurrency.rs`). Applying a patch is not among them: it types each edited rule with k-rust's `SentenceTyper::typing_in`, whose recursion has no stack guard, so on a worker's default stack a rule about 1,500 terms deep aborted the process where the calling thread's 256 MiB stack succeeds (review L1-3-1 D1; kink-native `a_deep_edited_rule_compiles_ahead_as_on_the_calling_thread`); since re-pin L1-3-fix-2 that typing runs on a stack sized from the rule's depth, but apply stays on the calling thread, in order. A compile refusal can depend on the calling thread's stack, so only a successful compile is taken from a worker and every refusal comes from the calling thread. Everything after compile that runs the simplifier stays sequential, outside every compile, and outside the watchdog where it is a load: the consistency check, every backend build (its load's critical-pair check and definedness discharge) and every execution, whose stack stops depend on the running thread's stack and on what other threads hold of the simplifier's process-wide stack budget ("Execute"; a stop refuses a mutant or excludes a run, so it would make a status or the score depend on the schedule). The worker count changes no status, row, report, record or hint (kink-campaign `tests/compile_workers.rs`, kink-flow `tests/compile_workers.rs`), only wall time and memory: on `examples/imp`, cold, mutant compiles are 28 % of the run, and 4 workers took 2.5 s off a 16 s run on average (8 paired runs on a shared host) while peak memory rose from 126 MiB to about 305 MiB; a warm run compiles nothing. The workers are capped at the host's parallelism and at half the process's memory allowance, which counts what a worker's share of a chunk holds at once: one compile in flight (an estimated 64 MiB plus 32 bytes per byte of the baseline's `definition.kore`) and the at most 8 mutants compiled ahead that it keeps (8 MiB plus 8 bytes per byte each, two to three times the 4.4-5.7 MiB measured on the small fixtures); `compile_ahead` keeps no more than 8 per worker, so the bound holds whatever a caller asks (`NativeValidator::compile_workers`, `KEPT_PER_WORKER`). The estimates are calibrated on small definitions and on k-rust's KEVM compile figure; no large definition was measured.

Deep terms (re-pin L1-3-fix-1, L1-3-fix-2, L1-3-tail): K bounds no term's depth, and a recursion that descends one level per term level overflows the thread it runs on, which aborts the process and loses every row of the run. k-rust guards or sizes its own recursions (loading, compiling, executing). kink's own are k-rust's typing of a rule (of an edited rule in `apply`, of every baseline rule when kink-patch resolves a universe or a sort-selected discovery), which has no guard, and serde_json's parse and serialization of kink's JSON, which nests two levels per term level; kink-patch measures each input's depth without recursion and runs that work on a stack sized from it (kink-patch `stack`; on the calling thread when enough of it remains), so the outcome is a function of the input and not of the thread (kink-patch `a_deep_rule_is_typed_alike_on_a_thread_too_small_for_its_typing`, `a_deep_patch_encodes_and_decodes_alike_on_a_thread_too_small_for_it`, kink-flow `deep_rules_are_judged_alike_on_a_thread_too_small_for_them`). Every reader of kink's JSON goes through kink-patch `parse_json`, and no JSON document kink reads or writes may nest deeper than `MAX_JSON_DEPTH`: 600,000 levels in a release build and 128,000 in the unoptimized test build, set so that dropping a document at the limit, the one recursion serde_json runs on the caller's stack, takes under half of the 256 MiB that kink's commands run on (`DEFINITION_STACK_BYTES`; a library caller handling documents that deep needs such a stack too). Past the limit a reader refuses the document with an error that names the limit, and each writer refuses to write it (kink-patch codec `CodecError::TooDeep`, which kink-flow reports as `edited-rule-too-deep`; kink-campaign's report; kink-corpus `Store::write_json`; a KORE test input as `inputs`/`too-deep`), so every reader accepts what its writer writes. The stack each step takes is sized from its own input's depth (a patch's from its document's exact depth, `Patch::document_depth`), so a shallow input never needs a large segment; when the host refuses a segment (an address-space limit such as `ulimit -v`), the refusal names the host and never the input: kink-flow reports the mutation as `error`/`host-stack-refused`, kink-corpus a KORE test input as `inputs`/`host-stack-refused`, and a rule's typing becomes a `not typed` diagnostic. The typing bound per level (kink-patch `TYPING_STACK_PER_LEVEL`) is set with a stated margin over the costliest of the term shapes measured, parametric productions included.

What a stored verdict is bound to (packets CACHE-ID and CACHE-ID-fix-1; kink-campaign `identity`): a stored verdict is honoured without re-deriving it only if the code that derived it is the code now running, and two identities say so.
kink's build identity, `kink_build`, is the SHA-256 of the running executable (decision D14-1 (a), first used by kink-flow's tier 1).
It guards all of kink's verdict code, including the code that has no version constant at all (the comparison and its Distinguish, the status fold, pattern-oracle matching, leaf adaptation, step events, feasibility, the census), and the linked k-rust; nothing has to be bumped for it to change.
kink's semantics identity, `kink`, is one object, `{k_rust_revision, fingerprint, canonical_patch, compiled_kore, patch_admission, claim_removal, mutant_consistency, mutant_effect, definition_exclusion, execution_request, result_schema, coverage, one_sided}`: it names the k-rust revision and kink's versioned algorithms (how a patch is addressed and admitted, no typing error refusing one since L2-2-fix-1; which claims a mutant loses; the consistency check; the compiled reading of an edit; the definition exclusions; the execution request, with state sets and their path-set replacement, no trace, run coverage, a cancellation as an error and the mutants' work budget, L1-1; what counts as a comparable flow result; how coverage is read; when a work-bound mutant run kills one-sidedly, L1-2 and L1-2-fix-1, kink-campaign `ONE_SIDED_VERSION`).
It is the human-readable part: a refusal names the first component that differs, and campaign manifests carry it, so campaign reports stay independent of the build.
Every store honoured without re-deriving its verdicts carries both and is refused or missed when either differs: each kink-corpus index entry and admission record names its writer's `kink_build` (outside the campaign report's bytes) and each campaign manifest names `kink`, so resume and summary refuse an entry of another build or identity, naming the build and the component, and summary reads an admission record of another build as missing; kink-flow's result key and tier-1 context hold both, so their records miss and are recomputed; kink-flow's warm-path memos (re-pin L1-4: a mutation's resolution facts and the specification's declaration census) key every record on both and on every input of the memoised value, so a record of another build, identity, specification or mutation text misses, and `run --verify` re-derives and compares every one; and `kink-flow report` refuses a run document of another build or identity.
Replay re-derives instead (it regenerates the manifest, re-runs the campaign and reproduces only byte-identical reports), so it needs no build binding; it still refuses another semantics identity in its environment check (`kink.<key>`) before regenerating anything.
kink-flow's killer hints carry neither: a hint decides no status.
An unreadable executable gives no build identity, and every honouring store then recomputes or refuses.
The rule for adding to the semantics identity: a constant whose change can change a verdict is a component (bump it whenever its algorithm changes what it decides); every other versioned constant (a `const` or `static` whose name ends in `_VERSION` or `_DOMAIN`, whose string value ends in `/v<N>`, `/v<N>.<M>` or `-v<N>`, or that names such a constant) is listed outside it with the path that checks it.
kink-campaign `tests/identity.rs` parses every kink member's sources and fails on a versioned constant in neither list.
A forgotten bump, or verdict code with no version, no longer lets a store be reused: the build identity changes with any edit that changes the executable.

Corpus resume: `kink-corpus run` resumes a definition whose completed campaign report is already in the store only when the index entry was written by this build (`kink_build`) with kink-corpus's run options (`run_options`, packet CACHE-ID-fix-1; every option is recorded, the one-sided rule's `one_sided` included, kink-campaign `RunOptions::value`, re-pin L1-2-land), and the report is checked against the manifest digest, the profile, the report and artifact digests, the report version and kink's semantics identity.
The store's bytes stay a function of its inputs except the writer's `kink_build` in each index entry and admission record, so the binary's and the library's stores differ only there (kink-corpus `tests/runner.rs`).
Any rebuild of kink therefore refuses every store an earlier build wrote: delete the store to rerun it with the new build.
`kink-corpus replay-check` re-derives a stored report instead, so it can check a store from another build.

**Checking a pattern.** When you write a program to exercise a situation, write the situation as a K pattern in `PATTERNS.toml` (`pattern = "<k> _:Int / 0 ~> _ </k>"`, as a rule's left-hand side is written) and claim the program hits it (`programs = ["divzero"]`).
`kink-flow query FLOW.toml PATTERNS.toml` answers, per (pattern, program), whether some run reaches a configuration that matches: `hit` with the matching configuration and the rules of a run to it, `no` (the claim is refuted: the program never does what you said it tests), or `unknown` with its cause.
A `no` needs the program's whole state space explored within the budget, a comparable baseline run and a definition that leaves no value to the implementation (decision 1's census), so a bounded or open run is `unknown`, never `no`; a `hit` needs only the run it found and a matched configuration k-rust shows defined (one holding an unevaluated call of a partial function is `unknown`), and stands under k-rust's choice of an open value and its strict reading of `andBool`, `orBool` and `#if`, one reading K allows.
Definitive answers are cached under a key that names the specification, the program, the compiled pattern, the budget and kink's build, `--verify` re-derives them, and no answer ever decides a mutation ([`crates/kink-flow/README.md`](crates/kink-flow/README.md), "Checking a pattern").

**Killing a survivor with `fuzz`.** When no program you can think of tells a survivor apart, take a program that reaches the edited rule (the run report's `reaching` lists them), mark its literals as holes in `TEMPLATES.toml` (k-rust-fuzz's `[[hole]]` keys), and run `kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID --kill MUTATION --mutations MUTATIONS.toml --no-confirm`.
It runs a k-rust-fuzz campaign in process on kink's own two sides (the admitted baseline and the claim-free mutant `run` would test) and prints the killing program as a `[[program]]` fragment; it never writes `FLOW.toml` or the cache.
Append the fragment and run `kink-flow run --only MUTATION`: only `run` decides the kill, with its own oracle.
The fuzz refuses up front what `run` could not confirm: a mutation `run` refuses, a definition exclusion on either side, a mutant that parses the template differently from kink's input (a `[macro]` edit), and a definition whose full critical-pair check has a finding you have not named (`--assume-joined NAME`, then `[spec] assume_joined`; every assumed name is printed beside the fragment as a premise, genuine ones flagged).
Each candidate's input is checked against kink's own assembly of the fragment, and the document warns about a template whose program is not comparable or does not reach the edited rule in the last run, suggesting the reaching programs as templates ([`crates/kink-flow/README.md`](crates/kink-flow/README.md), "Killing a survivor with `fuzz`").

### Commands

Every command prints one JSON document on stdout.
The exit status is 0 when the command did its job (survivors, timeouts and invalid mutations included),
1 when the manifest, the mutation list, the specification or a program is refused, a cache file cannot be written, or a corpus error stops a run,
and 2 on a usage error (message on stderr).

| Command | Does |
| --- | --- |
| `kink-flow check FLOW.toml` | Loads and admits the specification and parses every program; reports each refusal with its stage and reason. |
| `kink-flow results FLOW.toml [--verify] [--mutations MUTATIONS.toml]` | Fills the result cache for new or changed programs; lists every program's class, cause and baseline wall time (`wall_ms`) and every rule's coverage; `--verify` reruns every program and compares it with its cached result; `--mutations` also lists the rules no mutation of that list targets. |
| `kink-flow run FLOW.toml MUTATIONS.toml [--only ID]... [--verify] [--order cost\|corpus] [--compile-workers N] [--no-memo]` | Updates the result cache, resolves each mutation, runs the kill search, updates the outcome cache and the killer hints, and writes the report. The search tries the programs whose coverage witnesses an edited rule's edit first (they reached the rule, for an edit of its `requires`; they fired it, for any other edit), each group cheapest first (`--order corpus`: in `FLOW.toml`'s order); the order changes which killer is found first and the cost, never a status. `--verify` decides nothing from the outcome cache: it re-proves every cached outcome, reports each that differs (`mismatches`, exit 1) and writes no outcome and no hint. `--compile-workers N` compiles up to N mutants ahead of their turn (4 by default; 1 compiles each in its own call); it changes nothing but wall time and memory. A warm run reads the memos of what did not change (re-pin L1-4: each mutation's resolution facts, used only for a mutation tier 1 decides with no call, and the specification's declaration census, under keys that name every input, `kink_build` and `kink`); `--no-memo` reads and writes none, `--verify` re-derives and compares them. |
| `kink-flow report FLOW.toml` | Prints the last run's report again, byte for byte. |
| `kink-flow query FLOW.toml PATTERNS.toml [--only ID]... [--verify]` | Updates the result cache and answers each pattern on each program it claims (or on every program): `hit`, `no`, `unknown`, `invalid-pattern` or `error`, with the witness of a hit, refuted claims flagged; caches the definitive answers; `--verify` re-derives every answer and compares. |
| `kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID --kill MUTATION --mutations MUTATIONS.toml [--cases N \| --work W] [--seed S] [--max-work N] [--time-limit-ms T] [--assume-joined NAME]... [--one-path] --no-confirm` | Looks for hole values of a template that kill the mutation, on kink's own sides, and prints the killing program as a `[[program]]` fragment with its premises; writes nothing. Exit 1 also when the job is refused up front (a mutation `run` refuses, a definition exclusion, a mutant that assembles the template otherwise, unnamed findings). |

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

Coverage covers rewrite rules and equations alike: a `[function]` rule a program evaluates is covered too.
A rule none of whose compiled forms a run's coverage can name (a macro, alias or `smt-lemma` rule) is listed as `no-coverage-signal`, never as uncovered.
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
  "reaching": ["square"]
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

A survivor that no program can kill is an equivalent mutant: for example, swapping the operands of `+Int` changes no result.
Argue why, then drop it from `MUTATIONS.toml`.

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
- `reaching`: the comparable programs whose cached coverage witnesses an edited rule's edit: they reached the rule (k-rust `matched`) for an edit of its `requires`, and fired it (`applied`) for any other edit;
- `executed`: each program the mutant ran on, in order, with its `outcome` (`agree`, `distinguish`, `timeout`, `unknown`, `incomparable` or `error`) and, unless it agreed or distinguished, the `cause`; `cached: true` marks an outcome taken from the outcome cache (it comes first, and only agreements and kills are cached);
  `slots` names each oracle slot's outcome (`exit-stop`, `whole-term`), and a distinguishing slot's `sides`:
  for the exit stop each side's kinds (for example `["normal"]` against `["undefined-step"]`: the mutant applies a rule whose result is undefined, such as a division by zero, where the baseline ends),
  for the whole final configuration each side's number of final configurations and, on the killing program, the mutant's as KORE text (cut at 4000 characters, `truncated`);
  `wall_ms` is the mutant's run of the program and `baseline_ms` the program's baseline run, in milliseconds;
  a `timeout` cause says what k-rust returned when the bound fired (how many paths had ended and how deep the deepest went: many shallow paths suggest path explosion, one deep path non-termination), and an `unknown` cause the halt of each returned leaf (a `depth-bound` leaf means `max_depth` stopped it);
- `calls` and `call_wall_ms`: the programs of each runner call and its wall time;
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

- `results/<spec digest>/<program digest>.json`: one program's cached result (class, cause, baseline evidence, final configuration, rule coverage, and `wall_ms`, which orders the search and is part of no key);
- `outcomes/<context digest>/<mutation identity>.json`: one mutation's proved outcomes (`killed` or `agree`) per program, with an integrity digest per record;
  the context is kink's build, the k-rust revision, the solver profile, the specification digest, the budget and the oracles;
  a timeout, an unknown or an error is never cached;
- `hints.json`: each killed mutation's last killing program, keyed by the mutation's edits and its rules' text (no positions), a scheduling hint only (deleting it with `outcomes/` re-runs the searches cheapest killer first);
- `report.json`: the last run's report;
- `patterns/<spec digest>/<pattern digest>/<program digest>.json`: one cached pattern answer (`hit` with its witness, or `no`); `run` never reads it.

The specification digest covers every source file the specification loads, so editing the specification reruns every program and every mutation, each killed one first with its hint;
the program digest covers a program's text, start sort and variables, so editing a program reruns only that program.
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

A campaign manifest (`kink-campaign-manifest` v5) records the k-rust revision, the provenance format, the solver profile, the compile and backend options, the budget, the schedule, the operator id, version and policy, the baseline and per-mutant digests (SemanticInput, metadata-free structure, compiled KORE), the validation outcome of each mutant, and digests of the tests and the observation.
A campaign report (`kink-campaign-report` v4) embeds the manifest and adds the origins, each mutant's canonical patch, the affected sentences with old and new fingerprints, a normalized structural diff, the per-test oracle sides, the claims and the summary.
Both are canonical JSON with no wall-clock value and no absolute path, so repeated runs give identical bytes.

`replay` takes a report, the baseline artifact and the caller's declaration, including the selection code.
It checks the schema, the manifest digest, the build environment and the artifact digest, rebuilds every mutant from its canonical patch and checks its digests, then reruns selection and the campaign.
It returns `Reproduced` only when the regenerated report is byte-identical to the input; anything else is a refusal or a divergence, never a verdict.
Replay assumes the same kink build and operator code, no time bound firing in either run, and k-rust's provenance round trip and compilation determinism.

## Upstream requests

Requests kink makes of k-rust and KRS, and kink's premises on the in-repo k-rust, are recorded in the ledgers under [`upstream/`](upstream/README.md).

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

`kink/scripts/kink-tier.py` runs a tier of the kink packages (`-p` each package of `kink/crates`) with cargo-nextest from the root of k-rust's workspace (profile `kink` of the root `.config/nextest.toml`, which holds kink's overrides),
checks the run against the tier's budget from nextest's JUnit report (`target/nextest/kink/junit.xml` under the workspace root, where nextest writes it even when `CARGO_TARGET_DIR` moves cargo's build output),
and lints the tier markings: an ignored test outside a tier module would run in no tier, and a kink override of `.config/nextest.toml` that matches no test would stop applying.
Budgets are judged on a host whose load average is under half its CPUs, and only reported on a busier one.

Every commit to a kink crate must pass the gate tier in both solver profiles. From the root of k-rust's checkout:

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
KRUST_GATE_Z3=system with-z3-static-4.16.0 kink/scripts/kink-tier.py lint
KRUST_GATE_Z3=system with-z3-static-4.16.0 kink/scripts/kink-tier.py run gate
cargo clippy -p kink-native -p kink-campaign -p kink-corpus -p kink-patch -p kink-pattern -p kink-flow --all-targets --no-default-features -- -D warnings
kink/scripts/kink-tier.py lint --portable
kink/scripts/kink-tier.py run gate --portable
```

The heavy gate adds `kink/scripts/kink-tier.py run heavy` in both profiles.
`scripts/run-gates.sh kink` and `scripts/run-gates.sh kink-heavy` run the two tier pairs (`scripts/gates.toml`).
The tier script acquires Z3 as k-rust's gates do (k-rust `docs/testing.md`): by default its Z3 runs add k-rust's `z3-inference-gh-release`, which downloads the Z3 4.16.0 release at build time,
and `KRUST_GATE_Z3=system` links the Z3 the build environment provides instead, here the machine wrapper `with-z3-static-4.16.0`, which points the `z3-sys` build at a static Z3 4.16.0 library.
`--and EXPR` narrows a tier to the tests matching a nextest filterset, for example `--and 'package(kink-flow)'`, without judging the budget.
The Z3 profile runs every test of every kink package (`[z3]` of `kink/.config/kink-tiers.toml` says why no binary is skipped).
kink-flow's tests are profile-aware (merge packet M-1): its `z3` feature (default, forwarding to kink-native's) selects the Z3 column; a `no` that a complete exploration gives in the portable build is `unknown` under Z3, and the kink-tier and heavy tests whose subject is the outcome cache, the warm-path memos or the pattern cache (all off under Z3 by design; 32 kink-tier, 6 heavy) compile only in the portable build, while the Z3-only light test `kink-flow::outcomes both_caches_are_off_under_the_z3_profile` pins that both caches are off.
Under Z3 a run order can move a status only through an undecided solver answer that a reused backend's cache answers in another order; the order tests (`kink-flow::usability *_statuses_do_not_depend_on_the_order`) also check that no run of their fixtures takes one.
So the tier lint counts differ by profile: portable light 463, kink 482, heavy 132, external 7; Z3 light 463, kink 450, heavy 126, external 9 (the light and external columns also differ by tests that exist in one profile only, `cfg(feature = "z3")`).
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
A build that selects only kink packages with their default features takes k-rust's `z3-inference` alone, which links the Z3 the build environment provides (without `with-z3-static-4.16.0` or another provider it fails to link, `-lz3` missing);
a build that also selects k-rust with its default features (`cargo clippy --workspace`, `cargo nextest run --workspace`) takes k-rust's `z3-inference-gh-release`, which downloads the Z3 4.16.0 release into the build script's output directory once per target directory.

The dev and test profiles are k-rust's (the root `Cargo.toml`): the workspace at `opt-level = 1` with line tables only, dependencies at `opt-level = 3`;
debug assertions and overflow checks stay on for every package.
For a debugger session that shows local variables, use the `debugging` profile (`cargo test --profile debugging`).

## Retired tooling

The earlier official-K "G-track",
its TypeScript/Bun probes and the oracle were removed from the tree.
The local tag `archive/g-track-2026-08` marks the last commit that contains them.
