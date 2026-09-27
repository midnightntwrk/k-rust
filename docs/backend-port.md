# In-process backend port

This document tracks the port of Runtime Verification's Haskell backend to idiomatic Rust. The
reference checkout is intentionally ignored and is used as a behavioral oracle rather than as a
build dependency.

## Reference

- Repository: `runtimeverification/haskell-backend`
- Commit: `ad54c7a55085b726c4d3c2728242a7e0695b0439`
- Described version: `release-0.1.155-1-gad54c7a55`
- Local checkout: `haskell-backend/`

The current reference is a two-engine system. Booster provides the fast execution path, while Kore
provides the complete fallback for cases Booster cannot decide. The Rust implementation must port
the semantics of that combined system; reproducing Booster's incomplete subset without its Kore
fallback is not completion.

## Crate boundaries

The intended workspace structure is:

- `k-rust-kore`: host-independent KORE syntax, parser, printer, serialization, pattern traversal,
  and encoding sniff shared across the frontend and backend, the measurement counters
  (`k_rust_kore::measure`) every crate
  increments, and the well-known KORE identities (`k_rust_kore::names`: the `inj`, `kseq`,
  `dotk`, `append`, `rawTerm` symbols and the builtin sorts both halves test for). A spelling
  that crosses the KORE boundary lives there once; the frontend and the backend compare
  through its predicates instead of repeating the string.
- `k-rust-backend`: definition verification and internalization, matching, substitution,
  simplification, SMT reasoning, and rewriting. It depends on `k-rust-kore`, not on the frontend.
- `k-rust`: the K frontend and the unified `krust` binary. It compiles K to KORE and invokes
  `k-rust-backend` directly in the same process. `k_rust::backend` is the orchestration layer
  called by the CLI, RPC server, NAPI binding, and WASM binding.

Keeping the backend independent from frontend ASTs preserves KORE as the semantic boundary while
avoiding a package dependency cycle when the CLI links both halves into one static binary.

The public `Backend::execute` result carries the ordered effects committed on each `ExecutionLeaf`, including when observation is disabled.
`ExecutionResult.effects` is a compatibility copy when execution retains exactly one leaf; it is empty for multiple leaves, whose effects remain on their respective leaves.
An observed transition's effects attribute committed branch effects to that activity.

## Compiled rule catalog

`Backend::rule_catalog(module_name)` returns the compiled axioms of the same module selection used by execution.
Passing `None` selects the backend's default module.
Each `CompiledRuleOutput` has an `id`, a backend-classified `kind` (`rewrite`, `function-equation`, `simplification`, or `definedness`), `executable`, `label`, `priority`, `origins`, and `sharedIdentity` in JSON.
The catalog includes non-executable axioms with `executable: false`.
Each origin contains the backend's `Source` and `Location` attribute strings when present; it is not an input-sentence address.
A written sentence's kind is found by matching its source and location against an entry's origins.
A position absent from the catalog compiled to no axiom in the selected execution definition.
Equivalent written axioms form one entry with all origins in declaration order.
If distinct entries share an id, both have `sharedIdentity: true`, and the observation filter refuses that id as ambiguous.
The Node-API and WebAssembly TypeScript facades expose the same catalog through `backend.ruleCatalog(moduleName?)`.

## Module map

Run `cargo run -p algo-graph -- render module-map` to write the generated backend module-map projection to `target/algo/module-map.md`; it groups source-card algorithm IDs by their declared `k-rust-backend` site module and derives each module's counters from the graph's `measured-by` edges.

Rewrite theory lookup first preserves the top-symbol `TermIndex` sequence, then filters it by the
head of the generated `<k>` cell. The rule-side `RuleIndex` treats variables, overload members,
associative and idempotent heads, and missing or uncertain cells as wildcards; the subject side
also treats function heads and configurations with multiple `<k>` cells as uncertain, which
disables filtering. This is an over-approximation of matching: every rejected
candidate has a rigid incompatible head, while every retained candidate stays in its prior
priority and declaration position. Function, simplification, and ceil theories continue to use
only `TermIndex`.

## Behavioral slices

The port proceeds in dependency order, with differential tests against the pinned Haskell source
or its checked-in fixtures at every boundary:

1. KORE definition sharing and backend internal terms, symbols, sorts, and attributes.
2. Capture-avoiding substitution, sort-aware matching, injections, and internal collections.
3. Definition verification and internalization into indexed rewrite and equation theories.
4. Builtin evaluation and equation simplification to a fixed point.
5. Priority-aware rewrite steps, side conditions, branching, and execution bounds.
6. Z3-backed satisfiability, implication, model queries, and symbolic path constraints.
7. User-facing execution in `krust`, with the in-process backend selected by default and LLVM
   retained only as an explicit alternative compilation target.

## Completion contract

The port is complete only when all of the following are demonstrated from the current tree:

- `krust` can compile and execute representative K definitions without launching or dynamically
  linking the Haskell backend.
- The native binary includes frontend Z3 inference and backend SMT reasoning in-process.
- Supported concrete and symbolic executions agree with the pinned backend on final patterns,
  substitutions, predicates, branching, halt reasons, and rule traces.
- Function and simplification equations, rewrite priorities, injections, builtin collections, and
  relevant K hooks are covered by differential tests.
- Unsupported behavior is not silently reported as stuck or successful.
  A hook without an evaluator or applicable equations halts with a typed unsupported-hook error when every argument is constructor-like; symbolic applications remain unevaluated.
- Release and CI checks prove that the default executable path has no runtime dependency on
  `kore-exec`, `kore-rpc`, or `kore-rpc-booster`.

Incremental checkpoints may implement narrower vertical slices, but they do not reduce this
completion contract.

## JSON depth policy

The standalone KORE JSON and KAST term JSON readers and writers impose no nesting-depth limit; memory is their only parser bound.
The Node-API and WebAssembly backend request readers, the CLI KORE readers, the KORE RPC transport and payload reader, the backend facade, and the structured KAST definition reader all disable serde's default recursion limit or delegate to the iterative syntax codecs.
The RPC `KoreJson` payload uses `RawValue`, but the surrounding RPC frame and the backend and JavaScript host contracts intentionally retain `serde_json::Value`.
Those retained values still use recursive serialization and destruction, so their practical capacity is set by the host thread: roughly 200,000 JSON levels on the 64 MiB RPC workers, 50,000 on the 16 MiB WebAssembly test host, and 3,000 on Node's main thread.
KAST term traits and text codecs remain stack-bounded at roughly 80,000 levels on an 8 MiB thread, 160,000 on a 16 MiB thread, and 10,000 on Node's main thread.
Backend pattern internalization and backend term passes retain the 64 MiB CLI and RPC worker envelope.
No RPC or host surface applies a denial-of-service depth cap; process memory limits belong to the embedding application or process supervisor.

## Simplification iteration budgets

The backend limits simplification per fixed-point lineage rather than counting whole-pattern passes as Booster's `--equation-max-iterations` does.
The budget bounds the simplifier's own fixed point: rounds that apply simplification rules or builtins, and function equations over symbolic redexes or with residual definedness or `ensures` obligations, where a cut leaves a term equal to the input.
A function equation applied to a variable-free redex whose conditions are decided and whose result carries no constraint is a step of the definition's own computation with a determined value; it consumes no budget, because a cut there could only leave the application unevaluated and execution `Stuck` at a configuration the definition does not produce.
Determined ground function evaluation therefore runs to its value, bounded only by the caller's step deadline or cancellation and by the thread's stack (the typed `StackExhausted` error below); no default option bounds it, as no default option bounds the rewrite depth.
Execution, search, and proof configuration simplification follow Booster's exhaustion outcome: they retain the partial term or the original unsimplified constraints, record a `SimplificationBudgetExhausted` diagnostic, and continue.
Execution records every backend diagnostic on the `ExecutionLeaf` of the path whose work emitted it (`ExecutionLeaf::diagnostics`), each distinct diagnostic once per path in first-occurrence order: a state's own constraint and term simplification belongs to its path; in the rewrite step, each unit of work belongs to the candidates derived from its result, in emission order: a right-hand-side alternative's construction to its candidate, one application group's matching, recovery and conditions (a match split yields one group per sub-case) to that group's candidates and to the remainder, whose constraint negates the group's applicability, and the remainder's simplification and the lower-priority work on it to the remainder and the candidates derived from it; a step that halts the state belongs to its leaf; the simplification of a leaf or candidate pattern to that leaf or candidate. A branch or cut-point leaf is the parent state: it carries the parent path's diagnostics, and each candidate it reports carries its own (`AppliedRule::diagnostics`, `RemainderBranch::diagnostics`). Work no reported successor is derived from (a rule attempt that does not apply, an alternative refuted to bottom, a group the sequential step does not follow) is on no leaf, although a surrounding collector sees it; a leaf cut off by a cancellation or timeout after the step carries the work of the step and of its candidates done before the interruption. A leaf merged with equal final leaves keeps its own list, as it keeps its trace and branch.
The public execution response serializes a nonempty leaf `diagnostics` list as typed `BackendDiagnosticOutput` entries. Predicates in those entries use the same KORE JSON encoding as other wire predicates. An absent list means that path emitted no diagnostic.
For a `branch` or `cut-point` leaf, the response also serializes its reported successors as `candidates` with each candidate's constrained `state`, rule `uniqueId`, optional `label`, and own `diagnostics` list; a branch's remaining candidate is `remainder` with its constrained `state`, `ruleIds`, and diagnostics. The leaf's `diagnostics` remains the parent path's list.
Search attributes diagnostics by the same rule. Each state-set result (`SearchState::diagnostics`) and path witness (`PathWitness::diagnostics`) carries the list of the path its `trace` records: the simplification of each state on the path, the rewrite-step work each successor on the path was derived from, the externalisation of the reported copy (which the work state that continues the search does not inherit), and, for a state ending in a halting step (`Stuck`, an indeterminate or failed step, a cancellation after the step), that step's work. When state-set search deduplicates converging states, the kept state reports the recorded path's list, as it reports its trace; a dropped duplicate's own work is on no entry. The work of the rewrite step `state_may_expand` runs only to classify a result bound is on no entry. An `IncompleteSearch` entry carries the list of its state's path through that state. Matching a result against a pattern-search target is work on the match, not on the path: a `SearchMatch` or `PathSearchMatch` records it in its own `diagnostics`, apart from its state's or witness's list; an undecided match has no match entry, so its incomplete entry's state carries the path's list followed by the match's. Budget exhaustion is not an `IncompleteSearch` entry: it loses no successor. The public search responses serialize these lists as optional `diagnostics` on `SearchStateOutput`, `PathWitnessOutput`, `SearchMatchOutput`, and `PathSearchMatchOutput` with the same typed encoding as execution leaves. The KORE RPC responses are unchanged.
A caller collecting with `diagnostic::collect` around an execution or a search still receives every diagnostic in emission order: a nested collection forwards each emission to the enclosing collector as if it had been emitted there directly, also when the collected operation unwinds.
The standalone term simplifier retains typed `IterationLimit` errors.
An equation's side conditions (its `requires`, the definedness obligations of its bindings, and its `ensures`) are decided in their unsimplified form when simplifying them exhausts the budget, which may leave the equation unapplied; that exhaustion is recorded as a `SimplificationBudgetExhausted` diagnostic over `Predicates` followed by a `RuleConditionUnsimplified { rule_id, limit }` diagnostic naming the rule, once per rule and limit in a collection, and once per rule and limit on an execution leaf's path, where a `RuleConditionUnsimplified` follows (not necessarily directly) the exhaustion over `Predicates` with the same limit that it qualifies.
The backend does not yet implement Booster's separate equation-loop detector, so a non-terminating set of simplification rules, or a function unfolding over a symbolic argument, may produce a partial configuration with a diagnostic; a non-terminating ground function computation runs until the caller's step deadline or cancellation ends it, or ends with `StackExhausted`.

## Simplification stack depth

Simplification recursion depth is bounded by the native stack of the thread that runs it, not by a depth count or the iteration budget, which restarts for every equation condition and does not count determined ground function steps.
The simplifier reads the current thread's stack bounds at every fixed-point round and predicate entry and stops with the typed error `SimplificationError::StackExhausted` when less than a 128 KiB red zone remains, instead of overflowing the stack, which would abort the process.
The guard covers every native thread, whoever created it: CLI and RPC workers, Node-API calls on Node's JavaScript thread, and embedders' own threads.
On wasm32 the engine's call-stack limit is invisible to the module, so the guard is absent and exhaustion is a trap reported to the JavaScript host.
Ground function recursion reaches about 26,000 levels on a 64 MiB release thread (about 2.5 KiB per level in release builds and 16 KiB in debug builds).
Exhaustion is reported, never decided: an equation condition, definedness obligation, or `ensures` whose simplification is cancelled, interrupted by the step deadline, or runs out of stack propagates that error instead of being decided unsimplified, and `KeepPartial` budgets do not absorb it.
Execution ends the state with `Simplification(StackExhausted)`, a proof records an indeterminate leaf with that error, KORE RPC `execute` and `simplify` answer with a runtime error and `implies` with an implication-check error while the connection keeps serving, and the CLI prints the error and exits nonzero.

## Final search depth cuts

FINAL search treats `--depth N` as a cut of the execution graph.
A simplified configuration at depth `N` is a result without an additional rewrite attempt, including the initial configuration when `N` is zero.
A configuration below the bound is a result only when no rule applies.
Configurations whose constraints simplify to false and whole-state trivial or vacuous outcomes are not results.
The host backend retains `DepthBound` as an incompleteness signal for accepted frontier configurations; the CLI does not render that signal as an error.

Under strategy `all` without `stop_at_branch`, every path explored within `max_depth` and `max_breadth` ends in exactly one leaf before final merging.
A rule application with an empty result beside other applications of the same step ends no configuration; when observed, it is recorded in `discarded`.
The result has one of two readings, selected by `result_modality` and reported on the result as `modality`.
A `state-set` result (the default) is the disjunction of those leaves' configurations, merging structurally equal configurations, including depth- and breadth-bounded frontiers.
Merging loses no state: two leaves with one term, one constraint set, one effect journal, and one console state have the same future.
The first leaf in depth-first order retains its trace and halt reason.
Whole-state trivial and vacuous leaves carry no final configuration and are never merged.
A `path-set` result is those leaves unmerged: every explored path is exactly one leaf, with the same empty-result exception, and paths that converge on one configuration each keep their own trace, branch identity, observations, and halt reason.
The deduplicated configurations of a path-set result are the configurations of the state-set result, and exploration is identical under both.
An execution leaf's predicate implies the definedness of every partial term that a `requires`, `ensures`, right-hand side, or simplified state relied on along its path, with and without Z3, subject to the initial-state assumption below.
An instance excluded by a `requires` belongs to a remainder; an instance excluded by a carried right-hand-side definedness obligation or an `ensures` has no leaf.
With `assume_state_defined: true`, the initial state's definedness is assumed and need not be restated in the leaf predicate.
Builtin hooks are strict in every argument, including `andThenBool`, `orElseBool`, and `#if`, in concrete and symbolic evaluation; a value returned after a shortcut still carries the definedness of its arguments.
A rule or equation condition states the definedness of its Boolean terms when instantiated, before simplification or solver decisions can discharge the condition.
The contract interprets `total`, `functional`, and `preserves-definedness` attributes as part of the definition's meaning; a definition that declares a partial function total or falsely claims preservation is outside it.
The public-path [symbolic definedness tests](../crates/k-rust/tests/symbolic_definedness.rs) cover rule conditions in both solver profiles and the `assume_state_defined` modes; [rewrite tests](../crates/k-rust-backend/tests/backend/rewrite.rs) cover discarded hook operands and their leaf obligations.
`ExecutionResult.effects` holds the transcript only when exactly one leaf remains, which under `path-set` means one explored path.
The CLI and KORE RPC `execute` produce state-set results.
A `stuck`, `trivial`, `vacuous`, or `terminal` halt ends a path; `branch`, `cut-point`, `depth-bound`, and `breadth-bound` mark a frontier; `indeterminate`, `unsupported-hook`, `simplification-error`, `timeout`, and `cancelled` mark a failure.
Strategy `any` commits the first applicable rule of a step and makes no coverage claim, but it keeps that rule's right-hand-side alternatives and passes a symbolic remainder to later rules, so it can produce several leaves; `result_modality` applies to whatever leaves it produces, and the two readings coincide whenever no two of those leaves share a configuration.
With `stop_at_branch`, execution stops at the first branch point and reports its successors inside the branch halt.
For the same request, `Backend::execute` and `Backend::execute_observed` return leaves in the same order, equal in every field except `branch` and `observations`.
Unobserved execution leaves `branch` empty.
Observed branch identities do not depend on the rule filter: `ObservedRequest.rules = Some(vec![])` yields every identity and no observation events.

Printed execution, search, and pattern-match disjunctions use the structural order of the externalized KORE pattern; the order of an `\or` is not part of the compatibility contract, and differential gates compare its disjuncts as a multiset.

The backend facade exposes each execution leaf's halt reason as `HaltReasonOutput`, serialized with the same kebab-case reason in JSON.
Consumers may match the Rust enum exhaustively.
`detail` is human-readable context and must not be parsed as a halt class.
An `indeterminate` execution leaf carries `cause`, the structured reason the step stopped, with the same encoding as `IncompleteSearchOutput::Indeterminate.reason`.
Other leaves omit `cause`; `detail` remains legacy human-readable context.
The reachable causes are `surviving-macro-or-alias` (preprocessing left an executable symbol), `match` (unsupported unification remainder), `instantiation` (unbound rule variable), `requires` (undecided rule condition with no solver), `smt` (an undecided rule query), and `remainder` (an undecided priority-group remainder).
`SearchFailureOutput::solver_unavailable()` is true for `requires`, and for `smt`, `smt-predicate`, or a `remainder` satisfiability error whose SMT failure is `unavailable`.
It says this step needed a solver absent from the build; it does not promise that a solver-enabled build decides the path, and a `match` cause may depend on an earlier equation left unevaluated without a solver.
`UndecidedCondition` and `UndecidedPredicate` diagnostics report a solver that was asked and could not answer, never the absence of a solver.

A rule whose left-hand side matches and whose `requires` holds has applied even when its result is
empty (an `ensures false` or bottom right-hand side). Lower priorities and `owise` do not see that
sub-case. [Trivial rule results](compatibility.md#trivial-rule-results) gives the reason and the RPC differential row that records the Booster divergence.
When every execution leaf is dropped as trivial or vacuous, the CLI reports each leaf's depth, applied rule when available, and refuted obligation on stderr while retaining the `\bottom` result and exit status.
See [compatibility decisions](compatibility.md) for the source evidence, regression homes, and policies covering engine disagreements, supported frontend extensions, CLI scope, and reference exclusions.
