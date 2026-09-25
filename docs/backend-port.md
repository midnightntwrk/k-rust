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
Execution records every backend diagnostic on the `ExecutionLeaf` of the path that emitted it (`ExecutionLeaf::diagnostics`): the diagnostics emitted while one state is expanded are appended to its path's list, which the leaf it becomes or each successor it hands on carries, in first-occurrence order with each distinct diagnostic once per path; a leaf merged with equal final leaves keeps its own list, as it keeps its trace and branch.
A caller collecting with `diagnostic::collect` around an execution still receives every diagnostic in emission order: a nested collection forwards what it collected to the enclosing collector under that collector's once-per-collection rules.
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

Execution collapses structurally equal final configurations, including depth- and breadth-bounded
frontiers, while preserving the first leaf's trace and halt reason. Whole-state trivial and vacuous
leaves carry no final configuration and are not merged. Printed execution, search, and pattern-match
disjunctions use the structural order of the externalized KORE pattern; the order of an `\or` is not
part of the compatibility contract, and differential gates compare its disjuncts as a multiset.

The backend facade exposes each execution leaf's halt reason as `HaltReasonOutput`, serialized with the same kebab-case reason in JSON.
Consumers may match the Rust enum exhaustively.
`detail` is human-readable context and must not be parsed as a halt class.

A rule whose left-hand side matches and whose `requires` holds has applied even when its result is
empty (an `ensures false` or bottom right-hand side). Lower priorities and `owise` do not see that
sub-case. [Trivial rule results](compatibility.md#trivial-rule-results) gives the reason and the RPC differential row that records the Booster divergence.
When every execution leaf is dropped as trivial or vacuous, the CLI reports each leaf's depth, applied rule when available, and refuted obligation on stderr while retaining the `\bottom` result and exit status.
See [compatibility decisions](compatibility.md) for the source evidence, regression homes, and policies covering engine disagreements, supported frontend extensions, CLI scope, and reference exclusions.
