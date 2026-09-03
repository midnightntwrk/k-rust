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

- `k-rust-kore`: host-independent KORE syntax, parser, printer, and serialization shared across
  the frontend and backend.
- `k-rust-backend`: definition verification and internalization, matching, substitution,
  simplification, SMT reasoning, and rewriting. It depends on `k-rust-kore`, not on the frontend.
- `k-rust`: the K frontend and the unified `krust` binary. It compiles K to KORE and invokes
  `k-rust-backend` directly in the same process.

Keeping the backend independent from frontend ASTs preserves KORE as the semantic boundary while
avoiding a package dependency cycle when the CLI links both halves into one static binary.

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
Execution, search, and proof configuration simplification follow Booster's exhaustion outcome: they retain the partial term or the original unsimplified constraints, record a `SimplificationBudgetExhausted` diagnostic, and continue.
The standalone term simplifier and nested side-condition evaluation retain typed `IterationLimit` errors.
The backend does not yet implement Booster's separate equation-loop detector, so a genuinely non-terminating equation set may produce a partial configuration with a diagnostic.

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

A rule whose left-hand side matches and whose `requires` holds has applied even when its result is
empty (an `ensures false` or bottom right-hand side). Lower priorities and `owise` do not see that
sub-case. This follows kore-exec semantics and arbiter row 1; Booster's `OnlyTrivial` fall-through
is intentionally not mirrored, and the RPC differential excludes that oracle-specific shape.
