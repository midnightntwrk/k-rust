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
- Release and CI checks prove that the default executable path has no runtime dependency on
  `kore-exec`, `kore-rpc`, or `kore-rpc-booster`.

Incremental checkpoints may implement narrower vertical slices, but they do not reduce this
completion contract.
