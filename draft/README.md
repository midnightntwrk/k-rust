# KRS design draft

KRS is a proposed Rust-shaped language for authoring definitions for the
[K Framework](https://kframework.org/). It should let a reader who knows Rust
form a mostly correct mental model of a semantics without first learning K's
surface language, while retaining the capabilities needed by real K projects.

This directory is a pre-implementation design notebook. The semantic design is
now consolidated; exact macro punctuation and implementation details still
need the bounded validation work listed in the authoritative design.

## Documents

- [design.md](design.md) is the authoritative synthesized design and the
  starting point for implementation.
- [charter.md](charter.md) defines the goal, compatibility promise, scope, and
  implementation direction that led to the design.
- [design-sketch.md](design-sketch.md) shows a candidate Rust-to-K mapping and
  records the original candidate mapping. It is being superseded by the
  investigation decisions and should not be treated as authoritative where
  they differ.
- [semantic-gaps.md](semantic-gaps.md) inventories K features for which the
  obvious Rust analogy is incomplete or misleading.
- [research-backlog.md](research-backlog.md) records the completed investigation
  ledger and the bounded implementation-validation queue.
- [implementation-plan.md](implementation-plan.md) orders that queue into
  build milestones with crate boundaries and exit gates.
- [orchestration.md](orchestration.md) defines how Sol implementation agents
  are assigned, isolated, integrated, and gated across those milestones.
- [`investigations/`](investigations/) contains the completed evidence and
  decision records for those questions.

## Settled design summary

1. A KRS definition is a genuine Cargo crate. Real procedural attributes and
   macros preserve a rustc-valid host and emit descriptors for one shared KRS
   analyzer; K-only patterns and logic remain in explicit macro islands.
2. Open K sorts are attributed trait declarations. Attributed constructors
   declare membership, and the KRS analyzer closes the subsort graph as a
   path-independent relation, including legal diamonds. Rust blanket impls do
   not encode transitive membership; enums remain closed constructor families.
3. One K rule is one independently named, refutable `#[k::rule] fn` clause. Its
   parameter is a pre-pattern and its single result expression is a
   post-pattern; it is not a callable function and rules have no source order.
4. Nominal productions use structs/enum variants plus syntax attributes;
   grammar relationships and non-nominal productions use typed macro items.
5. Fixed configurations use nested structs. Cell collections, K sequences,
   associative collections, cell fragments, and matching logic use dedicated
   typed wrappers or macro patterns rather than pretending to be Rust values.
6. Object `Term<Bool>` conditions and matching-logic `MlPattern` are distinct.
   Partial K functions denote bottom when undefined and never use
   `Option::None` for that purpose.
7. The compiler owns a source-level K Definition IR. It can adapt this to the
   structured `k-rust` frontend or emit inspectable `.k` for any compatible K
   implementation; KRS does not generate Kore itself. The current Java
   frontend is a differential oracle, not a user-selected target.
8. Evaluation strategy uses typed production attributes, explicit contexts and
   context aliases use zero-return refutable clauses, and static desugaring,
   aliases, simplifications, and `anywhere` remain distinct sentence kinds.
9. Rust `use` is lexical only. Definition facets control theory composition,
   builtins come from a K-pin-specific compiler sysroot, and one lockfile pins
   the whole K/pyk toolchain.
10. The explicit notation is a stable reference surface. The host macros have
    transparent ordinary-Rust descriptor expansions; the later corpus study
    decides which additional ergonomic macros are readability wins.
11. The native `k-rust` integration is commit- and K-pin-specific. KRS retains
    its own IR and explicit frontend capabilities rather than inheriting an
    evolving frontend's AST as its language ABI.
12. Cargo owns packages, features, modules, and Rust dependencies. KRS adds a
    deterministic host collector, whole-theory checks, K-specific editor help,
    and supplemental external-K locking; it does not duplicate Cargo's graph.

These decisions are the result of challenges against IMP, KWasm, KMIR, KEVM,
the K user manual, and K 7.1.337's frontend and backends. See
[design.md](design.md) for the complete contract. Exact macro spellings remain
subject to the implementation spike, but the semantic boundaries are firm.

## Local sources

The source selection is explained in
[`good-k.md`](../../inspirations/runtimeverification/good-k.md). The initial
design pass uses:

- [IMP](../../inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics/imp.k)
  as the minimal end-to-end semantics;
- [KWasm](../../inspirations/runtimeverification/wasm-semantics/pykwasm/src/pykwasm/kdist/wasm-semantics/wasm.md)
  for readable examples of extensively reopened syntax sorts;
- [KMIR](../../inspirations/runtimeverification/mir-semantics/kmir/src/kmir/kdist/mir-semantics/kmir.md)
  for current rule and configuration conventions; and
- the [K user manual](../../inspirations/runtimeverification/k/docs/user_manual.md)
  as the feature-level source of truth; and
- [`k-rust`](../../inspirations/midnightntwrk/k-rust/README.md) as a
  Rust-native structured frontend adapter and a second implementation oracle.
