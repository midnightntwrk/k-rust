# Backend-agnostic investigation completion audit

Status: refreshed BAG-11 witness-order and complete-denotation coverage and
BAG-12 typed-oracle and inline-expectation integrity are independently
accepted. BAG-13 rejection findings remain repaired, and BAG-14 awaits its own
independent preflight, 26 August 2026.

This audit closes only work whose result can remain valid across execution
backends. It does not treat a Python fixture oracle as implementation evidence
for the future Rust frontend, semantic IR, lowering, executor, solver, or
runtime.

## Completion test

The package is complete when every acceptance requirement for execution-pattern
matching and semantic mutation has one of three explicit dispositions:

1. a portable contract plus schema, fixture, vector, or verifier evidence;
2. bounded historical evidence whose exact claim remains recorded; or
3. a named Rust-required proof that cannot be established without real stack
   behavior or measurements.

No finding may remain merely “future work” if it can still be settled through
backend-neutral identity, denotation, status, ordering, integrity, or failure
semantics.

## Current audit packets

- Execution, observation, corpus, and replay integrity: pending independent
  audit.
- Mutation, patch, campaign, and artifact-graph integrity: pending independent
  audit.
- Artifact identity/resolution now has separate semantic and byte roots, a
  closed role registry, strict locator/resolver rules, bundled canonical and
  opaque positives, derived replay closure, and permanent boundary
  adversaries. The integrated resource-capped zero-backend run passes 397,474
  serial checks, and the separate official-only Draft 2020-12 schema and
  fixture validation passes. Independent claim review remains pending.
- BAG-10 closes the entry-centric failure taxonomy, exact failure-site
  inventory, bidirectional finite placement reachability, diagnostic-only
  details boundary, and the checked lowering-cycle receipt protocol. Its toy
  checker proves only protocol conformance; real lowering proof remains with
  Rust. BAG-12 adds the exact `oracle-operand-production` context and four
  outer-failure placements; schema-to-taxonomy and taxonomy-to-schema
  reachability are exact for this packet. BAG-15/BAG-16 must rerun that proof
  when adding production or branch-collection placements.
- BAG-13 closes `portable-mutation-semantic-slice-v1` and every locally
  decidable term, signature, variable-scope, condition, attribute, and
  generated-provenance invariant. Patch output is atomically subjected to the
  complete portable definition checker with immutable baseline signatures;
  traces, terminals, and structured oracle values resolve exact definition
  identities; and each path's predicate, event payloads, and all witness
  bindings share one graph scope. It does not claim a complete K definition
  adapter: native form coverage, declaration tables, supported-surface
  injectivity, and native IR validity remain RS-01/RS-02 Rust proofs, with
  unsupported or lossy forms required to reject.
- BAG-11 closes portable query identity and finite denotation without widening
  that claim boundary. K source, normalized plan, and named query have
  separate role-typed identities; event vocabulary and side-table keys are
  derived over exactly the declared ordered input subset, including constant
  empty interfaces; variable declarations retain witness-binding grammar and
  nonlexical order; every persisted witness set is rederived including arm
  zero; and catalog-resolved corpus, replay, mutation-oracle/test, cache,
  policy, campaign, and report identities retain exact ordered selections and
  repetitions. K compilation, compiler-receipt correctness, solver
  evaluation, and source/plan equivalence remain future Rust proof. Retired
  whole-trace evidence remains historical only. Stable keyed witnesses now
  sort by path key, then semantic occurrence indices, binding digest, and arm
  ordinal; the occurrence replay digest is identity, not ordering authority.
  A persisted two-occurrence adversary permanently rejects replay-hash order
  selecting a later primary, and the verifier denotationally rederives every
  active-catalog pattern result whether or not another campaign consumer
  happens to select it.
- BAG-12 closes the portable semantics of all six admitted oracle kinds. The
  published manifest has one authority: ordered per-test
  `oracleDeclarations`; the active catalog contains typed declaration,
  operand, comparison, gate, evaluator-conformance, reachability, predicate,
  and semantic-output roles. Legacy projection/comparison/value roles survive
  only in the immutable execution-catalog snapshot needed by older
  corpus/replay identities and cannot authorize live mutation decisions.
  Declaration, operand, comparison, gate, reachability, predicate, and
  evaluator records have exact self-ID domains and role-typed resolution.
  The selected corpus and observation vocabulary are resolved only through
  the active catalog; every current test invocation is rederived. One shared
  side validator binds gates, comparisons, and outer results to the exact
  declaration, subject, test, profiles, terminal/crash, and producer attempt.
  Concrete-output media types and bytes, reachability side conditions and
  exact term sorts, predicate input provenance, and BAG-10 outer-side absence
  relations are all rederived. Inline normal expectations are schema-
  discriminated by kind and undergo the corresponding active-catalog,
  definition, projection, and derived-field validation before comparison; all
  nine built-in pairs have positive inline vectors, and one six-kind adversary
  rejects provenance drift that the comparator deliberately projects away.
  Incomparable results retain both sides and the
  exact comparison while carrying the taxonomy-bound failure. Gate rejection
  aborts scoring, and score counts and exclusions are rederived. All 36
  advertised drift cases execute exactly once as rejection tests; the
  inventory is not accepted as evidence by itself.
  Portable built-ins and exact finite rows are the only zero-backend decision
  authority. Native K-authored evaluation still requires both a matching
  conformant evaluator record and BAG-15 production evidence; BAG-16 still
  owns native exhaustive branch collections.
- Evidence inventory, checklist, contracts, and Rust handoff are updated for
  this repair. D1 and roadmap are intentionally outside this packet. Fresh
  independent BAG-11 and BAG-12 acceptance found no remaining blocker; this
  does not substitute for BAG-14's own preflight or later packet gates.

The final revision will replace the remaining pending entries with
finding-by-finding results and list the residual Rust-only questions.
