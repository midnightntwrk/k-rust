# Backend-agnostic investigation completion audit

Status: refreshed BAG-11 witness-order and complete-denotation coverage and BAG-12 typed-oracle and inline-expectation integrity are independently accepted.
BAG-13 rejection findings remain repaired.
BAG-14 per-attempt cache implementation and portable evidence were independently accepted after two finding-driven repair rounds, 26 August 2026.
BAG-15 operation receipts, fixed result wrappers, exact replay DAGs, and recursive version provenance were independently accepted after two finding-driven implementation repair rounds, 26 August 2026.
BAG-16's repaired collection-aware portable contract was independently
accepted after finding-driven preflight rounds. Independent contract and
graph/version/cache/registry auditors accepted the repaired implementation on
26 August 2026 at `bag16.py` SHA-256
`ee0915a13836ec29acfd5118425c3089029c48e3ad50d5a0f88abc15bfd238b0`.

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
  adversaries. The integrated resource-capped zero-backend run passes 417,480
  serial checks, and the separate official-only Draft 2020-12 schema and
  fixture validation passes. Independent claim review remains pending.
- BAG-10 closes the entry-centric failure taxonomy, exact failure-site
  inventory, bidirectional finite placement reachability, diagnostic-only
  details boundary, and the checked lowering-cycle receipt protocol. Its toy
  checker proves only protocol conformance; real lowering proof remains with
  Rust. BAG-12 adds the exact `oracle-operand-production` context and four
  outer-failure placements. The mandatory post-BAG-16 rerun is independently
  accepted after repairing broad absolute failure references in the successor
  pattern, corpus, and receipt schema surface. All 94 active taxonomy
  placements equal all 94 schema-reachable placements across 15 contexts;
  the successor delta is exactly five infrastructure `pattern-test`/`test`
  placements with `error` consequence. The focused proof passes 33,481 checks,
  official Draft 2020-12 validation passes, and the full verifier passes
  1,044,240 zero-backend checks.
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
- BAG-14 closes the portable cache key, record, completeness, reuse, conflict, and schedule-fold contracts without claiming a storage implementation.
  Execution and oracle requests have separate closed cycle-free keys; raw keys exclude outputs, schedules, cache lookup provenance, and locations.
  Immutable records bind complete ordered outputs, positive completion evidence, intrinsic reuse class, and exact finite producer rows whose input digests exclude claimed results.
  The bundled derivative graph independently recomputes definition/operator/selector/edit/patch/mutant identities, selector-to-patch authorization, terminal/trace/declaration/operand/gate/comparison identities and semantics, exact requested plans, and derived report statuses.
  Every oracle operand has one finite input-to-output producer row.
  First-kill and full reports share the exact validated prefix; the first-kill suffix has no child record; uncached, partial-hit, and full-hit materializations fold to byte-identical schedule-specific reports.
  Same-key differences cover terminal, outputs, completion, and production provenance and require quarantine.
  `fixtures/bag14-cache-artifact-catalog.json`, bound by the vector's `artifactCatalogDigest`, is an evidence-local derivative resolver snapshot rather than a relabelling of BAG-12's historical `external-required` graph.
  Rust still owns real store atomicity, locking, resolver availability, conflict remediation, resource isolation, and native BAG-15 production receipts.
- BAG-15 closes portable invocation/receipt identity, operation-specific result wrapping, receipt-backed BAG-14 execution and oracle cache evidence, result/receipt dataflow, report-publication direction, and exact recursive version provenance.
  Complete semantic success, completed semantic failure, bounded completion, diagnostic completion, and failed producer are distinct matrix states; only the failed producer has no wrapper.
  The full publication root contains every selected plan receipt, while the first-kill root has no suffix receipt; invalid materialization has no execution or oracle descendants.
  BAG-12's active-catalog declaration dispatcher and comparison validator are rerun before BAG-15 execution-pattern evidence, and every receipt failure resolves one exact active BAG-10 taxonomy placement.
  The evidence remains deterministic finite-vector production conformance and makes no native replay or publication claim.
- BAG-16 closes portable branch-collection occurrence identity, explicit
  search stops and pending work, empty-search authority, collection-aware
  pattern denotation, deterministic corpus folding, execution-only cache v2,
  successor shared-role dispatch, and recursive v2 closure roots. The verifier
  derives output order, path/result/coverage arithmetic, finite-row eligibility,
  inline expected-side semantics, cache precedence, receipt DAG direction, and
  registry set equality. The evidence does not claim native branch discovery,
  visit order, trace fidelity, solver completeness, or backend execution.
  The frozen candidate passed 82,452 direct BAG-16 checks, the official Draft
  2020-12 schema and fixture validation, and 1,034,971 full zero-backend checks.
  Refresh was byte-idempotent; the previously recorded generated-package
  SHA-256 remained
  `1e7ff376e109d1814570af58c9f58185aecdce2d4d16afd0144d4131e18e25ff`.
  Historical v1 schemas, fixtures, material, vectors, and taxonomy remained
  byte-frozen against Git commit `209df2e`.
- Evidence inventory, checklist, contracts, and Rust handoff are updated for
  this repair. D1 and roadmap are intentionally outside this packet. Fresh
  independent BAG-11 and BAG-12 acceptance found no remaining blocker.
  Two independent final BAG-14 audits reproduced the prior query, crash,
  result-coupling, catalog-identity, and finite-execution-row attacks and
  accepted the repaired subject with no remaining blocker; this does not
  substitute for later packet gates.

The final revision will replace the remaining pending entries with
finding-by-finding results and list the residual Rust-only questions.
