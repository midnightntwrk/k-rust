# BAG-16: corpus search and branch-trace replay completeness

Status: authorized backend-agnostic closure packet; activate after BAG-11,
BAG-14, and BAG-15.

## Objective

Bind corpus identity to its query search policy and make replay capable of
representing the complete branch-local trace collection consumed by a pattern
query. The current corpus omits `searchPolicy`, while a pattern result can
contain multiple path results but replay hard-codes one event trace. Early-stop
results also lack explicit visited/unvisited-work evidence.

This packet closes portable invocation identity, collection coverage, and
replay dataflow. It does not claim that the Rust backend discovered every
branch or faithfully executed the recorded search.

## Normative model

Add the exact closed `searchPolicy` value to query-coupled corpus manifests,
component invocation identity, replay identity, and BAG-15 execution-attempt
receipts. All linked artifacts must agree; changing policy under an unchanged
invocation or parent root rejects. Refreshing every affected identity instead
validly describes a new invocation and must not be rejected as drift.

Keep policy scopes distinct. Ordinary/final-result attempts do not acquire an
irrelevant query policy. Exhaustive branch collection may be query-independent
and reusable across BAG-11 plans. `existential-first` execution is
query-coupled and binds exact source, plan, selected query, and within-test
search policy because its stop condition depends on them. Corpus-level
stop-after-test-match is a separate scheduling policy.

An execution attempt produces one typed branch-trace collection rather than a
singleton trace edge. The collection binds the cycle-free BAG-15 producing
invocation, while its completed receipt lists the collection as an output; the
collection never contains that receipt ID. It also binds:

- the producing BAG-14 attempt key and BAG-15 cycle-free invocation digests,
  whose completed receipt later lists this collection as an output;
- test, program, definition, query, bounds, solver, compatibility, execution,
  options, observation, and search-policy identities;
- a semantic recorded visit-order sequence of visited branch records;
- a typed pending frontier/work count, representing discovered pending work
  units rather than unknowable future branches;
- one closed global search stop reason, distinct from branch terminal state;
  and
- a collection semantic ID.

### Exact collection and occurrence records

The `branch-trace-collection` record contains exactly:

```text
schemaVersion, collectionId,
attemptKeyDigest, invocationDigest,
testInvocationDigest, subject,
compatibilityProfileDigest, executionProfileDigest, solverProfileDigest,
boundsDigest, observationInputs, queryCoupling, searchPolicy,
visited, pendingWork, stopReason
```

`collectionId` is `k-in-k/branch-trace-collection/v1` over every field except
itself. The copied subject/test/profile/bounds/observation/query roots must
equal the resolved BAG-14 attempt key and BAG-15 invocation, not merely have
valid shapes. `queryCoupling` is the exact closed union: ordinary exhaustive
collection uses `{kind: query-independent}` and has `searchPolicy:
exhaustive`; a query-coupled collection uses `{kind: pattern-query,
patternSource, patternPlan, patternQuery}` and may use `exhaustive` or
`existential-first`. An ordinary/final-result attempt cannot publish this
collection, and a query-independent collection cannot claim an existential
stop.

`visited` is the semantic visit-order array. Each record contains exactly:

```text
branchKey, visitOrdinal, trace, traceOccurrence, disposition
```

`branchKey` is
`k-in-k/branch-occurrence/v1` over `{attemptKeyDigest, visitOrdinal}`; it is
producer-scoped and therefore need not expose a native KCFG identifier.
`visitOrdinal` equals its zero-based array position. `trace` is a role-typed
event-trace key. `traceOccurrence` is
`k-in-k/trace-occurrence/v1` over `{branchKey, trace}` and disambiguates equal
content digests without forbidding them. `disposition` is exactly one of
`normal`, `stuck`, `semantic-crash`, `depth-limit`, `time-limit`,
`branch-limit`, `result-limit`, `resource-limit`, `solver-unknown`,
`semantic-failure`, `backend-failure`, or `infrastructure-failure`, with the
kind-compatible BAG-09/BAG-10 terminal/failure key required by its schema arm.
No branch record contains pending work, a receipt ID, worker order, or
supplemental diagnostics.

`pendingWork` is exactly `{discoveredCount}` with a nonnegative integer; it is
not a list of guessed branches and has no trace keys. `stopReason` is the
closed global algebra `search-exhausted`, `match-found`, `depth-limit`,
`time-limit`, `branch-limit`, `result-limit`, `resource-limit`,
`solver-unknown`, `semantic-failure`, `backend-failure`, or
`infrastructure-failure`, plus the exact BAG-10 failure key for every arm
other than the first two. Global stop and path dispositions are validated
together; one may not be inferred by string equality with the other.

The collection points only backward to cycle-free request identities. The
BAG-15 receipt points forward to the collection as an output. Any schema that
puts the receipt key in the collection is a receipt/output cycle and rejects,
even when both self-IDs are refreshed.

Each visited record has a producer-scoped unique branch key, contiguous
`visitOrdinal`, a BAG-08 event-trace key, and a closed path disposition. Pending
work has no fabricated trace. Do not require trace digests to be unique:
distinct branches may legitimately share content-identical traces. Join paths
and witnesses by branch key plus trace key/occurrence, never digest alone. Do
not invent portable KCFG identity; native correspondence remains Rust-owned.

The matcher consumes the collection plus the normalized BAG-11 query plan.
Pattern-result path records must cover every visited branch exactly once in
visit order, including empty traces and incomplete/error paths. Every witness
identifies one branch and one trace occurrence. No extra, omitted, duplicate,
reordered, wrong-test, or wrong-invocation occurrence is permitted.

The BAG-11 result input is upgraded from a singleton event-trace root to one
role-typed `branch-trace-collection` key. Every path record adds exactly
`branchKey` and `traceOccurrence`; its existing trace key must equal the
resolved occurrence. Path array position equals the collection visit ordinal.
Every witness repeats the path's branch key and trace occurrence and still
uses BAG-11's exact event ordinals within that trace. Result identity covers
the collection key and all occurrence keys; it does not cover the later
production receipt. Retain singleton trace vectors only as explicit historical
v1 regression inputs or mechanically lift them to a one-branch collection;
they cannot satisfy the new multi-branch production schema directly.

Freeze a closed global stop algebra including `search-exhausted`, `match-found`,
depth/time/branch/result/resource limit, solver unknown, semantic failure,
backend failure, and infrastructure failure. Then freeze exact derived
search-completeness arithmetic:

- visited count equals visited records and pending count equals declared
  frontier units; recorded visit ordinals are contiguous, not lexically sorted
  or worker-completion ordered;
- `exhaustive` permits no query-satisfied early stop and derives complete
  coverage only from `search-exhausted`, zero pending work, and trustworthy path
  records; zero pending alone is never proof;
- `existential-first` may stop on the first witnessed match only with explicit
  `match-found`, a visited prefix in which no earlier path matched, and the
  final first validated witness. It remains incomplete coverage even when
  pending happens to be zero;
- `no-match` requires `search-exhausted`, zero pending work, every visited path
  a trustworthy nonmatch, and no witness; unknown/error may retain partial
  paths but cannot assert absence; and
- an overall complete-coverage claim derives from collection counts, stop
  reason, and every visited path result rather than from the reported path
  list alone.

The portable verifier checks this relational model. Native branch discovery,
the truth of unvisited/exhaustive counts, solver feasibility, stable KCFG
correspondence, stop-reason fidelity, and actual trace production remain
future Rust evidence.

Corpus aggregation consumes exact component result and BAG-15 receipt IDs;
skipped tests have neither attempts nor receipts. Reuse BAG-15's operation
registry for branch-collection production, pattern evaluation, and corpus
derivation rather than adding another receipt shape.

For every query-coupled corpus test slot, the manifest contains the exact
`searchPolicy` beside its ordered declaration/query selection. Its component
invocation digest is recomputed over the test invocation, BAG-14 attempt key,
source/plan/query, observation roots, and policy. A corpus component result
contains exactly the attempt key, attempt receipt, collection, pattern result,
and pattern-evaluation receipt for that slot. A corpus aggregate contains the
ordered component keys and one BAG-15 corpus-derivation receipt. All arrays
preserve manifest test order then declaration-slot order with repetitions;
none are sets or joins by bare query/trace digest. Skipped slots contain a
typed scheduling marker only and no attempt, collection, result, or receipt
key.

## Required evidence

- corpus IDs and component invocation IDs change when only `searchPolicy`
  changes;
- a two-branch collection replays through the typed execution-to-match edge;
- two distinct branch keys may positively share one content-identical trace
  digest without losing occurrence provenance;
- each path result and witness resolves to exactly one collection trace;
- exhaustive no-match derives complete coverage with zero unvisited work;
- existential-first match derives an honest early stop with explicit unvisited
  work; and
- corpus aggregation folds only exact component results produced under the
  manifest's search policy and branch collection.

Permanent adversaries must reject corpus/result/replay/attempt search-policy
drift under an unchanged invocation/parent root; omitted, extra, duplicate, reordered,
wrong-test, or wrong-invocation traces; a witness outside the collection;
`completeCoverage: true` or `no-match` with unvisited work; existential early
stop without `match-found` evidence; exhaustive query-satisfied truncation;
mixed keyed/unkeyed paths; noncanonical collection ordering; a multi-trace
result forced through the retired singleton replay edge; and collection drift
in profiles, bounds, program, query, or producing attempt.

Also reject digest-only joins that become ambiguous for two branches sharing a
trace; duplicate/noncontiguous branch keys or visit ordinals; pending work with
a fabricated trace; collection-to-completed-receipt self-cycle; generic
execution polluted by query policy or existential execution missing query
identity; lexical/worker-completion order substituted for visit order;
zero-pending claimed exhaustive without `search-exhausted`; `match-found`
claimed complete coverage; an earlier match skipped before the reported first
witness; a path omitted merely because its trace is empty/incomplete/error;
and skipped corpus tests with attempts/receipts.

## Ownership and dependencies

Integrate after BAG-11 supplies normalized query identity, BAG-14 supplies
attempt/completeness rules, and BAG-15 supplies generic execution receipts and
typed replay DAG edges. Reuse those receipts; do not define a second generic
operation-receipt system.

The worker may modify corpus, pattern-result, event-trace/collection, and replay
schemas and fixtures; corpus/pattern/replay vectors; contracts; refresh helper;
verifier; completion evidence; and Rust handoff notes. Do not change mutation
generation, define native KCFG semantics, edit goals/D1/roadmaps, or run backend
code.

## Acceptance

- search policy is part of every relevant portable invocation identity;
- replay represents branch-trace collections rather than pretending one trace
  is a multi-path result;
- path/witness coverage and early-stop arithmetic are exact and adversarially
  tested;
- BAG-15 receipts remain the sole generic producing-provenance mechanism;
- official Draft 2020-12 and zero-backend validation pass;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- checks are tiny and serial; and
- tracked and untracked whitespace checks pass.

### Post-BAG-12 root compatibility review — 23 August 2026

This review does not activate BAG-16 or replace its later independent
preflight. BAG-12's reachability/predicate/output finite rows are exact
registered conformance inputs tied to bundled producer traces and subjects;
they are not a substitute for this packet's branch-trace collection. BAG-16
must lift or replace those finite inputs through an exact collection and
BAG-15 production receipt while preserving the same truth/comparison
semantics. It must never infer native exhaustive coverage from a BAG-12
`finiteComplete` fixture flag.

The repaired manifest's active-catalog-only corpus and observation authority,
recomputed test invocation, replay `testId`, and source/plan/query/search roots
are the lower boundary for every new collection/component identity. BAG-16
must extend that one graph rather than load a second corpus, observation, or
trace registry by fixture filename. Its query-independent exhaustive arm must
resolve specifically to BAG-14's `observed-exhaustive` attempt kind; ordinary
and final-result attempts remain unable to publish a branch collection.

## Stop rule

Stop rather than claiming native branch exhaustiveness, inventing KCFG IDs,
deriving solver feasibility, or treating a portable collection receipt as
proof that the Rust backend followed it.
