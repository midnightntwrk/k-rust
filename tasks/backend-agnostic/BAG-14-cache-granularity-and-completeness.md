# BAG-14: cache granularity and completeness

Status: active portable implementation after fresh BAG-11/BAG-12 acceptance
and independent BAG-14 preflight acceptance on 26 August 2026. BAG-15 and
later packets remain gated.

## Objective

Make cached mutation evidence safe across `first-kill` and `full` scheduling.
The current execution policy calls one digest a suite-level cache key and binds
the baseline, patch, complete test manifest, and complete oracle manifest, but
it defines neither a cache-value schema nor a completeness relation. The key
also omits `scheduleMode`. Consequently, a first-kill report that never ran its
suffix can occupy the same apparent cache identity as evidence requested by a
full run.

This packet closes the backend-neutral identity, provenance, and reuse rules.
The future Rust stack still owns storage, eviction, locking, transport,
resource isolation, and proof that native results materialize the portable
records faithfully.

## Normative model

Cache immutable **per-attempt execution evidence**, not a scheduled suite
report. `first-kill` and `full` are report-construction policies: they decide
which planned attempts are requested and how already validated attempts are
folded into a campaign. They are not properties of the semantic result of one
fully specified attempt.

Define cycle-free invocation identities that exclude outputs and status:

1. `k-in-k/execution-attempt-key/v1` covers operation/schema and adapter
   versions; a closed baseline or mutant subject (the latter including
   baseline, candidate, patch, mutant, and output-definition identities); the
   exact test invocation (test, program, parser, start symbol, options, and
   bounds); compatibility, lowering, execution, and solver profiles; isolation
   policy; and observation inputs. Use a discriminated attempt kind, never
   nullable unchecked fields: ordinary, observed-exhaustive, or query-coupled.
   Query-coupled/existential execution additionally binds BAG-11 source, plan,
   query, and search policy; exhaustive raw trace production may remain query
   independent until BAG-16 closes branch-set semantics.
2. `k-in-k/oracle-evaluation-key/v1` covers the exact ordered BAG-12 normal
   operand or BAG-09 semantic-crash keys; test-scoped declaration;
   projection/comparison/query/predicate identity; BAG-09 crash and baseline
   policies; evaluator/operation versions; and all required BAG-08 keys.
3. A campaign invocation ID covers requested manifest/operator roots, ordered
   plan, and `scheduleMode`, excluding child outputs. A distinct report ID
   covers the exact ordered selected record IDs, statuses, exclusions, score,
   and schedule mode. BAG-15 later adds the derivation receipt; neither ID may
   be substituted for a raw cache key or include itself transitively.

`scheduleMode` is absent from raw attempt/evaluation keys and present in both
campaign identities. Cache hit/miss, location, latency, and lookup provenance
are supplemental and absent from every semantic identity.

BAG-05 execution-profile identity, BAG-08 artifact identity/resolution,
BAG-11 selected query identity, and BAG-12 typed oracle operands are mandatory
inputs where applicable. A test or oracle identity that changes must change
the corresponding key even if the produced value happens to be equal.

### Exact key algebra and identity domains

Do not leave `key` as an open object. An execution-attempt key contains
exactly:

```text
schemaVersion, keyDigest, operation,
subject, testInvocationDigest,
compatibilityProfileDigest, loweringProfileDigest,
executionProfileDigest, solverProfileDigest, isolationPolicy,
attemptKind
```

`keyDigest` is `k-in-k/execution-attempt-key/v1` over every field except
itself. `operation` is exactly `{operationId, operationVersion, adapterId,
adapterVersion}`; the portable operation ID/version and requested adapter
contract are inputs, while a completed producer receipt remains output-side
evidence. `subject` is the closed baseline or mutant union. The baseline arm
contains its exact definition key. The mutant arm contains the baseline-
definition, operator, patch, and mutant-definition BAG-08 keys plus
`candidateId` and `mutantId`. Artifact keys resolve through BAG-08; the two
embedded self-IDs must equal the enclosing campaign candidate/materialization
records. Do not invent catalog roles for records that remain embedded campaign
values. `testInvocationDigest` resolves to one exact
manifest test slot and therefore closes program, parser, start symbol,
options, bounds, and test identity. Copied profile and isolation roots must
equal that resolved invocation rather than merely have digest shape.

`isolationPolicy` is the exact embedded record
`{schemaVersion, isolationPolicyDigest, baselineState, mutantState,
sharedWritableState, observerState}`. Its digest is
`k-in-k/isolation-policy/v1` over the record without itself. The four v1
values remain `immutable`, `fresh-per-mutant`, `false`, and
`fresh-per-test-path`; changing any of them changes every affected attempt key.
The mutation execution policy embeds this same record. Do not hash the whole
cache/report policy or leave isolation as a shape-only copied digest.

`attemptKind` is exactly one of:

- `{kind: ordinary}` with no observation or query fields;
- `{kind: observed-exhaustive, observationInputs}` where the nonempty ordered
  role-typed artifact-key array is the complete observer/trace interface; or
- `{kind: query-coupled, observationInputs, patternSource, patternPlan,
  patternQuery, searchPolicy}` where the BAG-11 triple resolves internally and
  equals the selected test-scoped declaration.

Unknown fields, duplicate observation keys, ordinary attempts polluted with a
query, and query-coupled attempts missing any query root reject. BAG-16 may
replace the observed-exhaustive output with a branch collection, but it does
not change this cycle-free request identity.

An oracle-evaluation key contains exactly:

```text
schemaVersion, keyDigest, operation, evaluationKind,
declaration, semanticInputs, evaluator
```

`keyDigest` is `k-in-k/oracle-evaluation-key/v1` over every field except
itself. `operation` has the same exact operation/adapter shape.
`evaluationKind` is `baseline-admission` or
`baseline-mutant-comparison`. The admission arm has exactly one tagged
baseline semantic input; the comparison arm has exactly two tagged inputs in
baseline-then-mutant order. Each input is a resolved BAG-12 normal operand or
BAG-09 semantic crash, never a nullable digest, attempt status, or report
result. `declaration` resolves the test slot, projection, comparator,
terminal/crash policies, gate expectation, and all typed query/predicate
artifacts, so no independently editable generic artifact array is permitted.
`evaluator` contains the portable evaluator ID/version and, for K-authored
operations, the exact BAG-12 conformance key; built-ins require that key to be
absent. A declaration, side, evaluator, policy, conformance, or resolved-root
change changes the key even when normalized values compare equal.

Keys are embedded request records, not BAG-08 produced artifacts and not
receipts. A cache record repeats `keyDigest` next to the closed `key`, and the
two must agree. No output key, terminal state, failure, comparison outcome,
receipt ID, cache status, schedule mode, timestamp, or storage locator may
appear in either request key.

## Cache record and completeness

Add a closed cache record exactly shaped around
`{schemaVersion, recordId, kind, keyDigest, key, terminalRecord,
producedArtifacts, completion, reuseClass, productionEvidence}`. `recordId`
uses `k-in-k/cache-record/v1` over all semantic fields except itself, and the
key payload/digest is recomputed. Kind is only `execution-attempt` or
`oracle-evaluation`; invalid pre-execution validation is outside these kinds
unless a later typed validation record is introduced.

`terminalRecord` is a kind-discriminated closed union. An execution record
contains exactly one BAG-09 normal/stuck terminal, semantic-crash, exact
bounded-stop failure, or diagnostic-only failure. An oracle record contains
exactly one BAG-12 baseline-gate result, comparison result, exact bounded/
unknown evaluation failure, or diagnostic-only evaluation failure consistent
with its evaluation kind. It never embeds a campaign status or an untyped
value digest. `producedArtifacts` is the complete operation-declared output
sequence in role order, with no duplicate key; every key must resolve and the
sequence must equal the production evidence's outputs. Supplemental logs,
timestamps, cache-hit data, and backend diagnostics are absent.

Produced BAG-08 keys require resolver-relative material closure, not merely
referential closure. `completion` is exactly
`{producerStatus, evidenceClass, materialClosure, executionConformance}`:
`producerStatus` is the constant `complete`; `evidenceClass` is
`semantic-result`, `exact-bounded-attempt`, or `diagnostic-only`;
`materialClosure` is `repo-complete` or `external-required`; and
`executionConformance` is `finite-vector-proven`, `native-proven`, or
`not-proven`. The current package can prove bundled repo material;
`external-required` is not locally reusable merely because its key resolves
in the catalog. `not-proven` may preserve a structurally valid historical
record but cannot authorize native-result reuse.

`productionEvidence` is a closed seam, not an opaque digest. BAG-14 initially
admits only `{mode: finite-vector, vectorId, inputDigest, outputKeys}` for a
bundled registered deterministic vector whose inputs and outputs the verifier
recomputes. It must not register or fabricate an `operation-receipt` role
before BAG-15 supplies that role's schema and DAG. BAG-15 then deliberately
revises this union with `{mode: operation-receipt, receipt}` and reruns BAG-14
acceptance. Finite-vector evidence is forbidden for external material and
cannot be relabelled `native-proven`.

Use closed reuse classes:

- `semantic-result` for a validated normal/semantic-crash terminal or complete
  comparison (intentional incomparable folds to error/exclusion, never kill);
- `exact-bounded-attempt` for an exact timeout/depth/branch/result/resource/
  solver stop under identical bounds and profiles, never agreement or
  unbounded absence; and
- `not-reusable` for infrastructure/backend/worker/artifact corruption,
  interruption, or unchecked partial evidence.

The persisted reuse class is an intrinsic evidence classification, derived and
never trusted. `semantic-result` requires a kind-compatible complete terminal/
comparison and sufficient production/conformance evidence.
`exact-bounded-attempt` requires the exact bounded-stop terminal and identical
bounds and profiles. `not-proven` native execution, producer/output
disagreement, and every infrastructure/backend/worker failure derive
`not-reusable`. A semantic crash
may be `semantic-result` only through BAG-09's typed crash boundary; a BAG-12
incomparable comparison is a complete typed result but remains non-killing and
is reusable only as that exact error/exclusion result.

Resolver capability is a separate lookup-time eligibility gate and is never
covered by `recordId`: a record whose intrinsic class is reusable may be used
only when every required material artifact is available under the active
resolver. Thus `external-required` is ineligible in the package's repo-only
verifier but may become eligible in Rust without changing the cache record,
key, or intrinsic reuse class. Cache location and resolver availability remain
supplemental, as required above.

Skipped is scheduling data and has no cache record. No valid partial or
unpublished cache-record shape exists; quarantine/diagnostic records cannot be
promoted by refreshing an ID.

Completion is positive evidence, not a Boolean or the absence of an error.
Separate BAG-15 production evidence, which proves the exact adapter operation
produced terminal/result artifacts, from deterministic publication validation
of schema, IDs/key, material closure, terminal/failure semantics, and that
production evidence. BAG-14 owns the key/record shape and finite-vector seam;
BAG-15 later owns the receipt role/schema/DAG and extends that seam. Portable
vectors use a clearly finite registered producer, never a fake native receipt.
Until native evidence exists, a structurally valid record may state
`executionConformance: not-proven` but cannot claim native production.

A published record may be reused only for the exact operation it proves
complete:

- a successful terminal execution record can supply its typed execution
  result;
- a typed semantic crash is a complete semantic result only under BAG-09;
- a timeout, bound stop, or solver-unknown is complete evidence of that exact
  bounded attempt, but never evidence of semantic agreement or unbounded
  absence;
- an infrastructure error, worker loss, corrupt/missing artifact, interrupted
  write, or unvalidated partial record is not a reusable semantic result; and
- a skipped test has no execution cache record. `skipped` is report scheduling
  data, not an execution outcome.

Cache publication is atomic at the portable contract: a record becomes
reusable only after all publication checks validate. Future Rust evidence owns
actual store atomicity, locking, and resolver availability.

## Scheduling and reuse

The pre-execution campaign request contains exactly
`{schemaVersion, campaignInvocationId, manifest, operator, scheduleMode,
requestedPlan}`. `campaignInvocationId` is
`k-in-k/campaign-invocation/v1` over the record without itself. `manifest` and
`operator` are role-typed BAG-08 keys. `requestedPlan` is the exact manifest-
derived test/declaration slot sequence and contains only cycle-free request
identities, never cache records, receipts, statuses, outputs, or skips.
`scheduleMode` is `first-kill` or `full`; changing only it changes the campaign
invocation but none of the raw attempt/evaluation keys.

The materialized report contains the request key plus the exact ordered
selected cache-record IDs, derived test/oracle statuses, explicit scheduled-
but-unexecuted suffix, exclusions, score, and campaign status. Its
`reportId` is `k-in-k/mutation-report/v1` over every semantic report field
except itself. Under `full`, selected records cover the entire requested plan.
Under `first-kill`, they cover exactly the prefix through the first derived
kill; every suffix entry is `skipped` and has no record/receipt reference.
Cache hit/miss/source metadata is supplemental outside this record. BAG-15
will place the same request and selected-record closure into the derivation
receipt without redefining either identity.

A `first-kill` run may reuse exact cached attempts for its prefix and stop
after the first derived kill. It publishes a complete first-kill report and
only the attempt/oracle records that actually ran or were valid cache hits.
It must not publish cache records for the skipped suffix.

A later `full` run may reuse those exact prefix records, but it must execute or
resolve valid records for every remaining selected test before publishing a
complete full report. Conversely, a first-kill report may be derived from a
complete set of raw records by consuming only the manifest prefix through the
first kill. The reports have distinct campaign IDs because `scheduleMode` and
materialized plan differ, while shared raw records retain their identities.

Baseline gate records are required for every selected test/oracle before
mutant scoring, independent of a first-kill mutant suffix. A first-kill report
references only the mutant prefix through the first derived kill and explicitly
marks the suffix skipped without child references. Existing unrelated suffix
records in a store do not enter that report identity. Uncached, partial-hit,
and full-hit folds over the same chosen record IDs are byte-identical after
supplemental hit provenance is excluded.

No suite-level Boolean cache hit exists. Reuse is decided independently for
every required execution attempt and oracle evaluation, followed by ordinary
schedule-aware report derivation. Cache lookup order or hit/miss provenance is
supplemental and must not alter semantic report identity.

One request key identifies inputs, not a metaphysically unique observation.
Each immutable observation has its own record ID; identical keys plus identical
semantic terminal values may deduplicate. If one key has conflicting validated
values (for example timeout versus success), automatic reuse is invalid and the
key is quarantined. A report may select one exact record only through a declared
future rerun/consistency policy and names that record explicitly; it never
silently chooses newest or fastest. Conflict remediation and nondeterminism
policy remain Rust-owned.

An exact bounded-attempt record may reconstruct only the same historical
bounded request when that request permits recorded inconclusive evidence. Any
bound, profile, query, evaluator, isolation, or operation-version change
invalidates reuse. It cannot become `survived`, `agree`, or evidence for an
unbounded request.

## Required evidence

- one deliberately small, wholly repo-bundled definition/program/test/output
  graph whose every attempt, operand, terminal, comparison, and produced
  artifact has `repo` material; do not relabel the current
  `external-required` campaign graph merely to obtain a reusable positive;
- persisted execution-attempt and oracle-evaluation records for one baseline
  and at least two mutant tests;
- the same prefix records reused by both first-kill and full report vectors;
- a first-kill suffix that has no fabricated execution/oracle record;
- a later full report that reuses the prefix and supplies newly completed
  suffix records;
- equivalent uncached, partially cached, and fully cached materializations
  produce the same schedule-specific semantic report;
- timeout/unknown records remain bounded inconclusive evidence rather than
  agreement; and
- interrupted/error records are ignored or replaced atomically, never reused
  as semantic results.

Permanent adversaries must reject schedule/report records presented as raw
attempt entries, a first-kill partial suite reused as a full suite, fabricated
skipped-suffix entries, baseline/mutant subject reversal, patch or output-
definition drift, test invocation/profile/bounds/query drift, oracle/test
scope drift, changed projection/comparison/crash policy, cache hit with missing
or unresolved result artifacts, completion asserted over partial output,
error/worker-loss reused as agreement, bounded unknown reused under different
bounds, duplicate keys with conflicting terminal values, and a refreshed
self-ID that conceals any of those changes.

Also reject output/status/result inserted into an invocation key; schedule or
hit provenance inserted into a raw key; schedule omitted from campaign
invocation/report identity; parser/start/options/lowering/solver/isolation/
observer/attempt-kind/search-policy/operation-version drift; oracle operand
order or baseline-policy/evaluator drift; referential-only material asserted
available under the wrong resolver; `complete: true` without checked production
evidence; a fabricated skipped record or missing baseline gate; cached versus
uncached fold differences; one result reused for another query-coupling kind;
conflicting same-key values silently selected; and a suite-level Boolean hit.

## Ownership

The worker may replace the suite-level cache object in the mutation execution
policy, add cache-record schema/fixtures/vectors, and update mutation campaign
and manifest schemas/fixtures after BAG-11/BAG-12, contracts, artifact roles
and catalog after BAG-08, verifier, refresh helper, completion evidence, and
Rust handoff cache notes. Integrate after BAG-05, BAG-08, BAG-09 through
BAG-13. Coordinate its abstract production-receipt seam with BAG-15 rather
than inventing a second receipt system. Do not edit goals/D1/roadmap, implement a store, choose eviction or
locking policy, run native execution, or benchmark a backend.

## Acceptance

- cache identity is per immutable execution attempt or oracle evaluation;
- scheduling/report identity is separate and covers `scheduleMode`;
- completeness and atomic publication are explicit, typed, and verified;
- first-kill evidence cannot satisfy a full plan without exact suffix records;
- valid prefix records can be shared without making schedule order semantic;
- all mandatory adversaries reject through schema or semantic validation;
- zero-backend and official Draft 2020-12 validation pass;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- checks are tiny and serial; and
- `git diff --check` passes.

### Post-BAG-12 root compatibility review — 23 August 2026

This is not activation or independent preflight evidence. The repaired BAG-12
package now supplies a wholly bundled typed declaration/operand/gate/
comparison/terminal/output graph suitable for BAG-14's finite-vector positive;
the packet must use that graph or a deliberately smaller derivative rather
than relabeling historical `external-required` material. BAG-12's
operation-specific K-authored roles and fail-closed production-authority rule
do not change the cache key algebra: finite-vector records remain the only
zero-backend production arm, and K-authored/native decisions remain
non-reusable until BAG-15 defines and proves the exact receipt arm. The earlier
preflight resolutions—embedded candidate/mutant IDs, standalone isolation
policy identity, intrinsic reuse class, lookup-time resolver eligibility, and
no fabricated BAG-15 role—remain consistent with the repaired package.

Before delegation, an independent preflight must still verify the exact
current BAG-12 schemas/roles and confirm that BAG-14 does not copy BAG-12's
finite-row authority into a general native-production claim.

### Independent activation preflight — 26 August 2026

Independent review accepted portable activation against the exact current
BAG-12 declaration, operand, side, gate, comparison, evaluator-conformance,
campaign, and catalog roles. It confirmed that finite-vector evidence is not
native authority, `operation-receipt` remains absent until BAG-15, and the
packet has no dependency on the retired backend-specific path.

## Stop rule

Stop rather than choosing a Rust cache implementation, requiring a particular
database or filesystem layout, treating cache availability as semantic input,
or claiming native atomicity/concurrency behavior from portable records.
