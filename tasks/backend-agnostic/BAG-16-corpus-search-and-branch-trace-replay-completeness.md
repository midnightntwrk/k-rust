# BAG-16: corpus search and branch-trace replay completeness

Status: repaired portable contract and implementation independently accepted
on 26 August 2026 after fifteen preflight rejection reports and finding-driven
implementation repairs. The accepted implementation SHA-256 is
`ee0915a13836ec29acfd5118425c3089029c48e3ad50d5a0f88abc15bfd238b0`;
the test-local/global-root clarification was independently accepted at Git
commit `c157997`.

## Objective

Bind corpus identity to its exact query-search policy and make replay represent
the complete branch-local trace collection consumed by a pattern query. The
accepted v1 corpus omits `searchPolicy`, while its pattern result may describe
several paths but its replay edge carries one event trace. Early-stop results
also lack explicit visited/pending-work evidence.

This packet closes only portable request identity, production provenance,
collection coverage, query denotation, and corpus folding. It does not claim
that a native backend discovered every branch, visited branches in the recorded
order, or faithfully produced any recorded trace or stop reason.

## Version and migration boundary

Preserve every accepted BAG-08, BAG-11, BAG-14, and BAG-15 v1 artifact,
identity, operation, fixture, and registry closure as historical input. In
particular, do not silently reinterpret `event-trace/v1`, `pattern-result/v1`,
`execution-attempt` operation version 1, or `execution-attempt-result` version
1 as collection-aware records. A v1 singleton trace may be a regression input
or may be mechanically lifted by an explicitly versioned adapter vector, but
it cannot satisfy a v2 production edge directly.

BAG-16 adds the following versions and no aliases:

- occurrence-neutral `event-trace/v2`, `branch-trace-collection/v1`,
  `empty-search-decision/v1`, collection-aware `pattern-result/v2`, and the
  versioned corpus/component schemas defined below;
- query-neutral `execution-test-invocation/v2` and
  `execution-attempt-key/v2` request identities;
- `execution-attempt` operation version 2 with the existing BAG-15
  `execution-attempt-result` role at schema version 2;
- `pattern-evaluation` operation version 1 with sole wrapper role
  `pattern-evaluation-result`;
- `corpus-derivation` operation version 1 with sole wrapper role
  `corpus-derivation-result`;
- `oracle-operand-production` operation version 2, using the accepted
  `oracle-operand-production-result` wrapper schema and role, for the
  collection-backed execution-pattern and BAG-12 finite-row operands below;
- execution-only `cache-record/v2`, digest domain `k-in-k/cache-record/v2`, and
  `cache-semantics/v2`, whose constant kind `execution-attempt` admits the
  collection terminal and receipt-v2 production evidence defined below; and
- `replay-version-registry/v2`, digest domain
  `k-in-k/replay-version-registry/v2`, whose schema and operation unions admit
  the exact historical and BAG-16 versions reachable from one v2 closure.

All four operations use successor `operation-invocation/v2` and
`operation-receipt/v2` schemas and digest domains. Those schemas retain
BAG-15's exact invocation/receipt fields, producer algebra, cycle-free
one-wrapper direction, and the same BAG-08 `operation-receipt` role/family,
while closing their operation union over the BAG-16 arms and versions above.
Every BAG-16 invocation digest uses `k-in-k/operation-invocation/v2`; every
BAG-16 receipt ID uses `k-in-k/operation-receipt/v2`. Schema version and
operation version remain separate. The v1 schema bytes, digest domains, union,
and validator are unchanged, so no v1 receipt may claim a BAG-16 operation and
no v2 receipt may be substituted in a historical v1 closure. The successor
schemas, shared-role resolver dispatch, and recursive version registry are
added deliberately; no second receipt family or operation-specific receipt
role is permitted. A pre-BAG-16 BAG-15 report closure continues to require
exactly its old registry entries and rejects the new entries as surplus.

The accepted `cache-record/v1` identity, cache schema bytes, terminal union,
fixtures, and registry entries remain unchanged. A v1 record cannot contain a
branch collection or receipt-v2 production edge. The v2 cache record retains
BAG-14's exact field shape, request-key equality, completion algebra, and
conflict rules, but closes `kind` to the constant `execution-attempt`,
dispatches only execution-attempt operation v2, uses the new terminal arm, and
hashes under the v2 record domain. It has no `oracle-evaluation` arm. Oracle
evaluation continues to use the accepted cache-record/v1, cache-semantics/v1,
oracle-evaluation key, and operation-v1 contracts; no oracle record is silently
aliased under a v2 cache identity. The v2 cache record uses
`execution-attempt-key/v2`; accepted BAG-14 v1 records continue to use
`execution-attempt-key/v1`. Both remain cycle-free request identities, but they
are not interchangeable.

### Exact shared-role version dispatch

BAG-16 adds `artifact-role-specs/v2` without changing the accepted v1 registry
or historical catalogs. Its exact top-level record is
`{schemaVersion: 2, registryId, specs}`, with `registryId` equal to
`k-in-k/artifact-role-specs/v2` over the record except itself. BAG-16 also adds
`artifact-catalog/v2`, preserving the accepted catalog fields and adding the
exact `roleSpecRegistryId`; its `catalogId` uses
`k-in-k/artifact-catalog/v2` over the complete record except itself. Every
BAG-16 advertised closure embeds one exact v2 catalog and registry pair; their
IDs must agree. Semantic artifacts inside that catalog do not copy its catalog
ID, avoiding catalog/artifact identity fixed points.

A v2 role-spec entry is a closed union. Opaque-byte roles retain BAG-08's exact
single media/domain envelope. A structured role has one role, fixed canonical-
JSON media, and a nonempty, semantic-version-sorted, duplicate-free
`structuredVersions` array. Each arm fixes one semantic schema version, exact
schema ID and byte digest, semantic digest domain, self-ID payload projection,
and one closed dispatch arm: `{kind: schema-version, schemaVersion}` requires
that exact top-level integer, while `{kind: legacy-no-schema-version}` requires
the field to be absent and is permitted only for an exact accepted historical
schema whose frozen bytes omit it. A role may have at most one legacy arm. A
BAG-16 catalog is bound to exactly one v2 role-spec registry. After byte-
integrity, duplicate-key, canonical-JSON, and shared preflight checks, its
resolver selects the exact schema-version arm from a present top-level integer,
or the sole legacy arm when that field is absent, validates with that arm, and
recomputes that arm's semantic digest. A missing field without a legacy arm, a
legacy arm when the field is present, a noninteger field, or zero/multiple
selected arms rejects. This preserves accepted `pattern-query/v1` and any
other registered legacy bytes without adding a field to them. Schema guessing,
validator-first fallback, digest-domain trial, file-name dispatch, and
accepting one version through another arm are forbidden.

The artifact key remains exactly `{role, digest}`. Version is derived from the
resolved structured value and is not a second caller-supplied selector. The
active catalog rejects two entries with the same artifact key even when their
resolved schema versions differ. Roles that have only one admitted version use
a one-arm array. Historical catalogs remain bound to `artifact-role-specs/v1`
and therefore retain their single-schema dispatch. The shared roles
`event-trace`, `pattern-result`, `execution-attempt-result`, `cache-record`,
`oracle-operand-production-result`, and `operation-receipt` use this exact v2
dispatch; no suffixed role alias is introduced.

`replay-version-registry/v2` has the exact top-level shape
`{schemaVersion: 2, registryId, schemas, operations}`. Its ID hashes the record
except itself under its v2 domain. A schema entry fixes schema ID, semantic
schema version, and byte digest; its version is the role-spec arm's semantic
version even for a legacy-no-schema-version artifact. An operation entry fixes
one admitted operation kind/version pair. Both arrays are canonically sorted,
duplicate-free, and equal the complete reachable closure. Their unions admit
the historical entries needed by a BAG-16 graph plus exactly the BAG-16
schema/operation versions defined here; no arbitrary positive version or
unknown operation is allowed. The accepted replay-version-registry/v1 schema,
domain, fixtures, and BAG-15 closures remain byte-for-byte unchanged and cannot
represent or be substituted for a BAG-16 closure.

The execution-v2 and pattern-evaluation invocation digests are the active
replay request identities. Their paired result wrappers and receipts are the
active replay evidence. Do not create a parallel opaque replay-manifest
identity for the same operation graph. Accepted `replay-manifest/v1` files
remain historical singleton regression inputs only; they cannot be advertised
as collection replay.

## One frozen production DAG

The only active v2 dataflow is:

```text
operation-invocation/v2 (execution-attempt operation v2)
  -> occurrence-neutral event-trace/v2 artifacts
  -> branch-trace-collection/v1
  -> execution-attempt-result/v2
  -> completed operation-receipt/v2
  -> operation-invocation/v2 (pattern-evaluation operation v1)
  -> pattern-result/v2
  -> pattern-evaluation-result/v1
  -> completed operation-receipt/v2
  -> operation-invocation/v2 (corpus-derivation operation v1)
  -> corpus-result/component aggregate
  -> corpus-derivation-result/v1
  -> completed operation-receipt/v2
operation-invocation/v2 (oracle-operand-production operation v2)
  + completed execution or pattern-evaluation receipt/v2
  -> accepted oracle-operand value
  -> oracle-operand-production-result/v1
  -> completed operation-receipt/v2
```

There is no branch-collection producer operation or receipt. The traces and
collection bind the cycle-free execution invocation; the collection points
only backward. The execution result wrapper nests their keys, and the receipt
points forward only to that wrapper. Likewise, neither a pattern result,
component result, corpus aggregate, nor result wrapper contains the ID of its
own producing receipt. Every downstream consumer pairs a result wrapper with
its already-resolved producing receipt. Refreshing all self-IDs cannot make a
forward-to-receipt edge valid.

### Query-neutral execution request version 2

`execution-test-invocation/v2` contains exactly its schema version,
`testInvocationDigest`, test/program/parser/start/options/bounds roots, and no
declaration, source, plan, query, oracle slot, search policy, receipt, or
output. Its digest is `k-in-k/execution-test-invocation/v2` over every field
except itself. It is derived from the corpus test's execution inputs rather
than by hashing the accepted v1 test record that includes pattern selections.

`execution-attempt-key/v2` retains BAG-14's exact cycle-free key fields and
isolation/profile relations, changes its schema/domain to
`k-in-k/execution-attempt-key/v2`, and requires the v2 execution-test digest.
Its `observed-exhaustive` arm contains observation inputs but no query roots;
its `query-coupled` arm additionally contains the exact source/plan/query and
policy plus the selected `side-condition-conformance-table` key. Thus changing
a corpus's declarations or query list does not change a
reusable observed-exhaustive execution key when its execution-test inputs are
unchanged, while changing an existential query does change its key. Historical
BAG-14 keys and records retain their v1 test projection and cannot satisfy a
BAG-16 edge.

### Execution operation version 2

The operation invocation has `operationKind: execution-attempt`,
`operationVersion: 2`, one output role `execution-attempt-result`, and a
`parameters` arm containing exactly the complete embedded BAG-14
`execution-attempt-key/v2` plus its equal `keyDigest`. Its ordered generic
inputs remain the deterministic BAG-15 traversal of that key. It accepts only:

- `observed-exhaustive`, which is query-neutral and contains its exact ordered
  observation inputs; or
- `query-coupled`, which contains the same observation roots plus exact
  BAG-11 source, plan, selected query, side-condition table, and
  `searchPolicy`.

An ordinary attempt cannot produce a collection. An exhaustive reusable corpus
execution is canonically `observed-exhaustive`, never a query-coupled attempt
with an arbitrary query pasted onto it. A query-coupled attempt is required for
`existential-first`. Its selected source/plan/query and policy must equal the
corpus slot that requests it. Query-neutral exhaustive execution may fan out to
several pattern-evaluation slots for the same test/subject roots. No execution
identity is declaration-coupled merely because a later evaluator consumes it.

The exact v2 wrapper is:

```text
schemaVersion, resultId, attemptKeyDigest, invocationDigest,
terminalRecord, producedArtifacts, branchCollection
```

`resultId` is `k-in-k/execution-attempt-result/v2` over every field except
itself. `producedArtifacts` is the exact duplicate-free first-production-order
sequence obtained by scanning occurrences in visit order: append the
occurrence's terminal-state key for `normal`/`stuck`; for `semantic-crash`,
append the resolved crash's terminal-state key and then its semantic-crash key;
then append the occurrence's event-trace/v2 key. Terminal-free
`query-satisfied` and limit/solver/backend dispositions append only their trace.
Already appended keys are not repeated. After the visits, append the one
`empty-search-decision/v1` key exactly when the collection has no visited
paths, then append the one collection key. Thus every path terminal/crash and
trace has a declared execution production edge, while content-identical values
occur once even when several occurrences refer to them. `branchCollection`
equals the final entry. No v1 trace, pattern result,
receipt, or cache record occurs in the wrapper. These records relate only
fieldwise: the wrapper's `attemptKeyDigest` equals the embedded invocation
key's `keyDigest`; its `invocationDigest` equals the recomputed invocation
digest and the receipt's `invocationDigest`; the receipt's sole output is the
wrapper key, which must resolve before any nested wrapper field is compared;
the wrapper's `terminalRecord` equals both the receipt's `semanticTerminal` and
the cache record's `terminalRecord`; and the wrapper's nested
`producedArtifacts` equals the cache record's `producedArtifacts`. No equality
between the differently shaped whole invocation, wrapper, receipt, or cache
records is implied.

For operation version 2, `terminalRecord` is exactly
`{kind: branch-collection, collection, stopReason}`. Its collection key equals
both `branchCollection` and the last produced artifact, and its `stopReason`
equals the resolved collection stop reason. This is the one attempt-level
semantic terminal; individual BAG-09 terminals/failures remain in visited
dispositions. The successor cache-semantics/v2 execution-terminal union adds
only this version-gated arm; BAG-14's v1 union remains byte-for-byte unchanged.
`search-exhausted` and `match-found` select null receipt
failure; every limit/unknown/backend arm selects the exact embedded BAG-10
value carried by its stop reason. The completed receipt's
`semanticTerminal` and `failure`, wrapper terminal, cache terminal, evidence
class, and reuse class must agree exactly.

A completed limit, unknown, or backend-error execution still publishes exactly
one v2 wrapper under BAG-15's rule. Its collection may preserve trustworthy
visited-prefix evidence and its terminal/failure must agree with the global
stop algebra below. A producer-status `failed` receipt publishes no wrapper,
traces, or collection and can supply only the `execution-failure` component
arm. It must embed one of the exact BAG-10 infrastructure values admitted below
at `pattern-test`; execution-stage `backend-error` is instead a completed
collection terminal and cannot be relabelled as producer failure.

### BAG-10 producer-failure placement extension

BAG-16 adds the exact `pattern-test`/`test` error-consequence placement to
BAG-10's existing infrastructure classifications `process-launch`, `io`,
`artifact-corruption`, `worker-lost`, and `internal`, retaining each entry's
stage, retryability, evidence policy, and diagnostic-only details boundary.
This is one bidirectional taxonomy/schema extension, not a new classification
or generic operation-production context. It is available only to failed
execution-attempt-v2 and pattern-evaluation-v1 receipts that publish no output
or semantic terminal. The final BAG-10 placement audit must prove both
directions after BAG-16 lands. No infrastructure value may appear as a
completed collection stop or semantic path disposition.

### Occurrence-neutral trace version 2

`event-trace/v2` contains only its schema version, subject definition digest,
semantic event-vocabulary root, path predicate, ordered event content, and
`traceId`. `traceId` is
`k-in-k/event-trace/v2` over the record except itself. Events retain BAG-08's
closed event algebra and BAG-11 event indexing. The path predicate is required
because it participates in BAG-11's side-condition lookup; omitting or moving
it to occurrence metadata changes denotation and rejects. The definition must
equal the execution subject resolved through every collection occurrence. The
trace has no test, attempt, invocation, collection, branch/path key, visit
ordinal, disposition, terminal, query, search policy, receipt, worker, or stop-
reason field. Empty event arrays are valid. Production and occurrence
provenance live in the wrapper and collection, so equal semantic trace content
intentionally has one equal key.

### Empty-search decision

`empty-search-decision/v1` is a structured BAG-08 role with exact record
`{schemaVersion, decisionId, attemptKeyDigest, invocationDigest,
collectionScopeId, reason}`. `schemaVersion` is 1, `reason` is the constant
`finite-frontier-empty`, and `decisionId` is
`k-in-k/empty-search-decision/v1` over every field except itself. It binds only
the cycle-free execution request and collection scope; it contains no
collection, result, receipt, query outcome, or corpus edge.

Execution-attempt v2 is its sole producer. It is present exactly when the
visited sequence is empty and the stop is `search-exhausted`, and absent in
every nonempty or non-exhausted collection. The execution wrapper and
cache-record/v2 list it immediately before the collection. The collection and
pattern result repeat its key and independently resolve all three request
roots. This is the only empty-space authority; an empty array, pending zero,
or an evaluator-created marker is insufficient.

## Exact collection and occurrence algebra

`branch-trace-collection/v1` contains exactly:

```text
schemaVersion, collectionId, collectionScopeId,
attemptKeyDigest, invocationDigest, queryCoupling,
visited, pendingWork, stopReason, emptySearchDecision
```

`collectionScopeId` is `k-in-k/branch-collection-scope/v1` over
`{attemptKeyDigest, invocationDigest, outputOrdinal: 0}`. Because one execution
v2 invocation requests exactly one result and one nested collection, this is a
unique cycle-free occurrence namespace. `collectionId` is
`k-in-k/branch-trace-collection/v1` over every field except itself. A branch
never hashes `collectionId` back into that collection; all joins nevertheless
carry the resolved collection key as well as the scope and occurrence keys.

The attempt key is the single authority for subject, test invocation and its
program/parser/start/options/bounds, compatibility, lowering, execution and
solver profiles, isolation, observation inputs, and any selected query/policy.
The collection does not copy a second editable set of those roots. Resolution
must rederive them from the exact embedded BAG-14 key in the execution
invocation and cache record.

`emptySearchDecision` is either the exact produced key defined above or null.
It is nonnull exactly for empty `visited` plus `search-exhausted`, and null
otherwise.

`queryCoupling` is exactly:

- `{kind: query-independent}` for an `observed-exhaustive` key; or
- `{kind: pattern-query}` for a `query-coupled` key.

The latter does not duplicate the source/plan/query/policy: it requires their
presence in and resolution from the key. Query-independent implies
`searchPolicy: exhaustive`; query-coupled requires `existential-first`.
Query-coupled exhaustive execution has no v2 arm because its collection is
canonically reusable before selecting a query. An existential stop under
query-independent identity, or a query-coupled collection evaluated against
another query, rejects.

`visited` is semantic visit order. Each record contains exactly:

```text
branchKey, visitOrdinal, trace, traceOccurrence, disposition
```

`visitOrdinal` equals the zero-based array position.
`branchKey` is `k-in-k/branch-occurrence/v1` over
`{collectionScopeId, invocationDigest, visitOrdinal}`.
`traceOccurrence` is `k-in-k/trace-occurrence/v1` over
`{collectionScopeId, invocationDigest, branchKey, visitOrdinal, trace,
disposition}`. Including disposition prevents a refreshed ID from moving the
same trace occurrence between a normal and failed path. The pair
`{collection key, branchKey, traceOccurrence}` is the portable occurrence
join. A bare trace digest, branch key, or occurrence key is insufficient.

`trace` is an event-trace/v2 key and may equal another record's trace key.
Every resolved trace's definition equals the attempt subject definition and
its vocabulary equals the attempt's exact observation/event interface; empty
event arrays are not exempt.
`disposition` is the exact closed union `normal`, `stuck`, `semantic-crash`,
`query-satisfied`, `depth-limit`, `time-limit`, `branch-limit`, `result-limit`,
`resource-limit`, `solver-unknown`, or `backend-failure`. `normal`, `stuck`,
and `semantic-crash` carry their exact kind-compatible BAG-09 terminal/crash
value. `query-satisfied` carries no terminal or failure, is permitted only on
the final visited record of an existential `match-found` collection, and must
have that collection's canonical stopping witness. It is forbidden on an
earlier record and under every other stop. This is BAG-09's terminal-free
query-satisfied outcome, not an alias for normal termination. Each
limit/unknown arm embeds one exact BAG-10 value with stage
`execution`, context `pattern-path`, scope `path`, and the matching admitted
classification. `backend-failure` embeds the admitted `backend-error` value at
that same context/scope. No undefined generic semantic or infrastructure arm
is added; producer failure has no collection. A record has no pending work,
receipt, worker order, native KCFG ID, or supplemental diagnostics.

`pendingWork` is exactly `{discoveredCount}` with a nonnegative integer. It
counts discovered frontier units, not guessed future branches, and contains no
trace or branch identity. The global `stopReason` is the closed union
`search-exhausted`, `match-found`, `depth-limit`, `time-limit`,
`branch-limit`, `result-limit`, `resource-limit`, `solver-unknown`,
or `backend-failure`. Every limit/unknown arm embeds the exact admitted BAG-10
`pattern-test` value with matching execution classification;
`backend-failure` embeds `backend-error` at `pattern-test`. The first two carry
no failure. Infrastructure producer failure publishes no collection and is
represented only by the failed receipt/component arm. Global stop, execution
wrapper terminal/failure, each path
disposition, BAG-14 reuse class, and producer receipt terminal/failure are
validated together; none is inferred by equal spelling alone.

## Collection-aware pattern denotation

`pattern-result/v2` contains exactly:

```text
schemaVersion, resultId, collection,
patternSource, patternPlan, patternQuery, sideConditionTable, searchPolicy,
pathResults, witnesses, decision
```

`resultId` is `k-in-k/pattern-result/v2` over every field except itself. The
record consumes one collection key and exact BAG-11 source, plan, selected
query, and side-condition-conformance-table key. `decision` is the exact union:

- `{kind: match, completeCoverage, primaryWitness}`;
- `{kind: no-match, completeCoverage: true}` for a nonempty exhausted
  collection;
- `{kind: no-match, completeCoverage: true, emptySearchDecision}` for an empty
  exhausted collection;
- `{kind: unknown, completeCoverage: false, reason}`, where `reason` is exactly
  `{kind: indeterminate-denotation, firstIndeterminate}` or
  `{kind: execution-stop, failure}`; or
- `{kind: error, completeCoverage: false, failure}`.

`firstIndeterminate` is exactly `{collection, visitOrdinal, branchKey,
traceOccurrence}` and names the first visit-order trustworthy path whose
BAG-11 finite denotation is indeterminate. The execution-stop and error
failures are embedded typed BAG-10 values selected by the arithmetic below.
`emptySearchDecision` equals the collection's resolved produced key and is
forbidden in every other arm. The result
identity covers the effective search policy derived from the execution key,
ordered path records, witnesses, and decision; it never covers the later
evaluation receipt. Its `pathResults` has
exactly one record for every visited collection record, in visit order,
including an empty trace and every incomplete or error disposition. Each path
contains exactly `visitOrdinal, branchKey, trace, traceOccurrence,
disposition, evaluation`. `evaluation` is either `{kind: trustworthy, status:
match | no-match | unknown, denotation, witnesses}` with the complete BAG-11 finite
denotation, or `{kind: untrustworthy, failure}` with no witness or claimed
denotation. Trustworthy `unknown` means no candidate was proved true and at
least one side-condition lookup was `unknown`; it has no witness, is not a
BAG-10 failure, cannot prove absence, and always forces false complete coverage.
Another path's proved witness may still make the overall existence decision
`match`, but cannot make coverage complete. A proved witness makes its own path
`match` even when another candidate on that same path was indeterminate. The
occurrence fields and disposition equal the resolved
collection record. Mixed keyed/unkeyed paths and a singleton replay edge are
invalid.

Every witness repeats the collection key, visit ordinal, branch key, trace key,
and trace occurrence of its path, plus BAG-11's arm ordinal, event-index tuple,
canonical bindings, predicate, and event evidence. Its replay occurrence key
is `k-in-k/pattern-witness-occurrence/v2` over all of those fields and the
selected query. Witnesses sort first by collection `visitOrdinal`, then by
BAG-11's accepted within-trace order: lexicographic event-index tuple,
canonical binding digest, and arm declaration ordinal. A hash/replay key never
precedes semantic occurrence order. Identical trace content in two branch
occurrences is evaluated twice and yields occurrence-distinct witnesses; it is
not deduplicated by trace digest. `primaryWitness`, when present, equals the
first witness in this collection-aware order.

The finite validator independently derives each path denotation from its
resolved trace, plan, vocabulary, side-condition table, and occurrence. It
then derives the exact full witness list. No path, outcome, completeness, or
witness is trusted from the artifact. A witness outside the collection,
wrong occurrence, wrong query, wrong first witness, omitted duplicate
denotation, or digest-only join rejects even after every affected ID is
refreshed.

### Pattern-evaluation operation version 1

The generic invocation arm contains exactly the collection key, execution v2
result key, exact source/plan/query/table keys, and the effective search policy. Its
inputs have the closed ordered roles `execution-result`, `branch-collection`,
`pattern-source`, `pattern-plan`, `pattern-query`,
`side-condition-conformance-table`; its sole child role is
`execution-production`, naming the completed execution v2 receipt; and its
sole output role is `pattern-evaluation-result`. The child output must be the
paired execution wrapper, whose nested collection must be the input
collection. The effective policy and query relation must equal the execution
attempt kind exactly. For query-coupled execution, the table also equals the
attempt key; for query-neutral exhaustive execution, the later evaluator's
table is the sole denotation authority and therefore changes the pattern-
evaluation invocation without changing the reusable execution. For an empty collection, the invocation resolves the
same empty-search-decision through both the collection and execution wrapper;
the marker is not a separate evaluator-selected input.

`pattern-evaluation-result/v1` contains exactly its schema version, result ID,
invocation digest, and the one independently derived pattern-result/v2 key.
Every schema-valid, fully resolved finite evaluation invocation is a pure total
derivation and completes with that wrapper, null receipt failure, and semantic
terminal equal to the derived pattern decision. Denotational `unknown` and
`error` are pattern-result outcomes, not operation failures. Malformed,
unresolved, or inconsistent inputs reject before an invocation/receipt exists.
A producer-failed receipt is available only for the exact BAG-16
infrastructure/`pattern-test` placements above and publishes no wrapper. The
wrapper never contains its completed receipt; BAG-16 introduces no completed-
failure arm, failure context, or infrastructure alias for this pure evaluator.

### Oracle-operand-production operation version 2

The v2 execution-pattern arm contains exactly the declaration, subject,
pattern-evaluation invocation and result wrapper, resolved pattern-result/v2,
collection, and effective query/policy roots. Its ordered inputs are the
declaration, pattern-evaluation result, pattern result, and collection. Its
sole child is the completed pattern-evaluation receipt, and its sole output
role is the accepted `oracle-operand-production-result`. The child output must
equal the paired pattern-evaluation wrapper; success must name the exact
pattern result consumed by the BAG-12 projection. No execution trace or
singleton replay edge may be substituted.

Projection eligibility is exact. `pattern-outcome-v1` accepts a validated
`match` even when coverage is false, while `no-match` requires true complete
coverage. `pattern-outcome-bindings-v1` requires exhaustive policy and true
`completeCoverage` for either match or no-match because it represents the
complete binding multiset, not a known prefix. Unknown/error results are never
operands. A mixed match/indeterminate result or bounded/error-suffix match may
therefore produce outcome-only evidence but cannot produce bindings evidence.

The accepted oracle-operand-production result-wrapper schema and BAG-12
oracle-operand value schema remain semantically unchanged: their generic
`pattern-result` key resolves through artifact-role-specs/v2 to the v2 result.
The operation version, v2 invocation/receipt schemas, pattern result,
collection, pattern-evaluation wrapper, and child receipt all enter the exact
closure registry. This arm is required for BAG-12 execution-pattern operands.

The v2 finite-row arm covers concrete-output, reachability, and
structured-predicate declarations. It contains the declaration, subject,
execution-v2 invocation/result, collection, exact registered BAG-12 finite row
and query/table inputs, and the selected collection occurrence tuple for every
row producer trace. Its generic inputs are closed per declaration kind and in
this exact order: common `declaration`, `execution-result`, and
`branch-collection` edges; then concrete-output adds
`semantic-output-finite-table` and one `row-terminal`; reachability adds
`reachability-conformance-table`, `reachability-query`, then one repeated
`row-terminal` edge per row terminal in row order; structured-predicate adds
`predicate-conformance-table`, `predicate-query`, and one `predicate-input`.
Those are the only finite-row input edges. Its sole child edge is
`execution-production`, naming the completed execution-v2 receipt, and its sole
output role is `oracle-operand-production-result`. The child output equals the
paired execution wrapper, whose nested collection equals the collection input.

This arm is eligible only for a query-neutral `observed-exhaustive` execution
whose collection stops `search-exhausted` with pending zero and whose every
visited disposition is producer-complete `normal`, `stuck`, or
`semantic-crash`. The exact empty-search decision is required for zero visits,
but the accepted BAG-12 finite-row schemas have nonempty input vectors, so a
zero-visit collection cannot select this arm. A limit, solver/backend stop,
query-coupled or existential attempt, `query-satisfied` occurrence, failed
producer, or incomplete/untrustworthy occurrence is not a normal operand and
must flow through BAG-10/BAG-12 absence/failure semantics instead. A row's
reachability row's `finiteComplete` must be true and does not establish this
collection gate; concrete-output and predicate rows have no such field. The
collection independently establishes the common gate for all three kinds.

Every finite-row `producerTrace` entry must resolve as event-trace/v2 and join
one exact `{collection, branchKey, traceOccurrence}` in row order; omitted,
surplus, reordered, digest-only, or v1 producer traces reject. The semantic
input also joins that same occurrence, not merely its content-identical trace:
a concrete-output row's exact terminal evidence equals the occurrence's
normal/stuck disposition and terminal artifact, and its collection has exactly
that one visited occurrence; a reachability row's ordered
`(producerTraces, terminalStates)` vector equals the complete collection visit-
order vector, using each normal/stuck terminal artifact and each semantic-crash
artifact's exact `terminalState`; and a predicate row's `input` equals the
normal/stuck occurrence terminal selected by its `producerTrace`, with that
occurrence the collection's sole visit, after which its input projection and
bindings are independently rederived. Thus no row may omit or add a collection
occurrence, even when another occurrence shares trace content. Query, table,
subject, test invocation, definition, and profile roots must also equal the
declaration, execution key, and selected row. The portable row's truth,
predicate, and output projection/comparison semantics remain byte-for-byte
those accepted by BAG-12. Collection membership proves only that this finite
operation consumed the recorded trace; BAG-12 `finiteComplete` never proves
native branch exhaustion.

Every live BAG-12 declaration in the v2 active catalog reruns BAG-12's accepted
inline-normal-expectation dispatcher before any gate or comparison. The
declaration kind selects the exact schema branch; the validator resolves and
rederives all referenced terminal states, output bytes/hash/text, reachability
witnesses, pattern results, predicate inputs/projections/bindings, and
applicable definition/query roots. Historical inline execution-pattern
expectations resolve through their exact v1 role-spec arm; a BAG-16
collection-backed expectation resolves through the v2 pattern-result arm and
must equal its exact collection/query denotation. The same projection gate
applies before accepting an inline value: bindings requires exhaustive true
coverage, while outcome-only permits a false-coverage match but never an
incomplete no-match. Comparator projection never
authorizes skipping this validation. Missing active-catalog material,
wrong-version dispatch, or refreshed IDs around a provenance-equivalent but
wrong terminal/query value reject.

Exit-stop and final-result retain their accepted singleton operation-v1 paths
as historical evidence until a later portable packet explicitly defines
multi-branch selection for those projections. BAG-16 does not relabel them.

## Search, terminal, completeness, and reuse arithmetic

The verifier derives rather than trusts all counts and claims:

- visited count is `len(visited)`; visit ordinals are contiguous semantic
  visit order, never lexical branch order or worker-completion order; pending
  count is exactly the declared discovered frontier count;
- `search-exhausted` requires pending zero. Any limit, unknown, or backend
  stop carries its exact embedded BAG-10 value and is incomplete;
  `match-found` carries no failure and is valid only for query-coupled
  `existential-first`;
- `normal`, `stuck`, and `semantic-crash` paths have trustworthy `match`,
  `no-match`, or side-condition-indeterminate `unknown` evaluations.
  `query-satisfied` has trustworthy `match` only. Every limit, solver, or
  backend disposition has an untrustworthy evaluation with the exact equal
  path failure. No other disposition/evaluation pairing is valid;
- `exhaustive` forbids `match-found` and every `query-satisfied` path. Its
  decision is `match` whenever at least one trustworthy witness exists, even
  if a later path or global stop is unknown/error; this proves existence but
  complete coverage is false. With no witness, `error` has precedence when
  any path or global failure has error consequence, then `unknown` when any
  evaluation is indeterminate/untrustworthy or the global stop is not a clean
  exhaustion, and otherwise `no-match`;
- `existential-first` with `match-found` requires a nonempty visited prefix,
  every earlier path to be a trustworthy nonmatch, and the final visited path
  to be `query-satisfied` and contain the first validated witness. Its decision
  is exactly `match` with false complete coverage, even with pending zero;
- `existential-first` may also end `search-exhausted`; then it obeys the same
  no-witness precedence as exhaustive search. Any witness under existential
  `search-exhausted`, a limit, solver stop, or backend stop rejects because the
  policy should have produced `match-found` at its first witness. Thus honest
  existential exhausted no-match is representable without allowing a second
  successful stop route;
- true complete coverage requires `search-exhausted`, pending zero, every
  visited evaluation trustworthy and conclusive `match` or `no-match`, and the
  exact empty-search decision when there are no visits. A side-condition-
  indeterminate trustworthy path covers its trace but not the query denotation
  and therefore makes result complete coverage false. Zero pending without
  `search-exhausted` is never proof;
- outcome `no-match` requires true complete coverage, every nonempty visited
  path a trustworthy nonmatch, and no witness. `unknown` and `error` retain the
  exact prefix but cannot assert absence or complete coverage;
- an empty visited array is a complete no-match only under
  `search-exhausted`, pending zero, and an explicit trustworthy empty-search
  decision produced by execution v2; absence of records alone is not that
  decision;
- for an `error` decision, select the first visit-order embedded failure whose
  taxonomy consequence is error, or the global error failure when no path
  carries it. For `unknown`, select an execution-stop reason first: global
  unknown failure, then the first visit-order untrustworthy unknown failure;
  if neither exists, select `indeterminate-denotation` with the first
  visit-order trustworthy unknown path. This priority is total and is
  independently derived; and
- a limit/unknown/failure disposition must agree with its global stop and
  execution terminal where it caused termination. Earlier completed path
  dispositions may differ, but no later visit may appear after the stopping
  occurrence. Cache classification first applies BAG-14's inherited production
  and conformance gate: `executionConformance: not-proven` always makes the
  evidence `diagnostic-only` and the reuse class `not-reusable`, regardless of
  an otherwise clean or bounded collection. It cannot be promoted by a receipt,
  wrapper, terminal, pending count, or refreshed IDs. A finite-vector-proven or
  native-proven record with exact receipt/output/material agreement then
  inspects both the global stop and the complete nested collection with this
  closed terminal precedence: any global or nested
  backend/infrastructure/diagnostic failure makes the evidence
  `diagnostic-only` and the reuse class `not-reusable`; otherwise any global or
  nested depth/time/branch/result/resource limit or solver-unknown makes both
  the evidence and reuse class `exact-bounded-attempt`, reusable only under
  BAG-14's identical-key bounded rule; otherwise a validated `match-found`, or
  a trustworthy all-semantic `search-exhausted`, makes both
  `semantic-result`. No other combination is valid. This covers empty and
  clean-prefix global-only stops, gives a later global backend failure
  precedence over an earlier bounded path, and prevents a later clean global
  stop from erasing earlier incomplete/error evidence. The cache terminal,
  evidence class, reuse class, receipt failure, and every nested path
  disposition must agree with this precedence. Query-
  evaluation indeterminacy does not rewrite the already produced query-neutral
  collection's cache class. Neither `match-found` nor pending zero upgrades
  native conformance.

The pattern result's `completeCoverage`, outcome, failures, witnesses, path
statuses, and the cache-record/v2 terminal, evidence class, and reuse
class must equal this derivation. A completed receipt only proves atomic
publication; it does not turn an untrustworthy path into semantic evidence.

## Exact corpus slots, components, and aggregate

`corpus-manifest/v2` contains exactly:

```text
schemaVersion, manifestId, definition,
compatibilityProfileDigest, observationManifestDigest,
executionMode, solverProfileDigest, executionProfileDigest, bounds,
aggregation, tests
```

`aggregation` is exactly `{question: corpus-exists, schedulingPolicy,
failurePolicy: preserve-unknown-error}`; scheduling policy is `full` or
`stop-after-test-match`. `manifestId` is `k-in-k/corpus-manifest/v2` over every
field except itself. All roots retain their accepted v1 meanings and resolve
through the closure envelope's active catalog; the v2 manifest does not retain
v1's redundant flattened `patternQueries` alias or a catalog ID. The catalog
may contain the manifest, so copying `catalogId` into `manifestId` would create
an unsatisfiable catalog/manifest fixed point. The enclosing closure, not the
semantic manifest, binds the exact resolver snapshot.

`tests` is ordered. Each test contains exactly `{testOrdinal,
testInvocationDigest, slots}`. The digest resolves the exact query-neutral
execution-test-invocation/v2. Its program, parser, and options are exact
catalog-resolved test-local roots; its test ID and start symbol are likewise
test-local, while its bounds equal the manifest's global bounds. `testOrdinal`
equals its array position. Each ordered declaration/query slot contains
exactly:

```text
testOrdinal, slotOrdinal, slotId, testInvocationDigest,
declaration, patternSource, patternPlan, patternQuery,
sideConditionTable, searchPolicy
```

`slotOrdinal` is the zero-based position within the test. `slotId` is
`k-in-k/corpus-slot/v1` over all fields except itself.
Declaration/source/plan/query/table must be BAG-11's exact test-scoped selection;
repetitions are preserved. `searchPolicy` is `exhaustive` or
`existential-first`. Runtime requested/skipped state is forbidden in the
manifest and appears only in component results. Flattening is test order then
slot order.

For `exhaustive`, all slots of the same exact subject/test/observation attempt
roots select the one canonical query-neutral BAG-14 `observed-exhaustive`
execution key and may fan out to distinct pattern evaluations. For
`existential-first`, every slot selects its own BAG-14 `query-coupled` key with
the exact source/plan/query/table/policy. A component invocation contains exactly:

```text
schemaVersion, componentInvocationId, corpusManifest, slotId,
testOrdinal, slotOrdinal, executionAttemptKey, patternEvaluationRequest
```

Its ID is `k-in-k/corpus-component-invocation/v1` over all fields except
itself. `patternEvaluationRequest` is the cycle-free exact record
`{operationKind: pattern-evaluation, operationVersion: 1, patternSource,
patternPlan, patternQuery, sideConditionTable, searchPolicy}` and equals the
projection of those five semantic fields from the manifest slot. It does
not name an execution output, collection, downstream invocation, or receipt.
The execution key resolves every program, parser, options, bounds, profile,
lowering, isolation, observation, subject, and query/policy root; there are no
independently editable copies. The actual pattern-evaluation invocation can be
formed only after producer-complete execution and must equal this prior request plus
the produced execution wrapper/collection edges.

A component result has the common exact prefix
`{schemaVersion, componentResultId, kind, corpusManifest, slotId,
testOrdinal, slotOrdinal}` followed by exactly one closed arm:

- `evaluated` adds exactly `componentInvocationId, executionAttemptKey,
  executionResult, executionReceipt, collection, patternEvaluationInvocation,
  patternResult, patternEvaluationResult, patternEvaluationReceipt`;
- `execution-failure` adds exactly `componentInvocationId,
  executionAttemptKey, executionReceipt`, requires producer status `failed`,
  and has no wrapper, collection, or pattern child;
- `pattern-failure` adds exactly `componentInvocationId,
  executionAttemptKey, executionResult, executionReceipt, collection,
  patternEvaluationInvocation, patternEvaluationReceipt`, requires the pattern
  producer status `failed`, empty outputs, null semantic terminal, and an exact
  admitted infrastructure failure, and has no pattern result or evaluation
  wrapper; or
- `skipped` adds exactly `schedulingReason`, whose arm identifies the earlier
  matching test as `{kind: stop-after-test-match, stoppedAfterTestOrdinal}`,
  and has no attempt, wrapper, collection, result, receipt, or component-
  invocation key. The verifier rederives the named earlier test's match from
  prior components; the marker cannot assert it.

Every completed execution v2 receipt, including a limit, unknown, or backend
terminal with a recorded collection, must flow to
pattern evaluation so that the exact trustworthy/untrustworthy visited prefix
is represented. It cannot be shortened to `execution-failure`. That arm is
reserved for atomic producer failure with no wrapper or collection.

Every producer-complete non-skipped edge is paired wrapper plus producing
generic receipt and must resolve to the slot's exact invocation. An
`execution-failure` or `pattern-failure` instead resolves the
exact requested invocation through its failed receipt, requires empty outputs
and null semantic terminal, and forbids the absent wrapper. `componentResultId` is
`k-in-k/corpus-component-result/v1` over the union record except itself. It
does not contain its own corpus-derivation receipt. `schemaVersion` is the
constant 1 in every arm, and `kind` is exactly the selected arm name; neither
field may be duplicated inside the arm payload or omitted from the ID domain.

The corpus scheduling policy is explicitly `full` or `stop-after-test-match`
and is distinct from within-attempt search policy. `full` requests every slot.
`stop-after-test-match` evaluates all requested declaration slots of a test in
slot order, folds that test, and may skip only the suffix of later tests after
the first test-level match. It never skips the remaining declarations of the
matching test. Execution or pattern failure folds to the exact test-level
unknown/error state under the declared corpus failure policy; it is not a
match. Skipped slots have no producer evidence.

The `corpus-exists` fold is exact. A test is `match` when at least one slot has
a validated match; otherwise it is `error` if any slot has an error,
`unknown` if any slot is unknown, and `no-match` only when every slot is a
complete no-match. A corpus is `match` when at least one test is match;
otherwise it is `error` if any requested test is error, `unknown` if any is
unknown, and `no-match` only when every requested test is a complete no-match.
Thus a validated existential witness is not erased by another slot's failure,
but a failure cannot prove absence. Under `full`, later matches still override
earlier unknown/error for the existence question. Under
`stop-after-test-match`, the first matching test is the stop point after its
entire slot list has been folded; every later test and slot is skipped. Empty
test or corpus arrays are rejected rather than treated as vacuous no-match.

Every non-skipped component has one derived component decision. The evaluated
arm uses its exact pattern-result decision; execution/pattern failure uses the
exact receipt failure and its BAG-10 consequence. A test `error` selects the
first slot-order error component; if there is no match or error, test `unknown`
selects the first slot-order unknown component. A corpus `error` selects the
first test-order selected error component; if there is no match or error,
corpus `unknown` selects the first test-order selected unknown component.
Match always has precedence for this existential question. Selection is over
manifest test/slot order, never failure digest, receipt order, or completion
time.

`corpus-result/v2` contains exactly `schemaVersion, corpusResultId,
corpusManifest, schedulingPolicy, components, testResults, decision`.
`corpusResultId` is `k-in-k/corpus-result/v2` over every field except itself.
`components` is the exact flattened ordered component-result key sequence.
`testResults` is the exact test-order sequence of `{testOrdinal, slots,
decision}`, where slots are that test's contiguous component keys and decision
is the closed union: bare `match` or `no-match`; `unknown` or `error` with
exact `{causeComponent, cause}`; or `skipped` with its exact scheduling reason.
`cause` equals the resolved component's embedded BAG-10 failure or
side-condition-indeterminate reason without normalization. Top-level
`decision` is a separate closed four-arm union: `{kind: match,
completeCoverage}`; `{kind: no-match, completeCoverage: true}`; or `{kind:
unknown | error, completeCoverage: false, causeComponent, cause}` with the
exact selected cause. It has no `skipped` arm because a nonempty corpus always
derives one of those four outcomes even when later tests are skipped. Any other failing
component, a different failure from the selected component, or digest-order
selection rejects. These arrays are sequences, not sets or joins by bare
query/trace digest. `completeCoverage` is true exactly when there is no skipped,
execution-failure, or pattern-failure component, every manifest slot has its
one ordered `evaluated` component, and every resolved pattern result has true
complete coverage. This permits `full` and a stop-after-test-match run that
happens to exhaust all slots without scheduling a suffix; any producer failure,
incomplete pattern result, omitted component, or intentional scheduled suffix
forces false.

### Corpus-derivation operation version 1

The generic invocation contains the exact manifest, scheduling policy, and
flattened selected component-result sequence. Its ordered inputs are manifest
then component results. Its ordered child receipts are derived per component
in flattened order: evaluated and pattern-failure arms contribute execution
production then pattern evaluation (completed for evaluated, failed for
pattern-failure), execution-failure contributes only its
failed execution receipt, and skipped contributes none.
Repeated reuse of one execution or pattern-evaluation receipt is permitted
only when repeated manifest slots resolve to the identical invocation. The
corpus-derivation operation explicitly declares repeated child-edge
cardinality in those flattened slot positions: each occurrence retains its
edge, including identical query-coupled execution and pattern-evaluation
receipts, and pairs with the identical wrapper/collection each time. Repetition
outside those manifest-derived fan-out positions rejects. Skipped components
contribute neither child.
Its sole output role is `corpus-derivation-result`.

`corpus-derivation-result/v1` contains exactly schema version, result ID,
invocation digest, and the independently derived corpus aggregate key. Every
schema-valid derivation invocation deterministically produces that wrapper and
aggregate; component execution/pattern failures are data folded into the
aggregate's error/unknown decisions, not a second operation failure route.
Malformed or unresolved invocation graphs and corpus-shared-setup failures
reject before a derivation invocation/receipt exists. There is no completed-
failure or producer-failed corpus-derivation arm because BAG-10 admits no
producer/infrastructure placement for this pure fold. The completed receipt
has null failure and its semantic terminal equals the wrapper's aggregate
outcome. The wrapper never contains that receipt. The
aggregate is a root projection: its complete transitive receipt closure is
exactly the corpus-derivation receipt plus the child execution/pattern receipts
selected by its invocation. No campaign/report receipt, unused fixture receipt,
cross-corpus child, dangling output, or surplus component is reachable.

## Recursive registry closure

`portable-closure-root/v1` is the sole advertised BAG-16 evidence envelope.
It is a top-level canonical evidence envelope outside the BAG-08 artifact-role
vocabulary, containing exactly `{schemaVersion, closureId,
rootKind, result, receipt, cacheRecords, artifactRoleSpecs, artifactCatalog,
registry}`. `artifactRoleSpecs` and `artifactCatalog` are the complete
canonical artifact-role-specs/v2 and artifact-catalog/v2 records, their IDs
agree, and every reachable artifact resolves only through that embedded pair.
The envelope, catalog, and role-spec registry are not entries in that embedded
catalog, so no one hashes bytes that transitively contain its own catalog
entry and no self-cataloging regress is created.
`rootKind` selects one exact result role: execution-attempt-result,
pattern-evaluation-result, corpus-derivation-result, or
oracle-operand-production-result. The receipt must
be the completed/failed generic receipt for that exact result request; a
completed receipt must output the named result and a failed receipt has no
result, so failed-root arms use an exact null result. `cacheRecords` is the
duplicate-free execution-traversal-order sequence of cache-record/v2 keys for
every reachable completed execution receipt and is empty for a failed
execution with no wrapper. No caller may add or omit a cache record.

`registry` is the complete embedded replay-version-registry/v2 value, not an
out-of-band file choice or a relabelled BAG-15 v1 registry. `closureId` is
`k-in-k/portable-closure-root/v1` over
every field except itself, so changing the root, receipt, cache projection, or
resolver authority or registry changes the advertised closure. The envelope points backward to an
already complete result/receipt graph and is not produced by a new receipt.
It is provenance packaging, not a second producer mechanism or replay
invocation.

Starting at this envelope, traverse the exact typed artifact/wrapper/receipt/
cache closure and require set equality with its embedded registry. It must
include precisely the used schema byte digests and operation kind/version
pairs, including portable-closure-root/v1, cache-record/v2,
execution-attempt v2, pattern-evaluation v1, corpus-derivation v1,
oracle-operand-production v2, operation-invocation/v2, and
operation-receipt/v2, plus replay-version-registry/v2 itself, exactly when
reachable. Missing, surplus, duplicate,
aliased, stale-v1, or wrong-byte entries reject. The registry identity itself
is recomputed under BAG-15's rule. A bare result or receipt without this
envelope cannot make a BAG-16 registry-closure claim. Independent old BAG-15
closures remain valid with exactly their historical entries and must not be
globally forced to advertise BAG-16.

## Required evidence and permanent adversaries

Positive evidence must include:

- a two-branch exhaustive collection replayed through execution v2, pattern
  evaluation, and corpus derivation;
- two branch occurrences sharing one content-identical event-trace/v2 key but
  retaining distinct branch, trace-occurrence, path, and witness provenance;
- exact duplicate-free execution output ordering for every referenced
  terminal-state/semantic-crash and trace before the collection, including
  crash terminal-state then crash artifact then trace;
- exhaustive no-match and existential exhausted no-match with complete zero-
  pending coverage;
- a zero-visit exhausted collection with the exact produced empty-search
  decision and execution wrapper/cache ordering;
- a trustworthy side-condition-indeterminate path and exact unknown decision,
  plus a mixed match/indeterminate collection whose decision is match but whose
  coverage remains false;
- existential first-match with explicit prefix proof and honest incomplete
  coverage, including pending-positive and pending-zero examples;
- query-neutral exhaustive fan-out to two declaration slots and exact
  query-coupled existential identity;
- an execution-pattern BAG-12 operand produced through operation v2 from the
  exact collection-backed pattern-evaluation child; and
- concrete-output, reachability, and structured-predicate finite-row operands
  produced through operation v2 with exact occurrence-terminal joins and
  closed input/child edge order, including a multi-occurrence reachability row
  equal to its complete clean-exhausted collection vector;
- a global-only bounded stop and a global backend stop following an earlier
  bounded path, proving the closed cache precedence; and
- clean-exhausted and bounded collections with `executionConformance:
  not-proven`, both remaining diagnostic-only and not reusable before terminal
  precedence;
- BAG-12 positive inline expectations for every built-in pair through the v2
  catalog, plus one executable wrong-provenance case for each of the six kinds;
- full failure-component folds that force corpus `completeCoverage` false; and
- full and stop-after-test-match corpus folds with exact skipped-suffix
  evidence, cache-record/v2, closure-root-bound registry evidence, and
  deterministic multi-failure selection.

Permanent adversaries must reject omitted, extra, duplicate, reordered,
wrong-test, wrong-subject, wrong-invocation, wrong-query, wrong-policy, or
wrong-collection paths/components; a witness outside its collection; an
ambiguous digest-only join; duplicate/noncontiguous branch keys or ordinals;
pending work containing a fabricated trace; v1 trace/result supplied on a v2
edge; and a multi-branch result forced through the historical singleton edge.

Also reject a finite-row trace joined to the wrong occurrence terminal,
reordered reachability trace/terminal pairs, predicate input differing from its
occurrence terminal, a row omitting or adding a collection occurrence, any
finite-row operand from a bounded/solver/backend/existential/incomplete
collection, missing/surplus/reordered finite-row input or child edges,
an inline expected value accepted without its exact kind-specific validation,
a completed pattern-evaluation failure wrapper, a failure component with true
corpus coverage, a global-only stop without a cache class, a v1 registry used
for a v2 closure, and a legacy structured artifact dispatched through a
schema-version arm or vice versa.

Also reject top-level corpus `skipped`, and reject
`pattern-outcome-bindings-v1` production or inline expectation from a mixed-
indeterminate or bounded/error-suffix false-coverage match, including fully
refreshed enclosing IDs. The same false-coverage match remains a positive
`pattern-outcome-v1` case.

Also reject an execution wrapper/cache projection that omits, adds, duplicates,
or reorders an occurrence terminal-state, semantic-crash, trace, empty marker,
or final collection; and reject `finiteComplete` injected into the closed
concrete-output or predicate row shapes.

The cache adversaries include both unchanged and fully refreshed enclosing IDs
for promotion of `executionConformance: not-proven` to semantic-result or
exact-bounded-attempt. They must reject even when the collection terminal and
nested dispositions would otherwise select that class.

Also reject generic execution polluted by query identity, existential
execution missing exact query identity, exhaustive slots using query-coupled
keys, query-neutral existential collection, branch or occurrence identities
that omit collection scope/invocation/disposition, lexical or worker order in
place of visit order, witness hash order in place of BAG-11 order, an omitted
duplicate denotation for shared trace content, and a collection/output that
contains its own producing receipt directly or transitively.

Reject `completeCoverage: true` or `no-match` with pending work; zero pending
without `search-exhausted`; exhaustive `match-found`; existential early stop
without a final `query-satisfied` first witness or with an earlier match;
existential `search-exhausted`/limit/backend evidence containing a witness;
`match-found` claimed complete; side-condition indeterminacy relabelled as
no-match or BAG-10 failure; empty no-match without the exact produced exhausted
empty-search decision, or a marker on a nonempty collection;
failure/limit stop without its exact failure; terminal, failure, reuse, or
producer-status disagreement; and any untrustworthy path used to prove
absence.

Reject a component invocation that omits or duplicates test/slot ordinal, a
slot ID built from scheduling, a component with roots copied inconsistently
from its BAG-14 key, a skipped slot with any attempt/result/receipt, a stopped
test with unevaluated same-test declarations, a corpus fold out of manifest
order, a component/aggregate containing its own receipt, a separate branch
producer receipt, a non-generic receipt role, a missing/surplus registry entry,
an out-of-band registry not bound by the closure root, digest-order or
completion-order failure selection, or a BAG-16 entry injected into an
unchanged historical BAG-15 closure. Also reject cache-record/v1 with a
collection terminal, v1/v2 role dispatch by schema guessing or digest trial,
two same-key catalog entries distinguished only by schema version, and a
collection-backed pattern operand produced through operation v1.

For every identity-sensitive adversary, include both forms: unchanged parent
IDs and fully refreshed local/enclosing self-IDs. The relational validator must
still reject the refreshed form for wrong roots, occurrence, ordering,
terminal/failure arithmetic, wrapper/receipt direction, graph closure, or
registry set inequality. Merely proving that stale hashes reject is
insufficient.

## Ownership and dependencies

Integrate only after accepted BAG-11 supplies normalized query identity,
BAG-14 supplies exact attempt/cache/completeness rules, and BAG-15 supplies the
generic invocation, wrapper, receipt, DAG, and recursive registry contracts.
Extend that one graph and active catalog; do not load a second corpus,
observation, query, trace, or receipt registry by fixture filename.

The worker may modify corpus, pattern-result, event-trace/collection, operation
invocation/result-wrapper, replay, and registry schemas and fixtures; corpus,
pattern, replay, and adversarial vectors; artifact roles/catalog; contracts;
refresh helper; verifier; completion evidence; and Rust handoff notes. Do not
change mutation generation, redefine accepted v1 semantics, edit goals/D1/
roadmaps, invent native KCFG semantics, or run backend code.

BAG-12's reachability/predicate/output finite rows remain exact registered
conformance inputs. BAG-16 must lift their producer traces through the explicit
version boundary and exact execution-v2 production closure while preserving
truth/comparison semantics. It must never infer native exhaustive coverage
from a BAG-12 `finiteComplete` flag.

## Acceptance

- search policy is part of every relevant portable slot/invocation identity;
- execution v2 produces an occurrence-neutral trace collection through the
  sole BAG-15 result wrapper and receipt direction;
- path/witness coverage, stop/terminal/failure/reuse arithmetic, corpus slots,
  scheduling, root projection, and registry closure are exact and
  adversarially tested, including refreshed-ID variants;
- BAG-15 receipts remain the sole generic producing-provenance mechanism;
- historical v1 closure remains unchanged;
- official Draft 2020-12 and zero-backend validation pass;
- no K, Java, Haskell, Rust executor, compiler, backend, or solver command is
  run;
- checks are tiny and serial; and
- tracked and untracked whitespace checks pass.

## Stop rule

Stop rather than claiming native branch exhaustiveness, inventing KCFG IDs,
deriving solver feasibility, treating a portable receipt as proof that a
backend followed it, weakening accepted v1 identities, or extending the
retired backend-specific execution path.
