# Portable semantic contracts v1

Status: normative for the backend-agnostic conformance package, 22 August
2026. These are product semantics and interchange expectations, not a Rust API
or an internal IR layout.

## 1. Representation and identity

All portable artifacts are UTF-8 JSON with no floating-point values. Integers
are signed 64-bit. Duplicate object keys, lone UTF-16 surrogates, and strings
outside Unicode NFC are rejected. Object key order carries no meaning. Array
order carries meaning unless a field is explicitly declared to be a set.
The same boundary applies to every in-memory value passed directly to
canonicalization or digest derivation: only exact null, boolean, signed-64
integer, NFC string, list, and string-keyed dictionary host values are
accepted. Host coercions, scalar/container subclasses, non-string keys, and
cycles are rejected before sorting, serialization, UTF-8 encoding, or hashing;
shared acyclic values remain valid and serialize by value. Validation visits
arrays in index order and object keys and values in Unicode code-point key
order, yielding a deterministic reason and structural location without
normalizing or mutating the caller's value.
Canonical JSON is the compact UTF-8 serialization with NFC object keys sorted
by Unicode code point, no insignificant whitespace, JSON booleans/null in
lowercase, shortest decimal integers, and only quote, reverse-solidus, and
U+0000–U+001F escaping required by JSON. Non-ASCII scalar values are emitted
directly. This deliberately restricted profile removes the number and Unicode
ambiguities that full RFC 8785/ECMAScript canonicalization would otherwise
need to settle.

Every digest is lowercase SHA-256 over:

```text
UTF8(domain) || 0x00 || canonical-json(value)
```

The domain is a versioned ASCII string named by the owning schema. Digest
domains are never reused for a different semantic object.

A semantic sentence has distinct identity fields:

- `lineageId`: the stable relationship to one source or generated sentence;
- `contentFingerprint`: the complete sentence value at one revision;
- `bodyFingerprint`: the meaning-bearing body/conditions at one revision;
- human provenance: module, optional label, logical source, location, kind,
  and source/generated status. Every definition declares
  `representation: portable-mutation-semantic-slice-v1`; that representation
  field participates in the definition role projection and definition digest.

Labels are optional and may be duplicated. They are selectors only when an
operator declares and checks the expected cardinality. Absolute checkout paths
are not portable source identity. Generated identity records its generating
transformation and parent lineages. A content change preserves lineage when it
is a replacement of that sentence, but changes content/body fingerprints as
applicable.

For v1, an input lineage is deterministic within one baseline family. Its
digest input is the baseline-family ID, logical module, logical source URI,
source range, sentence kind, and `sourceOccurrenceOrdinal` among otherwise identical
source anchors. Checkout relocation does not change it. A file move or source
range move does; a label-only or body-only edit at the same anchor does not.
Cross-family lineage correlation is an explicit mapping artifact, never a
heuristic promise. Generated sentences have a null source occurrence ordinal.
Generated lineage uses the transformation ID/version, unique parent lineages
sorted in Unicode code-point order, generated role, and its sole deterministic
`generatedIdentity.ordinal`. Event
provenance refers to the original lineage plus the applied transformation
chain, so instrumentation does not erase mutation identity.

Identity digest inputs are the exact closed payloads under
`semantic-identity.schema.json`:

- `baselineFamilyId` uses `k-in-k/baseline-family/v1` over family name,
  sorted entry modules, and compatibility profile;
- input `lineageId` uses `k-in-k/input-lineage/v1` over baseline family,
  module, logical source, location, sentence kind, and source occurrence ordinal;
- generated `lineageId` uses `k-in-k/generated-lineage/v1` over
  transformation ID, ordered parent lineages, anchor identity, role, and ordinal;
- `bodyFingerprint` uses `k-in-k/sentence-body/v1` over the complete portable body,
  requires, and ensures terms;
- `contentFingerprint` uses `k-in-k/sentence-content/v1` over lineage,
  provenance, body fingerprint, attributes, and transformation chain;
- `definitionDigest` uses `k-in-k/definition/v1` over schema version,
  representation,
  baseline family, ordered modules/imports, and ordered sentence content
  fingerprints; and
- transformation identity uses `k-in-k/transformation/v1` over kind,
  operator ID/version, input definition digest, and manifest digest.

Module/import/source ordering in these payloads is semantic input ordering,
not map iteration. Only `entryModules` is declared a set and sorted before
hashing.

The portable definition fixtures additionally use `k-in-k/module/v1` over a
module name, ordinal, ordered imports, and ordered sentence content
fingerprints. Attribute preconditions use `k-in-k/attribute/v1` over the
canonical `{name, value}` attribute. These are semantic precondition
fingerprints, not host object hashes.

Every manifest/report fixture with a self-ID removes only that self-ID before
hashing the remaining normalized object. The domains are
`k-in-k/observation-manifest/v1`, `k-in-k/corpus-manifest/v1`,
`k-in-k/corpus-result/v1`, `k-in-k/replay-manifest/v1`,
`k-in-k/mutation-operator/v1`, `k-in-k/structural-diff/v1`,
`k-in-k/pattern-result/v1`, and `k-in-k/mutation-report/v1`. A mutation
campaign ID uses `k-in-k/mutation-campaign/v1` over its manifest digest,
operator identity, and scheduling mode.

The mutation execution policy uses `k-in-k/mutation-execution-policy/v1` over the policy without `policyId` and embeds the complete `k-in-k/isolation-policy/v1` record.
V1 has no suite-level cache key.
`keyDigest` uses `k-in-k/execution-attempt-key/v1` for one exact execution request or `k-in-k/oracle-evaluation-key/v1` for one exact typed oracle request.
`recordId` uses `k-in-k/cache-record/v1` over one immutable completed record without its self-ID.
`campaignInvocationId` uses `k-in-k/campaign-invocation/v1` over the schedule-specific request without its self-ID, and the cache mutation report uses `k-in-k/mutation-report/v1` over the selected-record closure and derived schedule result without its self-ID.
The ordered test/options and oracle declarations use `k-in-k/mutation-test-manifest/v1`, `k-in-k/mutation-options/v1`, and `k-in-k/mutation-oracle-manifest/v1` where those historical campaign artifacts remain active.
The field and catalog role for executor configuration are uniformly `executionProfileDigest` and `execution-profile`.
This digest identifies the complete canonical execution-engine configuration that may change observable behavior; it is distinct from semantic-family compatibility, solver configuration, per-test options, and explicit bounds.
A backend may construct the profile artifact, but corpus, pattern, replay, and per-attempt identities bind the same portable root without v1 aliases.

Pattern identity has three noninterchangeable BAG-08 keys. `pattern-source`
is the opaque K-authored byte artifact. `patternPlanDigest` uses
`k-in-k/pattern-plan/v1` over the complete normalized plan without its self
ID. `queryId` uses `k-in-k/pattern-query/v1` over the exact
`{patternSource, patternPlan, entryModule, exportedName}` record. The
self-identified query record contains exactly those four fields plus
`queryId`; entry and exported-name strings are preserved without imposing a
portable K identifier grammar. Generic `pattern`, `patternDigest`, and
untyped source/plan aliases are not v1 identities.

An observation vocabulary has semantic identity in
`k-in-k/event-vocabulary/v1` over its constructor mapping canonicalized by
constructor name. Constructor names are unique; ordered payload sorts and
origin mode are covered. Every plan binds that exact digest and resolves it
through one observation manifest. The compiler profile is provenance, not an
input to semantic `queryId`.

An execution-attempt key is a closed cycle-free request containing the exact operation and adapter versions, baseline or mutant subject, test invocation, compatibility/lowering/execution/solver profiles, isolation policy, and discriminated ordinary, observed-exhaustive, or query-coupled attempt kind.
A query-coupled attempt additionally binds the exact source/plan/query triple and BAG-11 search policy.
An oracle-evaluation key is a closed cycle-free request containing the exact operation and adapter versions, admission or comparison kind, test-scoped declaration, ordered typed operands or semantic crashes, and built-in evaluator identity or K-authored evaluator plus conformant authority.
Raw keys contain no output, terminal, result, status, schedule, timestamp, location, hit/miss, or receipt field.

A cache record repeats and recomputes its key digest, binds one kind-compatible terminal or typed oracle result, lists the complete ordered produced artifacts, carries positive completion evidence, and derives its intrinsic reuse class.
Only `semantic-result` and exact same-bounds `exact-bounded-attempt` evidence may be intrinsically reusable.
Diagnostic-only, incomplete, infrastructure/backend/worker failure, producer/output disagreement, and `not-proven` native execution are `not-reusable`.
Resolver capability is a separate lookup-time gate: `external-required` material may become available without changing any semantic ID, while it remains ineligible under the package's repo-only resolver.
Cache publication is all-or-none at the portable boundary; Rust must prove real storage atomicity and locking.

The BAG-14 finite seam is a registered deterministic input-to-output row whose input digest excludes terminal and output expectations.
It proves only the bundled vector result.
BAG-15 must add the native production-receipt branch deliberately; BAG-14 does not fabricate native production authority.

`first-kill` and `full` are report-construction policies, not raw attempt identity.
Both schedule-specific campaign invocation and report identities bind `scheduleMode`.
A first-kill report selects the exact prefix through the first derived kill and gives its skipped suffix no child record.
A full report may reuse that prefix only after every remaining selected slot has a valid record.
Uncached, partially cached, and fully cached folds over the same selected record IDs must produce byte-identical semantic reports because lookup provenance is supplemental.
One key with conflicting validated terminal, output, completion, or producer-provenance values is quarantined; no implicit newest/fastest choice is portable.

Baseline state is immutable; each mutant gets fresh writable state; no writable state is shared between mutants; and observer state is fresh for every test path.
Rust must prove native enforcement, but may not weaken this portable boundary.

Replay avoids an output/input digest cycle by separating its invocation from
its completed record. `invocationDigest` uses
`k-in-k/replay-invocation/v1` over the replay record without `replayId`,
`invocationDigest`, `expectedResultDigest`, or per-step `expectedArtifacts`
role/digest keys. A pattern result references this invocation
digest. After the result exists, `replayId` uses
`k-in-k/replay-manifest/v1` over the complete record except `replayId`,
including the expected result and artifact digests. Event-trace artifact
digests use `k-in-k/event-trace/v1` over the complete trace object.

Terms in interchange artifacts use the closed recursive `portable-term-v1`
algebra in `common.schema.json`: typed token, variable, application, rewrite,
sequence, and injection nodes. This is the normalized mutation-facing
semantic slice consumed by the two MVPs; it does not claim a complete K module
or production grammar. It covers the represented modules, imports, semantic sentences,
terms, conditions, attributes, and provenance. Sort declarations,
productions, module attributes, complete configuration metadata, macro/alias
detail, compiler-internal sentences, and other native forms are outside v1.
They may not be disguised as applications or silently dropped.

Applications carry a digest-shaped `symbolId` independently from their display
`label`. One definition graph assigns each ID exactly one display label,
result sort, arity, and ordered argument-sort sequence; distinct IDs may share
a label. Variables have one sort per sentence across body, conditions, and
attribute term values. Conditions are Bool-sorted, rewrite children have equal
sorts while the rewrite wrapper retains its independent sort, and injections
agree exactly with `fromSort`/`toSort`. Sequences remain ordered and acquire no
invented homogeneous/subsort law. Attributes are a unique name-keyed set whose
serialized list is already sorted by Unicode code point; validation rejects
noncanonical input rather than normalizing it.

Generated status is orthogonal to semantic `kind`: generated rules and claims
remain `rule` and `claim` with `generated: true`; `generated-rule` is not a v1
kind. A generated transformation chain ends in its transformation ID, and its
parents/anchor must resolve against the known transformation input or
destination boundary.

For parentless module-start/module-end insertion, the parent list is empty and
the anchor is deliberately the immutable input module fingerprint; other
generated roles require at least one parent. Standalone identity evidence
references the exact reviewed input and output definition artifacts. The
checker derives lineage and module-anchor sets from those definitions rather
than accepting claimant-declared ancestry sets. It resolves the generated
identity in the reviewed output: parented roles resolve every parent and their
anchor in the derived lineage sets, while parentless module roles resolve
their anchor in the reviewed input module set. Patch preflight also verifies a
module insertion anchor against the immutable baseline module.

The portable checker closes only these local invariants. Patch checking seeds
the symbol registry from the immutable baseline, checks every supplied value,
preserves replace-term/original-reference outer sorts, requires Bool condition
replacements, checks attribute target/name collisions atomically, and checks
the complete output. A successful diff states
`{portableApplication: applied-and-locally-well-formed, nativeIrValidation:
rust-proof-pending}`. Fresh consistent symbol IDs are therefore locally valid
but never native-valid evidence. Rust must enumerate the supported native K
forms and declaration/signature tables, then prove parsed-K/native-IR coverage
and injectivity for the explicitly declared supported surface for
mutation/observation. Unsupported or
lossy native forms must reject rather than disappear. Pretty-printed K is
never the semantic value.

## 2. Mutation discovery and selection

The four entities remain distinct:

- an **operator** owns structural discovery and mutation meaning;
- a **site** is one structural match in one immutable input definition;
- an **instance** is one operator plus one selected site or joined tuple and
  its bindings; and
- a **mutant** is the complete definition after one instance commits.

The backend/host may orchestrate but does not reproduce selectors using source
text, regular expressions, or host-language AST heuristics.

Discovery and policy derivation are separate. A mutation site registry records
the canonical site sequence, the canonical tuples emitted by the declared
K-authored join, and explicit discovery-exhaustion evidence. With a null join,
the tuple sequence is exactly one singleton per site. With a non-null join,
tuple members follow declared role order. The host never constructs a Cartesian
product or substitutes a different tuple sequence.

A selector clause's nullable `label` is an exact label filter when non-null
and imposes no label restriction when null. A site identity covers its typed
`termPath`; two matches in one sentence at different paths are distinct sites.

Selection policies derive instances from that registry:

- `exact` accepts a null unary registry or a declared N-role join. Only an
  exhaustive registry whose full tuple count and every tuple arity match
  `expectedTupleCount` and `expectedTupleArity` succeeds;
- `each` requires a null join with unary discovery tuples and derives one
  singleton instance per site in registry order;
- `tuple-each` requires a non-null join and derives one instance per supplied
  joined tuple in registry order; and
- `all-matches` requires a null join with unary discovery tuples. Zero sites
  derive no instance; otherwise every site is aggregated, in registry order,
  into one instance and at most one mutant.

For `all-matches`, `expectedTupleArity` remains the unary discovery arity. It is
not applied to the aggregate instance. Every instance records its underlying
`discoveryTuples`, each with its own canonical bindings. This prevents an
aggregate from merging same-named variables from different discovery tuples.
An ordinary instance has exactly one such record. Bindings within each record
have unique names ordered by name and use canonical `portable-term-v1` values.

Validation first checks registry identity, uniqueness, canonical tuple
membership/order, and exhaustion evidence; then policy/join compatibility and
discovery arity. Exhaustive `exact` zero/excess is
`cardinality-mismatch`; wrong arity or policy/join shape is `invalid-join`.
Either yields `selection-failed`, with no candidates, mutants, or score. Empty
exhaustive non-exact discovery is instead a complete empty generation.

Every policy has a positive candidate cap. The cap retains a canonical prefix
of the policy-derived instance sequence before patch deduplication. A
non-exhaustive registry or omitted derived suffix is `incomplete-generation`:
the retained prefix may be reported, but it is unscored and never claims that
the suffix is absent. A non-exhaustive `all-matches` aggregate is likewise only
a diagnostic hypothesis over the known prefix.

After patch evaluation, identical canonical patches produce one candidate with
every originating instance retained exactly once in derived sequence order.
Candidates, rejections, and mutants follow the ordinal of the candidate's first
origin; `candidateId` is only a tie-breaker. Refreshing a report ID cannot
legitimize omitted or permuted origins.

The digest-pinned patch template exposes a canonical `patchTemplateRoles`
interface. Each uniquely named role declares one patch operation and an
ordered nonempty list of selector roles. The declared source roles resolve to
the operator selector clauses in clause order and collectively cover that
selector interface; the host does not interpret template meaning.

Every retained origin carries one `editReceipt` per patch edit in patch order.
A receipt binds the edit, exact operator and patch-template identities, one
declared template role, and canonical sources from the origin's indexed
discovery tuples. Each source repeats its exact selector role and complete
tuple bindings. Receipt sources follow tuple/site order, exactly match the
template role's declared source-role order, and authorize the edit's target
lineage. Anchored insertions use their anchor lineage. Module-start/module-end
insertions remain valid general patches but are not provenance-complete
campaign edits in v1. Receipt sets are covered by `instanceId`; `editId`,
`patchId`, and `candidateId` remain unchanged so identical-patch deduplication
can retain distinct origin evidence.

## 3. Canonical patches and transactions

Every edit names its target lineage, expected target content fingerprint,
operation, and typed target path or deterministic sentence position as needed.
Replacement values are closed tagged values: lossless synthetic term,
lossless synthetic sentence, attribute name/value, explicit original-input
reference, or `none` for delete/remove. References never observe the result of
an earlier edit in the transaction. Insert at module start/end has null target
lineage/content and names the module; before/after insertion names and
fingerprints its anchor lineage.

Paths use the closed typed step array in `common.schema.json`: named semantic
fields, application arguments, sequence items, and attribute names. There is
no string escaping or host object-layout coordinate. Canonical edit order is
lexicographic over:

```text
(targetLineage, canonical-json(targetPath), operation, editId)
```

All edits are validated against the same immutable original definition before
any output definition is constructed. Validation progress is diagnostic only.
Commit happens once. On failure, `outputDefinition` is absent and
`appliedEditCount` is zero.

Within one sentence, edits are compatible only when their resolved target
regions are disjoint: neither path is identical to or a prefix of the other.
Identical target/path pairs are `duplicate-target`; ancestor/descendant edits
are `overlapping-edit`. Array
index changes caused by insert/delete are evaluated in original-input
coordinates and conflicting structural shifts are rejected. Distinct sibling
replacements may commit together. This is a v1 semantic decision; the accepted
R2 evidence proved only distinct-sentence atomicity and duplicate-target
rejection, so the same-sentence vectors await differential proof.

Supported semantic operations are `replace-term`, `replace-sentence`,
`delete-sentence`, `insert-sentence`, `replace-condition`, `add-attribute`,
`remove-attribute`, and `replace-attribute`. Insert positions are named
`before-lineage`, `after-lineage`, `module-start`, or `module-end`; no
incidental map/set iteration chooses a position. Adding an existing attribute
or removing a missing one is a precondition failure unless the operator
explicitly emitted an unchanged candidate, which is rejected as `no-change`.

Operation preconditions are closed. Term/condition/attribute edits require a
target lineage, current sentence content fingerprint, and nonempty typed path.
Replace/delete sentence use the empty path. Delete uses `none`; replace/insert
use a complete `portable-semantic-sentence-v1` value. Before/after insertion
names and fingerprints the same anchor lineage. Module-start/end insertion has
null target lineage/content and requires the module name plus current module
fingerprint. Every insertion position has an ordinal; multiple insertions at
one anchor/side are ordered by it, and duplicate ordinals conflict. Attribute
add requires a null expected attribute fingerprint; remove/replace require the
old attribute fingerprint. Deleting a sentence that anchors another edit,
editing a deleted/replaced sentence, or shifting the same structural region is
`overlapping-edit`.

Patch application is a transformation whose manifest digest is the patch ID.
An inserted sentence gets `k-in-k/generated-lineage/v1` identity from that
transformation ID, its parent lineages, its anchor identity, the insertion
position as its role, and the insertion ordinal. A sentence-relative anchor
identity is its lineage; a module-start/end anchor identity is the preconditioned
module fingerprint. Module-start/end insertions have no parent lineage.
Replacement preserves the target lineage; deletion removes
it. Normalized diff region fingerprints use `k-in-k/diff-value/v1` and record
old/new values plus affected provenance.

`vectors/patch-application-vectors.json` is the executable patch oracle. Its
`valueRef` fields select closed tagged values from that file's `valuePool`;
materialization computes edit and patch IDs before schema validation. The
string-path cases retained under `historicalRetiredStackShorthand` are only a
ledger of old evidence and are not a portable interface.

Candidate, patch, instance, and mutant IDs are content digests in their named
domains. A coupled transaction is one instance and one mutant regardless of
edit count.

The v1 digest payloads are exact:

- `siteId`: operator ID/version, baseline definition digest, target lineage,
  selector role, typed term path, and canonical bindings;
- `editId`: the edit value without `editId`;
- `patchId`: schema version plus canonical ordered edits;
- `instanceId`: operator ID/version, baseline digest, policy, ordered aggregate
  or ordinary site tuple, complete ordered per-discovery-tuple binding records,
  patch ID, and complete ordered edit receipts;
- `candidateId`: operator ID/version, baseline digest, and patch ID, allowing
  identical-patch deduplication while instance origins remain attached;
- `mutantId`: baseline definition digest plus patch ID; and
- report/replay IDs: their complete normalized manifests without their own ID.

Their digest domains are respectively `k-in-k/site/v1`, `k-in-k/edit/v1`,
`k-in-k/patch/v1`, `k-in-k/instance/v1`, `k-in-k/candidate/v1`,
`k-in-k/mutant/v1`, and the schema-named report/replay domains.

## 4. Observation and events

Observation instrumentation adds branch-local semantic state. An observed
semantic transition and its event/monitor update are one logical transition.
After erasing observation state, the instrumented definition must preserve the
original transition's applicability, program-state result, priority relations,
and branch structure for the supported rule subset. Unsupported or
non-conservative shapes fail before execution.

Observation selection is derived from the portable definition in module
ordinal and stored sentence order. The closed v1 selectors are `lineage`,
`label`, `attribute`, and `structural-term`; their complete derived lineage
lists must equal `matchedLineages` exactly, in definition order, and their
lengths must equal `expectedCardinality`. Duplicate or overlapping selections,
zero/excess cardinality, and any per-lineage validation failure reject the
whole installation without publishing a transformed definition.

`structural-term` is a deliberately bounded selector over
`portable-mutation-semantic-slice-v1`. It filters a nonempty, sorted,
duplicate-free sentence-kind set and an optional exact provenance label,
resolves a typed original-relative path from each retained sentence value,
requires an exact portable-term sort, and optionally requires an exact
application head label. A missing path, non-term value, wrong sort, or wrong
head is a non-match. Null `label` means no label restriction; null
`termHeadLabel` accepts any portable term of the declared sort. This selector
has no variables, recursive patterns, side conditions, negation, user
functions, or joins.

Arbitrary K-authored structural discovery is not part of this declarative v1
reference subset. Such an observer remains an opaque digest-pinned artifact
whose discovery and differential behavior require the native Rust stack; a
host must not approximate it with source text, regular expressions, or a
conventional AST heuristic, and it cannot be relabeled `structural-term`.

`RuleApplied` contains portable emitting-sentence provenance. Domain events use
declared constructors and typed K-term payloads. A manifest emission declares
either a null semantic site for an `emitting-sentence` event or a `{role,
termPath}` template for an `emitting-sentence-and-semantic-site` event. For
each actual emitting lineage, the concrete event origin carries `{siteId,
role, termPath}`, with `siteId` derived in `k-in-k/observation-site/v1` from
the observer digest/version, definition digest, target lineage, role, and
term path. One multi-match template therefore authorizes a distinct concrete
site identity for every selected lineage. Backend attempts, simplifier steps,
debugger records, and function-hook activity are diagnostics, not product
events unless a future compatibility profile explicitly promotes them.

The K-facing vocabulary may present an illustrative constructor such as
`memoryWrite(Address, Value, Origin)`. In JSON interchange, `payload` contains
only the declared semantic payload terms (`Address`, `Value`) and `Origin` is
losslessly decomposed into the mandatory event `origin` object. It is neither
dropped nor duplicated as an opaque payload term.

Every manifest payload binding uses a non-opaque typed source path into each
selected semantic sentence. The path must resolve to a `portable-term-v1`
value whose sort equals both the binding sort and its position in the declared
event vocabulary. Every semantic-site template path must likewise resolve for
every selected lineage. A missing path, non-term source, or sort mismatch
rejects the observation installation before a transformed definition is
accepted.

Each path owns its trace or monitor state. Event indices are zero-based and
contiguous on the **observed-event clock**. Transitions that emit no event do
not advance that clock. Events from sibling paths are never combined.

One transition may emit multiple events. Their order is fixed by the accepted
observation manifest: generic `RuleApplied` first when enabled, followed by
domain events in declaration order. An event records both transition ordinal
and emission ordinal. Duplicate manifest entries are rejected; runtime
scheduling never chooses event order.

## 5. Pattern meaning and witnesses

Patterns are authored in K. The portable boundary consumes a closed normalized
conformance plan produced from that source; JSON is not an authoring language
or an internal Rust IR. The v1 plan is flat, nonrecursive DNF with ordered,
nonempty arms. Each arm contains a nonempty atom list and exactly one fewer
relation than atoms. Atoms name an event constructor and a strictly increasing
list of unique payload positions. Relations are only `next-event` and
`eventually-after`. Recursive expressions, empty components, negation,
universal temporal claims, and extension nodes reject.

Top-level `{name, sort}` variables are the complete stable witness interface.
Names use the exact public witness-binding grammar
`^[A-Z][A-Za-z0-9_]*$`; plan declarations, payload bind/use clauses,
side-condition inputs, and persisted witness bindings cannot use different
name languages. Declaration order is semantic and is preserved exactly in
every witness binding list, including intentionally nonlexical order.
Every arm binds each declared variable exactly once, uses only declared
variables, preserves one sort per name, and has no hidden locals. Bind/use
order is exact `(atomOrdinal, payloadPosition)` order, so a later payload
position in the same event may use an earlier binding. Positions resolve
within the declared constructor arity and have the exact vocabulary sort.
Unknown constructors and vocabulary arity/sort/digest drift reject before
execution.

- `next-event(A, B)` requires event indices `i` and `i + 1` on one path.
- `eventually-after(A, B)` requires indices `i < j` on one path and permits
  any number of intervening observed events.
- Shared variables are K-term bindings under the path predicate and solver,
  not pretty-text or host-string equality.
- A witness contains the ordered matched indices/events, bindings, path
  predicate, provenance, explicit `armOrdinal` (including zero), bounds, and
  stop reason. It contains `pathKey` and `replayKey` together only when the
  executor can supply stable path identity.

An optional side condition contains one `pattern-side-condition` key, constant
result sort `Bool`, and a canonical declaration-order subset of plan
variables. Finite fixture evaluation uses the closed
`side-condition-conformance-table`: the exact key is condition artifact
digest, `k-in-k/bindings/v1` digest of the declared canonical input binding list,
and `k-in-k/path-predicate/v1` digest of the exact path predicate. Here the
binding list is exactly the declared `inputVariables` subset in plan
declaration order, not the complete witness interface; an empty list is a
valid constant side condition and hashes as canonical `[]`. The only
results are `true`, `false`, and `unknown`; a missing or differently keyed row
is `unknown`, never false. This table defines fixture denotation only and is
not a solver or evidence of equivalence to the K-authored condition.

For a single path with multiple valid occurrences, the canonical primary
witness is the lexicographically smallest event-index tuple, followed by the
canonical binding digest and arm declaration ordinal. Across keyed paths, the
executor returns all normalized witnesses in stable `pathKey` order, with the
same occurrence ordering inside each path, and selects the first as primary. A future
stack that cannot reproduce stable path keys must omit both keys, report all
witnesses, and leave `primaryWitness` absent rather than choose by scheduling
order. Unkeyed paths sort by intrinsic path-identity digest; witnesses within
each path sort by event-index tuple, binding digest, and arm declaration
ordinal, followed by a digest of the complete witness solely to make
serialization deterministic. That order never promotes an item to primary.

When a stable path key exists, `replayKey` is
`k-in-k/witness-replay-key/v1` over test ID, path key, and ordered event
indices. It identifies that exact replay occurrence but is not ordering
authority because hashing event indices can invert their semantic order.
Witnesses sort by path key, event-index tuple, binding digest, and alternative
declaration order. A present `primaryWitness` is exactly the first item in that
normalized list.

Occurrence matching scans the entire finite event sequence; prefix and suffix
events do not need to be consumed. Empty patterns and zero-length sequence
components are not in v1. Occurrences may overlap. Alternative arms retain
declaration order as the final deterministic tie-breaker, and identical arms
remain legal. A side condition
that is true admits a candidate, false rejects it, and solver-indeterminate
makes absence `unknown` unless another candidate supplies a match.

Every persisted finite result is checked against the complete denotation
independently derived from its resolved plan, event vocabulary, side table,
trace, and path predicate. Omitted, extra, reordered, or self-asserted
witnesses, bindings, arms, or path statuses reject even when the top-level
match/no-match outcome would remain unchanged.

K module imports, named entry lookup, and compilation remain K-facing source
semantics. A future native compiler receipt must bind exact source, normalized
plan, entry module/exported name, compiler profile/version, and diagnostics.
Portable plan validation is explicitly `not-proven` compiler conformance and
cannot promote a schema-shaped receipt to native evidence.

Retired `legacy-exact-trace` and other whole-trace evidence remains named only
as historical evidence. It cannot enter a v1 plan, query, witness, oracle
projection, or comparison. The normalized matcher always searches occurrences
within the finite trace; equality with the whole trace is not an operator.

Each execution-pattern declaration owns its own source/plan/query triple.
Every triple resolves its exact query artifact through the catalog, and its source and plan keys must equal that artifact's nested roots; every plan side condition likewise resolves through the catalog.
Corpus manifests flatten test declaration order followed by each test's query-selection order, preserving repetitions.
Mutation test invocations reproduce triples in exact per-test `oracleDeclarations` slot order.
Campaign requested plans retain mutation-test declaration order followed by each test's declaration-slot order.
Each query-coupled execution-attempt key binds only its exact selected source/plan/query roots, and each oracle-evaluation key binds its exact declaration and ordered semantic inputs; no suite-level flattened cache root exists.
Replay match steps consume event trace plus source, plan, and query keys.
Results, replay invocation/replay IDs, corpus IDs, mutation test/manifest IDs, per-attempt key/record IDs, policy IDs, and schedule-specific campaign/report IDs cover their respective roots.
Two named queries may share one source but must not share a query ID or be replaced by a global test query.

Search policy is an explicit replay input. `exhaustive` is the default and
continues through the declared finite search space. `existential-first` may
stop once a validated witness exists; the result is `match` with
`completeCoverage: false`, the stopping witness/path uses `match-found`, and
unvisited work is explicit rather than misclassified as exhaustive absence.
Replaying such a result uses the same recorded search policy. Path execution
termination (`terminal`, `stuck`, or a resource/solver stop) remains distinct
from this query-level early stop.

Every event trace carries an exact `definitionDigest`; even an empty-event
trace must resolve that identity and may not infer a definition from an empty
lineage subset. The trace predicate, every event payload, and every binding in
all witnesses for one `pathOrdinal` form one variable/signature graph scope.
Every event trace and corresponding pattern path carries the same
`executionTerminal`: null for query, limit, solver, and error stops; a
role-typed `terminal-state` key for normal or stuck completion; or a
role-typed `semantic-crash` key for an object-language crash. Terminal states
use `k-in-k/terminal-state/v1` over an exact `definitionDigest` and one complete
portable term from the declared semantic slice; term validation is seeded by
that definition's signatures. A trace accepts normal, stuck, or crash evidence
only when the terminal state resolves back to the trace's own
`definitionDigest`. Semantic
crashes use `k-in-k/semantic-crash/v1` over the execution-profile digest,
terminal-state key, and closed classification
`declared-object-language-crash`. Host exception text, process status, stderr,
stack traces, and pretty output cannot establish semantic-crash identity.

The current accepted evidence proves a single concrete head match and the
degenerate exact pair `[0, 1]` with two identical `RuleApplied` origins. It does
not prove distinct event types, gaps, subsequence search, sibling isolation, or
symbolic feasibility. Those vectors are contracts awaiting Rust differential
evidence.

## 6. Pattern outcomes and aggregation

Per query/test, exactly one outcome is returned:

- `match`: at least one validated feasible witness exists;
- `no-match`: the declared finite search space was exhausted with no witness;
- `unknown`: a depth, time, branch, result, resource, solver, or backend limit
  prevents an absence conclusion;
- `error`: invalid input/observer/pattern/definition or a global infrastructure
  failure makes the result untrustworthy.

A missing witness is never inferred from a trace alone. `no-match` requires an
explicit exhaustive stop. A bounded absence is `unknown`.

For existential corpus aggregation: a trustworthy match is conclusive even if
other paths/tests are unknown; otherwise a global error is `error`; otherwise
any incomplete path makes the result `unknown`; only complete absence is
`no-match`. A path-local error is incomplete and follows the same rule as
unknown unless it invalidates shared setup. Reports retain every component
status and do not erase uncertainty.

Corpus execution collects all tests by default. It stops before per-test work
for invalid shared setup and may stop early after a conclusive corpus-level
match only when the manifest requests it; skipped tests remain explicit. A
worker error never silently cancels already valid component results.

`corpus-manifest.schema.json` freezes the ordered test inputs and aggregation
policy. `corpus-result.schema.json` retains per-test and per-path statuses,
matching path keys, skips, failures, and derived counts. Component order is
manifest order. Empty corpora are invalid. A local path/test error contributes
incompleteness; only a shared-setup failure is a global `error`.

Conservativity compares the baseline execution tree with the instrumented tree
after erasure: program configurations, path predicates, parent/child topology,
terminal classification, and observable results must agree for the declared
profile. Observation terms, generated observation identities, and manifest
metadata are erased. A resource timeout can make this check inconclusive but
cannot demonstrate equivalence. Disabled observation is identity. Trace and
streaming implementations must return the same outcome, canonical primary
witness, bindings, and path predicate for every bounded finite conformance
trace; optimization state is not report-visible.

## 7. Mutation campaigns and scoring

The baseline definition must pass IR/lowering/backend validation and every
selected baseline oracle before candidates are scored. Otherwise the campaign
is `baseline-invalid` or `baseline-oracle-failed`, with no score.

A candidate may become:

- `killed`: at least one declared oracle distinguishes it;
- `survived`: every selected test/oracle completed and agreed with baseline;
- `invalid`: validation or compilation rejects the mutant;
- `timeout` or `unknown`: limits prevent a semantic conclusion; or
- `error`: infrastructure failure prevents a trustworthy result.

A proven semantic crash is a terminal operand, never a generic failure. An
infrastructure or backend crash is always `error` and never distinguishes a
mutant. `survived` requires complete execution. The default mutation score is
`killed / (killed + survived)`. Invalid, timeout, unknown, error, duplicate,
and no-change candidates are reported but excluded. Complete bounded agreement
classifies a valid mutant as `survived`; it never proves semantic equivalence.
V1 therefore has no equivalence status or opaque equivalence-evidence field.
A future `proven-equivalent` classification requires a later version with a
typed proof artifact, proof-system/checker identity, scope binding the
operator, baseline, mutant, and semantic profile, referential integrity, and
explicit score treatment. Rust implementation by itself is not such a proof
system. Syntactic no-change remains a candidate rejection, not semantic
equivalence.
The denominator and exclusions are explicit even when it is zero.

The score is serialized as an exact reduced rational `{numerator,
denominator}` with nonnegative numerator and positive denominator. When the
score denominator is zero, `ratio` is null. Decimal approximations are display
data and never part of the canonical report.

`first-kill` scheduling may stop after the first killing test in manifest
order. `full` scheduling records all killing tests. Either mode yields the same
mutant classification. The campaign report repeats the manifest's unique
ordered test IDs as `selectedTestIds`; every mutant carries exactly that order.
Under `full`, every test executes. Under `first-kill`, only the suffix after the
first killing test may be marked unselected and `skipped`. Multiple oracles are
disjunctive for killing, a killing test must reference a distinguishing oracle,
and every planned test must execute and agree before a mutant survives.

The manifest has one oracle authority: each test carries an ordered nonempty
`oracleDeclarations` array of role-typed declaration keys. There is no global
oracle-definition join and no per-test ID indirection. A declaration is
self-identified in `k-in-k/oracle-declaration/v1`, belongs to exactly one test
invocation and slot, and freezes the kind, four profile/bounds roots, baseline
gate, terminal/crash policies, projection, comparator, and kind configuration.
The live registry admits only these exact kind-compatible pairs:

- exit/stop class and declared object-program exit code;
- whole final term or ordered typed final-term paths;
- ordered semantic-output bytes or strict UTF-8 newline-normalized channels;
- finite reachability truth;
- execution-pattern outcome, optionally with a complete binding multiset; and
- structured-predicate Bool.

Every normal value is a structured `oracle-operand` whose
`k-in-k/oracle-operand/v1` identity covers its declaration, exact baseline or
mutant subject, test/profile roots, closed completion evidence, and
kind-specific normalized value. Equal semantic values may have unequal
operand IDs because provenance is part of operand identity. A comparison
therefore resolves both values and rederives their normalized-value digests;
it never compares operand IDs. The self-identified
`oracle-comparison-result` binds sides in baseline-then-mutant order, derives
the declaration's projection/comparator IDs, and returns only `agree`,
`distinguish`, or `incomparable`.

The baseline gate is a separate `baseline-oracle-gate-result` artifact.
`reference-only` accepts a complete side admitted by the four-value terminal
policy (`normal-only`, `normal-or-stuck`, `normal-or-crash`, or
`normal-stuck-or-crash`). `assert` compares the actual side with the
declaration-owned expected side through the same crash policy and kind
comparator. An inline normal expected side is discriminated by the declaration
kind and must pass the same portable kind-specific value-integrity rules before
comparison may project away provenance: terminal states, output bytes,
reachability witnesses, pattern results, and predicate inputs must resolve
through the active catalog; their definition/query/projection/binding roots
must agree with the declaration; and every derivable term, path, hash, text,
witness, result, and binding field must be rederived. Inline expectations do
not acquire operand identities or production evidence. A normal inline
expectation for a K-authored operation is not zero-backend decision authority
and must reject until a later production contract supplies an equivalent
kind-specific validator. Only `agree` is accepted. Gate status, assertion outcome, and an
exact `baseline-oracle-gate`/`baseline-mismatch` failure are rederived; a gate
result never recopies its expected value.

Campaign outer results are distinct from pure comparisons. `skipped` retains
no side, comparison, or failure. A baseline execution/operand-production
failure retains neither side; a mutant failure retains exactly the baseline
side; a comparison failure retains both sides; and conclusive agreement or
distinction retains both sides plus the exact comparison artifact and no
failure. BAG-10 maps the failure to `timeout`, `unknown`, or `error`.
`incomparable` retains both complete sides and the exact derived comparison,
requires the exact comparison-source `oracle/incomparable-result` placement,
and never kills. Every failure disposition is looked up by exact
stage/classification/context/scope in the active taxonomy; in particular,
`resource-limit` is `unknown`, never an error shortcut. Only `distinguish`
kills, while survival requires every selected slot to agree.

The active artifact catalog is the sole live semantic resolver. The mutation
manifest's `corpusManifestDigest` resolves a cataloged corpus, whose exact
cataloged observation manifest supplies the event vocabulary. Test IDs and
program/parser/start/options/bounds/profile roots rederive each invocation.
Gates, comparisons, and outer results use one side-validation algorithm that
binds normal operands or semantic crashes to the declaration, exact subject,
test invocation, profiles, terminal definition, and producer trace. Finite
output, reachability, and predicate rows authorize only their exact cataloged
subject and producing attempt.

Semantic crashes run through BAG-09's truth table before any kind comparator.
Cross-definition, test, query, profile, bounds, declaration, projection,
comparator, or side-order drift rejects the artifact even when every enclosing
self-ID has been refreshed. Host exceptions, process exit, diagnostics, and
infrastructure stderr are never semantic operands.

Observation transformations use the same declared revision and ordering for
baseline and mutant. Mutation identity is derived before observation; reports
link the observed rule provenance back to the original mutation target. A
mutant with an unchanged final result can therefore be killed by a changed
execution-pattern result.

`mutation-operator.schema.json` freezes the complete external declaration,
including phase, sentence kinds, selector/join digests, tuple count/arity,
candidate cap, pre/postconditions, generated-sentence policy, patch template,
category, and rationale. `structural-diff.schema.json` and
`replay-manifest.schema.json` freeze the report and replay boundaries. A
campaign must resolve its operator digest and repeat the declaration's policy,
tuple arity/count, and cap. A `mutation-materialization` replay records the operator,
candidate, patch, mutant, baseline, output definition, bounds, and structural
diff identities; a pattern replay cannot carry mutation identity. Structural
diff operations, paths, and affected provenance must agree with the referenced
patch. Execution-pattern witness digests resolve to complete pattern results.
Duplicate and no-change discoveries are candidate rejections, not output mutants;
invalid/timeout/unknown/error are mutant results
excluded from the exact score.

A valid baseline has one gate result for every ordered declaration slot, all
gates are accepted, and it has no failure. Any rejected gate derives
`baseline-oracle-failed`, aborts before mutant scoring, and forbids a score or
mutant result. Baseline-invalid and baseline-oracle-failed reports carry explanatory
failures and no mutant results or score. A complete campaign has an empty
top-level failure list. An `error` campaign has at least one campaign-scope
failure and publishes no mutant results or score; completed partial artifacts
may remain in external storage but are not silently retained as report results.

## 8. Validation layers and versioning

Failures are assigned to the closest completed boundary:

```text
input -> operator -> selection -> patch -> IR -> lowering ->
backend-validation -> execution -> observation/pattern -> oracle/report
```

The closed classifications and their outcome mapping are in
`failure-taxonomy.md`. Malformed structured output is `error`, never semantic
`no-match` or `survived`.

At the lowering boundary, `lowering-nontermination` requires affirmative
semantic evidence of a cycle or another proof of nontermination and therefore
makes a mutant `invalid`. Exhausting time while trying to establish lowering
termination is `lowering/time-limit` and yields `timeout`; exhausting another
declared resource is `lowering/resource-limit` and yields `unknown`. A bound
being reached is never promoted into proof of semantic nontermination.

Schemas are versioned independently but this package pins their compatible v1
set. Readers reject unknown required fields/enums unless a schema explicitly
marks an extension map. Reports include every schema version, definition and
transformation digest, execution bounds/profile, and replay artifact digest.

## 9. Artifact identity, resolution, and replay closure

An artifact has two non-interchangeable identities. `digest` is its role-typed
semantic identity. `contentSha256` is lowercase SHA-256 over the exact bytes a
locator returns. Canonical-JSON artifacts use the role's domain and exact
projection in `artifact-role-specs.json`; the bytes must be the package
canonical serialization exactly. Opaque artifacts use
`k-in-k/opaque-artifact/v1` over exactly `{role, mediaType, contentSha256}`.
Media types are the frozen lowercase, parameter-free values
`application/json` and `application/octet-stream`.

The serializer uses `\b`, `\t`, `\n`, `\f`, and `\r` for their five controls,
lowercase `\u00xx` for other U+0000--U+001F controls, required quote and
reverse-solidus escaping, and direct UTF-8 for non-ASCII scalars. It emits no
BOM, solidus escaping, non-ASCII escaping, insignificant whitespace, or
trailing newline. Alternate but decodable JSON bytes are not canonical JSON.

The catalog is the sole metadata authority. References are only artifact keys
`{role,digest}`. The live BAG-12 catalog uses structured
`oracle-declaration`, `oracle-operand`, `oracle-comparison-result`, and
`baseline-oracle-gate-result` roles; the manifest publishes only per-test
declaration keys. Legacy `oracle-projection`, `oracle-comparison`, and
`oracle-value` roles exist solely in the immutable pre-BAG-12 execution-catalog
snapshot needed to validate historical corpus/replay identities. They are
absent from the live mutation catalog and cannot authorize a declaration,
operand, comparison, gate, or campaign decision. Replay step edges are paired `inputArtifacts` and
`expectedArtifacts`, never parallel role and digest arrays. BAG-07 edit
receipts remain embedded identity inputs and do not become artifact roles.

The BAG-14 cache vector names `fixtures/bag14-cache-artifact-catalog.json` by exact `artifactCatalogDigest` as its authoritative derivative resolver snapshot.
That snapshot is separate from the live BAG-12 mutation catalog because BAG-14's wholly bundled finite positive must not relabel an existing `external-required` artifact.
The snapshot boundary is evidence-local, not a second general mutation-decision authority.
Its cache manifest, invocation, record, and report roles resolve only the BAG-14 graph.
Resolver availability, lookup source, cache location, hit/miss state, latency, timestamps, and eviction metadata are supplemental and absent from semantic identities.

The v1 resolver registry is closed. `repo-v1` accepts only `repo://`, requires
`bundled`, resolves from the real repository root, requires a regular file,
and rejects absolute, empty, dot, non-ASCII/control, backslash, percent-escape,
and symlink-escape paths. `rust-artifact-store-v1` accepts only
`artifact://`, requires `external-required`, is checked lexically, and is not
dereferenced by this package. Locator uniqueness is the complete normalized
locator; artifact uniqueness is `(role,digest)`. A locator is never evidence
that bytes exist.

Concrete entries always have a reviewed `contentSha256`. Unknown bytes are an
`unboundRequirement` with no digest. Such a requirement is permitted only in
an artifact-use recipe position and cannot replace a concrete manifest root.
The synthetic `.bin` files under `material/` are labeled conformance inputs,
not backend outputs. Structured external pins are derived from the exact
canonical serialization of their reviewed synthetic fixture values. The
bundled `material/mutation-selector.json` is the positive canonical-JSON
retrieval case; its semantic root intentionally differs from its raw byte
hash.

`replay-closure.json` is derived independently per replay. Referential closure
means every concrete pre-execution/supplied key has one catalog entry.
Material closure additionally requires every pre-execution key to be bundled
and byte/semantic verified and forbids unbound inputs. Execution conformance
is always `not-proven` here. Replay-generated intermediate and final values
remain typed DAG outputs without pre-existing catalog entries. This avoids a
self-cataloging cycle for result IDs whose documented projection includes a
replay invocation that itself names the catalog.
## 10. BAG-10 failure disposition and evidence boundary

The closed failure taxonomy is entry-centric and content-addressed. Every
schema-legal failure placement resolves to exactly one artifact consequence or
named versioned delegation, and every taxonomy placement is schema-reachable.
Failure details are diagnostic-only; semantically decisive evidence lives in
the separate `semanticEvidence` key array.

Lowering nontermination requires a resolvable, checked receipt bound to the
exact baseline or mutant subject, opaque lowering profile, execution profile,
proof kind, frozen relation, and registered checker version. The bundled toy
checker establishes protocol conformance only. A bounded stop remains a time
or resource limit until a future native checker proves the real relation.

## 11. Typed oracle evaluation and finite authority

The zero-backend evaluator implements only the frozen portable registry and
exact finite rows. A BAG-15 production receipt proves that an adapter produced
an artifact for one invocation; it does not prove that a K-authored operation
has the declared meaning. Native decision authority is a distinct structured
`oracle-evaluator-conformance` record, self-identified in
`k-in-k/oracle-evaluator-conformance/v1`. It binds the applicable typed
source/plan/query or comparison artifact, compiler and evaluator versions,
all three profile roots, a conformance suite, and a
`conformant|nonconformant` result. K-authored evaluation may authorize a
decision only when a matching `conformant` record and the exact production
receipt both resolve. The bundled nonconformant fixture is negative evidence
and can never be promoted by catalog membership.

Concrete output declares a nonempty ordered list of unique semantic channels.
Each value binds the exact channel `name`, exact lowercase parameter-free
`mediaType`, byte artifact, raw byte hash, and strict UTF-8 decode or null.
Exact-byte comparison includes name, media type, and byte content. UTF-8-lines
comparison requires valid UTF-8 and maps CRLF and lone CR to LF only. Invalid
UTF-8, missing bytes, extra/reordered channels, or catalog media/hash drift is
invalid operand production rather than inequality.

Reachability source bytes are opaque, while plans, queries, witnesses, and
finite tables are structured and role-typed. A plan declares variables in
binding order, one portable state pattern, and either null or one exact
`predicate-query` side condition. Variables bind complete terms of exactly
their declared sorts. The finite matcher checks node kind, sort, symbol ID,
arity, literal, first binding, and repeated-binding equality. A row binds one
exact query, ordered terminal-state inputs, a completeness flag, its derived
input-vector digest, and every derived witness ordered by input ordinal and
then binding identity. Absence is `not-reached` only when the finite input is
complete; proof bytes, evaluator profiles, and witness bytes are provenance,
not reachability truth.

Structured-predicate plans freeze input role/schema/projection roots, exact
variable sorts and order, Bool result sort, and finite-table or K-authored
mode. Each finite row binds the exact query, exact input artifact and canonical
input projection, ordered bindings and binding digest, and derived Bool.
Another input, query, projection, binding order, or missing row has no
authority. Missing finite authority and evaluator unavailability derive
`unknown`, never false.

Operand-production failures use BAG-10 context
`oracle-operand-production`: `input/missing-artifact` and
`oracle/projection-invalid` derive `error`; `oracle/evaluator-unavailable` and
`execution/solver-unknown` derive `unknown`. These placements are bidirectionally
closed in both taxonomy and context-specific schemas. They occupy the exact
failed outer side, never create an operand or comparison, and never kill a
mutant.

## 12. Operation receipts and result provenance

One generic `operation-receipt` contract covers mutation materialization, execution attempt, oracle operand production, baseline admission, oracle comparison, campaign derivation, and report publication.
Each invocation hashes its closed operation/version, adapter contract, parameters, ordered typed inputs, ordered child receipts, and one requested operation-specific wrapper role without hashing output keys or expected output bytes.
Each complete receipt publishes exactly that one wrapper and carries the wrapper's nested semantic terminal and exact BAG-10 failure or null.
Only `producerStatus: failed` publishes no wrapper and no semantic terminal.

An `execution-attempt-result` repeats the exact BAG-14 key digest, carries a distinct generic invocation digest, and contains the exact terminal record and ordered produced-artifact keys.
The execution receipt outputs only this wrapper; terminal, trace, and value artifacts are nested keys and bind the cycle-free invocation indirectly.
Admission and comparison wrappers likewise repeat the complete BAG-14 oracle-evaluation key, terminal, and produced-artifact sequence.
Every receipt-backed derivative cache record is accepted only when all of those fields equal an independently derived BAG-14 result.

Downstream operations consume a result wrapper together with its producing receipt.
The campaign derivation consumes exactly the selected materialization and cache-record receipt sequence in plan order; first-kill has no receipt for the skipped suffix.
Report publication consumes the derivation wrapper and receipt plus one exact recursive replay-version registry.
The publication invocation contains no expected report body, bytes, or digest, and the normalized report points backward only to its derivation receipt.
The registry is sorted and duplicate-free, covers exactly the portable schemas and seven operations used by the recursive report closure, and hashes exact bundled schema bytes.

The bundled BAG-15 graph is finite-vector production conformance.
It does not prove a native adapter, executor, cache store, compiler, backend, solver, or report publisher.

## 13. Collection-aware search, replay, and corpus derivation

BAG-16 preserves every accepted v1 byte and identity while adding explicit v2
dispatch for shared roles. An execution-attempt-v2 request is either reusable
query-neutral exhaustive observation or exact query-coupled existential search.
It produces occurrence-neutral event traces plus occurrence-scoped branch
records in semantic visit order, one global stop, explicit discovered pending
work, and an empty-search decision when clean exhaustion has zero visits.

The execution wrapper's duplicate-free output order is derived by scanning
occurrences: normal/stuck terminal then trace; semantic-crash terminal, crash,
then trace; terminal-free or incomplete dispositions contribute their trace;
the empty marker follows the visits when required and the collection is last.
The receipt outputs only that wrapper. Collection, trace, terminal, wrapper,
receipt, and cache records retain the BAG-15 backward-only DAG direction.

Pattern evaluation independently rederives every path denotation and witness.
Existence `match` outranks unknown/error evidence, but any indeterminate or
incomplete path keeps coverage false. Absence requires clean exhaustion,
pending zero, conclusive trustworthy paths, and the exact empty marker for no
visits. Outcome-only oracle projection may consume a proven false-coverage
match; the complete-binding-multiset projection requires exhaustive true
coverage.

Concrete-output, reachability, and predicate finite-row operands require a
clean query-neutral exhausted collection. Singleton projections equal the
sole eligible occurrence; reachability's ordered trace/terminal vector equals
the complete collection vector. Row `finiteComplete` applies only to
reachability and never substitutes for collection completeness. Every inline
expected normal value reruns BAG-12's kind-specific active-catalog validation
before comparison.

Corpus components preserve manifest test/slot order and repeated fan-out
occurrences. A pure corpus derivation deterministically folds match before
error, unknown, and complete no-match, selecting causes in manifest order.
Producer failures and scheduled suffixes force false coverage. The top-level
corpus decision is only match, no-match, unknown, or error; `skipped` is a
test/component scheduling arm, never a corpus outcome.

Cache v2 is execution-only. Production/conformance eligibility is checked
first, then global and nested diagnostic evidence precedes bounded evidence,
which precedes clean semantic results. A later stop cannot erase earlier
incomplete evidence. The embedded v2 role registry, catalog, cache projection,
and recursive version registry are closed by one non-cataloged portable root.
This is deterministic finite portable evidence, not proof that a backend found
all branches or emitted the recorded traces and stops.
