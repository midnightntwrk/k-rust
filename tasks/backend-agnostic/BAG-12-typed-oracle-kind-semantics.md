# BAG-12: typed oracle-kind semantics

Status: refreshed portable repair independently accepted on 26 August 2026,
including the kind-specific inline expected-value integrity repair. BAG-14
still requires its own independent preflight.

## Objective

Give every oracle kind admitted by the mutation manifest a typed operand and a
derived comparison result. The schema currently admits `exit-stop`,
`final-result`, `concrete-output`, `reachability`, `execution-pattern`, and
`structured-predicate`, but the verifier materially checks only final-result
equality and execution-pattern projections. The other enum values can report
arbitrary value digests and outcomes while the completion checklist calls
oracle semantics portable-closed.

This packet closes backend-neutral report and comparison semantics. Producing
the operands from native execution, evaluating K-authored projections or
predicates, and validating proof results remain future Rust-stack work.

## Normative model

Replace the one-size-fits-all pair of nullable value digests with three closed
structured roles and records:

1. `oracle-declaration`, self-identified in
   `k-in-k/oracle-declaration/v1`, binds exactly one test invocation and its
   manifest oracle slot, oracle ID/version, kind, compatibility/execution
   profile requirements, projection and comparison specifications, BAG-09
   crash and baseline-terminal policies, baseline gate, and kind
   configuration.
2. `oracle-operand`, self-identified in `k-in-k/oracle-operand/v1`, is one
   complete normal semantic value. It binds the declaration, subject,
   test/source invocation, compatibility/execution profiles, BAG-09 terminal
   shell, kind-specific normalized value, and exact BAG-08 artifact keys.
3. `oracle-comparison`, self-identified in
   `k-in-k/oracle-comparison-result/v1`, is the pure semantic decision record.
   It binds the exact ordered comparison sides, declaration/comparator
   identity, normalized value/projection digests, and derived outcome. Each
   side is a tagged union containing exactly one role-typed normal
   `oracle-operand` key or one BAG-09 `semantic-crash` key; side order is
   exactly baseline then mutant. BAG-15 separately owns the operation receipt
   proving which adapter/evaluator produced records; do not define a competing
   evaluation receipt here.

Operand identity includes provenance, so equal baseline and mutant values may
have different operand IDs. Comparison uses normalized values, never
operand-ID equality. One declaration belongs to one test invocation. Reusing
the same oracle definition in another test creates another declaration with
that invocation root; a declaration never contains an unordered set of
applicable tests. Manifest oracle order is preserved exactly, and every
selected oracle slot has exactly one declaration, baseline gate result, and,
when that slot executes for a mutant, one outer campaign oracle result.
Repeated query selections remain legitimate distinct slots.

Incomplete execution attempts are not operands: predicate, reachability, or
pattern `unknown`, bounds/solver stops, missing output, and typed failures
remain attempt/failure records and derive outer `timeout`/`unknown`/`error`
through BAG-10. Keep the campaign oracle-result envelope separate from
`oracle-comparison`. `skipped` has null baseline and mutant sides, no
comparison, and no failure. A baseline-execution failure may leave both sides
null; a mutant-execution failure retains only the baseline side; a comparison
failure retains both sides. No other null relation is legal. A comparison
artifact exists only when both tagged semantic sides exist. Its outcome is
`agree`, `distinguish`, or `incomparable`; `incomparable` must be accompanied in
the outer result by BAG-10's comparison-source
`oracle/incomparable-result` failure and never kills. Timeout, unknown, error,
and skipped are outer dispositions, not comparison outcomes.

All kinds share these rules:

- baseline and mutant sides use the same declaration and therefore the same
  oracle ID/version, kind, projection, comparison relation, test scope, and
  compatibility/execution requirements;
- compared artifacts resolve through BAG-08 and appear in canonical
  baseline-then-mutant order;
- `agree` and `distinguish` require two complete semantic sides and no
  failure; a side may be a normal operand or BAG-09 semantic crash, and the
  crash truth table runs before the kind comparator;
- `incomparable`, `timeout`, `unknown`, `error`, and `skipped` have their exact
  typed reason/absence relations;
- comparison records bind both ordered sides and the declared comparator
  identity; and
- a declaration/result mismatch or self-asserted outcome rejects even if all
  enclosing IDs are refreshed.

Projection and comparison specifications are a closed union: either one entry
from the v1 portable registry below or a K-authored BAG-08 artifact key with
compiler/evaluator requirement status. The declaration must choose a
kind-compatible registry pair; no free-form built-in name or arbitrary
projection/comparator pairing is allowed. Only built-ins and finite registered
conformance-table rows are executable by zero-backend code. An opaque artifact
digest or self-asserted receipt never authorizes `agree`, `distinguish`, or a
kill. K-authored evaluation remains pending until a registered BAG-15 receipt
exists.

The baseline gate is explicit. `reference-only` accepts any complete baseline
side allowed by BAG-09's baseline-terminal policy. `assert` carries exactly
one declaration-owned expected side: either an inline kind-specific normalized
normal value or a role-typed expected semantic-crash key. Run the same crash
policy and kind comparator between the expected side and the produced baseline
side. Only `agree` passes. A semantic crash never bypasses a normal-value
assertion merely because crashes are allowed; a terminal policy that excludes
the actual side, a distinguish, or an incomparable assertion derives BAG-09's
`baseline-mismatch` gate and aborts scoring. Baseline expectation changes
declaration, manifest, cache, and future receipt identity. Do not fake an
assertion with baseline-to-itself comparison.

### Closed v1 built-in registry

Freeze the following compatible projection/comparator pairs and reject every
other pairing or configuration:

- `exit-stop`: `terminal-class-and-declared-exit-v1` with
  `exact-terminal-class-and-exit-v1`;
- `final-result`: either `whole-portable-term-v1` with
  `exact-portable-term-v1`, or `selected-term-paths-v1` with
  `exact-ordered-path-values-v1`;
- `concrete-output`: either `ordered-output-bytes-v1` with
  `exact-ordered-output-bytes-v1`, or `ordered-output-utf8-lines-v1` with
  `exact-ordered-output-utf8-lines-v1`;
- `reachability`: `reachability-truth-v1` with
  `exact-reachability-truth-v1`;
- `execution-pattern`: either `pattern-outcome-v1` with
  `exact-pattern-outcome-v1`, or `pattern-outcome-bindings-v1` with
  `exact-pattern-outcome-bindings-v1`; and
- `structured-predicate`: `predicate-bool-v1` with
  `exact-predicate-bool-v1`.

Every registry entry has an explicit algorithm in the contract and verifier,
not merely an accepted name. `exact` means structural equality of the
validated normalized values. `ordered-output-utf8-lines-v1` requires strict
UTF-8 on every declared channel and maps CRLF and lone CR to LF without any
other Unicode, whitespace, final-newline, or channel normalization. Failure to
decode is invalid production of that projection, not ordinary inequality.

### Exact records and identities

Replace the manifest's global `oracles` plus per-test `oracleIds` join with
per-test ordered `oracleDeclarations`. Each entry is a BAG-08 key with role
`oracle-declaration`; its array ordinal is the semantic oracle slot. The
declaration repeats that `slotOrdinal`, a test-local `slotId`, and the exact
`testInvocationDigest`. Slot IDs are unique within one test; `oracleId` and an
otherwise identical semantic definition may legitimately repeat in another
test or slot. The manifest has no second global list whose join could drift.
Flattening for campaign/cache identity is test order followed by slot order,
with duplicates preserved.

The declaration record contains exactly:

```text
schemaVersion, declarationId,
testInvocationDigest, slotOrdinal, slotId,
oracleId, oracleVersion, kind,
compatibilityProfileDigest, executionProfileDigest, solverProfileDigest,
boundsDigest, baselineTerminalPolicy, crashPolicy,
baselineGate, projectionSpec, comparisonSpec, kindConfig
```

`declarationId` is `k-in-k/oracle-declaration/v1` over every field except
itself. The four profile/bounds roots must equal the resolved test/corpus
invocation rather than merely having digest shape. `baselineTerminalPolicy` is
the closed matrix `normal-only`, `normal-or-stuck`, `normal-or-crash`, or
`normal-stuck-or-crash`; semantic crash still follows `crashPolicy` during an
assertion or mutant comparison. `projectionSpec` and `comparisonSpec` are the
closed built-in or K-authored unions; `kindConfig` is the exact kind-specific
union. Do not retain redundant generic artifact arrays: validators traverse
and resolve every role-typed key in these typed fields.

More exactly, `baselineGate` is either `{mode: reference-only}` or
`{mode: assert, expectedSide}`. `expectedSide` is exactly one inline
`{kind, normalizedValue}` matching the declaration kind or one role-typed
semantic-crash key; it is declaration data, not a produced operand.
`projectionSpec` is either `{mode: portable-built-in, projectionId}` or
`{mode: k-authored, source, plan, query, conformanceRequirement}`; fields that
do not apply to a kind are absent, not null. `comparisonSpec` is either
`{mode: portable-built-in, comparatorId}` or
`{mode: k-authored, comparisonArtifact, conformanceRequirement}`.
`conformanceRequirement` is the constant `rust-proof-required`. The built-in
IDs must be one exact compatible registry pair; every K-authored key is
role-constrained by its kind. The old two-value BAG-09 terminal policy is
replaced by the four-value matrix: old `normal-required` maps to `normal-only`
and old `semantic-crash-allowed` maps to `normal-or-crash`; the two stuck-aware
values are explicit additions, not reinterpretations.

The normal operand record contains exactly:

```text
schemaVersion, operandId, declaration,
subject, testInvocationDigest,
compatibilityProfileDigest, executionProfileDigest, solverProfileDigest,
completionEvidence, normalizedValue
```

`operandId` is `k-in-k/oracle-operand/v1` over every field except itself.
`declaration` is an `oracle-declaration` key. `subject` is exactly baseline
`{side, definitionDigest}` or mutant
`{side, baselineDefinitionDigest, mutantId, mutantDefinitionDigest}`.
`completionEvidence` is a closed kind-compatible union: a single BAG-09
normal/stuck terminal shell, a BAG-11 pattern-result key, or a reachability
collection/table row. It is not a generic claimed-complete flag. BAG-15's
acyclic production receipt references the completed operand and exact
invocation; the operand never points forward to its producing receipt.
`normalizedValue` is the exact kind union.
Every copied invocation/profile/root and subject definition must resolve and
equal its enclosing manifest side. Again, typed fields are the artifact
closure; no independently editable artifact list exists.

The comparison record contains exactly:

```text
schemaVersion, comparisonId, declaration,
sides: [baselineSide, mutantSide],
projectionId, comparatorId,
normalizedValueDigests: [baselineDigest|null, mutantDigest|null],
outcome
```

`comparisonId` is `k-in-k/oracle-comparison-result/v1` over every field except
itself. Each side is exactly `{side, normalOperand, semanticCrash}` with one of
the last two non-null. A normal digest is
`k-in-k/oracle-normalized-value/v1` over exactly `{kind, projectionId,
normalizedValue}`; a crash slot has null because BAG-09 compares the resolved
crash semantic projection instead. `projectionId` and `comparatorId` must be
derived from the declaration, never copied authority. The verifier resolves
both operands and rederives every digest and the outcome.

Add a structured `baseline-oracle-gate-result` role:

```text
schemaVersion, gateResultId, declaration, actualSide,
assertionOutcome, status, failure
```

`gateResultId` is `k-in-k/baseline-oracle-gate-result/v1` over every field
except itself. `actualSide` is the same tagged side union with side fixed to
baseline. `assertionOutcome` is null for `reference-only`, otherwise exactly
`agree`, `distinguish`, or `incomparable` rederived against the declaration's
expected side. `status` is `accepted` iff the terminal-policy gate admits the
actual side and, for `assert`, assertion outcome is `agree`; otherwise it is
`error` with exactly one BAG-09 `baseline-mismatch` failure. The expected side
is stored only in the declaration and is not recopied into the result.

For baseline admission, a normal operand's completion evidence derives normal,
stuck, or branch-complete; branch-complete is admitted as normal. The four
`baselineTerminalPolicy` values apply uniformly to all kinds. A kind whose
normal operand cannot be constructed from stuck evidence produces an operand-
production failure before the gate; it does not reinterpret stuck as crash.
On the mutant side, kind eligibility below determines whether a complete stuck
execution produces a normal operand; semantic crashes always use the tagged
crash side.

The kind/completion matrix is exact:

| kind | normal operand completion evidence | stuck | semantic crash |
| --- | --- | --- | --- |
| `exit-stop` | one normal/stuck BAG-09 shell | always representable as the `stuck` normalized value | tagged crash side |
| `final-result` | one terminal-state projection | only with `stuckResultPolicy: comparable` | tagged crash side |
| `concrete-output` | complete declared channels from one normal/stuck attempt | representable when every channel is complete | tagged crash side; pre-crash output is not substituted |
| `reachability` | finite/BAG-16 collection with a derived truth value | path-local stuck states remain collection members | crash paths remain collection members; only absence of a valid collection uses a tagged crash side |
| `execution-pattern` | a validated BAG-11 result | stuck paths remain ordinary complete paths | crash paths remain ordinary complete paths; malformed/missing result is error, not a crash side |
| `structured-predicate` | complete declared input plus evaluation authority | representable only when the declared input projection exists | tagged crash side |

The baseline policy then admits or rejects the derived row; it does not change
the row's kind semantics. On mutant comparison, representable normal/stuck or
branch-complete operands reach the kind comparator, while a tagged crash uses
BAG-09's crash truth table.

### Evaluation authority and failure placement

A BAG-15 production receipt proves provenance only. It never proves that a
K-authored projection, query, or comparator implements its declared meaning.
Add a separate structured `oracle-evaluator-conformance` role. Its record
contains exactly `{schemaVersion, conformanceId, operationKind, source, plan,
query, comparisonArtifact, compilerId, compilerVersion, evaluatorId,
evaluatorVersion, compatibilityProfileDigest, executionProfileDigest,
solverProfileDigest, conformanceSuite, result}`; inapplicable typed keys are
absent. `conformanceId` is `k-in-k/oracle-evaluator-conformance/v1` over the
record without itself, and `result` is `conformant|nonconformant`. The future
Rust stack issues the record after running the named suite; the zero-backend
package may validate its shape and roots but cannot manufacture or promote a
result. A K-authored operation is decision-authorized only by a matching
`conformant` record plus the exact BAG-15 production receipt. Finite registered
rows authorize only their own exact fixture inputs.

Add BAG-10 context `oracle-operand-production` and close these placements in
both schema and taxonomy directions: `oracle/projection-invalid` derives
`error` for missing/wrong-sort paths, invalid UTF-8 under the UTF-8 projection,
malformed normalized output, or a result that contradicts its declaration;
`input/missing-artifact` derives `error` for required bytes/input that cannot
resolve; `oracle/evaluator-unavailable` derives `unknown` for missing
conformance authority or an unregistered finite row; and the existing
`execution/solver-unknown` placement derives `unknown` for native evaluator
indeterminacy. These failures occupy the failed side according to BAG-09's
absence matrix and never become operands or kills. A malformed published
record remains report/schema/referential-integrity rejection rather than being
converted into one of these runtime failures.

## Closed operand kinds

### `exit-stop`

Record exactly `{terminalClass: normal|stuck, exitCode: integer|null}` tied to
BAG-09's resolved execution-terminal shell. Do not copy the redundant
`stopReason`: derive `normal` only from a `terminal` stop with a normal
terminal-state key and `stuck` only from a `stuck` stop with a stuck
terminal-state key. The declaration names
`exitCodeMode: none|declared-program-exit`; `none` requires null,
`declared-program-exit` requires an integer on `normal`, and `stuck` always
requires null. A backend process status is never this value. Future native
evidence must prove that an exposed code is object-program semantics rather
than worker/backend exit. Limit/solver stops remain incomplete; BAG-09 handles
semantic crashes.

### `final-result`

Record the source terminal-state key and a closed projection value: either the
whole portable result term or canonical selected paths
`[{path, sort, value}]`. Paths use BAG-03/BAG-13's typed term-path grammar,
never strings; they are unique, prefix overlap is rejected, and declaration
and value arrays use encoded-path order. Every declared path must resolve in
the terminal term, its resolved sort and value must equal the recorded pair,
and BAG-13 local well-formedness applies to the whole operand graph. Missing,
wrong-sort, or overlapping paths make the artifact invalid rather than
unequal. Only BAG-09 normal terminal results are eligible; stuck is eligible
only when the declaration explicitly sets `stuckResultPolicy: comparable`, in
which case the same path rules apply. Pretty output is supplemental. A
K-authored projection needs a registered evaluator receipt; portable
whole-term and selected-path fixtures are recomputed.

### `concrete-output`

The declaration freezes a nonempty ordered list of unique semantic channel
names and one registry mode. Each value is exactly
`{name, mediaType, contentSha256, bytesArtifact, text}` in declaration order.
`bytesArtifact` has a distinct opaque `semantic-output-bytes` BAG-08 role;
catalog media type and byte hash must equal the record. `text` is required and
equals the exact strict UTF-8 decode iff decoding succeeds; otherwise it is
null and is legal only for the exact-bytes projection. The exact-bytes
projection compares name,
mediaType, and byte content in order; the UTF-8-lines projection requires
non-null text and applies only the frozen CR/CRLF mapping above. Missing,
duplicate, reordered, extra, unavailable, or hash-mismatched bytes make the
operand invalid, not unequal. External bytes require BAG-15 production
evidence before use; bundled finite fixtures are recomputed directly.
`stdout`/`stderr` are semantic only when declared as program-output channels
and linked to the producing attempt; infrastructure diagnostics never enter
the value.

### `reachability`

Use distinct BAG-08 roles `reachability-source`, `reachability-plan`,
`reachability-query`, `reachability-witness`, and
`reachability-conformance-table`. Source is opaque K-authored bytes. The
structured plan contains exactly `{schemaVersion, planId, variables,
statePattern, sideCondition}`. Variables use BAG-11's name grammar, are unique
in declaration order, and bind complete BAG-13 portable terms of their
declared sorts. `statePattern` is a BAG-13 portable term whose variable nodes
must be declared; the finite matcher is exact structural matching by node kind,
sort, symbol ID, arity, and literals, with first occurrence binding and later
occurrences requiring structural equality. `sideCondition` is null or an exact
`predicate-query` key over those bindings.

`planId` is `k-in-k/reachability-plan/v1` over the plan without its self-ID.
The query contains exactly `{schemaVersion, queryId, source, plan}` and uses
`k-in-k/reachability-query/v1` over the object without `queryId`. Compiler,
evaluator, profile, and conformance status are provenance in the declaration
and authority records, not query meaning. The witness uses
`k-in-k/reachability-witness/v1` over its exact query, terminal-state key,
bindings in plan declaration order, and optional stable path/replay pair; it
cannot contain proof bytes.

A finite table is self-identified over ordered rows. Each row binds the exact
query, an ordered nonempty array of terminal-state keys, its finite-complete
flag, and the complete ordered witness set rederived by the structural matcher
and optional predicate rows. `reached` requires at least one derived witness;
`not-reached` requires none and `finiteComplete: true`. A future BAG-16 branch
collection replaces the finite input array as production evidence while
preserving this truth rule. Compare only truth status, never witness, proof,
path, or receipt bytes: same status agrees and reached versus not-reached
distinguishes. Missing rows, bounded absence, or solver-indeterminate absence
are incomplete attempts, not operands.

Derive `inputVectorDigest` in `k-in-k/reachability-finite-input/v1` over the
ordered terminal-state keys and completeness flag. Rows are unique and sorted
by `(query.digest, inputVectorDigest)` lexically. Witnesses are ordered first by
input-state ordinal, then by the binding-tuple digest and canonical bytes; all
derived matches are present.

### `execution-pattern`

The declaration binds the exact BAG-11 source/plan/query triple, bounds, and
search policy and chooses one of two semantic projections.
`pattern-outcome-v1` compares only `match` versus `no-match`.
`pattern-outcome-bindings-v1` compares that outcome plus the canonically sorted
multiset of complete binding tuples projected in exact plan variable order
from the BAG-11-derived witnesses. A tuple is the canonical array
`[{name, sort, value}]`; its key is
`k-in-k/pattern-oracle-binding-tuple/v1` over that array. Sort by tuple key then
canonical tuple bytes, preserving duplicate tuples. This projection drops path
IDs, event ordinals, replay keys, predicates, terminal evidence, and proof
bytes. It is legal only for exhaustive search because existential-first does
not establish a complete binding multiset. A validated `match` is
eligible even when existential-first stopped with `completeCoverage: false`;
`no-match` is eligible only with exhaustive coverage. `unknown` and `error`
are never operands. Every included binding is rederived from the result and
BAG-11 denotation. Query, plan, test, bounds, search-policy, or projection drift
rejects; full witness/provenance equality is not a v1 semantic comparator.

### `structured-predicate`

Use distinct structured `predicate-source`, `predicate-plan`,
`predicate-query`, and `predicate-conformance-table` BAG-08 roles; do not
overload BAG-11 pattern-query or pattern-side-condition roles. Source is opaque
K-authored bytes. A plan contains exactly `{schemaVersion, planId,
inputRole, inputSchemaDigest, inputProjectionDigest, variables, resultSort,
evaluationMode}`. Variables use BAG-11's closed grammar, are unique in exact
declaration order, and `resultSort` is `Bool`; `evaluationMode` is
`finite-table-v1` or `k-authored-v1`. `planId` is
`k-in-k/predicate-plan/v1` over the object without itself. A query contains
exactly `{schemaVersion, queryId, source, plan}` and uses
`k-in-k/predicate-query/v1`; compiler/evaluator profiles and conformance status
are authority provenance, not semantic query identity.

A finite-table row binds exactly the query, role-typed input artifact key,
canonical input projection digest, ordered bindings, BAG-11-compatible binding
digest, and Bool result. The table is self-identified in
`k-in-k/predicate-conformance-table/v1` over its canonically ordered unique
rows. A complete value is `true` or `false` with exact input and canonical
bindings in plan declaration order. Reuse BAG-11's binding-digest algorithm,
but use predicate-specific query/table domains so rows cannot be replayed as
pattern side conditions. Bindings validate evaluation input; the v1 comparator
compares only the derived Bool. A missing row or solver unknown is incomplete,
not false. Arbitrary K/solver evaluation remains Rust-owned and requires the
separate conformance plus production authorities above.

Predicate table rows are unique and sorted lexically by
`(query.digest, inputArtifact.role, inputArtifact.digest, bindingsDigest)`.
The input projection digest is rederived from the declared input role/schema
and exact bytes/value rather than trusted from the row.

## Outcome derivation

Fold status in one order: `skipped` has no sides/failure/comparison; a typed
side failure derives timeout/unknown/error through BAG-10; two present sides
invoke BAG-09's crash truth table first; and exactly two normal operands invoke
the kind comparator. `distinguish` alone may kill. Intentional incomparability
is an oracle/test/mutant error or exclusion, never a kill, and survival
requires every selected oracle to complete and agree. No kind-specific
shortcut sets mutant status.

Malformed or drifting roots, kind, schema, profile, test, query, projection,
declaration, or side order are invalid artifacts/report provenance, not
semantic distinctions or taxonomy failures. Typed execution incompleteness
uses BAG-10 timeout/unknown/error. Only a valid pair that the declared relation
intentionally cannot compare yields `incomparable` plus
`oracle/incomparable-result`; add every new failure placement to BAG-10's
bidirectional schema/taxonomy reachability inventory. No kind may use generic
digest equality when its semantic value has a more precise rule, and no opaque
witness/proof digest may authorize a decision.

## Required evidence

- one positive agree and distinguish case for every executable built-in pair,
  including both modes where a kind has two pairs;
- invalid schema/projection/query drift cases for each structured kind, plus
  legitimate incomparable crash-policy cases in both orientations; all v1
  built-in normal comparators are total over valid same-declaration values;
- concrete-output byte/newline/channel cases;
- reachability reached, finite-table exhaustive not-reached, and bounded
  unknown cases; BAG-16 later adds branch-collection exhaustive evidence;
- structured-predicate true/false/unknown cases;
- execution-pattern same-final-result distinction remains linked to BAG-11's
  exact query identity; and
- at least one baseline case whose accepted semantic outcome is not ordinary
  successful termination.

Permanent adversaries must reject kind/operand mismatch, missing or extra
operand artifacts, baseline/mutant order reversal, declaration/projection/
comparison/test/profile drift, self-asserted comparison receipts, equal digest
with unequal normalized values, unequal byte storage with claimed exact-output
agreement, infrastructure stderr treated as semantic output, reachability
absence without exhaustion, witness for another proposition/query, pattern
comparison across query/plan/bounds, predicate result without its input, an
unknown result reported as agree, and any previously unchecked enum kind with
an arbitrary kill.

Also reject operand-ID equality used as value equality; an incomplete attempt
used as an operand; an operand present on the side whose execution failure
prevented it, while preserving the allowed baseline side on mutant failure and
both sides on comparison failure; comparison without two complete sides;
backend exit used as object exit; final-result duplicate,
unsorted, missing, or wrong-sort paths; concrete channel omission/reorder/
duplicate or text/bytes mismatch; proof-byte inequality treated semantically;
pattern witness/result/search-policy drift; predicate binding/plan drift;
baseline gate/expectation drift; a crash silently satisfying a normal
assertion; one declaration spanning multiple test invocations; omitted,
duplicated, or reordered per-test oracle coverage; an unknown or
kind-incompatible registry pair; an unknown evaluator; and a finite
conformance row for different roots.

Also reject a global oracle definition joined ambiguously to tests; declaration
slot ordinal/array position or invocation drift; a redundant artifact list;
wrong self-ID field exclusion or domain; copied profile roots that do not equal
the invocation; baseline gate status/assertion/failure drift; a gate result
that recopies a different expectation; normal-value digests on crash sides;
valid UTF-8 with null/wrong `text`; invalid UTF-8 under the UTF-8-lines mode;
missing projection inputs without the exact operand-production failure;
production receipt treated as evaluator conformance; evaluator conformance
used for different source/plan/query/profile roots; reachability query profile
or proof bytes treated as semantic identity; incomplete finite absence called
`not-reached`; pattern binding tuples in witness/path order or existential-
first used with the complete-binding projection; and predicate table rows with
different inputs, binding order, query, or projection roots.

## Ownership

The worker may add oracle declaration/operand/comparison, reachability-query,
and structured-predicate source/plan/query schemas and vectors, and modify
mutation manifest/campaign fixtures, contracts, artifact roles and catalog
after BAG-08, pattern identity after BAG-11, failure/crash relations after
BAG-09/BAG-10, verifier, refresh helper, completion evidence, and Rust handoff
oracle adapter notes. Integrate after BAG-06, BAG-08 through BAG-11, and
BAG-13. BAG-13 must freeze the portable term/symbol/local-well-formedness
surface before this packet defines final-result and predicate values.
Do not edit goals/D1/roadmap, execute native oracles, interpret arbitrary K
predicates/comparisons in Python, or run backend code.

## Acceptance

- every admitted oracle kind has a closed operand schema, registry entry, and
  derived result;
- declaration, operand, comparison, baseline-gate, evaluator-authority, query,
  witness, and table records have exact digest domains and resolution rules;
- values, witnesses, failures, and artifacts have exact kind-specific
  relations;
- all six kinds have positive, negative, incomplete, and drift evidence where
  applicable;
- baseline gating and mutant scoring consume the same validated semantics;
- portable finite-oracle conformance is not claimed as native K evaluation;
- all mandatory adversaries reject through schema or semantic validation;
- BAG-10 failure reachability remains bidirectionally exact after every new
  oracle placement;
- zero-backend and official Draft 2020-12 validation pass;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- checks are tiny and serial; and
- `git diff --check` passes.

### Root re-audit repair gate — updated 26 August 2026

The first integrated build passed its own zero-backend verifier but failed
three fresh independent audits. A repair is accepted only when all of the
following are implemented as semantic checks and exercised by executable
adversaries. Inventory labels, raw comparator-only examples, refreshed
self-IDs, and official-schema acceptance are not evidence by themselves.

1. Resolve the mutation manifest's exact `corpusManifestDigest` through the
   active BAG-08 catalog, resolve that corpus's exact observation manifest,
   and derive its vocabulary. Mutation, declaration, operand, cache, campaign,
   report, corpus, result, and replay validation must not consult fixed
   filename side authorities. Recompute and validate every current manifest
   test invocation from its exact test/program/parser/start/options/bounds
   fields; stale invocation IDs or changed test IDs reject transitively.
2. Resolve every live declaration, operand, comparison, gate, crash, query,
   conformance table, terminal, and semantic output through the active BAG-08
   catalog material. Direct fixture registries may locate expected test data,
   but cannot be an alternative semantic authority. Removing any referenced
   active-catalog entry must reject the complete manifest/campaign closure.
3. Add one side validator shared by gates, comparisons, and outer results.
   Side tags must match the resolved normal operand or semantic crash subject,
   exact declaration, baseline/mutant definition, test invocation, and all
   required profiles. Crash equality is evaluated only after this provenance
   validation. Swapped keys with refreshed IDs reject.
4. Derive terminal/completion provenance rather than trusting inline
   `normal|stuck` tags. Reachability finite rows, concrete outputs, predicate
   inputs, and pattern results must belong to the operand's exact subject and
   producing attempt. BAG-15 production evidence remains mandatory for native
   authority; finite rows authorize only their registered exact inputs.
5. Retain both complete sides and the exact comparison artifact when its
   derived outcome is `incomparable`, while also requiring the precise BAG-10
   `oracle/incomparable-result` failure. Every other failure follows BAG-09's
   exact side-absence relation. Couple `sourceSide` to the exact failure
   context/schema and derive the disposition from the matching BAG-10 taxonomy
   placement, including `resource-limit -> unknown`; no classification
   shortcut or source/failure cross-product is allowed.
6. Derive campaign baseline status and scoring eligibility from every baseline
   gate. Any rejected gate aborts mutant scoring with the exact BAG-09 failure;
   a campaign cannot retain `valid` baseline status or scored mutants after a
   gate error. An asserted expected normal side must have the declaration's
   exact oracle kind.
7. Enforce predicate binding sorts and exact input provenance. K-authored
   projection/query/comparison keys must use operation-specific catalog roles,
   and a native decision requires both a matching catalog-resolved `conformant`
   evaluator record and BAG-15 production receipt. Until BAG-15 exists, the
   zero-backend package must reject native decision authority rather than
   manufacture it. Retired legacy roles may occur only in the immutable
   execution-catalog compatibility snapshot and cannot satisfy live schemas.
8. Publish valid end-to-end declaration, baseline gate, normal operand,
   mutant operand, comparison, and outer-result evidence for all six oracle
   kinds and every built-in projection/comparator pair. Values must validate
   against their referenced terminals/bytes/tables before comparison. Include
   complete agree and distinguish cases, both incomparable crash orientations,
   unknown/incomplete cases, and the required non-ordinary accepted baseline.
9. Replace the nominal adversary list with a one-to-one executable registry:
   every advertised case names and runs its mutation/probe, and the verifier
   rejects missing or duplicate implementations. At minimum execute all
   cross-corpus vocabulary, stale test invocation/test ID, replay wrong-test,
   pattern result query/plan/search-policy, catalog removal, side reversal,
   crash provenance, output provenance, terminal relabel, reachability side,
   predicate sort/input, gate-abort, failure-source/context/disposition,
   incomparable-artifact, arbitrary K-role, and missing-production-authority
   cases found by the independent audits.
10. After repair, ordinary refresh must be run twice from the accepted state
    and produce identical package bytes. Then run the capped full verifier,
    official Draft 2020-12 validation, JSON/whitespace/cache/diff hygiene, and
    fresh independent audits over the refreshed state. Record only the final
    refreshed package hash; a pre-refresh hash is not completion evidence.
11. An asserted inline normal expected side must use the declaration kind's
    exact schema branch and pass kind-specific semantic validation before the
    comparator may discard provenance fields. Resolve and rederive referenced
    terminal states, output bytes and hashes/text, reachability witnesses,
    pattern results, predicate inputs/projections/bindings, and all applicable
    definition/query roots. Publish positive inline expectations for every
    built-in pair and executable rejection coverage for all six kinds,
    including a final-result expectation whose term agrees while its terminal
    key is absent from the active catalog.

### Refreshed acceptance evidence — 26 August 2026

Two consecutive ordinary refreshes produced identical package bytes. The
package fold over every file below `investigations/backend-agnostic-goal-closure/`
except `__pycache__` is
`c7e4ba9b91da20ecc800872f664d99447155c24a2de882a9e763a47ad738061b`.
The official Draft 2020-12 verifier passes 397,474 zero-backend checks.
Independent BAG-12 review accepted the kind-discriminated inline expectation
schemas, semantic provenance validation, nine built-in positives, and the
six-kind executable integrity probe. Fresh independent BAG-11 review accepted
the repaired producer ordering and complete active-catalog denotation sweep.

## Stop rule

Stop rather than treating opaque digests as oracle truth, turning backend
diagnostics into semantic output, inferring exhaustive absence from a bound,
or claiming future native projection/predicate/proof correctness.
