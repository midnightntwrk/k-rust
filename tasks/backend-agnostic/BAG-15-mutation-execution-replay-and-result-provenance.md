# BAG-15: mutation execution replay and result provenance

Status: fleshed and authorized backend-agnostic closure packet; activation is
held until BAG-12 is independently accepted and BAG-14 is integrated.

## Objective

Make mutation classifications replay-addressable rather than calling patch
materialization a replay of the mutant campaign. The current
`mutation-instance` replay is deliberately patch-only: it ingests the baseline,
applies the patch, validates the output definition/diff, and forbids program,
test, query, observer, solver, or execution identity. Yet a campaign links only
that replay from each mutant while reporting test and oracle results. An
ordinary-result kill has no execution replay at all, and an execution-pattern
replay is not required to be the one that supplied the campaign operand.

This packet closes portable replay scope, invocation identity, and result
provenance. Native commands, process topology, actual execution, and proof
that the Rust adapter reproduces a recorded result remain Rust-stack work.

## Replay kinds and honest names

Separate these closed replay operations:

1. **Mutation materialization**: baseline definition plus exact operator,
   candidate, patch, and adapter/profile identities produce the mutant
   definition and structural diff, followed by the declared validation stage.
   Rename or explicitly scope the current `mutation-instance` kind so it does
   not claim to reproduce tests or classification.
2. **Execution attempt**: exact baseline or mutant definition plus one test
   invocation, profiles, bounds, observation inputs, and execution adapter
   produce one typed terminal execution record. Its invocation identity is
   the same identity used by BAG-14 cache records.
3. **Baseline admission**: one exact baseline attempt/operand plus the
   test-scoped BAG-12 declaration and BAG-09 baseline policy produce the
   one-sided gate result. It is not a degenerate two-sided comparison.
4. **Baseline-mutant oracle comparison**: exact ordered baseline and mutant
   operands/attempt records plus one test-scoped BAG-12 declaration and its
   artifacts produce a typed comparison receipt/outcome.
5. **Campaign derivation**: exact manifest/operator/materialization roots,
   ordered attempt and oracle receipts, failure taxonomy, and scheduling mode
   produce the candidate statuses, campaign status, exclusions, score, and
   normalized report.

The campaign's declared schema/operation versions are semantic provenance,
not an unchecked decorative object. They exactly cover every schema and
operation kind used by the report/child receipts, resolve to the package's
declared versions, and are included in derivation identity.

Represent that provenance as one closed recursive registry
`{schemaVersion, registryId, schemas, operations}`. `registryId` is
`k-in-k/replay-version-registry/v1` over the record without itself. Schema
entries are exactly `{schemaId, schemaVersion, schemaDigest}`; operation
entries are exactly `{operationKind, operationVersion}`. Both arrays are
lexically sorted by their identifier/version tuple and duplicate-free. The
schema digest is lowercase SHA-256 over the exact bundled schema bytes named
by `schemaId`, not a digest copied from an instance or a reserialized schema.
The
verifier traverses the claimed report, every receipt in its exact child
closure, and every typed input/output artifact, derives the required entry
set, and requires set equality with the registry. Missing entries, surplus
decorative entries, duplicate aliases, unknown versions, and a digest for
different schema bytes reject. The registry covers portable contracts only;
producer implementation versions remain in receipts.

These may be separate manifests connected as a typed DAG. Do not encode a
whole campaign as one backend command or duplicate all child inputs in an
opaque suite blob.

## Invocation versus receipt

Every operation has two identities:

- an invocation digest over all requested inputs, semantic profiles, bounds,
  adapter/operation versions, and ordered step roles, excluding outputs; and
- a completed replay/receipt digest that also covers typed terminal status,
  expected outputs/failures, artifact references, and child receipts.

Every receipt is self-describing and recomputable: it contains a closed
operation kind and portable operation/conformance version; separate producer/
adapter identity; the full invocation payload plus digest; producer completion
status; ordered input/output BAG-08 keys; exact child receipt IDs; typed
semantic result/failure; and receipt ID. Adapter identity may affect native
fidelity without redefining the portable operation contract. Portable checks
validate the declared identity and graph; Rust proves producer mapping.

Keep producer completion distinct from semantic result. A producer may
`complete` an attempt whose exact semantic result is timeout, bounded unknown,
semantic crash, or typed infrastructure error. `completed` never means normal,
agreement, or reusable semantic success; fold reuse through BAG-14's exact
classes.

### Exact invocation and receipt algebra

Use one BAG-08 `operation-receipt` role and one generic closed receipt schema;
do not create operation-specific opaque receipt roles. The embedded invocation
contains exactly:

```text
schemaVersion, invocationDigest,
operationKind, operationVersion, adapterContract,
parameters, inputs, childReceipts, outputRoles
```

`invocationDigest` is `k-in-k/operation-invocation/v1` over every field except
itself. `adapterContract` is exactly `{adapterId, adapterVersion}` and names
the requested portable-to-native adapter contract, not a process or command.
`inputs` is an ordered array of `{edgeRole, artifact}` with a role-typed
BAG-08 key. `childReceipts` is an ordered array of `{edgeRole, receipt}` with
an already-resolved `operation-receipt` key. `outputRoles` is the exact
nonempty requested artifact-role sequence. Edge roles are closed per
operation, unique where the operation is one-to-one, and may repeat only where
that operation's declared cardinality permits repetition. There is no generic
unchecked `artifacts` array.

`parameters` is a discriminated exact union keyed by `operationKind`:

- `mutation-materialization` contains the BAG-07/BAG-13 baseline, operator,
  candidate, patch, compatibility/lowering profiles, and
  validation policy roots. It has no test, query, execution, or oracle fields.
  The mutation-instance/mutant-definition/diff are outputs and therefore may
  not appear in this invocation arm.
- `execution-attempt` contains exactly the complete BAG-14
  `execution-attempt-key` and key digest. The generic input edges must equal
  the deterministic typed artifact traversal of that key; they are DAG edges,
  not a second independently editable request.
- `baseline-admission` contains exactly the BAG-14
  `oracle-evaluation-key` whose kind is `baseline-admission`.
- `oracle-comparison` contains exactly the BAG-14 oracle-evaluation key whose
  kind is `baseline-mutant-comparison`.
- `campaign-derivation` contains the pre-execution campaign invocation key,
  schedule mode, exact ordered materialized plan entries, and selected cache-
  record/child-receipt keys. Its inputs and children equal that selection in
  manifest/test/oracle order.
- `report-publication` contains the derivation invocation/receipt, exact
  recursive version registry, and normalized report body excluding report and
  receipt self-IDs.

An operation-specific schema freezes each arm's field set, input edge roles,
child roles, output roles, and cardinalities. A digest with a plausible role
does not satisfy an edge whose operation arm did not declare it. BAG-16 may add
branch-collection production and corpus/pattern derivation arms to this same
union; it must not add a second receipt family.

The completed receipt contains exactly:

```text
schemaVersion, receiptId,
invocationDigest, invocation,
producer, producerStatus,
outputs, semanticTerminal, failure
```

`receiptId` is `k-in-k/operation-receipt/v1` over every field except itself.
`producer` is exactly `{producerId, producerVersion,
executionConformance}`; `executionConformance` is `finite-vector-proven`,
`native-proven`, or `not-proven` and follows BAG-14's reuse boundary.
`producerStatus` is `complete` or `failed`. `complete` means the producer
atomically published the declared output sequence and typed terminal, even
when that terminal is timeout, unknown, semantic crash, incomparable, or
another ordinary semantic failure. `failed` is reserved for producer/
infrastructure failure, has no semantic-success terminal, and cannot be
reused as semantic evidence.

For `producerStatus: complete`, `outputs` is an ordered array of `{edgeRole,
artifact}` and must match `invocation.outputRoles` exactly in length, role,
and order; every artifact resolves and is available under the declared
resolver. For `producerStatus: failed`, `outputs` is empty,
`semanticTerminal` is null, and `failure` is one exact BAG-10 producer/
infrastructure failure; intended output roles remain only in the invocation
and no downstream edge may consume them. `semanticTerminal` for a complete
producer is a closed operation-compatible union of the BAG-09 execution
terminal/crash/failure, BAG-12 gate/comparison/failure, materialization
validation result, or campaign/report result keys. `failure` is null exactly
when the selected complete-terminal relation permits it and otherwise one
BAG-10 failure with the exact operation context. The receipt never copies
cache-hit state, host exit, timestamps, paths, diagnostics, argv, or worker
identity into semantic fields.

Receipt wrapping does not invent a generic `operation-production` failure
context. Preserve the closest BAG-10 semantic boundary: baseline or mutant
execution, baseline-oracle gate, oracle comparison, campaign, or report
publication as appropriate. `operationKind` already records which producer
step failed. Any genuinely new placement introduced by a receipt arm must be
added bidirectionally to BAG-10's schema/taxonomy inventory; malformed receipt
graphs themselves are report schema/referential-integrity rejection, not
runtime semantic failures.

For bundled zero-backend positives, `finite-vector-proven` is authorized only
when the verifier recomputes the registered operation from bundled inputs and
obtains the exact outputs and semantic terminal. Merely refreshing a receipt
ID cannot promote `not-proven`, substitute an opaque producer, or authorize a
K-authored evaluator. BAG-12 evaluator conformance and this production receipt
are separate required authorities.

Expected output bytes or result digests are not invocation inputs. Step output
roles and required output arity are invocation inputs. This prevents an
output/input cycle while keeping the requested operation typed.

A produced trace, value, or branch collection binds the cycle-free execution
`invocationDigest`, never the completed receipt ID. The receipt then binds its
output keys and relational validation proves the association. An output cannot
contain the ID of a receipt whose own ID covers that output.

Parallel digest/role arrays must have equal arity, and every transformation
digest has a corresponding role or its own ordered transform step. If v1
supports exactly one observation transformation, state that cardinality in
schema instead of accepting an arbitrary array that the fixed role list cannot
type.

The receipt graph is checked as a graph, not only one edge at a time. Receipt
IDs are unique; every child exists before its consumer; a child output used by
the parent resolves to the same artifact key; no receipt is its own direct or
transitive child; every declared intermediate output has exactly the
operation-permitted number of consumers; and roots are exactly the receipts
selected by campaign/report publication. Unreferenced fixture receipts are
allowed only outside a claimed campaign closure. Within one claimed closure,
dangling, surplus, duplicate, reordered, or cross-campaign children reject.

## Campaign/result closure

Every executed baseline or mutant test record references exactly one execution
invocation/receipt for the reported subject and test. Every required baseline
gate references its exact baseline attempt and one-sided admission receipt
before any mutant child. Every non-skipped pairwise oracle result references
the exact ordered baseline and mutant operands/attempts and its comparison
receipt. BAG-09 semantic termination, BAG-11 query identity,
BAG-12 operand semantics, BAG-14 attempt/cache identity, and BAG-08 artifact
closure apply without alternate roots.

Execution-produced traces and result values bind their producing attempt
invocation; the completed attempt receipt binds them as outputs. A
content-identical event trace may be deduplicated as a semantic
artifact, but attaching it to another definition/program/profile/bounds root
requires another exact producing receipt; the trace's bare `testId` and path
identity are not invocation provenance.

The campaign-derivation receipt consumes exactly the records actually used:

- `full` requires all selected test attempts and oracle evaluations;
- `first-kill` requires the manifest prefix through the first derived kill and
  records the suffix as scheduled/skipped without fabricated replay receipts;
- invalid/timeout/unknown/error outcomes consume their typed terminal receipt
  rather than a successful-result placeholder; and
- baseline failure prevents mutant execution receipts and scoring exactly as
  the campaign contract requires.

Preserve three campaign layers: a pre-execution request invocation over the
full ordered plan and schedule mode with no children; a derivation invocation
over the exact chosen child record/receipt IDs; and a materialized report
receipt over derived statuses, exclusions, and score. The DAG is globally
acyclic, all inputs are available before their consumers, declared output
role/arity agrees exactly, and no dangling or surplus intermediate edge exists.

The campaign report links its derivation receipt, and each child result links
its own receipt. Replaying materialization alone may prove the output mutant
and diff; it cannot substantiate `killed`, `survived`, or any test/oracle
outcome.

## Abstract portability boundary

Portable replay records name versioned operations and typed artifact edges,
not shell command strings. The future Rust stack maps those operations to
native entry points and records implementation-specific diagnostics as
supplemental evidence. Backend commands/argv, worker placement, temporary
paths, and cache-hit provenance do not enter portable semantic identities.

Re-execution may produce different supplemental diagnostics or storage
locations. Acceptance compares the schema-defined semantic artifacts,
statuses, witnesses, and receipts. Byte-exact equality is required only where
the relevant artifact contract declares exact bytes semantic.

## Required evidence

- one materialization receipt linked to the mutant definition and diff;
- baseline and mutant execution receipts for an ordinary final-result oracle;
- baseline and mutant execution receipts plus the exact BAG-11 pattern replay
  for an execution-pattern oracle;
- baseline-mutant comparison receipts that bind both sides, the test invocation, and
  the declaration;
- baseline-admission receipts for every required baseline gate;
- a full campaign derivation from all child receipts;
- a first-kill campaign whose skipped suffix has no child receipt;
- an invalid pre-execution mutant stopping at materialization/validation with
  no fabricated execution/oracle children, plus an inconclusive execution
  represented by a completed attempt receipt with exact bounded evidence; and
- mutation materialization replay remaining independently useful without
  being described as classification replay.

Permanent adversaries must reject a patch-only receipt offered as kill
evidence, a result with no execution receipt, baseline/mutant subject reversal,
receipt/test or definition drift, pattern operand linked to another query or
replay, final-result operand linked to no producing attempt, oracle receipt
using another projection/comparison/crash policy, full derivation missing a
test, first-kill receipt on a fabricated suffix, baseline failure with mutant
children, result digest inserted into its own invocation, parallel role/digest
arity drift, transformation chain/role drift, the same trace asserted as
produced by another invocation without its exact receipt, dangling intermediate
output, missing/extra/incorrect declared schema versions, and a refreshed
self-ID concealing any changed edge.

Also reject output-to-receipt self-cycles or a receipt ID substituted for an
execution invocation; baseline admission substituted for pairwise comparison;
missing baseline admission before mutant children; producer `completed`
treated as normal/agreement; campaign request, derivation invocation, and
report receipt conflated; digest-only opaque receipts; a cyclic DAG,
unavailable input, wrong output role/arity, or surplus child; invalid
pre-execution evidence with execution children; comparison under another
candidate/campaign plan; and a child operation/schema kind absent from or
surplus to the exact recursive version registry.

## Ownership

The worker may revise replay schema/kinds/fixtures/vectors, add operation
receipts, and update mutation manifest/campaign schemas and fixtures after
BAG-12/BAG-14, contracts, artifact roles/catalog after BAG-08, verifier,
refresh helper, completion evidence, and Rust handoff replay notes. Do not edit
goals/D1/roadmap, prescribe Rust APIs or commands, execute a backend, or claim
native replay success.

## Acceptance

- patch materialization and execution/classification replay have honest,
  distinct scopes;
- every reported non-skipped test and oracle outcome has exact producing
  invocation/receipt provenance;
- campaign derivation consumes the schedule-required child receipts;
- invocation/result identity is cycle-free and every typed dataflow edge is
  closed;
- abstract replay remains usable across the stack replacement;
- all mandatory adversaries reject through schema or semantic validation;
- zero-backend and official Draft 2020-12 validation pass;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- checks are tiny and serial; and
- `git diff --check` passes.

### Post-BAG-12 root compatibility review — 23 August 2026

This review does not activate BAG-15 or replace its independent preflight.
The repaired BAG-12 graph preserves the intended authority split: a matching
`conformant` evaluator record proves semantic conformance, while this packet's
operation receipt proves production provenance. Neither record authorizes a
native K-authored decision alone. BAG-15 must use BAG-12's operation-specific
K-authored source/plan/query/comparison roles and exact declaration/test/
subject/profile roots; the generic receipt's typed edges must not reintroduce
the retired generic oracle roles or a fixture-filename side authority.

BAG-12's finite rows already carry exact bundled producer traces for portable
conformance cases. BAG-15 may wrap recomputed finite operations with
`finite-vector-proven` receipts, but it must not reinterpret those rows as
native production or create a receipt pointing backward from an operand. The
operand/trace/collection continues to bind the cycle-free invocation, and the
receipt points forward to the produced artifact. Independent preflight must
recheck this direction after BAG-14 fixes the final attempt/evaluation key and
cache-record schemas.

## Stop rule

Stop rather than freezing shell commands, process layouts, cache locations, or
backend diagnostics into the portable contract, and rather than treating a
portable recipe as proof that the future Rust implementation has replayed it.
