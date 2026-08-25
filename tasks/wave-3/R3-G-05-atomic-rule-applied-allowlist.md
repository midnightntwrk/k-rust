# R3-G-05: atomic exactly-two `RuleApplied` allowlist

Status: activated implementation packet on 21 August 2026. The activation
commit containing this file is the worker base and must be recorded exactly.

## Why this is the next dependency

Accepted R3-G-04 proves exact same-origin two-event adjacency, but cannot
discriminate order or a gap because both observations are identical. The next
required boundary is therefore producer-side: atomically instrument exactly
two distinct ordinary transition rules with generic `RuleApplied` events.

This packet introduces only that exact-two producer contract. It does not add
domain event constructors, temporal matching, symbolic execution, corpus
status, mutation operators, or a general allowlist size.

## Objective and fixture

Create a task-owned P3-like definition with `<k>` and integer `<state>` cells,
ordinary integer addition, and two safe cell-shaped transitions:

```k
rule <k> bump => 0 ... </k>
     <state> I => I +Int 1 </state>
  requires I >=Int 0
  ensures I +Int 1 >Int 0
  [label(bump-state)]

rule <k> drop => 0 ... </k>
     <state> I => I -Int 1 </state>
  requires I >Int 0
  ensures I -Int 1 >=Int 0
  [label(drop-state)]
```

The source declares the accepted `RuleOrigin` and `TraceEvent` productions but
does not contain a trace cell or instrumented rule. The accepted pre-CF
`KTraceConfigurationAugmentation-v1` adds the exact empty trace cell. The new
post-CF transformation instruments `bump-state` and `drop-state` together.

Required programs include:

- `bump + drop`, firing both selected rules once and then unselected addition;
- `drop + bump`, reversing their runtime order;
- `bump + bump`, repeating one selected rule; and
- an integer input firing neither selected rule.

Pin exact source/program hashes. For initial state `1`, `bump + drop` erases to
`<k> 0`, `<state> 1` and its trace contains exactly two distinct generic
origins in runtime order. Do not call this a temporal-pattern result.

## Sole new contract: `KRuleAppliedAllowlist-v1`

Project the official post-CF definition through the accepted typed boundary.
One exact K result contains:

- schema `KRuleAppliedAllowlist-v1`, transformation name/version, and the
  expected whole-definition fingerprint;
- exact candidate count `2`;
- one canonically ordered two-element target list with distinct lineages;
- homogeneous top-level status: both `apply` or both `already-present`;
- for each member, complete target lineage, module/label/source/location,
  content/body/conditions/attributes fingerprints, and provenance;
- for each member, one typed `appendGeneratedCellTerm` operation with declared
  parent path, trace cell metadata, fresh variable, before/after term, and the
  complete five-field `ruleApplied(ruleOrigin(...))` witness; and
- a canonical result fingerprint independent of pretty spacing.

K owns:

- structural selection of the two supported transition shapes;
- exact cardinality, distinctness, and canonical requested order;
- every target, path, constructor, payload, field placement, and fresh name;
- both typed operations; and
- apply/already/conflict classification for the pair.

K may use projected labels/provenance only after the supported structural shape
is recognized. The host may not search for fixture literals or reorder K's
members.

## Atomic generic host authority

Reuse `OfficialDefinitionAdapter-v1` and the accepted pre-CF hook. Do not add a
hook, plugin boundary, source parser, KAST-JSON round trip, or external-K patch.

The task-owned Java driver must:

1. parse one exact pair result;
2. validate both targets and operations completely against the same original
   `Definition`;
3. reject duplicates, overlap, stale members, unsupported paths, mixed
   statuses, and partial existing instrumentation;
4. prepare both immutable replacements without exposing an intermediate
   definition; and
5. only after both preparations succeed, perform one transformer traversal
   producing one new definition with exactly two changed primary-source rules.

Sequentially invoking the accepted unary driver twice is prohibited. A
successful validation of the first member followed by failure of the second
must still report zero applications and no output definition.

Idempotence is pair-wide:

- fresh input: two `apply` members, two applications, two changed rules, one
  output definition;
- second pass: two independently validated `already-present` members, zero
  applications, and the same transformed definition reference; and
- one-present/one-absent or mixed apply/already is a conflict, never repair.

## Required positive oracles

One resource-capped full-oracle run must establish:

- exact two candidates, validations, applications, and changed source rules;
- stable distinct target origins and K-declared canonical order;
- preservation of lineage, provenance, attributes, `requires`, `ensures`, and
  every original body node outside the inserted ancestors for both rules;
- pair-wide idempotence as specified above;
- baseline/instrumented trace erasure equality for all four programs;
- exact runtime traces for bump/drop, drop/bump, repeated bump, and neither;
- raw five-field runtime origins equal independently projected targets before
  portable projection;
- an independent ordinary-source definition with the same two trace updates;
- equality of transformed and ordinary-source focused runtime behavior;
- stable request/result/operation fingerprints, normalized focused/full Kore,
  syntax Kore, macros, runtime projections, and portable evidence across two
  task-local fresh compilations; and
- no transformation or backend artifact outside the task build directory.

The combined trace proves only that the producer emits both generic events.
Ordering and gap semantics remain for later K-authored matcher packets.

## Required failures

Every failure constructs no transformed definition, applies zero edits, skips
lowering/backend, and proves absence of task-known backend artifacts:

- zero, one, or three structurally selected targets;
- duplicate target or lineage and noncanonical K member order;
- stale first member and stale second member;
- invalid parent path, generated metadata, sort, freshness, constructor, or
  payload in either member;
- conflict on either target;
- false or mixed apply/already statuses;
- one-present/one-absent partial instrumentation;
- unsupported safe-insertion shape;
- forced preparation failure for the first and second operation;
- malformed, multiple, residual, unknown, or noncanonical exact result; and
- a Java fixture-literal scan violation.

Test mutations stay generic and task-owned. They may not transfer selection,
ordering, or term construction from K into Java.

## Resource-safe oracle and verification policy

Do not replay R3-G-04 or recursively rebuild any accepted ancestor. Verify
accepted commits, trees, source hashes, and committed evidence directly.
Consume accepted adapter/configuration/producer sources read-only from the
integration tree.

The package command is a zero-backend verifier over committed evidence,
source hashes, exact schemas, and zero-backend adversarial tests. It must not
launch `kompile`, `krun`, Java, or the Haskell backend.

The separate task-local full-oracle script must:

- acquire a nonblocking exclusive `flock` dedicated to K-in-K backend work;
- run all compiler/backend processes serially;
- lower its process priority;
- append `_JAVA_OPTIONS` forcing at most 1536 MiB and two active processors,
  rejecting any override above 2048 MiB or two processors;
- write only beneath one ignored task build directory;
- refuse to run when another K-in-K oracle owns the lock; and
- expose an explicit cache-finalization mode that reprojects a successful raw
  run after host/report-only changes without compiler/backend invocation.

The worker gets at most three substantive full-oracle cycles. Plan source and
zero-backend adversarial work first; do not spend a cycle on report wording.
An interrupted environmental run counts only if compiler/backend outputs were
used to change implementation or evidence.

## Evidence

Commit compact checkout-stable `results.json` and `report.md` including:

- activation/start revision, K/tool/accepted source pins, cycle history, and
  exact raw-run/finalization provenance;
- the new contract and K/host ownership boundary;
- both targets and portable origins, with raw values validated and omitted;
- exact atomicity/idempotence counts and preservation facts;
- all runtime, erasure, ordinary-source, repeat, and artifact oracles;
- every negative classification and zero-application/backend result;
- resource policy, effective installed-JDK heap precedence probe, lock policy,
  and routine zero-backend count;
- limitations, ambiguity, and whether typed domain events are unblocked.

Raw definitions, K output, compiler/backend logs, raw source paths/IDs, and
checkout-local artifacts remain under the ignored build tree.

## Ownership

The worker may modify only:

- `spine/rule-applied-allowlist/**`;
- `evidence/r3-g-05-atomic-rule-applied-allowlist/**`; and
- one new `r3:g:rule-applied-allowlist` entry in `package.json`.

Accepted spines/evidence, tasks, roadmaps/checkpoints/loop/goal/ADR documents,
other fixtures, lockfiles, external K, and existing package entries are
read-only.

## Acceptance

From the worker and integrated trees, these routine commands must finish
without compiler/backend processes:

```sh
bun run r3:g:rule-applied-allowlist
bun run check
git diff --check
```

Root audits the complete diff, raw-run logs, cached finalization, resource
guards, and committed evidence. Root does not repeat the heavy backend run.

## Stop/split rule

Stop and return a checkpoint rather than expanding if acceptance requires:

- changing accepted v1 producer/configuration contracts, adapter/hook, or
  external K;
- wrapping a bare rule or adding an operation other than
  `appendGeneratedCellTerm`;
- Java choosing targets, order, paths, constructors, payloads, or fixture
  literals;
- sequential partial application or healing mixed instrumentation;
- more or fewer than exactly two selected rules;
- domain events, temporal matching, symbolic work, mutation work, C1/C2, or a
  general allowlist;
- a second new contract/host boundary; or
- more than three substantive full-oracle cycles.

## Return contract

Return one clean worker commit. Report activation revision, cycle count,
contract, exact targets/operations, K/host ownership, atomicity/idempotence,
runtime/erasure/ordinary-source/repeat evidence, failures, resource behavior,
evidence hashes, limitations, ambiguity, and whether the typed domain-event
leaf is dependency-unblocked. Do not claim root integration or a temporal
result.
