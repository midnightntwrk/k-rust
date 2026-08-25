# R3-G-01: one trace-backed RuleApplied event

Status: stopped and split after the third substantive full-oracle cycle on
19 August 2026. Worker commit `c4ad784` passed its semantic replay in the
worker checkout, but root audit found that its frozen source provenance and
derived lineage/fingerprints embed that checkout's absolute path. It is not
integrated. `R3-G-01A` owns the checkout-stability repair; this file preserves
the original packet contract and cycle boundary.

## Objective

Replace R2-G-07's one-bit rule-applied oracle with one inspectable, typed
`RuleApplied` event appended to branch-local list trace state when the same P3
`bump-state` transition fires. K must structurally select the transition and
author the complete trace-cell update, including stable rule identity, label,
module, source, and location payload. The update and the original semantic
transition must remain one official rule application.

This packet proves one event and one concrete append. It does not define a
general event vocabulary, observation specification language, matcher,
monitor, corpus result, symbolic path, or multi-rule facility.

## Starting inputs and deliberate boundary

- the activation commit containing this packet, descended from accepted
  R2-G-07 commit `71379e4`;
- accepted `OfficialDefinitionAdapter v1`, the R2-G-07 post-CF projection,
  immutable rebuild, identity/provenance checks, parser hardening, and erasure
  oracles;
- P3's `bump-state`, firing `start`, and non-firing integer programs;
- `draft/goal/execution-pattern-matching.md`, especially sections 2, 4.2,
  4.3, and the distinction between rule events and domain events; and
- K v7.1.337 at
  `4a46d1231473b599c699160132fd6e76a5c46406`, using the pinned Haskell-backend
  profile.

Create a task-owned source fixture that is semantically P3 plus only:

```k
syntax RuleOrigin ::= ruleOrigin(String, String, String, String, String)
syntax TraceEvent ::= ruleApplied(RuleOrigin)
configuration ... <trace> .List </trace> ...
```

The source fixture must not instrument any rule. It deliberately supplies the
event productions and empty trace configuration through ordinary official K so
this packet adds only one post-CF contract. K-authored trace configuration is
the immediate follow-on packet after this event/append contract is stable.
Record hashes for every consumed fixture, shared normalizer, accepted spine
source, K source/hook, and tool pin. External K remains read-only.

## Sole new contract: `KRuleAppliedTrace-v1`

Project the post-CF official `Definition` before `KoreBackend.steps()` using:

- schema and whole-definition fingerprint;
- canonical modules and all primary-source rules with stable lineage, label,
  module, source/location, content/body/conditions/attributes fingerprints;
- complete typed rule terms using the accepted explicit constructors and
  metadata fingerprints; and
- canonical generated-cell and production descriptors sufficient to resolve
  the declared trace cell, list constructors, event constructor, origin
  constructor, token sorts, and every result term without source/KAST JSON.

The exact result contains:

- schema `KRuleAppliedTrace-v1` and transformation
  `p3-trace-bump-rule-applied@1`;
- expected definition fingerprint and exact candidate count;
- status `apply` or `already-present`;
- complete target lineage/provenance and stale-precondition fingerprints;
- one operation `appendGeneratedCellTerm`;
- input-relative application-argument path to an existing cell-bag parent;
- K-declared trace cell name and one fresh trace variable with declared sort;
- a complete typed before/after trace update whose after term appends exactly
  one `ruleApplied(ruleOrigin(ID, Label, Module, Source, Location))`; and
- a host-computed canonical result fingerprint independent of pretty spacing.

K chooses every constructor/label/name, payload field placement, fresh
variable, insertion path, target, cardinality, and apply/already/conflict
status. The stable ID in the payload is the selected rule lineage. K copies the
label/module/source/location from the structurally selected projected rule; it
must not use a Java-provided fixture constant.

One exact top-level typed K result is accepted. Multiple/residual output,
unknown constructors, noncanonical integers/strings, unsupported paths,
unresolved/ambiguous productions, sort-invalid result terms, variable
collisions, and payloads inconsistent with the selected rule reject.

## Generic host authority

Java may project and parse the contract, validate exact fingerprints, navigate
the declared path, resolve declared official generated-cell/production
metadata, validate a fresh variable and typed term graph, construct the
declared fragment with official constructors, and immutably rebuild the
ancestors/rule/module/definition. It may independently verify that the event
payload equals the target's projected lineage/provenance.

Java may not search for `bump`, `state`, `trace`, `ruleApplied`, `ruleOrigin`,
list labels, P3 module/labels, the event payload order, or the target/path.
Contract/schema names and generic operation constructors are not fixture
selection. Add a replay scan enforcing this literal boundary.

If the host would need a second new plugin boundary, source/KAST JSON
round-trip, backend trace parser, or fixture-specific constructor logic, stop
and split.

## Positive, idempotence, and runtime oracles

1. Compile the uninstrumented task-owned trace fixture through unchanged
   official K as the baseline.
2. Project the post-CF definition and run `KRuleAppliedTrace-v1`.
3. Require one `apply` candidate and validate all target, metadata, term, sort,
   path, freshness, and payload preconditions against the original definition
   before construction.
4. Apply exactly one rule edit. Preserve module/import/sentence cardinality,
   rule lineage, label, source/location, attributes including priority,
   `requires`, `ensures`, and every original body node outside rebuilt
   ancestors. Require a new `Definition`, one application, and one changed
   primary-source rule.
5. Reproject the output and run K again. Require one `already-present`
   candidate, independent host validation of exactly one equal trace update,
   zero further applications, and the same instrumented definition reference.
6. Continue through unchanged official lowering and the Haskell backend.

For `start`, require final `<k> 1`, `<state> 2`, and a trace containing exactly
one event. Its origin payload must equal the selected rule's recorded lineage,
label `bump-state`, module, source, and location. For the non-firing integer,
require `<k> 1`, `<state> 1`, and `.List`/empty trace. Erasing trace state must
equal the uninstrumented fixture and the accepted P3 program-state projection.

Compile an independent ordinary-source oracle with the exact same trace update
written in K source and require both full runtimes to match it. Repeat from
fresh output and require stable request/result fingerprints, normalized full
and focused Kore, syntax Kore, macros, event payload, and both runtimes. Syntax
Kore/macros must equal the uninstrumented trace fixture.

This proves only the two concrete paths. Do not claim symbolic branch
isolation, absence, backend-independent rule application, or general event
semantics.

## Required negatives

Every negative returns no instrumented definition, performs zero rule
applications, skips official lowering/backend, and emits no known backend
artifacts:

- stale target content or provenance fingerprint;
- zero and duplicate structural target cardinality;
- unsupported/out-of-bounds parent path;
- missing or ambiguous trace-cell/constructor metadata;
- result term with unknown constructor or incompatible sort;
- declared trace variable colliding with an existing target variable;
- same trace cell with a conflicting update/event;
- result claiming `already-present` on the uninstrumented rule;
- unsupported selected body without a safe cell-bag insertion point; and
- noncanonical, residual, multiple, or unknown exact-result encodings.

Record the closest failure class and prove zero applications/backend artifacts.
Test-only mutations may be generic and task-owned; they may not move fixture
selection or semantic choices into Java.

## Evidence and ownership

Generate exact compact `results.json` and `report.md` with:

- all source/tool/accepted-spine hashes and the actual full-cycle count;
- request/response/status/candidate/application/idempotence records;
- target identity/provenance/conditions/attributes and generated metadata;
- canonical declared operation and event payload;
- firing/non-firing/full/erased/ordinary-source/repeat oracles;
- every negative classification and artifact-absence result; and
- limitations, packet ambiguity, and the recommended K-authored trace
  configuration composition packet.

The worker may modify only:

- `spine/rule-applied-trace/**`;
- `evidence/r3-g-01-single-rule-applied-trace/**`; and
- the single `r3:g:rule-applied-trace` script entry in `package.json`.

The worker may inspect but not modify accepted spines/evidence, tasks,
roadmaps/checkpoints/loop/goal/ADR documents, external K, or P1/P2/P3 fixtures.
Raw build output belongs below the ignored new spine build tree.

## Acceptance

Add and pass from a checkout with no pre-existing acceptance output:

```sh
bun run r3:g:rule-applied-trace
bun run check
git diff --check
```

Replay must fail closed on a wrong pin/source/normalizer/accepted-spine hash and
must regenerate and byte-compare both committed evidence files.

## Stop/split rule

Stop with replayable evidence instead of expanding if acceptance requires:

- modifying accepted hook/configuration/rule-observation contracts or spines;
- K-authored trace configuration in this packet;
- a second new contract or host boundary;
- more than one selected rule/event or any domain event;
- event matching, monitors, temporal syntax, corpus aggregation, backend-log
  compatibility, symbolic exploration, C1/C2, or general `SemanticInput`; or
- more than three substantive full-oracle cycles.

Return one clean worker commit with task-owned changes only. State commit,
verdict, cycle count, contract, K/Java ownership, exact event payload,
idempotence, runtime/erasure/source oracles, negatives, limitations, ambiguity,
and the recommended trace-configuration composition packet.
