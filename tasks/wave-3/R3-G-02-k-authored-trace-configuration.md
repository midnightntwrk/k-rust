# R3-G-02: K-authored empty trace configuration composition

Status: stopped prototype on 19 August 2026. Worker commit `478ea27` completed
three substantive cycles and passed its frozen replay, but root's independent
audit rejected integration for incomplete cloned-shell equality and unchecked
failure-envelope semantics. The prototype remains on `agent/r3-g-02`; it is
not integrated. Repair is split into `R3-G-02A`.

## Objective

Remove the ordinary-source `<trace> .List </trace>` configuration cell from
the accepted one-event fixture, then make K author that exact empty list-backed
cell at the typed pre-CF hook. Continue through official cell checks and CF
generation, invoke the unchanged accepted `KRuleAppliedTrace-v1` post-CF
contract, and prove the same one-event firing/non-firing behavior.

The source fixture keeps the accepted `RuleOrigin` and `TraceEvent`
productions. This packet moves only empty trace configuration ownership into K;
it does not move event syntax, add an event, instrument another rule, match a
trace, add a monitor, or explore a symbolic branch.

## Starting inputs and exact fixture delta

- accepted integrated R3-G-01A tree at `1ac7bc1`;
- accepted `OfficialConfigurationTransformHook-v0` and
  `OfficialDefinitionAdapter v1` at the pinned pre/post-CF seams;
- accepted R2-G-06 configuration selection, immutable shell cloning,
  idempotence, and failure-envelope principles, without changing its contract;
- accepted `KRuleAppliedTrace-v1`, event/append K semantics, generic host
  validation, portable evidence projection, 16 negative groups, and evidence;
- `draft/goal/execution-pattern-matching.md` sections 4.2 and 4.3; and
- K v7.1.337 at
  `4a46d1231473b599c699160132fd6e76a5c46406`, using the pinned Haskell backend.

Create a task-owned input fixture equal to the accepted R3-G-01 fixture except
that line 27 is blank instead of:

```k
      <trace> .List </trace>
```

Keep the existing module names, event productions, imports, other line layout,
rules, contexts, conditions, and attributes. The blank line deliberately keeps
the selected rule's location stable while making the configuration genuinely
two-cell input. Record exact hashes for the activation packet, fixture,
accepted contracts/spines/evidence, hook patch, normalizers/projectors, K pin,
and all new task sources. External K remains read-only with exact expected
status ` M pyk/uv.lock`.

## Composition and contract budget

One official compiler run has this exact shape:

```text
official typed Configuration
  -> existing OfficialConfigurationTransformHook-v0
  -> new KTraceConfigurationAugmentation-v1
  -> official cell checks and CF generation
  -> existing OfficialDefinitionAdapter v1
  -> unchanged KRuleAppliedTrace-v1
  -> unchanged official lowering/backend
```

The run contains two K-facing contracts, but only
`KTraceConfigurationAugmentation-v1` is new. Do not revise either accepted
boundary or `KRuleAppliedTrace-v1`. A task-owned combined driver may compose
the existing seams and may reuse/copy accepted trusted-small host mechanics;
accepted spine files stay unchanged.

## Sole new contract: `KTraceConfigurationAugmentation-v1`

Project the pre-CF official definition as canonical typed data containing:

- schema and whole-definition fingerprint;
- all official `Configuration` sentences with module, source/location,
  stable lineage, content/body/`ensures`/attribute fingerprints;
- their complete typed K bodies and node metadata; and
- exact official production/sort descriptors sufficient to resolve the one
  declared initializer without source or KAST JSON round-trip.

The exact result contains:

- schema `KTraceConfigurationAugmentation-v1` and transformation
  `p3-add-empty-trace-cell@1`;
- expected definition fingerprint and exact candidate count;
- status `apply` or `already-present`;
- target lineage and stale-safe content/body/condition/attribute fingerprints;
- one operation `cloneLeafCellWithTypedContentFromInput`;
- input-relative paths to the existing cell-bag parent and leaf-cell shell
  template;
- K-declared new cell name; and
- one complete typed, ground initializer term with an exact official
  production key and sort.

For this packet the initializer is exactly the official nullary `.List`
application of sort `List`. It is not a token. The accepted two-cell input has
parent path `[2]` and state-shell template path `[2,1]`; after append, the
canonical nesting is `#cells(#cells(KCELL, STATECELL), TRACECELL)`. These are
acceptance observations, not Java constants: K must derive and return the
paths and initializer from the projected structure and descriptors.

One canonical top-level result is accepted. Reject residual/multiple output,
unknown constructors, noncanonical integers/strings, unsupported paths,
unresolved or ambiguous productions/sorts, non-nullary or sort-invalid
initializers, variables, and malformed operation envelopes.

## Ownership split

K owns:

- structural two-cell target selection;
- apply/already-present/conflict and candidate cardinality;
- target and stale preconditions;
- parent/template paths and new cell name; and
- the exact nullary List production/sort descriptor and complete initializer.

Java may project and parse the contract, resolve exact official
production/sort descriptors, navigate declared paths, clone only the declared
four-argument `#configCell` shell/properties/name-token metadata, replace the
start/end names, install the resolved typed initializer, immutably rebuild
ancestors/configuration/module/definition, and validate the exact delta.

Java may not search for `T`, `k`, `state`, `trace`, `.List`, `List`, P3 module
or rule labels, choose the target/path/template/name/initializer, or contain a
fixture-specific initializer exception. Generic validation may require a
four-argument official configuration-cell shell with equal start/end names,
one uniquely resolved ground nullary initializer, a cell-bag parent, and no
same-name sibling. Official cell checks/CF remain final authorities for the
new cell declaration.

## Positive, idempotence, composition, and runtime oracles

1. Compile the two-cell fixture through an identity pre-CF hook as the no-trace
   baseline.
2. At the real pre-CF hook, invoke the new contract, require one `apply`,
   validate all preconditions/descriptors/paths, and apply one immutable shell
   clone with typed content.
3. Preserve definition/module/import/sentence/configuration cardinality,
   configuration identity/provenance/conditions/attributes, and every original
   body node outside rebuilt ancestors. Require one changed configuration and
   one new official `Definition` reference.
4. Reproject before leaving the hook. Require one `already-present`, independent
   validation of exactly one equal trace cell, zero further applications, and
   the same augmented definition reference.
5. Let unchanged official checks/CF create the trace cell productions.
6. At post-CF, run unchanged `KRuleAppliedTrace-v1`: require `apply`, one rule
   edit, then independently validated `already-present` with no second edit.
7. Continue through unchanged official lowering and the Haskell backend.

For `start`, require `<k> 1`, `<state> 2`, and exactly the accepted one
`RuleApplied` event with exact selected-rule lineage/label/module/source/location.
For the non-firing integer, require `<k> 1`, `<state> 1`, and an empty trace.
Erasing trace state must equal both the two-cell no-trace baseline and accepted
P3 program state.

Compile an independent ordinary-source oracle that contains both
`<trace> .List </trace>` and the exact source-authored event update. Require
both full runtimes to equal it. Compare focused official trace-cell generation
against an ordinary-source trace-configuration oracle and classify only the
expected trace-shell source/location provenance difference. Syntax Kore and
macros must be byte-stable across fresh K-authored repeats. Their portable
semantic projections must equal the ordinary-source trace fixture after
erasing only that classified trace-shell source/location difference.

Repeat from fresh output. Require stable portable request/result/operation
fingerprints for both contracts, focused configuration/rule projections,
normalized full Kore, syntax Kore, macros, event payload, and both runtimes.

## Checkout-stable evidence

Raw execution must retain and validate the exact absolute run-local official
source and every source-derived lineage for both configuration and rule
contracts. Only after raw validation, committed evidence uses explicit
repository-logical source identities and structurally rederives every dependent
lineage, typed metadata hash, definition/request/result/operation descriptor,
ordinary-source oracle, and event payload. Do not relabel opaque raw digests.

Sort projected collections by portable identity before hashing. Structural
typed translation, unique descriptor mapping, collision/residual checks, and
the broadened Java semantic-literal scans from R3-G-01A remain mandatory.
Root will independently replay acceptance from a second workspace-aligned
detached worktree before integration.

## Required failures

New pre-CF failures cover:

- stale definition or target content/provenance;
- zero and duplicate structural target cardinality;
- unsupported/out-of-bounds parent or template path;
- malformed/non-leaf shell template;
- missing or ambiguous initializer production/sort metadata;
- unknown, non-nullary, variable-bearing, or sort-invalid initializer;
- a same-name cell with conflicting content/shape; and
- false `already-present` on the two-cell input.

Every pre-CF failure performs zero configuration applications, returns no
transformed definition, invokes the post-CF adapter zero times, and emits no
known backend artifacts. Exact-result malformed/noncanonical cases fail at the
envelope.

After successful pre-CF composition, retain the accepted R3-G-01A post-CF
negative modes and classifications unchanged. They must see one successful
configuration application/idempotence validation but zero rule applications
and no backend artifacts. Do not add new post-CF semantics merely to restate
those tests.

## Evidence and ownership

Generate compact checkout-stable `results.json` and `report.md` under
`evidence/r3-g-02-k-authored-trace-configuration/`, recording:

- pins, source hashes, raw/portable invariant, and actual full-cycle count;
- both contracts' pass-1/pass-2 request/result/status/candidate/application and
  idempotence records;
- declared operation, paths, exact initializer descriptor, configuration/rule
  deltas, and provenance/condition/attribute preservation;
- firing/non-firing/full/erased/ordinary-source/repeat oracles;
- every pre- and post-CF negative classification and artifact absence; and
- limitations, ambiguity, and the recommended first matcher packet.

The worker may modify only:

- `spine/trace-configuration-composition/**`;
- `evidence/r3-g-02-k-authored-trace-configuration/**`; and
- one new `r3:g:trace-configuration` script entry in `package.json`.

All accepted spines/evidence, tasks, roadmaps/checkpoints/loop/goal/ADR files,
P1/P2/P3 fixtures, lockfiles, and external K are read-only. Raw output belongs
under the ignored new spine build tree.

## Acceptance

From a clean worker checkout with no pre-existing task build output:

```sh
bun run r3:g:trace-configuration
bun run check
git diff --check
```

Replay must fail closed on every pinned hash/source/tool mismatch and regenerate
and byte-compare both evidence files. Root repeats all three commands from a
fresh workspace-aligned detached worktree at a different absolute path.

## Stop/split rule

Stop with replayable evidence instead of expanding if acceptance requires:

- changing either accepted hook/adapter boundary, accepted spine, or
  `KRuleAppliedTrace-v1`;
- a second new K-facing contract or host/plugin boundary;
- source/KAST JSON round-trip or external-K modification;
- more than one configuration edit or operation;
- general non-nullary initializer synthesis or configuration patch algebra;
- fixture/event/list/target/path selection in Java;
- moving event syntax into K, another rule/event, domain events, matching,
  monitors, symbolic execution, corpus aggregation, general `SemanticInput`,
  or C1/C2; or
- inability to resolve the official nullary List production uniquely pre-CF,
  or more than three substantive full-oracle cycles.

Return one clean worker commit with task-owned changes only. State commit,
verdict, cycle count, both contracts and their K/Java ownership, exact
initializer/event payload, idempotence, runtime/erasure/source/repeat oracles,
failures, portability proof, limitations, ambiguity, and the recommended first
trace matcher packet.
