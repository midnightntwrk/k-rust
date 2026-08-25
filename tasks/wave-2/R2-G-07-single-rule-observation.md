# R2-G-07: conservative single-rule observation latch

Status: activated implementation packet on 19 August 2026. The activation
commit containing this file is the worker's exact starting revision.

## Objective

Compose the accepted K-authored pre-CF configuration augmentation with exactly
one K-authored post-CF rule augmentation. Structurally select P3's explicit
state-changing `bump` transition and append one generated observation-cell
fragment whose rewrite is `0 => 1`. When the original transition fires, its
semantic update and latch update must be one official rule application.

Prove conservative behavior after erasing observation state, non-firing
behavior, identity/provenance preservation, deterministic idempotence, and
fail-closed validation. This is a one-bit rule-applied observation oracle. It is
not a general event, trace, monitor, temporal matcher, or multi-rule facility.

## Starting inputs

- the activation commit containing this packet, descended from integrated
  R2-G-06 commit `985d8fa`;
- accepted `OfficialConfigurationTransformHook-v0`,
  `KConfigurationAugmentation-v1`, and `OfficialDefinitionAdapter v1`;
- R2-G-06 configuration spine/evidence and the R2-G-05 Java/source oracles;
- `draft/goal/execution-pattern-matching.md`, especially conservative
  instrumentation and branch-local state requirements;
- P3's `bump-state` rule, ordinary `start` program, and one task-owned program
  that does not fire the selected transition; and
- K v7.1.337 at
  `4a46d1231473b599c699160132fd6e76a5c46406`, using the pinned Haskell-backend
  profile.

Record the activation revision and all K/source/hook/configuration-spine hashes.
The external K checkout and installation remain read-only.

## Composition boundary

One top-level compilation must perform, in order:

```text
official configuration parsing
  -> accepted R2-G-06 K configuration augmentation at the pre-CF hook
  -> official cell checks and CF-01..03 generation
  -> KRuleObservation-v1 at OfficialDefinitionAdapter v1
  -> official KoreBackend.steps / emission / Haskell backend
```

Reuse `KConfigurationAugmentation-v1` unchanged and preserve its first-pass
`apply`, second-pass `already-present`, and validation record. The new rule
transformation runs only after official generation has made the observation
cell sort/production available and before meaning-bearing rule lowering.

The implementation may create a task-owned composition driver and reuse or
mechanically factor accepted R2-G-06 host code. Do not alter either accepted
schema or weaken its replay. If safe composition would require a second new
host/plugin contract, stop and split rather than adding it implicitly.

## Sole new contract: `KRuleObservation-v1`

The request/result contract projects the post-CF official `Definition` before
`KoreBackend.steps()`:

- schema and whole-definition fingerprint;
- canonical modules and all primary-source rules with stable lineage,
  content/body/`requires`/`ensures`/attribute fingerprints;
- complete typed rule terms using explicit application, rewrite, sequence,
  token, variable, alias, and injected-label constructors with metadata
  fingerprints; and
- canonical generated-cell descriptors sufficient to name an available cell
  production, label, body sort, and metadata without serializing official KAST
  JSON or source.

The exact result contains:

- schema `KRuleObservation-v1` and transformation
  `p3-observe-bump-state@1`;
- expected whole-definition fingerprint and exact candidate count;
- status `apply` or `already-present`;
- target rule lineage/content/body/`requires`/`ensures`/attribute fingerprints;
- one operation `appendGeneratedCellUpdate`;
- input-relative path to the declared existing cell-bag parent in the target
  rule body;
- generated cell name `observation`;
- declared before token `0` and after token `1`; and
- a host-computed canonical result fingerprint from parsed fields and
  constructors, independent of pretty whitespace.

Paths use only zero-based ordered application arguments needed by this rule.
One exact top-level typed K result is accepted; multiple/residual results,
unknown constructors, noncanonical values, and unsupported paths reject.

## Ownership split

K must structurally recognize the explicit `bump`/state-changing rule shape,
including its K/state relationship rather than a label-only match. K chooses
the target/preconditions, parent path, observation cell name, `0`/`1` values,
candidate cardinality, and apply/already/conflict status.

Java may generically project/parse/validate, navigate the declared rule path,
resolve exactly one official generated cell production/label/body sort from
the K-declared cell name, construct the declared typed cell fragment with an
official rewrite between the declared tokens, append it under the declared
cell-bag parent, immutably rebuild ancestors/rule/module/definition, and validate
the result. Java may not search for `bump`, `state`, `observation`, `0`, `1`, the
P3 module/label, or choose the target/path/update independently of K.

Generic operation validation may require an existing official cell-bag parent,
an available unique generated cell production matching the declared name, a
declared leaf body sort accepting both tokens, and absence of a same-name cell
for `apply`. It must reject unsupported/non-leaf metadata rather than synthesize
compiler behavior.

## Positive and idempotent transformation

1. Run accepted R2-G-06 pre-CF augmentation and validate its two K passes.
2. At the post-CF adapter, project the definition and invoke the new K semantics.
3. Require one `apply` candidate, validate all target and generated-cell
   preconditions against the same original post-CF definition, and resolve the
   parent/production before constructing output.
4. Apply exactly one rule edit. Preserve module/import/sentence cardinality,
   rule lineage, label, source/location, attributes (including priority),
   `requires`, `ensures`, every original body node/metadata outside rebuilt
   ancestors, and all non-target sentences/configuration-generated metadata.
5. Require a new official `Definition` reference, one application, one changed
   source rule, and changed definition/target content/body fingerprints.
6. Reproject that output and invoke K again before lowering. Require
   `already-present`, exact candidate cardinality one, independent host
   validation of exactly one equal declared cell update, zero further
   applications, and the same instrumented `Definition` reference.
7. Return it to unchanged official lowering/backend.

Run the ordinary `start` program. Require final `<observation> 1`; erase the
observation cell and require exact `<k>`/`<state>` equality with the accepted
R2-G-06 uninstrumented configuration-only runtime.

Add one task-owned P3 program that terminates without firing the selected rule
(an integer value is sufficient). Require final `<observation> 0` and erased
state equal to the same program on the R2-G-06 configuration-only definition.

Repeat from fresh output. Require stable request/result fingerprints for both
rule passes, focused normalized definition Kore, syntax Kore, macros, firing
and non-firing runtime. Syntax Kore/macros must equal the configuration-only
oracle. The target rule's official lowered identity may change because its body
changes; lineage/provenance at the adapter seam must not.

## Required negatives

All negatives return no instrumented definition from the post-CF adapter,
perform zero rule applications, skip official lowering/backend, and emit no
backend artifacts:

- stale target content fingerprint;
- zero and duplicate structural target cardinality;
- unsupported/out-of-bounds parent path;
- missing or ambiguous generated observation-cell metadata;
- a same-name target-rule cell update with a conflicting before/after value;
- a result claiming `already-present` on the uninstrumented rule; and
- an unsupported selected rule body that lacks a safe cell-bag insertion point.

Record exact failure classes: K selection, envelope, stale precondition,
generated-metadata, path/operation, conflict, or conservative-shape rejection.
The accepted pre-CF configuration stage may run internally for these cases, but
no post-CF transformed definition is returned and no backend artifact is built.

## Conservativity record

Record both configuration and rule request/response fingerprints/statuses,
hook/adapter invocation counts, rule target/operation/path, validation and
application counts, same-reference flags, before/after definition and rule
fingerprints, preserved identity/provenance/attributes/conditions, official
generated-cell metadata used, backend construction, both program runtimes, and
erasure comparisons.

This packet proves only the two exercised concrete paths. It must not claim
general branch/priority conservativity, absence, or event semantics.

## Owned paths

The worker may create or modify only:

- `spine/rule-observation/**`;
- `evidence/r2-g-07-single-rule-observation/**`; and
- the single `r2:g:observation` script entry in `package.json`.

The worker may inspect but not modify accepted configuration/definition spines
or evidence, hook patch, task/roadmap/checkpoint/loop/goal/ADR documents,
official K, P1/P2/P3/W1 fixtures, or other package entries. Raw build output
belongs below the ignored new spine build tree.

## Acceptance

Add and pass:

```sh
bun run r2:g:observation
bun run check
git diff --check
```

The task replay must start without pre-existing output, fail closed on a wrong
pin/source/hook/configuration-spine hash, and regenerate compact source-bound
`report.md` and exact `results.json` evidence.

## Stop/split rule

Stop with replayable evidence instead of expanding if acceptance requires:

- changing accepted hook/configuration/definition contracts or their spines;
- a second new shared contract or host plugin boundary;
- Java fixture selection or choice of cell/path/before/after values;
- more than one target rule/edit or a rule operation other than the exact
  generated-cell update;
- source/KAST JSON round-tripping or external K modification;
- event constructors/payload binding, trace/list state, multiple rules,
  monitors, temporal matching, symbolic exploration, C1/C2, or compiler-stage
  ownership; or
- more than three substantive full-oracle cycles.

Return one clean worker commit containing task-owned changes only. State commit,
verdict, full-cycle count, contract, K/Java ownership, composition results,
firing/non-firing/erasure/idempotence oracles, negatives, limitations, packet
ambiguity, and the recommended first trace-backed `RuleApplied` packet.
