# R2-G-06: K-authored idempotent configuration augmentation

Status: accepted and integrated as `985d8fa` on 19 August 2026. Activation
commit `21be439` was the worker's exact starting revision.

## Objective

Use K to structurally select P3's typed pre-CF configuration and author exactly
one canonical augmentation that adds the inert branch-local
`<observation> 0 </observation>` leaf proven by R2-G-05. Apply it through
`OfficialConfigurationTransformHook-v0`, then let official cell checks and
CF-01 through CF-03 generation, the accepted post-CF adapter, official lowering,
and the Haskell backend consume the result.

Prove exact selection, stale-safe validation, deterministic application, and
idempotence. This packet adds configuration state only. It does not instrument
a rule, define/emit an event, append a trace, advance a monitor, implement a
matcher, or introduce general configuration patch algebra.

## Starting inputs

- the activation commit containing this packet, descended from integrated
  R2-G-05 commit `a720a4e`;
- accepted `OfficialConfigurationTransformHook-v0` source-bound overlay and
  evidence under `investigations/r2-g-05-pre-cf-hook-prototype/**`;
- `KDefinitionTransport-v1` identity/provenance principles, but not its schema;
- `draft/decisions/official-definition-adapter-v1.md` and the execution-pattern
  instrumentation contract;
- P3's typed nested configuration and ordinary program;
- the accepted R2-G-05 typed Java augmentation and ordinary-source fallback as
  independent structural/runtime oracles; and
- K v7.1.337 at
  `4a46d1231473b599c699160132fd6e76a5c46406`, using the pinned Haskell-backend
  profile.

Record the exact activation revision and all K/source/overlay pins and hashes.
The external K checkout/install remain read-only.

## Sole new contract: `KConfigurationAugmentation-v1`

The contract contains both the K request vocabulary and its one exact result
envelope. It is independent of `KDefinitionTransport-v1` and both definition
patch schemas; do not revise those accepted contracts.

The host request projects the official pre-CF `Definition` at the hook as:

- schema ID and whole-definition content fingerprint;
- modules in canonical name order;
- every official `Configuration` sentence with module, kind, source/location,
  stable lineage, content/body/`ensures`/attribute fingerprints; and
- its complete typed K body using explicit application, rewrite, sequence,
  token, variable, alias, and injected-label constructors, including node
  metadata fingerprints needed for validation.

Unordered official collections require declared canonical ordering. Application
arguments and sequences remain ordered. The request need not transport
non-configuration bubbles or make them transformable, but the host's definition
fingerprint and validation retain them.

The one result envelope contains:

- schema `KConfigurationAugmentation-v1`;
- transformation `p3-add-observation-cell@1`;
- expected whole-definition fingerprint;
- exact candidate cardinality;
- status `apply` or `already-present`;
- target configuration lineage, content, and body fingerprints;
- one operation kind `cloneLeafCellFromInput`;
- input-relative typed path to the existing cell-bag parent;
- input-relative typed path to the existing leaf-cell template;
- new cell name `observation` and new leaf token value `0`; and
- one complete canonical result fingerprint computed by the host from parsed
  constructors/fields, independent of pretty whitespace.

Paths use only the minimum ordered application-argument vocabulary required by
the fixture. Indices are zero-based. K emits canonical fields and one exact
top-level typed result; the host rejects residual/multiple results and never
silently reorders or repairs K output.

## Ownership split

K must:

- structurally recognize the nested P3 configuration from transported terms;
- distinguish an unaugmented target, the exact already-present observation
  leaf, and a conflicting observation-named leaf;
- choose the target lineage/preconditions, parent/template paths, cell name,
  token value, status, and candidate cardinality; and
- emit a stable canonical result.

Java may generically encode official configuration values, invoke/parse K,
validate fingerprints/cardinality/status/paths, navigate ordered K terms, clone
the declared input leaf, replace only the declared name/value tokens while
preserving their official sorts/attributes and all other template nodes, append
under the declared cell-bag parent, rebuild immutable ancestors, and validate
the output graph. Java may not search for P3's `<T>`, `<k>`, `<state>`, or
`<observation>` structure, choose the template/parent, or supply the new name or
value independently of K's result.

Generic host validation may require that a clone source is an official parsed
four-argument `#configCell`, its start/end names agree, its contents are one
typed token, the parent is the official cell-bag constructor, and the proposed
new name is absent. These are operation semantics, not P3 selection.

## Positive application

At the pre-CF hook:

1. Project the complete configuration slice and invoke K.
2. Require one `apply` result and exact candidate cardinality one.
3. Validate definition/target lineage, content, body, side-condition, attribute,
   and path preconditions against the same original official definition.
4. Resolve both parent and template before constructing output.
5. Apply exactly one immutable `cloneLeafCellFromInput`; preserve definition,
   module, import, other-sentence, configuration `ensures`/attributes/provenance,
   and every original body node/metadata outside rebuilt ancestors.
6. Require one changed configuration, one application, a new official
   `Definition` reference, unchanged module/sentence/configuration cardinality,
   and changed definition/target content/body fingerprints.
7. Reproject that returned pre-CF definition and invoke K a second time. Require
   status `already-present`, the exact same target lineage, candidate
   cardinality one, zero applications, and return the same augmented official
   definition reference without reconstructing it.
8. Only then return from the hook to official cell checks/generation.

Continue through unchanged `OfficialDefinitionAdapter v1`, official lowering,
Haskell compilation, and ordinary P3 execution. Require `<observation> 0`, and
baseline-equal `<k>`/`<state>` after erasure.

Run a fresh complete repeat. Require stable request/result canonical
fingerprints, focused generated-observation projection, normalized definition
Kore, syntax Kore, macros, and runtime. The focused configuration-generation
markers must equal both the R2-G-05 typed Java oracle and ordinary-source
fallback; classify expected provenance differences.

## Required negatives

Use K-authored modes or task-owned typed input mutations as appropriate. Every
failure occurs before returning a transformed definition from the hook, invokes
the post-CF adapter zero times, and emits no backend Kore/compiled artifacts:

- stale target content fingerprint;
- zero or duplicate structural target cardinality;
- unsupported/out-of-bounds template or parent path;
- an existing observation-named leaf whose shape/value conflicts with the exact
  augmentation (must reject, not report `already-present`); and
- a result claiming `already-present` on the unaugmented input.

Record the closest boundary and distinguish K selection failure, result-envelope
validation, stale precondition, path/operation validation, and conflicting
existing state. Application count remains zero in every negative.

## Idempotence and validation records

The task record must include request/response fingerprints for both passes,
candidate counts/statuses, target fingerprints, canonical operation/paths,
validated/application/changed-configuration counts, same-reference flags,
before/after definition and target fingerprints, metadata/provenance/condition
preservation, callback/post-CF invocation counts, CF/backend construction flags,
and negative classifications.

`already-present` is valid only when K structurally recognizes exactly one leaf
equal to the declared canonical augmentation and the host independently
validates it at the declared parent. A same-name conflict is an error.

## Owned paths

The worker may create or modify only:

- `spine/configuration-augmentation/**`;
- `evidence/r2-g-06-k-configuration-augmentation/**`; and
- the single `r2:g:configuration` script entry in `package.json`.

The worker may read but not modify the R2-G-05 overlay/oracles, accepted
definition spine/evidence, task packets, roadmaps/checkpoints/loop, goal/ADR
documents, official K source/install, P1/P2/P3/W1 fixtures, or other package
entries. Raw compiler outputs belong under the ignored new spine build tree.

## Required outputs and acceptance

Produce K semantics, a trusted-small Java hook adapter, exact-result parser,
deterministic replay, compact `report.md`, and source-bound `results.json`.
Add and pass:

```sh
bun run r2:g:configuration
bun run check
git diff --check
```

The task command must start without pre-existing output and fail closed on a
wrong K/source/overlay pin, missing tools, contract/oracle mismatch, or external
source mutation beyond the recorded pre-existing status.

## Stop/split rule

Stop with replayable evidence instead of expanding if acceptance requires:

- changing `OfficialConfigurationTransformHook-v0`, its upstream patch, the
  accepted post-CF adapter, or accepted definition transport/patch schemas;
- modifying/rebuilding the external K checkout/install;
- a second shared contract or a general synthetic K-term/configuration patch
  vocabulary;
- Java selection of fixture structure, paths, new name, or initializer;
- more than one configuration edit/application or more than the exact clone
  operation;
- source/KAST JSON round-tripping;
- event constructors, rule instrumentation, traces, monitors, matchers,
  symbolic execution, C1/C2, parsing, lowering, or Kore-emission ownership; or
- more than three substantive full-oracle cycles.

Return one clean worker commit containing task-owned changes only. State the
commit, verdict, full-cycle count, contract, tests, K/Java ownership split,
positive/idempotence/negative results, limitations, packet ambiguity, and the
recommended next conservative rule-observation packet.
