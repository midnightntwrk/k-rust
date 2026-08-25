# R2-G-02: canonical single-sentence input-relative patch

Status: accepted and integrated as `c1605d2` on 19 August 2026. Activation
revision: `0722781087985b88bec35bd1698d292b00db4501`.

## Objective

Introduce exactly one shared contract, `KDefinitionPatch-v1`, and use it to
have K propose the already-established P3 `start-program` edit as a canonical
single-sentence patch. A trusted-small Java applier must validate the complete
patch against the original in-memory official `Definition`, apply it without
JSON or K-source round-tripping, and return a new official definition through
`OfficialDefinitionAdapter v1` before official lowering.

This packet proves patch proposal, validation, application, provenance, and
backend consumption for one supported edit. It does not define the full patch
algebra, synthetic replacement terms, multi-edit transactions, general
`SemanticInput`, observation instrumentation, or independent compilation.

## Starting inputs

- the activation commit containing this packet, descended from `085b86b`;
- `tasks/wave-2/R2-G-01-k-definition-transport.md`;
- `draft/decisions/official-definition-adapter-v1.md`;
- `draft/k-in-k-delivery-loop-2026-08-19.md`;
- `spine/definition-transport/**` and accepted R2-G-01 evidence;
- W1-D's `p3-start-to-bump` implementation, replay, focused Kore normalizer,
  and edit record under `investigations/w1-inprocess-adapter/`; and
- K v7.1.337 at
  `4a46d1231473b599c699160132fd6e76a5c46406`, using the pinned Haskell-backend
  profile.

Record the exact activation revision in the task-specific result manifest.

## Contract fixed by this packet

`KDefinitionPatch-v1` is a typed K result contract layered on, but not folded
into, `KDefinitionTransport-v1`. Its supported positive value contains:

- schema ID `KDefinitionPatch-v1`;
- transformation ID and version `p3-start-to-bump@1`;
- expected input-definition fingerprint;
- exactly one target lineage;
- expected target content and body fingerprints;
- exactly one `replaceTermFromInput` edit;
- a typed target path relative to the selected rule body;
- a typed replacement-source path relative to that same unmodified body; and
- deterministic edit/patch cardinality.

Use typed path-step constructors, not slash-delimited strings. The minimum
path vocabulary needed by P3 is:

- rewrite left/right; and
- application argument by non-negative index.

The positive K patch replaces the `add(read(), bump())` term at the rewrite
right path with the existing `bump` subterm at rewrite-right/application-arg
1. K must discover that structure and construct both paths. The host may
implement the generic meaning of typed path navigation and immutable
replacement, but it may not rediscover `add(read(), bump())`, choose `bump`,
or encode this operator as a Java label-specific transformation.

The replacement source is resolved from the original official object before
application. Reusing that original K node preserves its official attributes
and typed `Production` metadata. Ancestor nodes must be rebuilt through
official K constructors while preserving their original attributes. This
packet deliberately does not decode synthetic `DTerm` values back into
official terms; that would require another explicitly designed contract.

The host computes the canonical patch fingerprint from the parsed typed fields
and constructors, independent of pretty-output whitespace. It must validate
one exact top-level typed result and reject residual or multiple results.

## Required behavior

1. Preserve every R2-G-01 identity and rejection behavior.
2. Project the supported source rules from the lossless in-memory official
   definition through `KDefinitionTransport-v1`.
3. Invoke K to structurally select the P3 `start-program` rule and produce the
   one `KDefinitionPatch-v1` edit described above.
4. Parse one exact typed patch result; do not accept arbitrary residual K
   configurations or use regex matches as a substitute for validating the
   whole result shape.
5. Before constructing any output definition, validate schema,
   transformation ID/version, definition fingerprint, edit count, target
   lineage/content/body fingerprints, both paths, indices, and supported path
   steps.
6. Resolve both paths against the same original rule body. Apply the validated
   edit immutably and replace exactly one official `Rule` while preserving its
   `requires`, `ensures`, sentence attributes, label, source, and location.
7. Validate after application that:
   - exactly one source-sentence lineage changed content;
   - target lineage, sentence attributes, `requires`, and `ensures` stayed
     equal;
   - target content/body and definition fingerprints changed;
   - the output is a different official `Definition` reference; and
   - module and local-sentence counts did not change.
8. Continue through official `KoreBackend.steps()`, Kore emission, Haskell
   compilation, and P3 execution.
9. Emit a structured record containing the typed patch, canonical patch
   fingerprint, before/after fingerprints, validation boundary, target and
   replacement paths, changed-lineage count, and application count.
10. Reject stale target content and an unsupported path step at
    `post-k-patch-pre-apply`, before creating an output definition or emitting
    backend artifacts.

Validation may be stricter than the minimum above. Failure classification must
remain deterministic and visible in the record.

## Required oracle cases

### Accumulated identity regression

The acceptance command must exercise Peano and P3 identity through the current
transport implementation, including K selection, official lowering, normalized
Kore equality, and runtime equality. It may embed R2-G-01's checks in the new
replay rather than invoking its fixed default output path.

### Positive P3 patch

Compile and execute:

- an official P3 baseline;
- the new K-proposed/applied patch; and
- a freshly generated W1-D `p3-start-to-bump` in-process reference edit.

Require:

- the new runtime output is byte-identical to the W1-D reference edit;
- P3 finishes with `<k>` value `0` and `<state>` value `2`;
- syntax Kore and macros remain byte-identical to the official baseline;
- the focused normalized `start-program` Kore projection equals the W1-D
  in-process reference projection;
- the focused projection differs from baseline and contains `Lblbump` but no
  `Lbladd`, `Lblread`, or now-unneeded `#Configuration` binder; and
- the structured record satisfies every provenance/application invariant in
  the required behavior section.

W1-D is an oracle only. Production code must not call its mutation function or
copy its Java label-specific transformer into the host applier.

### Negative patches

Use K-authored negative result modes or fixtures to exercise:

- an otherwise well-shaped patch with a stale target content fingerprint; and
- an otherwise well-shaped patch containing a recognized transport value for
  an unsupported path step.

Both must be rejected at `post-k-patch-pre-apply`, record zero applications,
and produce none of `definition.kore`, `syntaxDefinition.kore`, `macros.kore`,
`backend.txt`, `compiled.bin`, or `haskellDefinition.bin`.

Do not add a multi-edit or overlapping-edit case to this packet; those belong
to the later atomic transaction contract.

## Owned paths

The worker may create or modify only:

- `spine/definition-transport/**`;
- `evidence/r2-g-02-single-sentence-patch/**`; and
- the single `r2:g:patch` script entry in `package.json`.

The existing ignore for `spine/definition-transport/build/` covers all raw
compiler output. Do not commit generated compiler directories, caches,
binaries, full Kore/KAST dumps, scanners, or verbose logs.

The worker may inspect but not modify task packets, roadmaps, loop/checkpoint
records, goals, existing R2-G-01 evidence, investigations, fixtures, official
K, unrelated package entries, or other repository paths. If a required change
falls outside owned paths, report it to the root instead of applying it.

## Required outputs

- production K semantics and Java adapter/applier changes under the owned
  spine;
- one deterministic replay invoked by the package entry below;
- compact `report.md` and source-bound `results.json` under
  `evidence/r2-g-02-single-sentence-patch/`;
- exact activation revision, K pin, schema ID, source hashes, oracle outcomes,
  negative classifications, and remaining limitations in the manifest; and
- one worker commit containing only task-owned changes.

The worker return must report its commit, acceptance result, oracle-cycle
count, any packet ambiguity, new shared contract, and recommended next leaf.

## Acceptance command

The worker must add and pass this exact checked-in command from a clean
activation worktree:

```sh
bun run r2:g:patch
```

The command must build the transport/patch semantics and Java driver, run all
cases above, compare the oracles, reject the two invalid patches, and emit a
compact machine-readable manifest. It must fail closed on missing tools,
wrong K revision/version, pre-existing output, or any oracle mismatch.

Also run:

```sh
bun run check
git diff --check
```

## Stop/split rule

Stop, preserve evidence, and return `split-required` or a classified blocker
if acceptance requires:

- a second new shared contract beyond `KDefinitionPatch-v1`;
- synthetic typed-term reconstruction or parsing official attributes from
  strings;
- more than one edit, multi-sentence atomicity, overlap semantics, insertion,
  deletion, condition edits, or attribute edits;
- Java code that structurally recognizes the P3 labels to decide the mutation;
- broadening `KDefinitionTransport-v1` beyond the Peano/P3 supported subset;
- source/KAST JSON round-tripping or official emitted `parsed.json` as input;
- modifying official K, fixtures, goals, roadmaps, or investigations;
- pre-CF configuration augmentation; or
- independent lowering, Kore emission, C1, or C2 work.

After three substantive full-oracle cycles without acceptance, stop and return
the smallest reproducible failure rather than beginning a fourth cycle.

## Integration result

The Sol worker returned `afb9a0f018585e1416659def3f48b903ba5c07ba`
after three complete passing oracle cycles. The root reviewed the complete
task-owned diff, verified the K/host responsibility split and source hashes,
and independently reran `bun run r2:g:patch` plus `bun run check` before
integrating the worker commit as `c1605d2`.

Accepted evidence is under
`evidence/r2-g-02-single-sentence-patch/`. The only interpretation choice was
zero-based application-argument indices. No stop condition, scope expansion,
or second shared contract was required.
