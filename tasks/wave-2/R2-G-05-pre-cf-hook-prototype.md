# R2-G-05: executable pre-CF configuration-hook prototype

Status: accepted and integrated as `a720a4e` on 19 August 2026. Activation
commit `d16e1ae` was the worker's exact starting revision.

## Objective

Prototype exactly one upstream-shaped configuration transformation hook in the
pinned official frontend and demonstrate that it can be paired with
`OfficialDefinitionAdapter v1` in one compiler lifecycle. The hook receives an
official typed `Definition` after all configuration bubbles have become
`Configuration` sentences and before cell checks and
`GenerateSentencesFromConfigDecl.gen`. It returns the definition consumed by
those official stages.

Prove identity and one task-specific inert `<observation>` cell augmentation.
The prototype must be a source-bound patch compiled as a temporary classpath
overlay; it must not modify or rebuild the external K checkout or installed K.

This packet validates the missing host seam only. It does not transport the
configuration through K, define a K-facing configuration patch, instrument a
rule, emit an event, build a trace/monitor/matcher, or take ownership of CF-01
through CF-03.

## Starting inputs

- the activation commit containing this packet, descended from integrated
  R2-G-04 commit `39c514d`;
- `tasks/wave-2/R2-G-04-pre-cf-observation-seam.md` and its accepted evidence;
- `draft/decisions/official-definition-adapter-v1.md`;
- `investigations/w1-inprocess-adapter/**` and the accepted definition spine;
- the P3 nested configuration/program and W1 ordinary-source observation
  fallback as an independent oracle; and
- K v7.1.337 at
  `4a46d1231473b599c699160132fd6e76a5c46406`, using the pinned Haskell-backend
  profile and matching source checkout.

Record the exact activation revision, installed/source pins and hashes,
environment, upstream patch hash, overlay class hashes, and commands in compact
task evidence. Fail closed on any mismatch or dirty change to the external K
source beyond its recorded pre-existing status.

## Sole experimental contract

This packet introduces only `OfficialConfigurationTransformHook-v0`:

```text
official outer definition + config/default/MAP preparation
  -> official configuration bubble parse/disambiguation/sort inference
  -> transformConfigurations(Definition): Definition
  -> official configuration cell checks
  -> official GenerateSentencesFromConfigDecl.gen
  -> official non-configuration bubble parsing and pre-compilation checks
  -> OfficialDefinitionAdapter v1
  -> official KoreBackend.steps / emission / backend
```

The hook value contains typed `Configuration` sentences and may still contain
non-configuration `Bubble` sentences. The callback is invoked exactly once per
top-level compilation, is synchronous, and defaults to identity for every
existing entry point. It must reject a null result and transformer exception
before CF output or backend artifacts are constructed.

For this prototype, validate that the returned graph changes only
`Configuration` sentences in existing modules. Preserve definition/module
identity fields, imports, all non-configuration local sentences, configuration
count, `ensures`, attributes, source/location provenance, and untouched inner
metadata. The augmentation may change exactly one configuration body.

The whole-`Definition` shape deliberately refines R2-G-04's tentative
`UnaryOperator<Configuration>` recommendation. Module identity, configuration
cardinality, and deterministic validation require surrounding context. This is
still one callback at the same discovered midpoint, not a general pre-CF
pipeline.

## Source-bound overlay

Create a compact unified patch against the exact pinned official sources. It
may change only the minimum source files required to:

- add a backward-compatible identity-default entry point;
- thread one `Function<Definition, Definition>` (or equivalent Java functional
  type) to the typed midpoint;
- apply it immediately after `defWithParsedConfigs` is constructed and before
  `checkConfigCells`;
- reject null deterministically; and
- retain the existing post-CF `Function<Definition, Definition>` unchanged.

The replay must copy only the exact patched official source files into ignored
task build output, apply the checked patch there, compile overlay classes
against installed development jars, and place those classes before official
jars in the probe driver's classpath. Verify by bytecode/signature inspection
that identity-default and two-pipeline entry points exist and that the callback
precedes cell checks/generation.

Do not edit the external checkout, the Nix store, installed jars, or official
source files in place. Do not commit copied official source. The patch is an
upstream proposal/prototype, not an accepted public K API or a production pin.

## Required positive modes

Use a task-owned in-process Java driver that reuses the pinned compiler
lifecycle and Haskell backend.

### Identity

- Invoke the old/default entry point and the explicit identity hook on fresh P3
  outputs.
- Record one hook invocation and require the callback input/output to be the
  same official `Definition` reference.
- Cross an identity `OfficialDefinitionAdapter v1` after configuration
  generation in the same invocation.
- Compare focused normalized definition Kore, syntax Kore, macros, compiled
  runtime, module/sentence counts, and representative provenance against a
  fresh unpatched official baseline.
- Require the old/default and explicit-identity paths to agree.

### Inert typed augmentation

- At the hook, find exactly one P3 `Configuration` by module and stable
  source/location provenance and reject any cardinality mismatch.
- Construct one task-specific typed `<observation> 0 </observation>` leaf in
  the existing generated-top configuration body without parsing or regenerating
  source. Reuse/copy the official typed metadata needed by the surrounding
  configuration constructors; preserve the original configuration's
  `ensures`, attributes, source/location, and every existing cell subtree.
- Return a new official definition graph and validate the one-configuration
  structural delta before official cell checks run.
- Let official `checkConfigCells` and `GenerateSentencesFromConfigDecl.gen`
  generate the observation cell sort, production, initializer, and rules.
- Cross the post-CF adapter and validate that the original `Configuration` is
  gone, official observation sentences exist, and existing sentence provenance
  remains.
- Compile/execute the ordinary P3 program. Require an observation value of `0`
  and exact baseline `<k>`/`<state>` after erasure.
- Compare a focused normalized observation configuration/generation projection
  with the existing ordinary-source fallback. Classify any permitted source or
  location difference explicitly; do not demand unrelated whole-Kore equality.
- Repeat from a fresh output and require stable normalized artifacts and
  runtime.

The Java augmentation is a seam oracle, not the product transformation. It may
be fixture-specific and may construct this one inert typed cell. Do not expose
it as a shared patch operation.

## Required negatives

Run all negatives through fresh outputs and require no backend Kore or compiled
artifacts:

- a hook returning null rejects at `post-config-parse-pre-cell-check`;
- a hook throwing a sentinel exception rejects at that same boundary;
- a hook returning an unauthorized non-configuration sentence change is
  rejected by task validation before cell checks; and
- a hook producing a duplicate `<k>` cell reaches the official transformed
  input cell check and is rejected before generation/backend output.

Records must distinguish callback invocation, task validation, official cell
validation, post-CF adapter invocation, CF output construction, and backend
artifact construction. No rollback implementation is needed because the
official input is immutable and failures occur before output publication.

## Required outputs

Under `investigations/r2-g-05-pre-cf-hook-prototype/`, produce:

- the exact upstream patch and source/hash manifest;
- task-owned driver, augmentation/validation helpers, replay, fixtures or
  projections, and negative probes;
- `report.md` and `results.json` binding claims to source, overlay, artifacts,
  runtime, and one full-cycle count; and
- one deterministic `verify.sh` or equivalent entry point.

Raw copied/patched source, classes, compiler outputs, and logs belong only in
the ignored task `build/` directory. Checked evidence must be compact. Do not
commit official source copies or large compiler artifacts.

## Owned paths

The worker may create or modify only:

- `investigations/r2-g-05-pre-cf-hook-prototype/**`; and
- the single `r2:g:pre-cf-hook` script entry in `package.json`.

The worker may inspect but not modify task packets, roadmap/checkpoints/loop,
accepted evidence/spine, P1/P2/P3 or W1 fixtures, the external K checkout, the
installed K distribution, or other package entries.

## Acceptance command

Add and pass:

```sh
bun run r2:g:pre-cf-hook
```

It must fail closed on a wrong pin/source/patch, dirty unexpected K source,
pre-existing output, overlay not taking precedence, missing negative, or any
oracle mismatch. Also run:

```sh
bun run check
git diff --check
```

## Stop/split rule

Stop with preserved evidence rather than expanding if acceptance requires:

- editing/rebuilding the external K checkout/install instead of a temporary
  exact-source overlay;
- patching more than the minimum frontend plumbing needed for the one hook;
- reimplementing or changing configuration parsing, cell checks, or
  `GenerateSentencesFromConfigDecl` semantics;
- a second new shared contract, K-facing configuration patch, general
  synthetic-term transport, event/rule instrumentation, trace, matcher, or
  symbolic runner;
- source/KAST JSON round-tripping claimed as the typed transformation;
- modifying the accepted post-CF adapter or definition patch spine;
- taking ownership of CF-01 through CF-03, C1, C2, parsing, lowering, or Kore
  emission; or
- more than three substantive full-oracle cycles.

Return one clean worker commit containing task-owned changes only. State the
commit, verdict, full-cycle count, tests, exact upstream patch surface, hook
contract, positive/negative outcomes, limitations, packet ambiguity, and the
recommended next K-authored configuration-augmentation packet.
