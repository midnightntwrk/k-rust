# R2-G-04: pre-CF observation/configuration seam investigation

Status: accepted and integrated as `39c514d` on 19 August 2026. Activation
commit `f4dcd7e` was the worker's exact starting revision.

## Objective

Classify whether pinned official K exposes a narrow, composable typed seam
after a configuration bubble has become an official `Configuration` value and
before `GenerateSentencesFromConfigDecl.gen` expands it into CF-01 through
CF-03 sentences. Determine whether that seam can be paired with
`OfficialDefinitionAdapter v1` for a future K-authored observation-cell
augmentation, or whether the next packet instead needs a minimal upstream hook
or an explicit observation-state redesign.

This is an executable boundary investigation. It does not implement general
observation events, rule instrumentation, traces, matchers, synthetic
configuration patches, `SemanticInput v1`, or independent configuration
generation.

## Starting inputs

- the activation commit containing this packet, descended from integrated
  R2-G-03 commit `daca204`;
- `draft/decisions/official-definition-adapter-v1.md`;
- `draft/goal/execution-pattern-matching.md`, especially its branch-local
  instrumentation contract;
- `investigations/w1-egress/**` and
  `investigations/w1-inprocess-adapter/**`;
- accepted R2-G-01 through R2-G-03 packets and evidence;
- P3's nested `<k>` / `<state>` configuration and ordinary program; and
- K v7.1.337 at
  `4a46d1231473b599c699160132fd6e76a5c46406`, using the pinned Haskell-backend
  profile and matching source tree under
  `../inspirations/runtimeverification/k` relative to the workspace family.

Record the exact activation revision, resolved installed tool paths, K source
revision, relevant official source hashes, environment envelope, and every
command in task-specific evidence. Fail closed if the installed pin and source
revision do not match.

## No new production contract

This packet may define a task-local result/evidence schema only. It must not
change `OfficialDefinitionAdapter v1`, `KDefinitionTransport-v1`, either patch
schema, or introduce a configuration/observation patch schema.

A candidate counts as a **narrow typed seam** only if all of these hold:

1. It exposes official typed `Configuration` body, `ensures`, attributes,
   source/location provenance, and the inner production/sort metadata needed
   by official generation.
2. A small total transformation function can return an identity or augmented
   typed value before official `GenerateSentencesFromConfigDecl.gen` runs.
3. The same invocation then completes official remaining bubble resolution,
   checks, the accepted post-CF adapter position, `KoreBackend.steps()`, Kore
   emission, Haskell compilation, and execution.
4. It uses the installed pinned artifacts without modifying/rebuilding
   official K, K source regeneration, emitted KAST JSON, source-text
   round-tripping, reflective access to private members, or a project copy of
   `DefinitionParsing`'s private configuration parsing/generation pipeline.
5. Its lifecycle and injection route are explicit enough to replay after a K
   upgrade. A source-code location alone is not a composable seam.

Protected subclassing or a narrow dependency-injection override is admissible
only when it reaches the typed pre-generation value without reproducing the
private algorithm. One-off reflection may be used to inspect a value for
diagnosis, but a reflection-dependent route must be classified unusable.

## Required investigation

### 1. Pin-local lifecycle map

Bind source observations to exact files, symbols, visibility, and source
hashes for at least:

- `DefinitionParsing.parseDefinitionAndResolveBubbles`;
- both relevant `resolveConfigBubbles` overloads;
- the conversion from `Bubble` to `Configuration`;
- `GenerateSentencesFromConfigDecl.gen`;
- `Kompile.run`'s accepted transformation function; and
- the Guice/provider construction path for `DefinitionParsing`.

Record a concise call/visibility map showing where an external composition
function can and cannot run. Verify conclusions against the installed
development jars with a compile/link or bytecode-signature probe; reading the
checkout alone is insufficient.

### 2. Candidate matrix

Evaluate at least these routes against every narrow-seam criterion:

- the existing public `Kompile.run(... Function<Definition, Definition> ...)`
  transformation;
- public/protected `DefinitionParsing` entry points and subclassing;
- a narrow Guice/provider override using installed artifacts;
- direct public use of `GenerateSentencesFromConfigDecl.gen`;
- post-CF construction through `OfficialDefinitionAdapter v1`; and
- ordinary-source regeneration as the already demonstrated fallback.

For each route record: observed value before/after CF generation, lifecycle
entry, metadata retained, identity capability, augmentation capability,
compatibility with the post-CF adapter, forbidden mechanism required, verdict,
and the smallest missing API if rejected. Do not label source fallback or a
post-CF generated-sentence reconstruction as typed pre-CF success.

### 3. Executable probes

Build the smallest installed-artifact Java probe needed to test the strongest
non-forbidden candidate. It must have an identity mode and an augmentation
mode or return a replayable compile/link/lifecycle blocker before claiming the
candidate is unavailable.

If a narrow typed seam is available:

- observe exactly one P3 `Configuration` before generation;
- in identity mode return the same typed value and compare focused definition
  Kore, syntax Kore, macros, and ordinary runtime with a fresh official
  baseline;
- in augmentation mode add one inert branch-local `<observation>` leaf with a
  deterministic initializer at the typed configuration value, leaving
  `<k>`/`<state>` behavior unchanged;
- let official generation create its cell sorts, productions, initializer,
  and rules, then cross the accepted post-CF adapter position and backend;
- show the observation cell in structured generated-definition/Kore evidence,
  run the ordinary P3 program, and compare the erased terminal `<k>`/`<state>`
  projection with baseline; and
- repeat augmentation from a fresh output and require stable normalized
  artifacts.

The inert cell is a seam oracle only. Do not instrument a semantic rule or
introduce an event vocabulary.

If no narrow typed seam is available:

- preserve the strongest candidate's exact failure (compile/link error,
  inaccessible typed midpoint, DI/lifecycle incompatibility, or forced private
  pipeline copy);
- still replay the accepted post-CF identity path and the existing ordinary
  source observation fallback so the negative result is localized to the
  pre-CF composition point; and
- specify the smallest hook signature and placement that would make the probe
  possible, including its input/output value, validation/error behavior, and
  composition order relative to default configuration insertion, cell checks,
  official generation, non-configuration parsing, and the accepted post-CF
  adapter.

### 4. Required classification

End with exactly one primary classification:

- `narrow-typed-seam-available` — all criteria and positive probes pass;
- `pin-private-seam-needs-hook` — the typed midpoint exists but the installed
  pin cannot compose there without a forbidden mechanism; or
- `observation-design-change-required` — even a minimal hook at that midpoint
  would not support conservative branch-local augmentation, with an executable
  reason rather than preference.

For the second classification, distinguish a small upstream/internal hook from
taking ownership of CF-01 through CF-03. For the third, name the replacement
state architecture and the product invariants it retains or loses. Do not
select C1/C2 or broaden project scope in this packet.

## Required evidence and outputs

Under `investigations/r2-g-04-pre-cf-observation-seam/`, produce:

- `report.md` with verdict, lifecycle map, matrix, probe results, remaining
  unknowns, and one recommended next packet;
- `results.json` with the task-local schema, exact classification, pins/source
  hashes, candidate verdicts, executed probes, oracle results, and forbidden
  mechanisms avoided or encountered;
- source, scripts, fixtures, normalized projections, and compact failure
  evidence needed for deterministic replay; and
- one `verify.sh` or equivalent deterministic entry point.

Raw compiler outputs may live below the task directory's ignored `build/`
subdirectory. Checked evidence must be compact and source-bound. Do not commit
installed K artifacts, copied official source files, large compiler output, or
unrelated prior evidence.

## Owned paths

The worker may create or modify only:

- `investigations/r2-g-04-pre-cf-observation-seam/**`; and
- the single `r2:g:pre-cf-seam` script entry in `package.json`.

The worker may inspect but not modify the roadmap, delivery loop, product
checkpoint, ADRs, goal documents, task packets, accepted spine/evidence,
official K source/install, P1/P2/P3 fixtures, or other package entries.

## Acceptance command

Add and pass:

```sh
bun run r2:g:pre-cf-seam
```

The command must start from no task build output, fail closed on a wrong pin or
pre-existing output, regenerate the checked claims, and exit zero for a fully
evidenced one-of-three classification. Also run:

```sh
bun run check
git diff --check
```

A negative seam classification is an accepted investigation outcome, not a
failed acceptance command, when the exact blocker and both localization
controls are replayed.

## Stop/split rule

Stop with preserved evidence rather than expanding if acceptance would
require:

- modifying/rebuilding official K or relying on reflection in the proposed
  production route;
- copying or reimplementing private configuration parsing/generation logic;
- defining a shared configuration or observation patch contract;
- K-authored general observation transformation, synthetic term vocabulary,
  event emission, rule instrumentation, trace matching, or symbolic running;
- changes to the accepted definition-transport/patch spine;
- source/KAST JSON round-tripping claimed as the typed seam;
- taking ownership of CF-01 through CF-03, C1, C2, Kore emission, or parsing;
  or
- more than three substantive full probe cycles.

Return one clean worker commit containing task-owned changes only. The worker
return must state the commit, classification, full-probe cycle count, tests,
strongest candidate, exact blocker or positive seam, proposed minimum hook if
any, limitations, and recommended next packet.
