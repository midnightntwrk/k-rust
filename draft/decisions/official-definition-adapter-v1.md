# ADR: OfficialDefinitionAdapter v1

Status: accepted for the pinned initial G1 track on 19 August 2026.

Compatibility pin: K v7.1.337 at
`4a46d1231473b599c699160132fd6e76a5c46406`, Haskell-backend profile.

This is a pin-specific internal adapter decision. It is not a claim that K
exposes a stable public extension API, and it does not freeze `SemanticInput`
or a pre-configuration transformation boundary.

## Context

G1 needs a lossless definition value that K-in-K can transform and return to
official K before meaning-bearing lowering. W1-A demonstrated that the hidden
JSON `--post-process` hook works only after all Kore frontend passes and that
emitted `parsed.json` is not a replayable compiler input. W1-D then demonstrated
an unchanged in-process composition using the official compiler lifecycle.

Accepted evidence is under:

- `investigations/w1-egress/`; and
- `investigations/w1-inprocess-adapter/`.

## Decision

Use an in-process adapter over the pinned official
`org.kframework.definition.Definition` at this seam:

```text
official parseDefinitionAndResolveBubbles
  -> official pre-compilation checks
  -> OfficialDefinitionAdapter.apply(Definition): Definition
  -> official KoreBackend.steps()
  -> official post-compilation checks
  -> ModuleToKORE/Haskell backend
```

The adapter is composed through the `Function<Definition, Definition>`
pipeline accepted by `Kompile.run`. It reuses the official Guice request scope,
options, parser, backend provider, files, diagnostics, binary loader, and
backend lifecycle. It must not serialize the definition through KAST JSON or K
source at this boundary.

## Ownership and trust boundary

Official K is trusted before the adapter for:

- outer and inner parsing;
- imports, disambiguation, and sort inference;
- typed inner terms and their `Production` attributes;
- configuration parsing and CF-01 through CF-03 sentence generation;
- definition trimming/exclusion; and
- official pre-compilation checks.

Official K is trusted after the adapter for:

- the selected `KoreBackend.steps()` sequence, including contexts, strictness,
  function-with-configuration, cell concretization, and sentence numbering;
- post-compilation checks;
- Kore emission; and
- Haskell compilation and execution.

K-in-K owns the transformation performed at the seam, adapter-level input and
output validation, transformation identity, lineage, content fingerprints,
and the replay manifest.

## Identity contract

`UNIQUE_ID` is not stable identity at this boundary. It is assigned later by
official sentence numbering and correctly changes when a pre-numbering rule
body changes.

Every transformed sentence record must keep distinct:

- lineage identity derived from module, sentence kind, label, source, and
  location;
- input and output content fingerprints;
- body, `requires`, `ensures`, and sentence-attribute fingerprints where
  applicable;
- transformation identity and version; and
- validation outcome.

Source labels remain optional and are not assumed unique. Lineage identifies
the source relationship; fingerprints validate content and stale
preconditions.

## Collection and serialization rules

The official immutable Scala object graph is the lossless compiler-side value.
Scala sets do not acquire an ordering promise merely because a serializer emits
an array. Any K-facing transport must explicitly distinguish ordered sequences
from unordered collections and define its own deterministic canonical form.

Emitted official `parsed.json` is an observation artifact, not the adapter
schema: in the pin it trims `DEFAULT-CONFIGURATION` and omits inner
`Production` attributes required by later passes.

## Validation boundary

The adapter validates its returned value before calling backend steps. The
initial stable classification is `post-transform-pre-backend`. W1-D proves
that a null returned definition is rejected at this boundary and produces no
backend Kore.

Feature-specific packets must add closer validation for their own invariants;
official post-compilation checks are necessary but not a substitute for
adapter validation.

## Structural identity oracle

Across independent JVMs, generated sort-predicate axioms may use alpha-equivalent
`_GenN` binders. Identity comparison may normalize only those generated
binders, scoped within individual top-level Kore blocks. No broader array,
axiom, or text sorting is authorized by this ADR.

Syntax Kore, macros, and representative runtime output remain byte-comparison
oracles where demonstrated.

## Packaging and upgrade rule

The adapter depends on pinned internal packaging:

- development jars under `lib/kframework/java/*`;
- the official injector and request-scope lifecycle;
- injectable frontend/backend services;
- the `Kompile.run` pipeline signature; and
- the installed launcher's native executable and library environment.

Every K upgrade must replay the adapter acceptance suite. If the seam or
lifecycle disappears, stop with a classified API/DI/packaging blocker. Do not
modify official K or reconstruct frontend/backend behavior without a new scope
decision.

## Consequences and non-decisions

This decision removes the need for JSON/source round-trip reconstruction for
post-CF sentence transformations. It also leaves several matters deliberately
open:

- the K-facing semantic-definition transport;
- the full `SemanticInput` schema;
- canonical patches and transaction semantics;
- pre-CF observation/configuration augmentation;
- validation for broader rule shapes; and
- C1/C2 compiler independence.

The W1-A `--post-process` route remains only a late diagnostic/fallback seam.

