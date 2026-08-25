# OfficialDefinitionAdapter v1 candidate decision

## Decision

Accept one in-process adapter contract over the pinned official
`org.kframework.definition.Definition`:

```text
official parseDefinitionAndResolveBubbles
  -> official pre-compilation checks
  -> OfficialDefinitionAdapter.apply(Definition): Definition
  -> official KoreBackend.steps()
  -> official post-compilation checks
  -> official ModuleToKORE and selected backend
```

The W1-D driver demonstrates this composition without changing official K and
without serializing the definition. It seeds the official Guice request scope,
uses the same options, parser, `Backend` provider, file services, diagnostics,
binary loader, and Haskell backend, and differs from `KompileFrontEnd.run()`
only by composing the adapter function before `backend.steps()`.

This is the candidate production boundary for initial G1 sentence
transformations. It is not a frozen `SemanticInput v1` and is not a pre-CF
configuration seam.

## Trust boundary

Trusted before the adapter:

- official outer parsing, imports, inner parsing, disambiguation, sort
  inference, and typed inner terms;
- official configuration parsing and CF-01 through CF-03 sentence generation;
- the trimming/exclusion selected by `DefinitionParsing`; and
- `Kompile.preCompilationChecks`.

Trusted after the adapter:

- every selected `KoreBackend.steps()` transformation, including
  function-with-configuration, contexts, strictness, cell concretization, and
  sentence numbering;
- `Kompile.postCompilationChecks`;
- `ModuleToKORE`, Haskell compilation, program parsing, and execution.

The adapter owns validation of its returned value before the backend pipeline.
The demonstrated boundary rejects a null returned definition with a stable
`post-transform-pre-backend` classification and emits no backend Kore.

## Losslessness and collections

The input and output are the official immutable Scala object graph. Modules,
imports, local sentences, sentence attributes, inner K-node attributes, typed
`Production` attributes, source/location objects, and collection semantics do
not cross JSON or source text. Peano identity retained 1,934 inner production
attributes; P3 identity retained 1,961. Both identity modes returned the same
`Definition` reference and equal before/after content, inner-attribute, and
primary-source projection fingerprints.

The adapter does not promise iteration order for Scala sets. Fingerprints use
a bounded adapter-owned canonical projection: official sorted definition text
plus sorted module/sentence metadata and a positional inventory of inner K
attributes, including the full attributes of typed inner `Production` values.
This projection is evidence for the seam, not a semantic IR or interchange
format.

## Identity, lineage, and fingerprints

At this seam, source, location, and labels are available. `UNIQUE_ID` is not:
the pinned Kore pipeline assigns it later in `NumberSentences`. Therefore the
candidate contract carries independent fields:

- `lineageSha256`: module, sentence kind, label, source, and location;
- definition `before.contentSha256` and `after.contentSha256`;
- target body, requires, ensures, and sentence-attribute fingerprints; and
- the transformation identity/mode.

For P3 `start-program`, lineage, label, source, location, sentence attributes,
requires, and ensures remained equal while the body fingerprint changed from
`e85ae80f...1108e` to `8f6370ff...45b8`. Official later numbering then changed
the final compiled `UNIQUE_ID` from `2a6d3637...03be` to
`894b0a68...a3f`. This is the desired behavior: stable lineage is separate
from content identity.

## API and packaging dependencies

The candidate depends on pinned internal packaging, not a versioned public K
extension API:

- installed development jars under `lib/kframework/java/*`;
- `Main.getInjector`, `Main.seedInjector`, and `SimpleScope` lifecycle;
- injectable `KompileOptions`, parsing options, `Backend`, `FileUtil`,
  `BinaryLoader`, diagnostics, and stopwatch services;
- public `Kompile.run(..., Function<Definition, Definition>, ...)`;
- `DefinitionTransformer`, `TransformK`, and immutable definition ADTs; and
- service-loaded Haskell backend bindings.

The installed Nix `kompile` launcher also supplies pinned Flex, Bison,
compiler, Java, and Kore executables. The standalone launcher projects those
generated PATH entries and K native-library path before starting Java. A K
upgrade must revalidate both the Java API signatures and launcher layout.

## Structural oracle qualification

Across independent JVMs, raw `definition.kore` can choose `_Gen0` versus
`_Gen1` for binders in generated sort-predicate axioms. The replay scopes
alpha-normalization to those `_GenN` binders within blank-line-delimited Kore
blocks. The complete normalized Peano and P3 definition Kore is equal between
official baseline and in-process identity; `syntaxDefinition.kore` and
`macros.kore` are byte-identical, as is runtime stdout. No other Kore
normalization is applied.

The P3 edit is earlier than W1-A's late post-process edit. Consequently,
official `ResolveFunctionWithConfig` observes that the edited rule no longer
calls `read()` and omits the now-unneeded `#Configuration` match/binder. The
focused Kore diff records exactly the body edit plus that official-pass
consequence. Runtime is byte-identical to W1-A's edit oracle: `<k>` is `0` and
`<state>` remains `2`.

## Limitations

- This is an internal, pin-specific adapter and requires recompilation/replay
  for every official-K upgrade.
- It is after configuration generation and cannot add configuration cells or
  perform other pre-CF augmentation.
- It does not define the full semantic input, patch, transaction, validation,
  or diagnostic schemas.
- The fingerprint projection is adapter-owned evidence, includes absolute
  source provenance, and is not cross-worktree byte-stable.
- Only identity, one labeled typed rule edit, and one malformed return are
  demonstrated. Broader transformation invariants need feature-specific
  validation.
- Raw final Kore bytes are not the identity oracle across independent JVMs;
  only the narrowly alpha-normalized projection is stable in this packet.

## Fallback and upgrade rule

Retain W1-A's hidden JSON `--post-process` route only as a late bounded
fallback. Prefer this in-process boundary whenever an edit must be consumed by
official lowering. If a future K pin no longer exposes the injector lifecycle,
`Kompile.run` pipeline parameter, or installed development jars, stop with a
classified API/DI/packaging blocker rather than modifying official K or
reconstructing frontend/backend behavior.
