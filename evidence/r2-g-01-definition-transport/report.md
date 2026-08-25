# R2-G-01 accepted evidence

Status: pass on 19 August 2026 against K v7.1.337 at
`4a46d1231473b599c699160132fd6e76a5c46406`.

## Acceptance

Run from a checkout without a pre-existing replay output:

```sh
bun run r2:g:transport
```

The replay compiles `KDefinitionTransport-v1`, compiles baseline and
transport-identity Peano/P3 definitions through the pinned Haskell backend,
and exercises the resulting programs. Generated compiler trees and raw logs
remain below the ignored `spine/definition-transport/build/` directory.

## Result

- Peano returned the original official `Definition` reference with zero K
  selections.
- P3 returned the original reference with exactly one K-authored structural
  selection of `start => add(read(), bump())`.
- The returned P3 lineage, content, and body fingerprints matched the original
  in-memory `Rule`.
- Baseline and identity `definition.kore` were equal after the established
  block-scoped `_GenN` alpha-normalization. Syntax, macros, and representative
  runtime output were byte-identical.
- Stale lineage, stale content, and a duplicated structural target were
  rejected at `post-k-selection-pre-backend`; none emitted backend Kore.

The compact machine-readable result is `results.json`; its source hashes bind
the result to the accepted transport, driver, replay, and normalizer. The
replay also emits raw records, projections, logs, checksums, and its own
`results.json` locally for diagnosis. A read-only Sol audit independently
replayed the stable tree and found no structural-selection blocker; its
evidence-tightening findings were incorporated before the final replay.

## Boundary retained

The host projects and validates; K defines the structural selection. Identity
does not reconstruct the official definition from transport data. Official K
still owns parsing, disambiguation, inference, configuration generation,
lowering, Kore emission, and execution. Official emitted `parsed.json` is not
used as replay input.

The result does not authorize patches, general `SemanticInput v1`,
observation/configuration augmentation, mutation features, or C1/C2 work.
