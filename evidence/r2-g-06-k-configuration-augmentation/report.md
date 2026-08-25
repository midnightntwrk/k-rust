# R2-G-06 accepted evidence

Status: pass on 19 August 2026 against K v7.1.337 at
`4a46d1231473b599c699160132fd6e76a5c46406`.

## Acceptance

Run from a checkout without pre-existing acceptance output:

```sh
bun run r2:g:configuration
```

The replay compiles the `KConfigurationAugmentation-v1` semantics, installs the
accepted source-bound pre-CF hook overlay in an isolated build tree, performs
two fresh K-authored augmentations, compares the R2-G-05 Java and ordinary-source
oracles, exercises all negatives, and runs the generated definition through the
pinned Haskell backend. Raw outputs remain below the ignored
`spine/configuration-augmentation/build/` tree.

## Result

- K structurally selected the sole P3 configuration and authored its target
  lineage/fingerprint preconditions, cardinality, parent/template paths, new
  name/value, and `apply` status. The generic host validated and applied exactly
  one typed leaf clone, changing exactly one configuration.
- Reprojection made K return `already-present` with cardinality one. The host
  independently validated the declared existing leaf and returned the exact
  augmented `Definition` reference without reconstruction.
- Metadata, conditions, provenance, module/sentence cardinality, and every
  original node outside rebuilt ancestors were preserved. Official CF
  generation, lowering, Haskell compilation, and execution produced `<k> 1`,
  `<state> 2`, and `<observation> 0`.
- The fresh repeat had stable request/result fingerprints, normalized Kore,
  syntax/macros, and runtime. Focused generation markers matched both independent
  oracles; the expected provenance distinction is that the typed clones inherit
  the state-cell source while ordinary source owns an observation line.
- Stale content, zero/duplicate targets, invalid paths, conflicting existing
  state, and false `already-present` all rejected at their declared boundary
  with zero applications, zero post-CF calls, and no backend artifacts.

## Boundary retained

Java projects complete typed configurations and generically validates and
applies K's declaration; it does not select P3 structure, paths, the cell name,
or initializer. The contract exposes one fixture-specific
`cloneLeafCellFromInput` operation only. It adds no event, rule instrumentation,
trace, monitor, matcher, C1, or C2 behavior, and the accepted hook overlay remains
temporary and source-bound.

There was no packet ambiguity requiring a split. The recommended next packet is
one conservative single-rule observation using this branch-local configuration
state, without expanding into trace or matcher work.
