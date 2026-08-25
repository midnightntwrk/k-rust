# W1-D: lossless in-process official-definition adapter

Status: authorized bounded investigation by the Wave 1 checkpoint of
19 August 2026.

## Objective

Determine whether the pinned official K frontend can expose a lossless
in-memory `Definition` after parsing, disambiguation, sort inference, and
configuration generation, allow a typed transformation, and then continue
through `KoreBackend.steps()`, Kore emission, Haskell compilation, and
execution without modifying official K.

This packet tests the proposed production adapter seam. It does not define the
full `SemanticInput v1`, add a pre-CF configuration seam, implement observation
instrumentation, or implement independent lowering/Kore emission.

## Starting inputs

- the root revision containing this packet and
  `draft/k-in-k-wave-1-checkpoint-2026-08-19.md`;
- W1-A evidence and replay scripts under `investigations/w1-egress/`;
- K v7.1.337 at
  `4a46d1231473b599c699160132fd6e76a5c46406`;
- the Peano and P3 fixtures; and
- the existing structural and backend behavior oracles.

Record the exact root starting revision before work.

## Questions

1. Can a standalone or embedded driver compose an in-memory transformation
   after `parseDefinitionAndResolveBubbles` and before
   `KoreBackend.steps()` using the pinned artifacts/APIs?
2. Does this preserve inner term/production attributes, modules/imports,
   sentence attributes, source/location provenance, and collection semantics
   without JSON round-tripping?
3. Do Peano and P3 identity transformations produce the same selected Kore and
   runtime behavior as their official baselines?
4. Can the P3 `start-program` edit be applied before meaning-bearing lowering
   so official function/context/cell lowering consumes the transformed rule?
5. Which stable identity, lineage, and before/after fingerprint fields are
   available or must be adapter-owned?
6. Does at least one malformed or unsupported returned transformation fail at
   a defined validation boundary?
7. What official/internal API stability and packaging assumptions would the
   adapter introduce?

## Owned paths

The agent may create or modify only:

- `investigations/w1-inprocess-adapter/**`.

The agent may inspect but not modify existing repository source, task packets,
reports, root package manifests, the pinned K checkout, or the installed K
distribution. If composition requires an official-K source modification,
preserve that as a classified blocker rather than applying it.

## Required outputs

- `investigations/w1-inprocess-adapter/report.md` using the common worker
  return contract;
- machine-readable results and a compact evidence digest manifest;
- standalone source/build/replay material needed to reproduce the experiment;
- a candidate `OfficialDefinitionAdapter v1` decision stating the exact seam,
  trust boundary, API/packaging dependencies, and limitations;
- identity/provenance/fingerprint observations from both fixtures;
- exact commands and acceptance results.

Generated compiler directories, caches, binaries, scanner outputs, and large
KAST/Kore dumps must remain ignored. Commit compact projections, diffs, logs,
and digests instead.

## Acceptance

Accept with `pass` if one unchanged pinned-toolchain driver:

1. obtains a lossless in-memory definition at the proposed seam;
2. performs identity on Peano and P3;
3. reaches matching selected Kore and representative runtime behavior;
4. applies the stated P3 rule edit before lowering and observes the expected
   localized structural/behavioral change; and
5. records provenance plus separate before/after content fingerprints.

Accept with `classified-blocker` if the seam cannot be composed without
official-K modification, but the precise API, classpath, dependency-injection,
or lifecycle blocker and smallest next decision are preserved reproducibly.

## Stop rule

Stop after three substantive full-oracle cycles without acceptance, or when
progress requires:

- modifying official K;
- designing more than one new shared adapter contract;
- implementing pre-CF configuration augmentation;
- defining the full semantic IR;
- reconstructing missing frontend behavior outside official K; or
- implementing independent Kore emission.

