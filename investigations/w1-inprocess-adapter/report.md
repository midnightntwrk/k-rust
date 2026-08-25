# W1-D lossless in-process official-definition adapter report

## Verdict

`pass`

One unchanged pinned-toolchain standalone driver obtains the lossless official
in-memory `Definition` after parsing/configuration generation, applies one
typed adapter function, then continues through `KoreBackend.steps()`, official
Kore emission, Haskell compilation, and execution. Peano and P3 identity pass
the selected structural and runtime oracles. The P3 `start-program` edit is
consumed by official lowering and produces the expected `<k> 0`, `<state> 2`
behavior. Source/location/lineage and distinct before/after fingerprints are
recorded. A null returned definition fails at the defined pre-backend adapter
validation boundary.

No official-K file, existing repository file, manifest, contract, fixture, or
package configuration was modified.

## Starting revision

`57c02599ab970a4d95b7155cf9801adca9bc179c` on branch
`agent/w1-inprocess` in
`/home/sebdev20/Documents/git/workspaces/starstream-fv/k-in-k2-wt-inprocess`.

Pinned K:

- release: `v7.1.337`;
- commit: `4a46d1231473b599c699160132fd6e76a5c46406`;
- executable:
  `/nix/store/18pfm4wc0m4b8phf1x7nwla65iv2s44r-k-7.1.337-4a46d1231473b599c699160132fd6e76a5c46406/bin/kompile`.

## Implemented route

`OfficialDefinitionDriver.java` reuses the official injector and request
scope, injects the same compiler/backend services as `KompileFrontEnd`, and
mirrors its compilation lifecycle. The material composition is:

```java
Function<Definition, Definition> pipeline = adapter::apply;
pipeline = pipeline.andThen(backend.steps());
kompile.run(definitionFile, mainModule, syntaxModule, pipeline,
    backend.excludedModuleTags());
```

`Kompile.run` performs `parseDefinitionAndResolveBubbles` and pre-compilation
checks before invoking that function. The official backend pipeline,
post-compilation checks, `ModuleToKORE`, Haskell compilation, and `krun` remain
unchanged. The driver never calls `ToJson`/`JsonParser` at the seam and never
reconstructs frontend or backend behavior.

The exact candidate contract, trust boundary, dependencies, and limitations
are in `adapter-decision.md`.

## Commands executed

Exact exploratory, focused, negative, and replay commands are recorded in
`commands.md`. The complete acceptance replay is:

```sh
investigations/w1-inprocess-adapter/replay.sh \
  investigations/w1-inprocess-adapter/replay
```

A clean accepted run at `replay-pass` exited 0 and printed
`W1-D replay: pass`.

## Acceptance results

| check | result | evidence |
| --- | --- | --- |
| Lossless official `Definition` at seam | pass | same in-memory ADTs; inner production attrs counted/fingerprinted |
| Peano identity | pass | full definition Kore equal after scoped `_GenN` alpha-normalization; syntax/macros and runtime byte-equal |
| P3 identity | pass | same structural/runtime oracle |
| P3 pre-lowering edit | pass | one target and one `add(read(), bump()) -> bump()` replacement |
| Official passes consume edit | pass | function-with-config omits its formerly required `#Configuration` binder |
| P3 structural change localized | pass | focused normalized start-rule diff; syntax/macros byte-equal |
| P3 behavior | pass | byte-equal to W1-A edit oracle; `<k>` 0 and `<state>` 2 |
| Provenance/lineage/fingerprints | pass | source, location, label, lineage, sentence attrs, before/after component digests |
| Malformed return boundary | pass | null `Definition` rejected before backend, exit 113, no `definition.kore` |
| Replay | pass | `replay.sh` clean exit 0 |

No packet acceptance check failed.

### Identity qualification

Separate JVMs in this pin can emit alpha-equivalent generated sort-predicate
axioms with `_Gen0` versus `_Gen1`. Raw Peano/P3 `definition.kore` therefore
need not be byte-identical. The replay normalizes only `_GenN` binders, scoped
to blank-line-delimited top-level Kore blocks; the entire resulting definition
Kore is equal. Peano normalized definition digest is `31a8642e...321c`; P3 is
`45f91880...e1b6`. `syntaxDefinition.kore`, `macros.kore`, and representative
runtime stdout are byte-identical. This is a relational selected-Kore pass,
not a claim of raw-byte identity across JVMs.

### Losslessness and provenance observations

| observation | Peano | P3 |
| --- | ---: | ---: |
| modules | 65 | 65 |
| local sentences | 561 | 578 |
| K nodes inventoried | 2,199 | 2,250 |
| K nodes with attributes | 1,941 | 1,970 |
| typed inner `Production` attrs | 1,934 | 1,961 |
| primary-source sentences | 8 | 16 |

Identity returned the exact same `Definition` reference for each fixture.
Before/after content, official text, inner-attribute inventory, and
primary-source projection fingerprints are equal in both records.

At the pre-lowering seam, P3 `start-program` has label `start-program`, source
`p3/fixtures/coupled.k`, location `[27,8,27,30]`, and no `UNIQUE_ID`.
Adapter-owned lineage is `072a30a1...b66c`. The edit preserves that lineage,
sentence-attribute fingerprint, source/location, requires, and ensures while
changing the body and whole-definition fingerprints. After official sentence
numbering, compiled `UNIQUE_ID` changes from `2a6d3637...03be` to
`894b0a68...a3f`, confirming that lineage and content identity are correctly
separate.

## Evidence paths and digests

Compact committed evidence is under `evidence/`:

- adapter records for Peano identity, P3 identity/edit, and malformed return;
- representative runtime stdout;
- focused Kore diffs showing the edit and official pre-lowering consumption;
- final compiled source/provenance projections;
- the malformed diagnostic; and
- retained/generated SHA-256 manifests.

Selected accepted digests:

| evidence | SHA-256 |
| --- | --- |
| Peano identity record | `da900c93e179299302a6fe64759dac8a428477c1544254c5921d90ef667eb964` |
| P3 identity record | `a8d4c7361d1865cca57a40b7882b69b3ce699fb4c90e71064492182009703786` |
| P3 edit record | `4a7915d4ca7f783de23d19f90151a047af767e5dd42157a380ed9351a2bfe066` |
| malformed record | `164fcc0d4b235626f527f72d53ebabd2f4f2f6574fdb69a4e87e66452e1b6ac4` |
| Peano runtime, baseline/identity | `acadee28ab2a2231e8165e5148cc6bf89df2e91a7de5443cb0833a664d078507` |
| P3 runtime, baseline/identity | `1d23163a56975a2c8d9c3991a16f1920eaefaa8595c9625c63cccaacc43d27f7` |
| P3 runtime, reference/in-process edit | `8c7e395db8507411c1e36cbff0fb8c0d0e77e14032e078e162527c8a4411d52f` |
| start-program diff | `e4178bc847b54b61be48e2f4b9b0bb3050bd0fe242039158e1b8623925821289` |
| pre-lowering consumption diff | `04def24b59f2020dc01f07b5345b0d1872abd308f820ef3732d4163b32f50b11` |

`evidence/generated-SHA256SUMS` retains digests for omitted large/raw
artifacts. Compiler output directories, scanners, caches, binaries, full JSON,
and full Kore dumps remain ignored and are regenerated by `replay.sh`.

## Newly discovered contracts

1. The desired post-CF/pre-lowering composition is already expressible by the
   public `Kompile.run` pipeline parameter; no official modification is needed.
2. The installed distribution contains sufficient development jars and
   service metadata, but a standalone driver must reproduce the generated Nix
   wrapper's executable/native environment as well as the Java classpath.
3. `UNIQUE_ID` does not exist at this seam. It is assigned later and changes
   after a pre-numbering body edit. Source/location/label plus adapter lineage
   and content fingerprints are the correct identity split.
4. Keeping inner `Production` attributes requires staying in memory. The
   demonstrated counts survive identity without a JSON round trip.
5. An edit before `ResolveFunctionWithConfig` can remove generated structure
   that a late post-process edit leaves stale. Here the official pass removes
   the no-longer-needed configuration binder.
6. Raw backend Kore has a narrow cross-JVM alpha-name instability for
   generated `_GenN` binders. Selected structural identity must scope that
   normalization explicitly rather than claim raw bytes.
7. A returned transformation needs an adapter-owned validation boundary before
   backend steps; official post-compilation checks are later and are not a
   substitute for validating a null/unsupported result.

## Requested shared-contract changes

Request one concrete shared `OfficialDefinitionAdapter v1` contract using the
seam and trust boundary in `adapter-decision.md`. Its minimum record fields are
transformation identity, input/output content fingerprints, lineage identity,
source/location/label provenance, and validation outcome.

Do not yet freeze `SemanticInput v1`, add pre-CF augmentation, or generalize the
bounded fingerprint projection into a semantic IR.

## Remaining unknowns

- Which additional sentence edits preserve every invariant expected by all 32
  Kore frontend passes.
- The public/stability commitment, if any, for the internal Guice modules,
  installed development jars, and `Kompile.run` signature across K releases.
- Whether other backends register different lifecycle or packaging
  dependencies than the demonstrated Haskell backend.
- The exact typed pre-CF boundary required for observation-cell augmentation;
  this packet deliberately does not investigate it.
- The future full semantic-input and transformation-validation schemas.
- Whether `_GenN` alpha drift occurs cross-host in more Kore constructs than
  the generated sort predicates observed here.

## Recommended next packet

Write the concrete adapter ADR and issue one bounded identity/provenance
transformation-spine packet over `OfficialDefinitionAdapter v1`. Keep
pre-configuration observation augmentation as a separate packet. Do not begin
C1/C2 fan-out or freeze the full semantic input until the adapter record and
feature-specific validation spine are accepted.
