# W1-A official-K ingress, configuration, and egress report

## Verdict

`pass`, with a deliberately narrow adapter decision.

The hidden official-K `--post-process` route demonstrated identity re-entry
for both Peano and P3, byte-identical selected structural output, equal
sentence identity/provenance projections, and byte-identical backend behavior.
A typed edit to one already-concretized P3 sentence re-entered, compiled, and
executed deterministically. The exact missing contract for the preferred
earlier boundary is isolated: official emitted `parsed.json` is not a lossless
replay artifact, and no serialized or CLI seam exists between typed
configuration parsing and configuration-sentence generation.

The observation-cell edit compiled and executed deterministically through an
ordinary K-source fallback. It proves that trusted official CF can generate
the augmented configuration; it does not claim a typed pre-CF round trip.

## Starting revision

`9f30221d08de4b0f710061ce599b3c7f9f860273`

Pinned K:

- release: `v7.1.337`
- commit: `4a46d1231473b599c699160132fd6e76a5c46406`
- resolved executable:
  `/nix/store/18pfm4wc0m4b8phf1x7nwla65iv2s44r-k-7.1.337-4a46d1231473b599c699160132fd6e76a5c46406/bin/kompile`
- actual KAST envelope emitted by this pin: version 4

The K source checkout was at the pinned revision with a pre-existing unrelated
`M pyk/uv.lock`; W1-A did not modify it.

## Outcome and route decision

| route | result | exact boundary | decision |
| --- | --- | --- | --- |
| `--post-process` JSON KAST | pass on Peano and P3 identity; pass on one P3 sentence edit | after every Kore frontend pass/check, before `ModuleToKORE` | bounded temporary fallback |
| `--outer-parsed-json` from pyk | blocked before artifact production | outer modules; rule/configuration bodies still bubbles | not typed G1 egress |
| emitted `parsed.json` replayed with `--outer-parsed-json` | blocked | desired post-CF/pre-lowering location | artifact is trimmed and loses inner-node attrs |
| canonical generated K source | unavailable | would re-enter normal source compilation | no definition-level canonical emitter exists |
| ordinary K source with observation cell | pass, twice identically | before all official parsing/CF | configuration fallback only |

The demonstrated adapter decision, trust boundary, limitations, and fallback
are in `adapter-decision.md`.

### Answers to packet questions

1. Official K accepts a returned fully compiled KAST v4 definition through
   `--post-process`, then reaches official Kore/backend output. It accepts an
   outer KAST definition through `--outer-parsed-json`, but the available pyk
   producer cannot convert syntax sentences in these fixtures and this
   boundary contains untyped bubbles. Ordinary K source remains replayable.
   Emitted `parsed.json` is structured but is not replayable as compiler input.
2. No supported serialized/CLI route was found for transforming parsed,
   disambiguated source sentences and typed configuration terms before
   configuration generation. `resolveConfigBubbles` parses a `Configuration`
   and immediately calls `GenerateSentencesFromConfigDecl` inside one protected
   operation.
3. The working post-configuration boundary is later than desired:
   `--post-process` runs after all 32 Kore frontend passes. It trusts CF-01,
   CF-02, and CF-03 completely, plus function-with-config, contexts,
   strictness, cell concretization, numbering, all other selected lowering,
   and the checks that run before the hook.
4. Identity succeeded for Peano and P3. `definition.kore`,
   `syntaxDefinition.kore`, `macros.kore`, and runtime stdout were byte-equal
   between baseline and identity. The explicit projection of user-source
   sentences was also equal (3 selected Peano sentences, 13 selected P3
   source/generated sentences).
5. The P3 `start-program` sentence was changed from `start => read() + bump`
   to `start => bump` at the typed fully compiled boundary. Exactly that
   labeled rule changed in selected KAST/Kore; execution changed `<k>` from 1
   to 0 while `<state>` remained 2. Adding `<observation> 0 </observation>` in
   source caused official K to generate the cell sort, constructors,
   initializer, projections, and final cell. Two complete compiles/runs were
   byte-identical. The two edits do not yet share one typed route.
6. Under `--post-process`, `label`, `UNIQUE_ID`, source, and location survived
   identity and the sentence edit. The edited rule kept
   `UNIQUE_ID(2a6d…03be)` despite its changed body, proving that this ID is
   stale after a post-numbering edit. JSON array order did not survive the
   parse/serialize cycle; final Kore and the stable projection did. Source
   fallback assigns new source paths/locations and regenerates identities.

## Commands executed

The exact material commands, including failed route invocations and shell
redirections, are in `commands.md`. The deterministic acceptance replay is:

```sh
investigations/w1-egress/replay.sh investigations/w1-egress/replay
```

It verifies the baseline is an ancestor, verifies the pinned executable path
and release, rebuilds both identity fixtures, applies the sentence edit,
builds the observation fixture twice, compares artifacts/behavior, and writes
digests. A clean replay during W1-A exited 0 and printed:

```text
W1-A replay: pass
```

## Evidence paths and digests

The complete digest manifest for the locally generated evidence is
`investigations/w1-egress/evidence/SHA256SUMS` (SHA-256
`0b79e601d984653d054924924a5656c7d7b6ac95f40c992557fe78e6c1634e9f`,
180 files, 18 MiB at capture time). The compact commit intentionally retains
the manifest rather than those generated compiler directories; `replay.sh`
reconstructs them.

Key evidence:

| evidence | SHA-256 |
| --- | --- |
| Peano baseline/identity `definition.kore` | `6b0ff9714c8c06d7259f462633b275bc9f8412ffa9e0e2311cfe56af1acbf6b0` |
| Peano baseline/identity runtime | `acadee28ab2a2231e8165e5148cc6bf89df2e91a7de5443cb0833a664d078507` |
| P3 baseline/identity `definition.kore` | `de31f8d0d419fb9f8ffd2201f400df9f06ef02999b8e62da0947fe50f1ec45d5` |
| P3 baseline/identity runtime | `1d23163a56975a2c8d9c3991a16f1920eaefaa8595c9625c63cccaacc43d27f7` |
| P3 edited `definition.kore` | `7360cc555ac8cfb6015f97970841154d88c1f9d9f35d62ad43bea4516312b5fa` |
| P3 edited runtime | `8c7e395db8507411c1e36cbff0fb8c0d0e77e14032e078e162527c8a4411d52f` |
| observation `definition.kore` (both repeats) | `4967b0dc5d7edb722b39455ef1d69977a2f17a75203d291f4a5cc28966a02945` |
| observation runtime (both repeats) | `bd078f608534aed42d4e4b094e456839fff7d834195497090274626ac29a7ea4` |
| source audit | `46c147cab4dbcb10c9a043358a3703c26b68fa987eb61b605c0c641ea02b7cbb` |
| pyk outer-route failure stderr | `9919f9c31b6db4efe165e83ff2862343f3104b269812f460efc27fd5ea9500e3` |

Compact committed evidence:

- `evidence/cycle-1/runtime`: baseline and identity runtime outputs;
- `evidence/cycle-1/logs/peano-identity.stderr`: initial KAST-version failure;
- `evidence/cycle-2`: focused KAST/Kore diffs and runtime output;
- `evidence/cycle-3`: material parsed-KAST re-entry debug stacks;
- `evidence/cycle-4/runtime`: deterministic observation outputs;
- `evidence/projections`: sentence identity/provenance projections;
- `evidence/outer-route`: pyk outer producer failure;
- `evidence/source-audit`: pinned environment and relevant official source
  excerpts.

Generated compiled directories, KAST/Kore dumps, multi-megabyte adapted JSON,
backend/cache binaries, and replay trees are excluded from the commit. Their
paths and digests remain in `SHA256SUMS`, material conclusions remain in the
compact projections/diffs/results, and `replay.sh` recreates acceptance.

## Acceptance checks passed and failed

Passed:

- identity re-entry through one official-K route on Peano;
- identity re-entry through the same route on nested-configuration P3;
- byte-identical final Kore structural artifacts for both fixtures;
- equal selected sentence identity/provenance projections for both fixtures;
- byte-identical representative backend behavior for both fixtures;
- one typed, labeled sentence edit accepted by official K, compiled, and
  executed with the expected localized structural and behavioral difference;
- one observation-cell source fallback accepted, compiled, and executed twice
  with byte-identical raw JSON, Kore, and behavior;
- replay script from the recorded revision.

Failed or intentionally not claimed:

- full `compiled.json` byte/current-normalization identity after
  `--post-process` (set-backed arrays reorder; no normalization was broadened);
- official pyk outer-KAST production for these syntax fixtures;
- direct emitted-`parsed.json` re-entry;
- typed pre-configuration observation augmentation;
- canonical typed-definition-to-K-source emission;
- one unified typed route for both sentence and configuration edits.

These failures do not invalidate the packet's pass rule because the same route
demonstrated identity for both fixtures and a safe typed transformation, while
the earlier configuration contract is isolated precisely.

The cycle labels cover distinct packet questions, not four unsuccessful
full-oracle retries: acceptance was obtained in cycle 1, so the stop rule of
three substantive full-oracle cycles *without acceptance* was never exceeded.
Cycles 2–4 localized the safe edit, the failed earlier seam, and the requested
configuration behavior respectively.

## Newly discovered contracts

1. The pinned compiler's actual definition envelope is KAST v4; the nearby
   pipeline developer document still states v3.
2. `--post-process` is JSON KAST → JSON KAST after the complete frontend and
   after post-compilation checks, not a general parsed-definition hook.
3. Official `ToJson` serializes K applications/rewrite structure but omits
   inner K-node attributes. Semantic-cast `Production` attributes required by
   `ComputeUnboundVariables` are therefore absent from emitted `parsed.json`.
4. Emitted `parsed.json` also trims `DEFAULT-CONFIGURATION`, while
   `parseDefinitionAndResolveBubbles` unconditionally looks it up. Adding an
   empty reachable module exposes the later missing-attribute failure but does
   not make the artifact replayable.
5. `Definition`/module/import/sentence collections cross JSON through
   set-backed structures; serializer array order is not an identity contract.
6. `UNIQUE_ID` is assigned before `--post-process` and is not recomputed. A
   post-hook mutation needs separate before/after structural fingerprints and
   lineage; the surviving ID alone must not validate content.
7. Source and location provenance survive the demonstrated JSON hook, as do
   user labels, but a source-regeneration fallback necessarily creates new
   provenance unless a mapping manifest is carried separately.
8. The available pyk outer parser recognizes syntax declarations, but its
   AST-to-KAST conversion has no `SyntaxDefn` sentence implementation for the
   tested pin, so `kompilex` is not a usable producer for these fixtures.

## Requested shared-contract changes

1. Define `OfficialDefinitionAdapter v1` as an in-memory boundary over a
   lossless official `Definition`, after configuration generation and before
   `KoreBackend.steps()`. Pin K release/commit and state that CF-01 through
   CF-03 are trusted.
2. Make attribute completeness explicit. A serialized alternative must carry
   inner-node `Production`/sort metadata required by later checks/passes; do
   not call current emitted `parsed.json` replayable.
3. Separate stable sentence identity from content fingerprints. Record input
   fingerprint, output fingerprint, parent ID, and transformation ID; either
   recompute backend `UNIQUE_ID` after edits or transform before numbering.
4. Type collections in the adapter schema as ordered sequence versus set and
   add a focused set-aware structural projection. Do not globally sort arrays
   in the existing normalization policy.
5. If typed observation/configuration augmentation is required before CF,
   expose a second, explicitly earlier seam between parsed `Configuration`
   terms and `GenerateSentencesFromConfigDecl`; do not reconstruct CF output
   in TypeScript.
6. Correct the KAST version in the pinned pipeline documentation or negotiate
   it from the artifact rather than hard-coding v3.

## Remaining unknowns

- Whether a small in-process Java adapter can compose a transformation before
  `KoreBackend.steps()` without relying on unstable dependency-injection
  internals.
- Which sentence edits are safe at the post-process boundary beyond the one
  feature-isolated already-concretized rewrite.
- Whether official backend consumers rely on stale `UNIQUE_ID` values in
  coverage/debug/proof workflows not exercised here.
- Whether a supported definition-level source formatter exists outside the
  inspected Java/pyk paths; none was found in the pin.
- The exact typed pre-CF API needed for additive cells, multiplicities,
  initializer variables, and observation rules.
- Negative behavior for malformed returned compiled KAST; pre-hook checks do
  not rerun after post-processing.

## Recommended next packet

Run one bounded **in-process post-configuration adapter** packet, with no
independent lowering or source emitter:

1. wrap pinned `Kompile.run` so an in-memory transformation is composed before
   `KoreBackend.steps()`;
2. expose lossless typed `Definition` input/output without JSON serialization;
3. replay Peano and P3 identity against the same Kore/runtime oracle;
4. apply the same `start-program` edit before function/context/cell lowering;
5. verify source/location/label plus separate before/after fingerprints; and
6. stop with a classified blocker if this requires modifying official K or
   more than one new shared adapter contract.

After that succeeds, authorize a separate pre-CF configuration-seam packet for
typed observation-cell augmentation. Do not fold it into the adapter packet.
