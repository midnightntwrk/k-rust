# Semantic mutation testing

Status: proposed feature contract, 19 August 2026.

## 1. Goal

Let an author specify a mutation of a K language definition as a K
meta-rewrite, generate replayable mutant definitions, run a test corpus against
them, and report which tests distinguish each mutant from the baseline.

A mutation may edit one semantic sentence or several related sentences. A
coupled mutation is one coherent hypothesis and must be applied atomically.

This is mutation testing *of the semantics*, not mutation of programs written
in the defined language.

## 2. Why this belongs in K-in-K

An ordinary K rule rewrites a program configuration. A semantic mutation is
one meta-level higher: it rewrites a representation of K modules and rules.
K-in-K already intends to represent those definitions as data and lower them
with K rules, making semantic mutation a direct use of the architecture rather
than a source-text preprocessor.

The transformation boundary is `SemanticInput v1`: parsed, disambiguated,
sorted sentences with source provenance, before meaning-bearing lowering and
Kore axiom generation. This gives operators structured rule bodies and allows
normal compilation to regenerate all downstream artifacts.

Mutating emitted Kore is a distinct future phase. It can be useful for backend
research, but it must not be confused with mutating the language author's
semantic rules.

## 3. Core model

The system distinguishes four concepts:

- **operator:** a named K meta-semantics that discovers and proposes a kind of
  change;
- **site:** one structural match or one related tuple of matches in a specific
  definition;
- **instance:** one operator applied at one selected site/tuple with concrete
  bindings; and
- **mutant:** the complete definition produced by atomically applying one
  instance.

The conceptual pipeline is:

```text
baseline source
  -> SemanticInput
  -> discover mutation candidates using K rules
  -> canonical atomic patches
  -> validate and select instances
  -> apply one instance to fresh SemanticInput
  -> normal K-in-K lowering and Kore emission
  -> compile validation
  -> test/proof/trace-pattern oracles
  -> mutation report
```

The host orchestrates this pipeline, but it does not interpret the structure
of a K rule or implement mutation meaning.

## 4. Definition representation required by operators

Every mutable sentence exposes at least:

- stable sentence ID, optional source label, module, and source location;
- sentence kind (`rule`, `claim`, `context`, `alias`, and so on);
- left/right rewrite terms or complete body pattern;
- `requires` and `ensures`;
- attributes;
- variable/sort information;
- whether it is source-authored or generated; and
- a structural fingerprint.

Operators match this representation with K patterns. They do not use regular
expressions over `.k` text. Source formatting and comments need not survive;
identity and provenance must.

The definition API must provide deterministic module/sentence lookup and
replacement, plus constructors for edit values. Operators should not depend on
the incidental cell layout of the compiler pipeline.

## 5. Mutation operator contract

An operator module declares:

- a stable operator ID and version;
- the allowed mutation phase and sentence kinds;
- its structural selector;
- any joining condition between multiple sites;
- the patch it proposes;
- expected match cardinality or an explicit enumeration policy;
- preconditions and postconditions;
- whether generated sentences may be selected; and
- a human-readable rationale/category.

K rules may perform arbitrary structured analysis needed to construct the
patch. The externally visible result is nevertheless a canonical patch rather
than an opaque rewritten definition. This makes validation, atomicity,
deduplication, diffs, and replay precise.

Thus the user's mutation is still a rewrite rule over semantic data; the rule
rewrites a mutation-discovery configuration into a patch value. A separate,
trusted-small applier commits that value. In schematic form:

```k
rule <definition> D </definition>
     <request> mutate-write-and-load </request>
     <candidates> .MutationPatches
               => MutationPatch(
                    replaceTerm(WRITE-ID, OLD-W, NEW-W),
                    replaceTerm(LOAD-ID,  OLD-L, NEW-L))
                  ...
     </candidates>
  requires relatedRules(D, WRITE-ID, LOAD-ID)
```

This is illustrative rather than frozen syntax. The patch layer is what lets
one K rule describe a two-sentence change while still guaranteeing all-or-none
application.

The initial patch operations are:

- replace a sentence;
- delete a sentence;
- insert a sentence at a deterministic module position;
- replace a term within a named sentence;
- replace a condition; and
- add, remove, or replace an attribute.

An edit records the expected old fingerprint. Applying it to a different
sentence version fails instead of retargeting silently.

## 6. Single-site and coupled mutations

A single-site instance contains one or more edits rooted in one selected
sentence. A coupled instance contains edits rooted in two or more distinct
sentences selected together by one operator.

For example, an operator may select the rule that stores a value and the rule
that later retrieves it, bind a shared representation choice, and propose a
consistent change to both. The selection is a tuple with a K-defined joining
condition, not two unrelated mutants combined after discovery.

Coupled application obeys these invariants:

- all expected sentence fingerprints still match;
- all site IDs are distinct unless an operator explicitly supports multiple
  non-overlapping edits within one sentence;
- edits do not overlap ambiguously;
- every precondition holds;
- the whole patch validates; and
- either all edits commit or none do.

There is no observable partially mutated definition.

The system does not automatically form the power set or Cartesian product of
single-site candidates. Higher-order combinations grow explosively and often
lack a coherent bug hypothesis. Explicit coupled operators and explicitly
listed mutation plans are supported first; bounded automatic combination is a
later, opt-in policy.

## 7. Site selection and enumeration

The operator chooses one of these policies:

| policy | behavior |
| --- | --- |
| `exact` | Stable IDs/labels must resolve to exactly the declared sites. |
| `each` | Produce one instance for each structural match, in canonical order. |
| `tuple-each` | Produce one instance per tuple satisfying the K join, in canonical order. |
| `all-matches` | One instance edits all matches as one atomic patch. |

Every policy has an explicit maximum candidate count. Truncation yields an
incomplete-generation status and is never silently treated as a complete
mutation set.

Candidate ordering is deterministic over module order, source location,
sentence ID, and patch fingerprint. Structurally identical patches are
deduplicated and their originating bindings are retained in the report.

## 8. Validation

Validation is layered so failures are classified at the closest boundary:

1. **operator validation:** the operator module and declared policy are valid;
2. **selection validation:** cardinality, tuple joins, IDs, and fingerprints
   match;
3. **patch validation:** edits are non-overlapping, atomic, and phase-correct;
4. **IR validation:** modules, imports, sorts, variables, attributes, and
   sentence invariants remain well formed;
5. **lowering validation:** the normal semantic pipeline reaches its declared
   fixed point and emits valid Kore; and
6. **backend validation:** the selected backend accepts the mutant artifacts.

A mutant that does not compile is `invalid`, not `killed`, unless a particular
study explicitly declares compile rejection to be the expected observable.
The default mutation score excludes invalid mutants.

The baseline must compile and pass every selected oracle before any mutant
results are scored.

## 9. Test and oracle semantics

Each mutant runs in isolation with declared resource bounds. Supported oracles
include:

- process exit and backend stop class;
- final configuration or selected cell values;
- expected concrete output;
- reachability/proof result;
- execution semantic-pattern assertions; and
- user-supplied structured predicates over result artifacts.

A valid mutant is:

- `killed` when at least one selected test produces a declared distinguishing
  result;
- `survived` when all selected tests complete and agree with the baseline
  under the declared oracle;
- `timeout` or `unknown` when resource/solver limits prevent that conclusion;
  or
- `error` for infrastructure failures.

Crashes can be configured as kills when they are observable semantic failures,
but infrastructure errors remain separate. The report records the first
killing test and all killing tests when the full run is requested.

Equivalent-mutant detection is undecidable in general. The system may detect
duplicate output fingerprints, unchanged patches, or equivalence under a
bounded oracle, but otherwise labels equivalence `unclassified`; it does not
inflate the mutation score with an unsupported guess.

## 10. Coverage and scheduling

Stable sentence identity connects runtime coverage to mutation sites. After
the basic implementation is correct, the runner may select tests that cover at
least one edited sentence. For a coupled mutant, the candidate test set is the
union of coverage for all edited sites; requiring a test to cover every site is
an optional stronger filter and must be named.

Coverage-based selection is an optimization only. It must be possible to run
the complete corpus, and sampling/pruning policies must be recorded in the
result manifest.

Compilation and test artifacts are cached by content digest over:

- baseline definition and compatibility pin;
- operator module and version;
- canonical patch;
- compiler/backend options; and
- test/oracle manifest.

No mutant shares a writable kompiled directory or runtime state with another.

## 11. Report and replay

Each instance report contains:

- operator ID/version, bindings, policy, and instance ID;
- baseline and mutant definition digests;
- canonical ordered edits with old/new fingerprints;
- all affected sentence IDs, labels, modules, and source locations;
- a normalized structural diff;
- validation outcome and closest failure stage;
- compiler/backend/test commands and bounds;
- tests selected, skipped, killed, survived, timed out, or errored;
- oracle details, including execution-pattern witnesses when relevant; and
- artifact paths/digests sufficient for replay.

The top-level summary gives category counts and the explicitly defined score
denominator. Coupled mutants are one mutant each, regardless of edit count.

## 12. Minimum viable slice

Use one small semantics and implement:

1. an exact-site operator that changes one rule body;
2. a structural `each` operator that changes a side condition or operator at
   every matching rule independently;
3. an exact atomic operator that coherently changes two rules;
4. canonical replace-term/replace-sentence patches;
5. precondition fingerprints, IR validation, and isolated compilation;
6. baseline plus mutant execution against a small corpus;
7. final-state and execution-pattern oracles; and
8. deterministic JSON reports and structural diffs.

The slice is accepted when:

- the single-site operator produces the expected independent instances;
- the coupled operator produces exactly one mutant containing both edits;
- forcing either coupled edit to fail leaves no output mutant;
- zero, one, and excessive selector matches are classified according to the
  declared policy;
- stale sentence fingerprints fail before compilation;
- one mutant is killed by an ordinary result oracle;
- one mutant with the same final result is killed by a trace-pattern oracle;
- an ill-sorted mutant is reported as invalid rather than killed;
- a timed-out mutant is not reported as survived;
- the baseline remains unchanged; and
- repeated runs produce identical candidate IDs, patches, and normalized
  reports.

## 13. Later extensions

- bounded automatic higher-order combinations with interaction-strength
  policies;
- operators over contexts, configurations, claims, and generated sentences;
- a separate post-lowering/Kore mutation phase;
- proof-guided or coverage-guided mutant pruning;
- distributed execution and resumable scheduling;
- subsumption and bounded equivalence analysis; and
- source-preserving pretty-printing of mutants.

## 14. Feasibility evidence in the pinned toolchain

The current project already captures parsed/compiled KAST and emitted Kore from
K v7.1.337, detects a deliberate semantic source mutation at several artifact
boundaries, and carries source attributes through its oracle. In the inspected
pyk API, sentences expose label/`UNIQUE_ID` identity and the coverage helper
maps backend rule IDs back to source sentences.

This is enough evidence for deterministic site identity, replay, coverage, and
compile/test orchestration. The missing enabling feature is the production
`SemanticInput` definition API on which mutation operators can match and emit
patches; the current oracle's whole-file mutation is not yet that API.

## 15. Explicit non-goals for the MVP

- regex replacement over K source;
- silent mutation of every matching rule;
- automatic combination of unrelated mutations;
- scoring non-compiling mutants as killed;
- general equivalent-mutant detection;
- exact preservation of comments/whitespace;
- concurrent mutation of a shared definition directory; and
- treating a coupled mutant as several independent score entries.
