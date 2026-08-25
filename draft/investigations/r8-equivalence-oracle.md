# R8: Equivalence oracle

> R11 retains these layers and adds a normalized `k-rust` Definition snapshot
> plus Java-versus-Rust frontend KORE comparison. See
> [R11](r11-k-rust-frontend-integration.md) and the authoritative design.

## Decision

KRS should use a **layered differential oracle**, not one golden file. The
acceptance test for a translated definition is:

1. equivalent source-level definition structure after K parsing;
2. equivalent object-language parsing;
3. equivalent concrete and search behavior; and
4. equivalent proof outcomes for a selected symbolic corpus.

No individual layer is sufficient. Compiled KAST/Kore equality catches lowering
mistakes early but is sensitive to K frontend changes; behavioral tests are
more stable but cannot cover the whole definition.

## Oracle layers

### 1. KRS frontend tests

These do not depend on K and should be exact golden tests:

- CST and semantic IR snapshots for representative KRS items;
- name resolution, sort/subsort closure, and exhaustiveness diagnostics;
- normalized relational pre/post IR for rules;
- attribute validation and raw-attribute preservation;
- deterministic generated symbol/rule IDs; and
- generated `.k` plus generated-to-KRS source map.

Formatting-only changes may deliberately update the `.k` golden. Semantic IR
goldens should change only for a language/lowering decision.

### 2. Parsed-definition comparison

Compile the hand-written K baseline and the KRS-generated `.k` with the same K
pin and `--emit-json`. Compare normalized `parsed.json`, not raw bytes.

Normalization should:

- select project modules rather than all imported builtin modules;
- sort modules, imports, set-valued sentences, attributes, and commutative
  collections canonically;
- remove `Source`, `Location`, digest, parser-production provenance, generated
  unique IDs, and other non-semantic metadata;
- map explicitly declared KRS symbols/rule labels to their baseline names;
- alpha-normalize generated and anonymous variables; and
- retain sort signatures, productions, attributes with semantic effects,
  configuration-generated cells/initializers, rule bodies, conditions, and
  claims.

This is the primary lowering-completeness oracle. `parsed.json` is produced
after inner parsing, configuration expansion, cast insertion, and related
frontend work, so equality here proves more than textual resemblance.

Raw `parsed.json` is not stable across K releases. Store the K pin with every
golden and regenerate intentionally when adding support for a new K version.

### 3. Compiled-definition/Kore comparison

Compare a normalized projection of `compiled.json` or `definition.kore` for the
same pinned K release. This catches interactions with strictness desugaring,
macros, sort injections, cell completion, and backend lowering that may not be
obvious in source-level KAST.

Do not require textual Kore equality. Module/sentence order, frontend-generated
identifiers, locations, and backend metadata are unstable. Prefer structural
hashes of normalized symbol declarations, axioms, and rewrite rules.

This layer is valuable for the compiler test suite but should not be the public
definition of semantic equivalence across K versions.

### 4. Object-language parser corpus

Feed the same accepted and rejected strings to parser artifacts built from the
baseline and KRS definitions.

For accepted inputs, compare normalized Kore/KAST terms and pretty-printed
round trips. For rejected inputs, require both definitions to reject; diagnostic
wording need not match.

The initial IMP corpus must cover:

- every operator and literal;
- precedence and associativity (`1 + 2 * 3`, chained comparisons);
- brackets;
- dangling `else`;
- statement sequencing and blocks;
- token boundaries and invalid tokens; and
- pretty-print/parse round trips.

Grammar equivalence cannot be inferred from matching constructor declarations,
so this is a release-blocking layer.

### 5. Concrete execution and bounded search

Run identical initial configurations through both definitions and compare
normalized final configurations. IMP already supplies useful expression and
statement matrices in `src/tests/integration/test_expr.py` and `test_imp.py`.

Add traces at rule-label granularity for small programs. Final-state equality
alone can miss differences in evaluation order or an accidentally applicable
rule. Trace comparison should permit explicitly documented stuttering steps
introduced by lowering.

For nondeterministic definitions, compare sets of normalized results from
bounded search, not enumeration order. Include deadlocks/stuck states and depth
bounds in the result identity.

### 6. Symbolic execution and proof corpus

Compile both definitions with the same Haskell backend and prove the same
claims. Compare:

- passed/failed/incomplete status;
- terminal and stuck frontier counts;
- normalized final constraints for small claims; and
- applied user-rule labels for representative paths.

IMP's `examples/specs` already covers symbolic variables, `requires`,
`ensures`, existential result variables, branching, loops, circularity, and
multi-cell updates. A minimal initial proof corpus should include one claim from
each category.

Exact KCFG shape, node numbering, solver timing, and simplification counts are
not semantic and can vary with backend versions or heuristics. They are useful
performance/regression signals, not equivalence requirements.

## Milestone gates

### M0: One constructor and rule

- exact KRS IR golden;
- generated K compiles;
- normalized parsed-definition fragments match; and
- one concrete execution matches.

### M1: Full IMP

- all source modules represented with no raw K sentences except explicitly
  accepted escape-hatch tests;
- full accepted/rejected parser corpus matches;
- all existing concrete IMP integration cases match;
- bounded traces match for representative control flow; and
- the selected proof corpus has identical outcomes.

### M2: Open syntax and collections

- a KWasm slice demonstrates modular extension and overloaded lists;
- a collection-cell example compares search-result sets; and
- reordering independent KRS rules leaves normalized outputs unchanged.

### M3: Production readiness

- KMIR slice exercises modern attributes and symbolic execution;
- dual `.k`/outer-KAST adapters, if the latter exists, produce equal normalized
  parsed definitions;
- diagnostic source-map tests point K failures back to KRS spans; and
- compatibility is tested against every declared K release pin.

## Stable versus pinned artifacts

| Artifact | Expected stability |
|---|---|
| KRS CST/IR and diagnostics | Stable across K releases |
| Generated `.k` | Stable for a KRS compiler version, modulo formatting policy |
| Parsed/compiled KAST | Golden only within a pinned K release |
| Textual Kore | Do not golden directly |
| Parsed object-program terms | Structurally stable when symbols are explicit |
| Concrete/search results | Semantic and expected to remain stable |
| Proof pass/fail and final property | Semantic and expected to remain stable |
| KCFG shape, timing, solver steps | Informational/performance only |

## Required tooling

Build a small `krs-diff` utility around the K pin that:

1. compiles baseline and generated definitions with `--emit-json`;
2. normalizes KAST/Kore using explicit allowlists of semantic fields;
3. parses and executes corpus cases through pyk or the built parser;
4. compares result sets and proof summaries; and
5. explains the first structural difference using KRS item IDs and source maps.

The normalizer must be versioned and tested. A normalizer that removes an
unknown field by default can hide semantic drift; unknown KAST nodes or
attributes should fail closed until classified.
