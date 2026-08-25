# R6: K lowering boundary

> Historical boundary decision: this report predates the Rust-native
> `k-rust` frontend. Its findings about pyk and the Java frontend remain valid,
> but [R11](r11-k-rust-frontend-integration.md) adds a viable structured native
> adapter while retaining `.k` as the compatibility path.

## Decision

KRS should own a typed, target-neutral **K Definition IR**, and its supported
production boundary should initially be generated `.k` source consumed by the
normal K frontend.

An outer-KAST JSON emitter is worth adding later as an experimental,
K-version-pinned adapter and differential oracle. It should not be the only
lowering path. KRS should not generate Kore directly.

This is stronger than the original “emit `.k` during bootstrap” hypothesis:
textual K is currently the only complete, supported boundary that resolves
imports and builtins and exercises all frontend parsing/desugaring in the same
way as hand-written definitions.

## Representations found

### Pyk outer KAST

`pyk.kast.outer` defines useful structured classes for most definition items:

- `KDefinition`, `KFlatModule`, and `KImport`;
- `KSyntaxSort`, `KProduction`, lexical/priority/associativity sentences;
- `KRule`, `KClaim`, `KContext`, and `KBubble`; and
- structured `KInner` terms for rule bodies.

The shapes are a good reference for KRS's Definition IR. They are not presently
a complete authoring API. In the checked-in K 7.1.337 source,
`pyk.kast._ast_to_kast` implements definitions, modules, imports, and requires,
but its sentence conversion is deliberately unimplemented. Running:

```text
pyk parse-outer .../imp-semantics/imp.k --main-module IMP
```

fails on the first `SyntaxDefn` with:

```text
AssertionError: Unimplemented Sentence->KSentence conversion
```

Pyk's `KSentence` set also lacks a public `KConfiguration` class even though
the Java KAST JSON reader supports that node.

### Java frontend KAST JSON

The Java frontend has a versioned JSON representation (`format: "KAST"`,
currently version 4). `JsonParser` accepts structured definitions, modules,
productions, rules, claims, contexts, configurations, bubbles, and inner terms.
`kompile` has a hidden `--outer-parsed-json` input mode.

This route can in principle avoid reparsing KRS-generated rule terms: KRS could
emit `KRule` and `KConfiguration` nodes directly and still let the frontend
expand configurations and apply later compilation passes.

It is not a stable standalone interface:

- the flag is hidden and the JSON version must exactly match K;
- JSON `KDefinition` has no `requires` processing in `JsonParser`;
- outer-parsed input therefore has to bundle all reachable builtin modules;
- feeding a normal compilation's `parsed.json` back into `kompile` fails because
  it no longer contains `DEFAULT-CONFIGURATION`, which outer-parsed compilation
  assumes is present; and
- pyk does not currently provide complete construction/round-trip support for
  this pre-desugaring form.

The concrete round-trip experiment was:

```text
kompile --backend kore --emit-json .../imp.k
kompile --backend kore --outer-parsed-json <first-output>/parsed.json
```

The first command completed in roughly five seconds. The second failed in
`DefinitionParsing.resolveConfigBubbles` while looking up the absent
`DEFAULT-CONFIGURATION` module. Thus even K's emitted `parsed.json` is not a
self-contained valid input to its outer-parsed mode.

### Parsed and compiled JSON

`kompile --emit-json` produces:

- `parsed.json`, after imports, builtin loading, inner parsing, configuration
  expansion, cast insertion, and other parsing work; and
- `compiled.json`, after the backend-independent kompile pipeline.

These are excellent inspection and golden-test artifacts. They are too late to
serve as the authoring boundary: source configurations have already become cell
productions and initializer functions, and source rules already contain
frontend-generated labels and semantic casts.

### Kore

Kore is the backend definition language, not merely a serialized `.k` AST.
Direct generation would require KRS to reproduce or deliberately bypass
frontend behavior for configurations, user lists, record patterns, macros,
strictness/contexts, cell completion, sort inference and injections, overloads,
fresh variables, generated predicates/projections, and backend normalization.
That would turn a surface-language project into a competing K frontend and
create a much larger correctness obligation.

## Recommended architecture

```text
KRS CST
  -> KRS semantic/type IR
  -> K Definition IR
       |-> canonical .k emitter (supported path)
       |-> outer-KAST vN adapter (experimental/version-pinned)
       `-> debug JSON for KRS tools
  -> stock kompile
  -> parsed.json / compiled.json / Kore
```

The Definition IR should model concepts at the source-definition level, before
K expands them:

- modules/imports and a separate dependency manifest;
- sorts, productions, grammar groups, tokens, and attributes;
- configurations as cell trees with defaults and multiplicities;
- relational pre/post rule patterns, conditions, contexts, and claims; and
- stable KRS item IDs and source spans.

It should not copy either pyk's Python classes or KAST JSON byte-for-byte.
Adapters can absorb K release changes while the KRS type checker and language
remain stable.

## Source locations and diagnostics

Generated `.k` makes K diagnostics naturally point at generated files. There is
no documented textual `#line`/source-map mechanism in the inspected frontend.
KRS should therefore:

1. emit deterministic generated files with one definition item per stable KRS
   item and explicit stable K labels/symbols;
2. write a sidecar map from generated byte/line ranges and K labels to KRS
   spans;
3. invoke K through a KRS driver that rewrites diagnostics and proof rule IDs
   through that map; and
4. retain generated `.k` paths and locations in verbose diagnostics for
   debugging the lowering itself.

The future JSON adapter can attach K's internal Source/Location attributes
directly, but that is not a reason to couple the base compiler to a hidden API.

## Testing implications

For every K pin supported by KRS:

- compile generated `.k` through stock `kompile`;
- compare selected normalized portions of `parsed.json` and `compiled.json` to
  the hand-written K baseline;
- when the JSON adapter exists, compile both emitted `.k` and emitted JSON and
  require equal normalized parsed definitions;
- compare program parses, concrete/search results, and proof outcomes rather
  than relying only on pretty-printed K; and
- treat KAST JSON version or schema changes as adapter compatibility work, not
  changes to the KRS language.

## Consequences for the surface design

KRS does not have to mirror every frontend-generated K constructor. It should
model author-visible semantics and let K perform its standard desugarings. The
raw escape hatch should emit source-level K attributes or, for genuinely
unmodeled sentences, a clearly delimited raw-K item. A raw-K item reduces
portability and source mapping but is safer than silently trying to approximate
an evolving K feature.
