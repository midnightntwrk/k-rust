# R11: Native integration with `k-rust`

## Decision

Add a native `k-rust` frontend adapter without replacing KRS's own semantic and
K Definition IRs. Keep deterministic `.k` emission as the standard source
artifact. The pinned current K implementation is a differential consumer of
that artifact, not a target selected by KRS authors.

The intended architecture becomes:

```text
KRS source
  -> KRS CST and resolved semantic/relational IR
  -> KRS source-level K Definition IR
       |-> k-rust Definition adapter -> k-rust frontend passes -> KORE
       `-> canonical .k emitter
             `-> any compatible K frontend -> KORE
  -> existing LLVM/Haskell backends
```

The native adapter should become the preferred development path after it
passes the full IMP and feature-capability gates. It should not become the only
path while `k-rust` is an evolving v0.x frontend. KRS itself still does not
generate KORE or reimplement frontend passes. It either invokes the native
frontend or emits the K source definition for an ecosystem frontend.

Do not replace KRS Definition IR with `k_rust::definition::Definition`. The
latter is a very useful adapter target, but it follows one frontend's internal
source model and compatibility ordering. KRS still needs stable source-level
identities, Rust paths, typed KRS attributes, macro provenance, target-neutral
capabilities, and the ability to compare native lowering with the meaning of
the emitted `.k`.

## Why this changes R6

R6 found no complete supported structured authoring boundary in pyk or the
Java frontend. Its recommendation to emit `.k` was correct for those APIs.
`k-rust` adds the missing boundary:

- a public flat `definition::Definition` containing modules, imports, syntax
  sentences, configurations, contexts, rules, and claims;
- public structured `kast::Term`, `Sort`, `Label`, and term metadata;
- public definition resolution, catalogs, relations, checks, configuration
  expansion, inner parsing, and individual compilation passes; and
- `kompile::compile_loaded_definition`, which runs the ordered K frontend
  pipeline and returns `definition.kore`, `syntaxDefinition.kore`, and
  `macros.kore` in memory.

This is not direct KORE generation by KRS. It is a native Rust implementation
of the same semantic frontend boundary which R6 wanted to preserve.

## Checkout inspected

The inspected checkout is:

```text
repository: github.com/midnightntwrk/k-rust
commit:     58f33885b736148dae189623d1aac989ce9be475
version:    0.3.0
date:       2026-08-18
license:    BSD-3-Clause
K pin:      7.1.337 / 4a46d1231473b599c699160132fd6e76a5c46406
```

It contains about 39,856 lines of Rust implementation and 12,867 lines of
top-level Rust tests. The portable local gate exposed 438 tests and all passed:

```console
cargo test -p k-rust --no-default-features --locked
```

The default-feature build compiled Rust code but failed while linking the
downloaded static Z3 archive against this host's older C++/glibc runtime. That
is a packaging/host-toolchain issue, not a failed frontend test. It matters to
KRS: native Z3/MPFR support must be an explicit target capability, and portable
builds cannot compile the full bundled prelude when rule ambiguity requires
Z3.

## Existing compatibility evidence

The repository reports and tests substantially more than a parser skeleton:

- 1,499 of 1,504 pinned upstream `.k` files accepted by the outer parser; the
  five exclusions match malformed or already-rejected reference fixtures;
- K outer and Markdown loading, `requires`, module imports, locations, grammar,
  configurations, rule bubbles, user lists, records, and casts;
- an Earley/chart object-language parser with scanner precedence,
  associativity, ambiguity factoring, and sort inference;
- KAST text/JSON v4 and KORE text/JSON ASTs and printers;
- configuration expansion and ordered passes for strictness, contexts,
  anonymous `#fun`, function configuration, macros, fresh values, projections,
  predicates, cell concretization, and sort injection;
- KORE emission for normal rules, claims, functions, `owise`, simplification,
  `anywhere`, macros, aliases, reachability, overloads, and generated axioms;
- a structural KORE differential corpus against the pinned Java/Scala
  frontends; and
- real Haskell and LLVM backend smoke scripts.

Its coverage closely matches the exact K features which forced KRS to retain a
frontend boundary. Reusing those passes is much safer than either reproducing
them or making KRS-generated text the only integration mechanism.

## Direct structured-AST probe

[`r11-k-rust-direct-probe.rs`](r11-k-rust-direct-probe.rs) demonstrates the
important boundary. It:

1. lets `k-rust` prepare a minimal configuration;
2. injects a constructor and transition rule as structured
   `definition::Sentence` and `kast::Term` values;
3. reconstructs the resolved module graph;
4. calls `compile_loaded_definition` for LLVM;
5. parses both returned KORE definitions; and
6. confirms that the directly injected symbols reached KORE.

The probe passes against the portable library build:

```text
direct structured Definition -> KORE probe passed
```

Only the small bootstrap configuration is parsed from K text because the
current public API has no `prepare_definition(Definition, ...)` entry point.
The injected constructor and rule never pass through K's source parser. This
proves the essential adapter is viable while also exposing the API work needed
for a clean integration.

## Recommended adapter boundary

Translate KRS Definition IR into `k_rust::definition::Definition`, not its
outer source AST and not its KORE AST.

| KRS Definition IR | `k-rust` target |
|---|---|
| sort declaration or synonym | `Sentence::SyntaxSort` / `SortSynonym` |
| nominal or grammar production | `Sentence::Production` |
| precedence or associativity relation | `SyntaxPriority` / `SyntaxAssociativity` |
| configuration schema/initializer | `Sentence::Configuration` with structured `Term` |
| transition/equation/static rule | `Sentence::Rule` with structured rewrite and typed attributes |
| context/context alias | `Sentence::Context` / `ContextAlias` |
| reachability claim | `Sentence::Claim` |
| object term/pattern | `kast::Term` |
| KRS source identity | source/location attributes plus the KRS sidecar |

KRS should construct already-resolved rule terms rather than emitting `Bubble`
strings. This skips the K inner parser for KRS-authored clauses while retaining
all later checking and lowering passes. Generated `.k` exercises the parser on
the differential path and catches any mismatch between the structured adapter
and the textual meaning.

`definition::json` is useful for tests but not an adequate primary boundary:
KAST JSON v4 cannot represent `ContextAlias`, and JSON deliberately omits some
compiler term metadata. In-process Rust types are the stronger interface.

## API and integration work required

The v0.3 API is close but not yet ideal. KRS should either contribute or carry
a narrow versioned adapter for an entry point resembling:

```text
prepare_definition(
    definition: Definition,
    backend: CompilationBackend,
    builtin_provider: ...,
) -> Result<LoadedDefinition, ...>
```

or a `compile_definition` which performs preparation and compilation in one
call. It needs to expose the invariant-preserving equivalents of:

- sort-synonym application;
- backend module filtering;
- default-configuration and MAP imports;
- configuration expansion;
- optional bubble resolution for mixed raw K dependencies; and
- final `ResolvedDefinition` construction.

Constructing `LoadedDefinition` through its public fields, as the probe does,
is suitable evidence but too easy to get subtly wrong as the permanent API.

Overloaded and parametric applications need special attention. `TermMetadata`
can carry a catalog-scoped `ResolvedProductionId` and explicit sort, and later
sort injection/KORE conversion uses it. KRS has enough origin and sort data to
select the production, but the adapter needs a supported way to attach or
rebase that identity after the complete module catalog is known.

## Source maps and diagnostics

`k-rust` already has renderer-independent diagnostic codes and sentence-level
source/location attributes. Nested terms can retain byte spans and resolved
production identities through many frontend transformations.

It does not remove the need for KRS's source map:

- parsed nested spans are currently relative to the inner source fragment;
- the README lists absolute nested-source remapping as TODO;
- generated KRS terms and ergonomic macro expansions need origin stacks, not
  just one K location; and
- stable Rust paths and KRS-specific diagnostics are outside the K frontend.

The native adapter should attach KRS source/location attributes wherever they
remain meaningful and retain a sidecar from every generated sentence/term ID
to its KRS span and macro-expansion origin. Native `DiagnosticCode` values can
then be translated without scraping Java diagnostic text.

## Builtins and packaging

`k-rust` bundles the exact K 7.1.337 builtin sources behind a portable
`builtin::embedded` provider. KRS should reuse this closure for the matching
frontend pin rather than ship a second byte-for-byte copy. The typed
`k::builtin` sysroot remains a KRS API generated from and checked against those
modules and `k-rust` catalogs.

`Krs.lock` should pin as one compatibility unit:

- KRS compiler/Definition IR schema;
- exact `k-rust` crate version and commit;
- exact K source/builtin pin used by that crate;
- reference K/pyk pin used by differential tests; and
- backend versions.

Until stable releases prove otherwise, a KRS update must not float across
`k-rust` commits merely because the Cargo semver range permits it.

## Current limitations relevant to KRS

1. The project is v0.3 and its documented current scope stops at KORE artifacts;
   Haskell and LLVM backends and `krun`/`kprove` orchestration remain external.
   A possible future Rust backend should not be assumed in KRS's v1 design.
2. There is no clean public structured-Definition preparation entry point yet.
3. Absolute nested source mapping and some provenance warnings remain TODO.
4. Manually built parametric applications can require explicit production
   metadata which the source parser normally supplies.
5. The KORE emitter explicitly rejects existential variables in equations,
   macro claims, and `owise` claims. Native build must reject those until
   supported, while `.k` emission can still represent them for another
   compatible frontend.
6. The optional Haskell unsafe-`anywhere` removal pass is intentionally absent.
   KRS should keep its stricter policy of rejecting `anywhere` for Haskell
   rather than allowing a backend to discard it.
7. Native Z3/MPFR features add a substantial linker/platform boundary. The
   portable library works but reports `Z3InferenceRequired` where the native
   inference path is semantically necessary.

These limitations justify capability negotiation between native build and
source emission; they do not undermine the native architecture. Build targets
select LLVM or Haskell semantics, not a frontend implementation. Differential
testing can explicitly invoke the pinned reference K toolchain, but that is a
compiler-development operation rather than part of the language target model.

## Qualification gates

Before making `k-rust` the default frontend, require:

1. a public invariant-preserving structured Definition entry point;
2. the full KRS IMP port compiled natively and emitted as `.k`;
3. equality of normalized parsed/source definition structure where comparable;
4. structural KORE multiset comparison between the pinned reference frontend
   and Rust-native artifacts;
5. identical parser corpus, execution, bounded search, and proof outcomes;
6. explicit capability diagnostics for every unsupported KRS sentence/binder;
7. source-map tests through contexts, strictness, macros, cells, and generated
   rules;
8. overloaded, parametric, open-sort-diamond, and collection-cell fixtures;
9. LLVM and Haskell backend smoke tests consuming native artifacts; and
10. locked native and portable build profiles, including a documented Z3
    toolchain strategy.

Once these gates pass, `.k` remains a user-visible expansion/debug artifact and
compatibility fallback rather than the mandatory path for every normal build.

## Consequences for the macro roadmap

The native Definition AST gives ergonomic KRS macros a particularly strong
oracle: explicit KRS and macro-using KRS must lower to identical KRS IR and
then identical `k-rust` Definition values before any frontend pass runs.
`krs expand` can still print the canonical explicit KRS and generated `.k`.

Do not confuse KRS authoring macros with K's static `[macro]`/`[alias]` rules or
with `k-rust`'s `expand_macros` pass. The former elaborate the KRS source; the
latter are sentences inside the authored K theory.

## Sources inspected

- root README, Cargo manifests, license, notice, and recent commit history;
- public `definition`, `kast`, `outer`, `inner`, `kompile`, `kore`, builtin,
  and diagnostic APIs;
- the complete ordered compilation driver and individual frontend passes;
- configuration, rules, strictness, contexts, functions, macros, freshness,
  sort-injection, and KORE-emission tests;
- KAST/KORE JSON limitations and source-metadata handling;
- structural reference differential and backend smoke infrastructure; and
- the local portable test suite and the direct structured-AST probe.
