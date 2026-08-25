# Investigation ledger and validation queue

The design investigations are complete. Their conclusions are consolidated in
[design.md](design.md); the reports below preserve evidence, alternatives, and
target experiments.

The dependency order, workspace shape, and milestone exit criteria are in the
[implementation plan](implementation-plan.md).

## Completed investigations

| ID | Topic | Result |
|---|---|---|
| R1 | [Rust parser boundary](investigations/r1-parser-boundary.md) | Stock Rust outer grammar plus typed attribute and macro islands; no parser fork. |
| R2 | [Open sorts](investigations/r2-open-sorts.md) | Marker traits plus a compiler-closed, path-independent subsort relation; enums remain closed. |
| R3 | [Rule surface](investigations/r3-rule-surface.md) | One independent refutable function clause per rule; reject the `Option<State>` ABI. |
| R4 | [Object grammar](investigations/r4-object-grammar.md) | Nominal syntax attributes plus typed grammar item macros. |
| R5 | [Configuration and framing](investigations/r5-configuration-framing.md) | Nested structs, nominal cell wrappers, and compiler-owned path-independent framing macros. |
| R6 | [Lowering boundary](investigations/r6-lowering-boundary.md) | Own a K Definition IR and emit `.k` through the stock frontend; do not target Kore directly. |
| R7 | [Symbolic logic and claims](investigations/r7-symbolic-logic.md) | Separate object terms, object Boolean conditions, and ML patterns; explicit binders and bottom. |
| R8 | [Equivalence oracle](investigations/r8-equivalence-oracle.md) | Layered structural, parser, execution, search, and proof differential tests. |
| R9 | [Evaluation and static forms](investigations/r9-evaluation-and-static-forms.md) | Typed strictness, contexts, static clauses, `k::fun`, and global function context all fit; `anywhere` is not Haskell-portable. |
| R10 | [Modules, builtins, and toolchain](investigations/r10-modules-builtins-toolchain.md) | Lexical Rust imports, explicit theory facets, pinned sysroot builtins, deterministic generated modules, and kdist integration. |
| R11 | [Native `k-rust` integration](investigations/r11-k-rust-frontend-integration.md) | Add a structured native frontend adapter while retaining KRS IR and portable `.k` emission. |
| R12 | [Real-Rust host architecture](investigations/r12-rust-host-architecture.md) | Use genuine Cargo crates and proc-macro descriptors feeding one shared KRS analyzer; Rust paths are authoritative, Rust trait closure is not. |

## Implementation-validation queue

These are bounded prototype or equivalence tasks. They can refine surface
punctuation, validation rules, or emitter organization, but none requires a
new language-model investigation before implementation begins.

### V0A: Harden the real-Rust host boundary

Promote the R12 prototype into ordinary `krs-syntax`, `krs-ir`, `krs-core`,
and narrow `krs-macros` crates. Generate an explicit host collector for each
selected definition facet so semantic dependencies cannot disappear through
linker dead-code elimination. Resolve build-local Rust type keys to stable
package/module/item identities before serialization.

Golden-test proc-macro expansion, invocation diagnostics, and rust-analyzer
navigation. Enforce the one-source-token/one-mapped-expansion-use span rule.
Decide between linker registration and an explicit generated registry only
after testing host collection during cross compilation and Wasm embedding;
that mechanism must not leak into semantic IR.

### V0: Qualify the `k-rust` Definition adapter

Add a converter from KRS Definition IR to `k_rust::definition::Definition` and
an invariant-preserving preparation API around the v0.3 frontend. Pin commit
`58f33885b736148dae189623d1aac989ce9be475` with K 7.1.337. Extend the direct
R11 probe to configurations, contexts, overloaded and parametric terms,
collection cells, binders, and both backend selections.

Keep `.k` emission enabled and compare its meaning with native lowering. A
missing native feature must be an explicit capability result: native build
fails, while source emission may remain available. Do not add a frontend axis
to semantic targets and never silently switch implementations, drop, or
reinterpret a sentence.

### V1: End-to-end IMP slice

Implement enough of the proc-macro descriptor surface, shared semantic IR,
Definition IR, `.k` emitter, and source map to compile the checked-in
IMP-shaped sample. Then port the full modern IMP grammar, configuration,
rules, functions, contexts, and proof claims. Run every R8 oracle layer at the
pinned K version.

This is the release-blocking synthesis test and should happen before adding
more surface conveniences.

### V2: Pattern-island grammar

Freeze and implement the payload grammars for `term!`, `k!`, `cells!`,
`fragment!`, `list!`, `set!`, `map!`, `cell_set!`, `cell_list!`, and
`cell_map!`. Cover multiple entries, keyless map selection, symbolic
construction, legal remainder positions, and formatter behavior.

Keep the Rust-expression subset as real expression procedural macros so
rust-analyzer can navigate it. For K-only binders, rewrites, cells, and
associative patterns, expose the same shared payload parser through a thin KRS
editor layer; do not claim rust-analyzer understands a foreign token grammar.

### V3: Configuration frontend edge cases

At the pinned K release, golden-test input-dependent initializer defaults,
optional and repeated cell initialization, fully filled versus partial
`SortCells` fragments, and collection-cell construction/removal. Turn the
accepted subset into KRS validation with source-local diagnostics.

### V4: Generated module and facet fixture

Compile a two-package fixture containing public program syntax, public
administrative terms, private constructors, and dependency rules. On LLVM and
Haskell, verify that generated direct/private imports parse all rules, expose
only `syntax-root`, compose the chosen theory, and never make lexical `use`
semantically active. Port IMP's parser, executable, library, and verification
facets to decide whether `root` plus features needs an explicit `compose` list.

### V5: Pinned builtin registry

Generate reviewed bindings for `BOOL`, `INT`, `MAP`, `LIST`, `SET`, `BYTES`,
`STRING`, `K-EQUAL`, and `ML-SYNTAX`. Compare their source signatures and
attributes with parsed KAST, and compile at least one use of every exposed
operation on every claimed backend.

### V6: Symbols, diagnostics, and packaging

Verify deterministic public symbols, rule labels, predicates, projections,
list terminators, and initializer names across source moves which should or
should not be breaking. Exercise K-to-KRS diagnostic rewriting. Link one raw K
package by content hash, induce module/symbol collisions, and diagnose both
origins before backend execution.

### V7: kdist/pyk parity

Build one target through `krs build` and the generated kdist bridge. Require
identical normalized sources and compiled artifacts, and verify that pyk can
consume the generated target descriptor, symbol map, and source map.

### V8: Backend capability matrix

Probe typed attributes and binders across LLVM and Haskell, especially
`anywhere`, set variables, unbound universals, fresh generators, hooks,
symbolic/concrete filters, and raw attributes. A missing capability must be a
KRS error or explicit cfg boundary; it must never silently weaken a sentence.

### V9: Corpus-driven ergonomic macro study

Run this only after V1 produces a complete, explicit KRS port of IMP. Preserve
that port as the reference branch, then introduce one candidate built-in macro
at a time and inspect the actual source diff. Every candidate must expand to
the same resolved semantic IR and pass the unchanged R8 parser, execution,
search, and proof oracles.

Evaluate candidates on more than line count:

- whether the semantic operation becomes easier to recognize at a glance;
- whether bindings, frames, sentence kind, and unusual quantifiers remain
  visible;
- reduction in repeated syntax and simultaneous reduction in local context;
- quality and locality of diagnostics;
- ease of grep, rename, formatting, and expansion review;
- readability of small rules as well as repeated large patterns; and
- whether Rust-familiar humans and agents infer the intended behavior without
  learning an unrelated mini-language.

The comparison should include the hand-written K source, explicit KRS, and
macro-using KRS, but the decisive diff is explicit KRS versus macro-using KRS.
Retain a macro only where the latter is a clear readability win. Implement
built-ins through the shared parser plus the existing procedural-macro facade
and provide a deterministic descriptor-level `krs expand` view. General
user-defined semantic procedural macros remain a later design question.

Likely areas to test include repeated multi-cell framing, families of similar
rules/equations, grammar boilerplate, and configuration construction. Do not
pre-approve macros which hide sentence kinds, binder kinds, target capability
boundaries, or the `Term<Bool>`/`MlPattern` distinction.

## Deferred feature design

The following features may remain behind a diagnostic or `raw_k!` for v1:

- recursive matching-logic aliases and matching-mu fixed points;
- fresh variables on equations, simplifications, or claims;
- automatic totality, termination, confluence, or simplifier-soundness proofs;
- backend-independent execution of set or unbound-universal variables;
- broad `BagCells`, streams, and external cell composition support;
- a version-pinned outer-KAST JSON emitter;
- general user-defined semantic procedural macros;
- removing `.k` emission or the reference differential path before the native frontend has a
  stable compatibility record.

These deferrals do not weaken the core IR: bottom, binder kinds, sentence
kinds, source spans, and target capabilities remain explicit from the start.
