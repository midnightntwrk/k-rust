# Project charter

## Problem

K is powerful, but its authoring language is unfamiliar to most software
engineers and to many coding agents. Rust is unusually well represented in
both communities and model training data. A Rust-shaped notation could make K
definitions easier to write, review, generate, and maintain without replacing
K's execution and proof infrastructure.

KRS is a language for **semantics authors**. It is not a compiler that gives
ordinary Rust programs K semantics automatically, and it is not a new rewrite
engine.

## Goal

Given a KRS definition, produce the same kind of definition that could have
been authored in `.k` files, preserving enough source information that K
parse, compilation, execution, and proof diagnostics can point back to KRS.

The ideal experience is:

- structs, enums, traits, modules, imports, functions, patterns, and attributes
  mean what a Rust reader expects whenever that expectation is compatible with
  K;
- every deliberate deviation is small, visually explicit, and documented;
- K-specific concepts remain expressible rather than being hidden behind an
  attractive but incomplete Rust analogy; and
- generated output remains usable by the existing K and pyk ecosystem.

## What “like Rust” means

“100% exactly like Rust” is a direction, not a literally attainable property:
Rust describes deterministic executable programs over closed nominal types,
while K describes rewrite theories over open term sorts and symbolic patterns.
We should track compatibility in separate dimensions instead of treating it as
one binary claim.

1. **Lexical and grammatical compatibility.** Use ordinary Rust tokens and
   item forms. Supported KRS source is a genuine Cargo crate whose KRS
   attributes and item macros expand before rustc checks relational forms.
2. **Name and type compatibility.** Modules, visibility, generics, structs,
   enums, traits, and patterns should follow Rust rules unless a documented K
   capability requires otherwise.
3. **Behavioral compatibility.** An ordinary `fn` or `match` should be
   deterministic and ordered. Relational behavior must be marked with
   `#[k::rule]`, `#[k::claim]`, or similarly conspicuous notation.
4. **Diagnostic compatibility.** Reuse Rust terminology and error shapes where
   the underlying condition is genuinely analogous.
5. **Tool compatibility.** Rust formatting, Cargo, rustc, Clippy, macro
   expansion, and rust-analyzer are part of the supported host experience.
   K-only macro interiors additionally require KRS-aware editor support.

The compatibility promise should eventually be stated construct by construct.
“Rust-shaped” must never imply Rust behavior where K behaves differently.

## Design principles

### Semantic honesty over surface purity

Use a K-specific attribute or macro when ordinary Rust syntax would cause a
competent Rust reader to infer the wrong behavior. Nondeterministic rules are
the clearest example.

### Open-world features use open-world Rust concepts

K syntax sorts can be extended by imported modules. Attributed Rust traits
have the right declaration shape; attributed constructors add membership to a
KRS-owned open relation. Rust blanket impl closure does not work at legal
subsort diamonds, so the Rust trait solver is not the semantic authority.
Enums remain closed and are never silently reopenable.

### Small explicit core, library-defined convenience

The compiler should understand a limited semantic core: sorts, productions,
configurations, patterns, rewrites, equations, contexts, claims, attributes,
and modules. Builtins, collection APIs, and common strategies should live in a
versioned standard library as much as practical.

### Lossless access to K

K evolves, and mature definitions use backend- or project-specific attributes.
KRS needs typed support for common features plus a clearly marked raw escape
hatch. Unsupported features should not force authors to abandon KRS or wait for
a compiler release.

### Inspectable lowering

The lowering pipeline should preserve stable item/rule labels and source spans.
During bootstrap, generated `.k` is a useful debugging and differential-testing
artifact. The compiler architecture should still target a structured K
definition IR so it is not permanently coupled to K's pretty-printed syntax.

### Validate against real semantics early

IMP is the first completeness test, but not the design ceiling. KWasm tests
open syntax and grammar scale; KMIR tests modern symbolic rules and large data
models; KEVM tests attributes, proof performance, and ecosystem integration.

## Proposed compilation shape

```text
KRS source
  -> Cargo/rustc + KRS procedural macros
  -> rustc-valid declarations and descriptors
  -> deterministic host collector
  -> KRS typed/relational IR
  -> K definition IR
       |-> structured k-rust Definition -> Rust K frontend -> Kore
       `-> generated .k -> any compatible K frontend -> Kore
  -> existing backends
```

KRS does not generate Kore directly. On the native route, `k-rust` performs
the important desugarings and validations for grammar, cells, strictness,
collections, macros, and generated predicates. The `.k` route defers that work
to whichever compatible K frontend consumes the artifact. Native build may
become the default after qualification; generated `.k` remains useful for
inspection, ecosystem interchange, and differential testing. The current Java
frontend is one reference consumer, not a KRS target.

## Initial scope

An MVP should be able to translate the modern IMP semantics and run the same
programs through K. That requires:

- modules, `use`, visibility, and builtin imports;
- open sorts, closed data types, constructors, tokens, and subsorts;
- concrete syntax metadata, precedence, associativity, and formatting;
- one hierarchical configuration with initial values;
- rewrite rules over one or several cells, side conditions, and rule labels;
- strict/sequential evaluation and `KResult` membership;
- deterministic total and partial helper functions; and
- a raw attribute escape hatch.

The next compatibility tier adds collection cells and patterns, arbitrary
contexts, macros/aliases, simplification lemmas, fresh/existential variables,
symbolic constraints, and reachability claims.

## Non-goals for the first implementation

- Reimplementing a K backend, prover, or pyk.
- Accepting arbitrary Rust programs as semantics definitions.
- Preserving Rust ownership, borrowing, layout, or runtime performance
  semantics in the metalanguage.
- Hiding all K terminology. Users will still need to understand rules,
  configurations, symbolic terms, and claims.
- Proving the compiler correct before a useful differential-testing oracle
  exists. A correctness story is a later goal, not an excuse to skip a clear IR
  and deterministic lowering now.

## Early success criteria

1. A KRS port of IMP compiles and has equivalent parse and execution behavior
   on a shared corpus.
2. Reordering independent `#[k::rule]` items does not change semantics unless
   an explicit priority says it should.
3. A new module can add a result type or instruction family without editing
   the module that declared `KItem`, `KResult`, or the parent syntax sort.
4. Generated K names and errors map back to stable KRS paths and spans.
5. Every K feature used by the chosen IMP corpus is either modeled explicitly
   or rejected with a specific diagnostic—never silently dropped.
