# R12: Real-Rust host architecture

## Question

Should KRS remain a standalone compiler for Rust-parsable source, or should a
KRS definition be a genuine Cargo crate whose procedural macros expand into
ordinary Rust descriptors before lowering through `k-rust`?

The native implementation of the K frontend makes the second option much more
practical, but does not by itself answer questions about Rust type checking,
whole-crate collection, rust-analyzer, macro hygiene, spans, or honest modeling
of K's open and relational semantics.

## Candidate architectures

### A. Standalone KRS compiler

```text
.rs-shaped KRS -> syn/KRS resolver -> KRS IR -> k-rust
```

The source uses Rust outer grammar but need not pass `cargo check`. KRS owns
attributes, macro islands, whole-definition collection, and diagnostics.

Expected advantages: direct control, straightforward global analysis, stable
IR, and no dependence on proc-macro expansion or linker registration.

Expected costs: rust-analyzer reports false errors, K-specific macro interiors
remain opaque, Cargo is not the package/build authority, and “just Rust” is
limited to parsing and visual familiarity.

### B. Rust-hosted KRS declarations

```text
Cargo crate -> KRS proc macros -> ordinary Rust descriptors
           -> whole-definition collection -> KRS IR -> k-rust
```

Attributed items and function-like macros are real Rust macros. Their expanded
form is an explicit Rust descriptor API which passes `cargo check`. A KRS
driver coordinates Cargo, validates the aggregated theory, and invokes the
native K frontend.

Expected advantages: real Rust package/name tooling, rust-analyzer on ordinary
structure, inspectable expansion, one Rust dependency graph, and direct native
handoff.

Expected costs: proc-macro and linker-collection complexity, limited LSP inside
opaque token trees, difficult spans, and a risk that expansions erase the
symbols or types users expect rust-analyzer to navigate.

### C. Two independent source frontends

Both a standalone parser and proc macros independently lower author source.

Reject unless forced. Two semantic frontends are likely to drift on binding,
hygiene, diagnostics, and feature support. Shared parsing libraries do not
remove the duplicate orchestration and conformance burden.

### D. Rust-hosted source with shared KRS analysis

This is the likely refinement of B:

- real macros make the crate acceptable to rustc and expose descriptors;
- macro payload parsers live in ordinary shared crates, not inside the
  `proc-macro` facade;
- the KRS driver/analyzer performs open-sort closure, grammar composition,
  relational checking, target capabilities, and `k-rust` lowering; and
- rust-analyzer handles genuine Rust, while a thin KRS-aware layer handles
  macro interiors and whole-definition semantics.

This preserves one semantic frontend while accepting that rustc cannot prove K
semantics.

## Non-negotiable invariants

Any selected architecture must retain:

1. one authoritative KRS semantic/relational IR;
2. path-independent open-sort closure including diamonds;
3. explicit unordered rule/equation/claim sentence kinds;
4. explicit binder, object-Boolean, matching-logic, framing, and capability
   distinctions;
5. stable package/item identities independent of compilation order;
6. deterministic expansion and `.k` emission;
7. KRS-to-generated-term source provenance; and
8. the same `k-rust` Definition and behavioral equivalence oracles.

Passing `cargo check` is not sufficient if it weakens one of these invariants.

## Decision gates

Prefer D over A only if the prototype demonstrates all of the following:

| Gate | Required evidence |
|---|---|
| G1 Rust validity | Representative attributed sorts, constructors, refutable rules, and macro patterns pass `cargo check`. |
| G2 Honest openness | A real subsort diamond is accepted without reopenable enums, conflicting blanket impls, or path-dependent membership. |
| G3 Global collection | Items from nested modules and dependency crates aggregate deterministically with stable origin paths. |
| G4 Shared semantics | Macro expansion constructs descriptors; whole-definition K semantics remain in one shared analyzer/IR. |
| G5 Native handoff | Aggregated descriptors can produce a structured `k-rust` Definition and KORE artifact. |
| G6 Diagnostics | Invalid relational syntax produces useful invocation-local spans; generated/frontend errors map back to source. |
| G7 Rust tooling | rust-analyzer has no false outer-language errors and provides navigation/completion for ordinary modules, paths, traits, and constructors. |
| G8 Macro tooling | Limitations inside `term!`, `cells!`, and `ml!` are measured and small enough for a thin KRS extension. |
| G9 Inspectability | `cargo expand`/`krs expand` produces stable, comprehensible descriptor Rust. |
| G10 Packaging | Native/portable features and cross-crate builds do not require unstable Rust ABI or compiler-private APIs. |

If G1-G5 or G10 fails, retain A. If only G6-G9 is incomplete, D remains viable
with an explicit KRS editor/tooling work item rather than a promise that Rust
macros alone provide complete LSP behavior.

## Prototype plan

Build a disposable Cargo workspace under
[`../prototypes/rust-hosted/`](../prototypes/rust-hosted/) with:

1. `krs-core`: ordinary descriptor types and deterministic cross-crate
   collection;
2. `krs-macros`: minimal `#[sort]`, `#[constructor]`, and `#[rule]` procedural
   macros;
3. `semantics-lib`: open sorts, a subsort diamond, constructors, and a refutable
   rule in a dependency crate; and
4. `semantics-app`: another module/rule, aggregation, and a structured
   `k-rust` handoff.

Run:

- `cargo check`, `cargo test`, and `cargo clippy`;
- `cargo expand` snapshots;
- accepted and rejected diagnostic fixtures;
- cross-module/crate deterministic-order tests;
- a direct Definition-to-KORE smoke test;
- rust-analyzer project diagnostics and symbol/navigation probes; and
- an explicit coherence counterexample for the tempting blanket-impl encoding
  of transitive subsorting.

## Decision

Select **D: Rust-hosted source with shared KRS analysis**.

A KRS package is a genuine Cargo crate. KRS attributes and item macros are
real procedural macros which preserve or produce rustc-valid declarations and
register ordinary Rust descriptors. A host-built collector deterministically
aggregates those descriptors, and one KRS analyzer computes all global K
meaning before adapting the KRS Definition IR to `k-rust` or `.k`.

```text
Cargo source crate
  -> KRS procedural macros
  -> rustc-valid declarations + explicit descriptors
  -> deterministic host collector
  -> one KRS semantic/relational IR
  -> KRS Definition IR
       |-> structured k-rust Definition -> KORE
       `-> deterministic .k
```

This is meaningfully “real Rust”: Cargo, rustc, rustfmt, Clippy, Rust module
resolution, and rust-analyzer operate on the authored crate. It is not a claim
that Rust's type system supplies K semantics or that the expanded descriptor
program is an executable implementation of the specified language. KRS still
owns open-sort closure, relational binding, grammar composition, sentence
kinds, framing, target capabilities, and source-to-generated provenance.

Architecture A is retained only as a recovery option, not as a second source
frontend. Architecture C remains rejected.

## Prototype

The disposable workspace is
[`../prototypes/rust-hosted/`](../prototypes/rust-hosted/). It contains:

- `krs-core`, with static descriptors, stable origins, a deterministic
  collector, Rust-type references, open-sort analysis, and a provisional
  `k-rust` adapter;
- `krs-macros`, with `#[sort]`, `#[constructor]`, `#[rule]`, and representative
  `term!`, `cells!`, and `ml!` procedural macros;
- `semantics-lib`, containing the `Value -> Expr -> KItem` and
  `Value -> KResult -> KItem` diamond, constructors, a refutable rule, and a
  nested module;
- `semantics-app`, which contributes another constructor and rule, aggregates
  the dependency, computes closure, and compiles structured sentences to
  KORE; and
- rejected-rule, coherence-diamond, and editor-tooling fixtures.

The prototype deliberately keeps descriptors much smaller than the final IR.
It proves the architecture and identity path, not the full KRS surface.

## Results by gate

| Gate | Result | Evidence and remaining qualification |
|---|---|---|
| G1 Rust validity | Pass | The attributed sorts, constructors, refutable rule signatures, and expression macros pass `cargo check`, tests, and Clippy with warnings denied. `#[rule]` consumes the refutable parameter before rustc's irrefutability check while retaining a named Rust item and type references. |
| G2 Honest openness | Pass | The real Rust trait diamond passes. KRS maps rustc-resolved trait-object `TypeId`s to stable sort origins, then computes a deduplicated four-node closure. No blanket membership impl is generated. The counterexample fixture fails with E0119 for the two tempting blanket impls at the diamond join. |
| G3 Global collection | Pass | `inventory` collects dependency-crate, root-crate, and nested-module registrations. KRS ignores linker order and sorts by package/module/item origin. A semantic dependency must be linked; the production driver should generate an explicit host collector root for selected theory facets rather than rely on incidental Rust use. |
| G4 Shared semantics | Pass | Macros emit declarations and descriptors only. Open-sort closure and cross-item validation occur once in `krs-core`. Production payload parsers must move into an ordinary `krs-syntax` crate shared by the proc-macro facade, analyzer, formatter, and editor layer. |
| G5 Native handoff | Pass | Aggregated constructor/rule descriptors become structured `Sentence` and `Term` values, enter `compile_loaded_definition`, and produce reparsable KORE containing `foo` and `bar`. Like R11, the smoke adapter uses a parsed bootstrap configuration because `k-rust` v0.3 lacks a public structured preparation entry point. |
| G6 Diagnostics | Partial, non-blocking | An invalid rule points exactly at the `_` pattern with a macro-owned explanation. Careful token-span preservation also supports navigation. The prototype does not yet attach origin stacks to analyzer or `k-rust` diagnostics; the production IR/source-map work remains required. |
| G7 Rust tooling | Pass | rust-analyzer 1.97.1 reports no project diagnostic and the LSP probe resolves ordinary supertraits, imports/completion, attribute paths, rule sort paths, constructor patterns/bodies, dependency items, and ordinary references. |
| G8 Macro tooling | Pass for Rust-expression payloads; extension required for K syntax | `term!`, `cells!`, and `ml!` payloads parsed as Rust expressions retain go-to-definition when each source token is emitted exactly once. K-specific balanced token grammars cannot receive native Rust binding/type semantics and still need a thin KRS editor layer. |
| G9 Inspectability | Pass with a dedicated view required | Two `cargo expand` runs had identical SHA-256 `6c879255a03726fe0790cc17cb9f05d43fba36494e117e2f9fe41ae4929fd510`. The rule descriptor is direct and readable, but recursively expanded `inventory` machinery is noisy. `krs expand` should stop at the descriptor/reference surface. |
| G10 Packaging | Pass with collector constraints | The host workspace and cross-crate tests use stable Rust only, `k-rust` with default features disabled, and no compiler-private API or dynamic Rust ABI. Both the semantics library and native app pass `cargo check --target wasm32-unknown-unknown`. `inventory` documents a Wasm constructor caveat; KRS should execute a host collector and treat direct target-side inventory as optional. |

The critical gates G1-G5 and G10 pass. The partial source-map work in G6 and
the K-specific part of G8 are editor/compiler implementation tasks, exactly as
the decision rule allowed; they do not justify giving up genuine Cargo/Rust
hosting.

## Important findings

### Rust paths can be authoritative without Rust subsorting

Stringifying `Expr` is not sufficient because equal spellings in different
modules can denote different traits. Conversely, serialized `TypeId` values
are not stable public identities. The useful combination is:

1. generated descriptors carry a rustc-resolved type-key function for a sort
   trait or constructor type;
2. collection uses that key only within the current host build to join
   references to declarations; and
3. KRS replaces the temporary key with the declaration's stable
   package/module/item identity before serialization or hashing.

This lets rustc resolve paths and catch missing items while KRS remains the
authority for semantic membership and closure.

### Expansion spans are part of the macro ABI

rust-analyzer navigation became reliable only when an authored token was
mapped into exactly one meaningful expansion position. Repeating the same
source-spanned path in a descriptor, a hidden type check, and `stringify!`
made navigation ambiguous or intermittent. Generated duplicate uses must have
call-site spans, while exactly one type-checking use retains the source span.

The production macro helpers need golden LSP tests, not only token snapshots
and `trybuild` diagnostics.

### Link-time inventory is a prototype mechanism

The experiment proves stable whole-crate aggregation is possible without
rustc internals. It does not commit KRS forever to `inventory`. The permanent
collector must support selected definition facets, cfg/features, explicit
dependency retention, host execution during cross compilation, and source
provenance. An explicit generated collector crate or linker registration are
both compatible with the chosen architecture because descriptors and the KRS
analyzer boundary remain unchanged.

### rust-analyzer is strong, not omniscient

The actual LSP navigation/completion probe passes. The unstable
`rust-analyzer unresolved-references` batch subcommand in version 1.97.1
panics inside its next-solver code even on the isolated tooling fixture; this
is a rust-analyzer CLI defect and is not reproduced by `cargo check`, project
diagnostics, or the LSP requests. It should not be used as the KRS editor gate.

Rust-expression macro payloads can retain normal navigation. Once a payload
uses K-only binders, rewrites, cell notation, or associative patterns, the
Rust server sees an opaque token tree. KRS should augment those islands rather
than promise that procedural macros make a foreign grammar native to
rust-analyzer.

## Production requirements implied by the decision

1. Keep `krs-syntax`, KRS semantic/relational IR, Definition IR, and analysis
   in ordinary libraries. The `proc-macro` crate is a narrow facade.
2. Make Cargo the crate graph, module, feature, and dependency authority. Put
   KRS facet/target metadata under Cargo metadata and keep only external K/raw
   artifact pins in a supplemental KRS lock if Cargo cannot represent them.
3. Generate an explicit host collector for the selected definition facet. Do
   not depend on an unused Cargo dependency being retained by accident.
4. Resolve Rust type keys to stable KRS item identities before building the
   serializable IR. Never persist or compare raw `TypeId` values across builds.
5. Treat source-span discipline as tested public macro behavior.
6. Provide `krs check` for whole-definition semantics and `krs expand` for the
   clean descriptor/reference form; Cargo/rustc cannot replace either.
7. Keep `.k` emission and the R8 differential oracles beside the native
   `k-rust` path.
