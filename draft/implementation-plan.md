# KRS implementation plan

This is the dependency-ordered build plan for the architecture selected in
[R12](investigations/r12-rust-host-architecture.md). The
[design](design.md) remains the language contract and the
[research backlog](research-backlog.md) remains the detailed validation ledger.
This document answers a narrower question: what should be built, in what
order, and what evidence permits work to proceed to the next stage?

## Target outcome

The first useful release is not “all of K in Rust notation.” It is an explicit,
rustc-valid IMP definition which:

1. is an ordinary Cargo package with working rust-analyzer navigation;
2. produces one resolved KRS semantic IR from proc-macro descriptors;
3. emits deterministic, inspectable `.k`;
4. lowers the same Definition IR through `k-rust` to KORE;
5. reports host, KRS, and frontend errors at authored source locations; and
6. matches the pinned reference semantics in parsing and execution.

Ergonomic macro selection begins only after that explicit reference definition
passes. The first release may be verbose; it may not be semantically ambiguous.

## Build order

```text
M0 contracts and workspace
  -> M1 real-Rust descriptor/collector path
  -> M2 smallest dual-lowering definition
  -> M3 explicit IMP vertical slices
  -> M4 complete IMP equivalence gate
  -> M5 package/toolchain hardening
  -> M6 corpus-driven ergonomic macros
```

Diagnostics, source maps, determinism, and editor probes are not a final
polish phase. Each milestone extends them alongside its language surface.

The existing validation queue maps onto these milestones as follows:

| Milestone | Backlog work absorbed |
|---|---|
| M0-M1 | V0A and the identity/span portions of V6 |
| M2 | V0 plus the smallest end-to-end part of V1 |
| M3-M4 | V1-V3 and the IMP portions of V5/V8 |
| M5 | V4-V8 package, builtin, diagnostic, parity, and capability work |
| M6 | V9 |

## Initial workspace

Start with the fewest crates that preserve the required dependency direction:

```text
Cargo.toml
crates/
  krs/             # author-facing facade, Term types, host registration
  krs-macros/      # narrow proc-macro facade
  krs-syntax/      # shared attribute and macro-payload parsers
  krs-ir/          # descriptors, stable IDs, semantic IR, Definition IR
  krs-compiler/    # collection validation, resolution, analysis, .k emission
  krs-k-rust/      # versioned adapter to the pinned native frontend
  krs-cli/         # collector orchestration and user commands
tests/
  ui/              # accepted/rejected macro fixtures
  lsp/             # rust-analyzer protocol probes
  definitions/     # smoke and IMP Cargo packages
```

Do not create separate crates for every IR pass initially. Split a crate only
when a real dependency cycle, portability boundary, or independently versioned
API requires it.

The dependency direction is strict:

```text
krs-macros -> krs-syntax + krs-ir
krs        -> krs-ir + krs-macros
krs-compiler -> krs-ir + krs-syntax
krs-k-rust -> krs-ir + pinned k-rust
krs-cli    -> krs-compiler + krs-k-rust
author crate -> krs
```

`krs-macros` must not depend on `krs`, and no IR crate may depend on the CLI or
`k-rust`.

Examples retain the design's author-facing `k::` path even if the published
Cargo package is named `krs`. Macro expansion must discover the actual facade
crate name so normal Cargo dependency renaming continues to work.

## Interfaces to freeze early

### Host descriptor versus compiler IR

Keep two representations visibly separate:

- `HostDescriptor` is static, rustc-valid registration data. It may contain a
  function which obtains a build-local `TypeId` for joining a Rust path to its
  declaration.
- `DescriptorBundle` is deterministic and serializable. It contains only
  stable package/module/item IDs, parsed payload data, cfg state, and source
  provenance. It never contains `TypeId`, function pointers, linker order, or
  Rust ABI values.
- Resolved semantic IR contains KRS meaning: sort closure, constructor
  membership, bindings, grammar relations, cells, sentence kinds, and effects.
- Definition IR contains source-level K sentences and terms ready for either
  the `.k` emitter or `k-rust` adapter.

The collector is the only component allowed to convert `HostDescriptor` into
`DescriptorBundle`. The compiler never analyzes linker registrations directly.

### Stable identity

Every declaration receives a structured identity resembling:

```text
PackageId + module path + item name + item kind + disambiguator
```

The exact encoding is versioned, but these rules apply immediately:

- Rust type keys are used only to resolve paths within one host process.
- `PackageId` is derived from locked semantic namespace and Cargo package
  identity, never an absolute checkout path.
- Serialized identities never include a raw `TypeId` or address.
- Moving a private item may change an internal ID without changing public
  symbols unless the design explicitly says the move is breaking.
- Duplicate short names in different modules and packages are legal and must
  be covered by the first collector tests.
- Generated K labels are derived in one documented pass, never independently
  by the `.k` and `k-rust` adapters.
- Source file IDs use normalized package-relative paths plus content identity;
  machine-specific workspace prefixes never enter reproducible artifacts.

### Source provenance

Use an origin stack rather than one optional span:

```text
authored token range
  -> attribute or function-like macro invocation
  -> generated descriptor field
  -> semantic IR node
  -> Definition IR sentence/term
  -> frontend diagnostic or generated artifact range
```

The first implementation must settle how byte ranges survive stable proc
macros. If stable span APIs cannot serialize the needed ranges, reparse the
authored file for provenance using the same `krs-syntax` parsers and match it
to descriptor identities. That is a provenance pass, not a second semantic
frontend.

### Collector protocol

`krs-cli` generates a small host-only collector Cargo package under the target
directory. It:

1. depends on every package selected by the definition facet;
2. explicitly references each dependency so linker retention is intentional;
3. uses the exact selected Cargo features and KRS cfg values;
4. resolves build-local Rust type keys to declaration registrations;
5. validates and deterministically sorts the bundle; and
6. writes a versioned canonical JSON `DescriptorBundle` to stdout while logs
   remain on stderr.

The collector is built for the host even when the defined language is destined
for another platform. Its protocol is data, not a dynamic Rust library ABI.
Keep the registration mechanism behind this protocol so `inventory` can later
be replaced without changing semantic IR.

### Command contract

The initial commands have distinct responsibilities:

| Command | Contract |
|---|---|
| `cargo check` | Validate the Rust host, proc-macro expansion, Rust paths, and ordinary Rust items. |
| `krs check` | Run `cargo check`, collect descriptors, and validate the complete KRS theory and selected target capabilities. |
| `krs expand` | Print stable descriptor/reference Rust without recursively exposing linker-registration noise. |
| `krs emit-k` | Emit the canonical descriptor, semantic, Definition IR, `.k`, symbol-map, and source-map projections. |
| `krs build` | Compile the same Definition IR through the native `k-rust` frontend and produce KORE artifacts. |

No command silently falls back from native lowering to another frontend. The
reference frontend is invoked only by explicit differential-test tooling.

## M0: Production skeleton and contract spikes

### Scope

Promote architectural seams, not prototype code. Establish the workspace,
schema versions, identity types, provenance model, and native adapter boundary
before adding language breadth.

### Deliverables

- Root Cargo workspace with formatting, Clippy, tests, and minimum supported
  Rust version in CI.
- `krs-ir` definitions for `ProtocolVersion`, `StableItemId`, `SourceFileId`,
  `SourceRange`, `OriginFrame`, `HostDescriptor`, and `DescriptorBundle`.
- Deterministic serialization golden for an empty bundle and a hand-built
  sort/constructor/rule bundle. Canonical JSON is the initial inspectable
  collector protocol; a binary encoding is unnecessary before measurements
  justify it.
- A focused stable-proc-macro span probe covering an attribute argument, a
  refutable parameter, a nested pattern token, and a macro payload token.
- A narrow `krs-k-rust` wrapper around the exact commit and K pin from R11.
- A tracked upstream/API task for structured Definition preparation in
  `k-rust`; the local wrapper may use the R11 bootstrap only behind a clearly
  provisional function.
- Written invariants for every conversion between host descriptors, semantic
  IR, Definition IR, and `k-rust` types.

### Exit gate

M0 is complete when:

- descriptor serialization is byte-for-byte deterministic;
- two same-spelled items in different modules have distinct stable IDs;
- no serialized value depends on `TypeId`, pointer identity, or iteration
  order;
- the source-range approach can recover every token in the span probe; and
- `krs-k-rust` is optional and `krs-ir` builds without native solver features.

If precise nested ranges cannot be recovered, stop adding macros and resolve
the provenance design. Sentence-only source locations are not enough.

## M1: Real-Rust authoring and collection

### Scope

Implement the smallest production-quality host surface: sort declarations,
constructor declarations, and one simple rule shape. Reproduce R12 without its
hard-coded short-name or incidental-linking assumptions.

### Deliverables

- `#[k::sort]` on marker traits, including multi-parent diamonds.
- `#[k::constructor(sort = Path, syntax = "...")]` on unit and record
  structs.
- `#[k::rule]` on one refutable parameter and one result term.
- Rust-expression `term!` support sufficient for named constructors; K-only
  pattern grammar remains deliberately small.
- Shared payload parsers in `krs-syntax`; the proc-macro crate performs parsing
  and code generation but no global K analysis.
- Rename-safe facade path generation, including Cargo dependency renames.
- Generated host collector driven by `cargo metadata` and definition metadata.
- Conversion of build-local Rust keys to stable IDs before bundle output.
- Deterministic collection across root crates, dependency crates, nested
  modules, features, and backend cfg values.

### Test matrix

- Passing `cargo check`, rustfmt, and Clippy fixtures.
- `trybuild`-style rejected fixtures for wrong attribute placement, missing
  paths, duplicate declarations, malformed rule signatures, and invalid
  payloads.
- Diamond closure and the E0119 blanket-impl counterexample.
- Same short sort/constructor names in two modules and two dependency crates.
- A dependency selected only through the generated collector, proving explicit
  link retention.
- Repeated collection under randomized source/dependency ordering, producing
  identical bundle bytes.
- LSP diagnostics, completion, go-to-definition, rename, and hover probes for
  every authored path retained through expansion.
- Span goldens that ensure each authored token maps to one meaningful
  expansion use.

### Exit gate

M1 is complete when an external sample Cargo package depends only on the
author-facing `krs` crate, passes ordinary Rust tooling, and produces the same
resolved `DescriptorBundle` on repeated clean builds. No `.k` output is needed
yet, but no unresolved names or closure computation may be deferred to an
adapter.

## M2: Smallest dual-lowering definition

### Scope

Build one tiny executable theory through the complete architecture. Use the
R11/R12 `foo => bar` semantics or an equally small counter language; do not
start with full IMP.

### Minimum language surface

- `KItem`, `KResult`, and one object sort.
- Two zero-argument constructors with concrete syntax.
- One `<k>` configuration cell and initializer.
- One unconditional transition rule.
- Sentence and term origins on every generated node.

### Deliverables

- Semantic analysis for declared sorts, membership, rule root/result sorts,
  duplicate symbols, and the selected configuration.
- Minimal Definition IR for modules, imports, syntax sorts, productions,
  configuration, and rules.
- Canonical `.k` emitter with deterministic formatting.
- Structured `k-rust` adapter for the same Definition IR nodes.
- Initial implementations of `krs check`, `krs expand`, `krs emit-k`, and
  `krs build`.
- Symbol map and source map sidecars shared by both lowering routes.

### Oracles

1. Emitted `.k` parses with the pinned reference frontend.
2. Native lowering returns reparsable `definition.kore` and
   `syntaxDefinition.kore`.
3. Parsing the emitted `.k` through `k-rust` and using the structured adapter
   produce equivalent normalized source definitions where comparable.
4. Native and reference KORE sentence multisets match after documented
   normalization.
5. The transition executes from `foo` to `bar` on at least one backend.
6. An induced sort or rule error points back to the exact authored token.

### Exit gate

M2 is the first hard architecture gate. Do not broaden grammar, configuration,
or macro syntax until the same collected bundle passes both lowering routes
and one real execution. Any difference must be explained as an explicit
frontend capability, never papered over by route-specific semantic IR.

## M3: Explicit IMP vertical slices

### Scope

Port IMP in small end-to-end increments using only the explicit reference
surface. Each increment extends both lowering routes and all applicable
oracles.

### Slice A: Expressions and object grammar

- token sorts and lexical precedence;
- record and enum constructors;
- production groups, precedence, associativity, brackets, and strictness;
- arithmetic and Boolean builtins; and
- parser accept/reject and unparse round trips.

Gate: representative IMP programs have the same parse trees through emitted
`.k` and the structured/native route.

### Slice B: Configuration and state

- nested fixed cells and initializers;
- `KSequence`, `Map`, and configuration field types;
- assignment and variable lookup; and
- explicit cell framing with source-local diagnostics.

Gate: initialization and straight-line assignment traces match the reference
definition on the selected concrete backend.

### Slice C: Control flow and evaluation

- sequencing, conditionals, loops, and evaluation contexts;
- guarded rules with `Term<Bool>` conditions;
- strict/seqstrict lowering and generated contexts; and
- bounded search result comparison.

Gate: representative terminating and branching programs match final states and
bounded-search frontiers.

### Slice D: Static and verification forms

- total/partial functions and equations;
- simplification, aliases, context aliases, and explicit priorities;
- matching-logic patterns and binders needed by IMP claims; and
- the first proof claims on the Haskell backend.

Gate: function behavior, normalized claims, and proof outcomes match the
pinned reference.

### Cross-cutting requirement

Every new construct must land as a complete vertical change:

```text
shared parser -> descriptor -> semantic IR -> Definition IR
              -> .k emitter + k-rust adapter
              -> diagnostics + expansion + oracle fixture
```

A surface form is not complete if only one lowering route understands it.

## M4: Complete IMP equivalence and v0.1 gate

### Scope

Replace the incremental fixtures with a complete modern IMP port and run the
full R8 oracle stack.

### Required evidence

- Descriptor bundle, semantic IR, Definition IR, `.k`, expansion, symbol map,
  and source map snapshots are deterministic.
- Accepted/rejected program corpora and unparse results match.
- Normalized parsed/source definition structures match where frontend models
  are comparable.
- Native and pinned reference KORE match structurally within the documented
  compatibility policy.
- Concrete execution traces and final states match.
- Bounded-search result sets and constraints match.
- Selected proof claims have the same status and normalized terminal/frontier
  constraints.
- Moving a private item and a public item exercises the documented stable-name
  compatibility behavior.
- Diagnostics are tested at Rust expansion, KRS analysis, K frontend, and
  backend boundaries.

### v0.1 definition of done

v0.1 may be called usable when:

1. the complete explicit IMP package is rustc-valid and navigable;
2. `krs check`, `expand`, `emit-k`, and native `build` are reproducible;
3. native and source paths pass the agreed equivalence gates;
4. failures map to authored source with no raw generated-path requirement for
   ordinary debugging;
5. Cargo metadata and supplemental K toolchain locking reproduce the build;
   and
6. unsupported native/backend features fail as typed capability diagnostics.

Ergonomic convenience macros are not part of this definition of done.

## M5: Package and toolchain hardening

This work starts with minimal forms earlier but is release-gated after IMP:

- multi-package definition facets and explicit theory composition;
- generated collector caching and invalidation;
- public versus internal syntax roots and generated K module visibility;
- pinned builtin registry generation and signature checks;
- raw `.k` FFI packages with content hashes;
- LLVM/Haskell capability matrix;
- kdist/pyk target descriptors and artifact parity;
- cross-host builds and Wasm collector/embedding behavior; and
- stable diagnostic codes and machine-readable output.

Exit when a clean checkout can reproduce the same artifacts through the CLI
and kdist bridge, and when package composition never depends on lexical `use`
or accidental linker retention.

## M6: Corpus-driven ergonomic macro study

Preserve the explicit IMP port as the reference branch. Introduce one
candidate macro at a time and compare the actual source diff while keeping the
semantic IR and R8 oracles unchanged.

Start with repeated patterns which are likely to produce real clarity:

- multi-cell framing;
- families of near-identical rules/equations;
- configuration construction; and
- repeated grammar boilerplate.

For every candidate, measure semantic visibility, binding clarity, source
reduction, diagnostics, formatting, grep/rename behavior, expansion
readability, and rust-analyzer behavior. Retain it only when explicit KRS versus
macro-using KRS is a clear readability win. User-defined semantic macros remain
deferred.

## Continuous quality gates

These run from the first milestone where they are meaningful:

| Layer | Required check |
|---|---|
| Rust host | fmt, check, Clippy with warnings denied, MSRV, doc tests |
| Macro UI | accepted/rejected fixtures and stable invocation-local spans |
| Editor | diagnostics, definition, completion, rename, hover, macro payload navigation |
| Collection | clean-build determinism, duplicate-name disambiguation, explicit dependency retention |
| IR | schema/version checks, deterministic serialization, invariant/property tests |
| `.k` | canonical text snapshot, parse, normalized source-structure comparison |
| Native | portable `k-rust` compile, KORE parse, capability errors |
| Behavior | parser corpus, execution, search, and proof oracles as surface grows |
| Packaging | Cargo lock, supplemental KRS lock, cross-target and clean-checkout reproduction |

CI should report which layer failed. A generic “K compilation failed” result is
not an acceptable interface once source mapping exists.

## Immediate implementation queue

The first three reviewable changes should be:

1. **Workspace and contracts:** create the production workspace, `krs-ir`
   identity/provenance/protocol types, deterministic bundle serialization, and
   the focused span probe.
2. **Host surface and collector:** add `krs-syntax`, the thin proc macros,
   facade registration, generated host collector, diamond/duplicate-name/UI
   fixtures, and the LSP probe.
3. **Dual-lowering smoke:** add minimal configuration/rule Definition IR,
   canonical `.k`, the `k-rust` adapter, CLI commands, source maps, and the
   `foo -> bar` execution/equivalence gate.

Each change leaves the workspace green and produces an inspectable artifact.
The third change is the checkpoint at which beginning the explicit IMP port is
justified.

## Explicitly deferred

Do not put these on the critical path to the first IMP release:

- a custom Rust parser or rustc compiler plugin;
- general user-defined semantic macros;
- a new K backend or direct KORE generation;
- removal of `.k` emission or the reference differential path;
- every K attribute before it appears in IMP or a scheduled stress corpus;
- a full standalone language server instead of a thin macro-island extension;
- dynamic Rust plugin ABIs; and
- readability macros chosen without an explicit before/after corpus diff.

These can be revisited after M4 without changing the descriptor, semantic IR,
or Definition IR boundaries established by M0-M2.
