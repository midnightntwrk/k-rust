# KRS language-tour roadmap

## Outcome

The first published tour should take a Rust-literate reader from a two-constructor rewrite theory to the complete IMP definition, then add KRS's static-semantics, verification, composition, and language-scale features.
The reader should finish able to author, inspect, format, check, emit, and build a KRS definition without mistaking symbolic KRS constructs for executing Rust.

The tour should be comprehensive by routing every `tour.toml` concept to one of three destinations:

- the linear tour for concepts needed to build a useful language;
- the reference for catalogs and explicit compatibility forms;
- the boundaries page for qualified, open, and unsupported surfaces.

## Decisions made by this plan

### Use claim-specific authority

`draft/readability/spec/imp.rs` is authoritative for idiomatic spelling of the implemented IMP surface, and its executable counterpart is `tests/m4/rust-definition/src/imp.rs`.
Current public API and tests decide whether a construct is supported.
Design decisions supply rationale only when they agree with that implementation evidence.
Conflicts must be reported rather than silently resolved in favor of any one document.
`draft/readability/result/` is valuable design history, but its own README says its examples do not compile and were superseded.

### Retain the small theory as a later synthesis

The compact synthesis specimen is the M2-sized `foo -> bar` theory.
It combines symbolic terms, a computation cell, initialization, and one unordered rule without requiring the size of IMP.
This is a scaffolded whole-definition preview: it names the roles of sorts, constructors, configurations, initializers, K sequences, and rules, while their syntax and full contracts remain formally introduced in the later chapters recorded by `tour.toml`.

During implementation, write the dependency-ordered full tour before finalizing this synthesis page.
Keep the compiling specimen as an early integration fixture, but withhold the page from primary navigation until every previewed name has a canonical concept destination.
The final quick tour may use short hover glosses or linked annotations, but those explanations must be generated from or checked against the same concept ledger rather than maintained as a second glossary.

The primary tour should establish the package workflow and then grow IMP monotonically through the existing M3 slices:

1. expressions and grammar;
2. evaluation and expression rules;
3. statements, state, and maps;
4. conditionals, blocks, and loops.

The complete IMP file is the first capstone, not the first listing.

### Separate operational, static, and proof clauses

Transition rules, equations, simplifiers, aliases, contexts, and reachability claims have different meanings even when they share a refutable-function shape.
The tour must introduce them in separate chapters and compare them explicitly.

### Teach current status as part of the language

Every feature example must carry a visible status when it is not fully current:

- `current` means implemented and positively evidenced;
- `qualified` means a bounded supported shape whose limits are stated beside it;
- `reference` means supported explicit syntax that is not the idiomatic first spelling;
- `unqualified` means accepted surface without an end-to-end positive specimen;
- `open` and `unsupported` must never appear as usable syntax.

This is especially important for repeated cells, one-path claims, hooks, matching logic, optional cells, and large semantics ports.

## Information architecture

The initial site should use the following navigation.
Individual bullets are pages; grouped pages may be combined during writing only if all page outcomes remain independently testable.

### Start here

- What KRS defines
- The five-minute theory
- Create a definition package
- The edit, format, and check loop

### Build IMP

- Open sorts and values
- Constructor families and syntax templates
- Brackets, precedence, and associativity
- Strictness and evaluation results
- Expression rules and symbolic builtins
- Statement grammar, formatting, and `avoid`
- Configurations and declarative initialization
- Computation sequences and control flow
- Maps and simultaneous machine rules
- Framing, narrowing, and overlap
- Complete IMP

### Understand applicability and failure

- Object-Boolean `requires`
- Explicit fallback with `owise`
- Normal forms, stuck terms, traps, and backend capability errors
- Reading diagnostics and source ranges

### Inspect the compilation

- Readable layer 1 and explicit layer 2
- Definition IR and emitted K
- Native KORE artifacts
- Stable identities and source maps

### Add static semantics

- Total and partial functions
- Equations and numeric equation priority
- Static aliases
- Named evaluation contexts
- Simplification lemmas

### Verify semantics

- Reachability and path modalities
- Preconditions and postconditions
- Existential and anonymous values
- Circular claims
- Proof capability boundaries

### Scale and compose

- Nested cells and fragments
- Repeated cell collections
- Bytes, List, and Set
- Typed hooks
- Multiple packages and definition facets
- cfg values, backends, and stable symbols
- What KWasm, KMIR, and KEVM currently qualify

### Reference

- Attribute and macro index
- Builtin sort and operation index
- Pattern and term-island grammar
- Explicit/reference surface
- CLI and artifact index
- Diagnostic stages

### Boundaries

- Restricted Rust inside KRS declarations
- Qualified and unqualified features
- Open design questions
- Unsupported and future concepts

## Page contract

Every narrative page should contain:

1. one sentence stating what semantic problem the construct solves;
2. the smallest compiling idiomatic layer-1 example;
3. a plain-language account of what the example means;
4. one important Rust analogy and the point where that analogy stops;
5. one observable check, emitted fragment, execution trace, or diagnostic;
6. links to the relevant reference entries and the next dependent page.

Every page introducing syntax should also name:

- whether source order matters;
- whether the construct is host Rust, a checked KRS island, or generated output;
- which names are inferred and which provide stable identity;
- what failure looks like when the construct is ill-formed or inapplicable.

The prose should use semantic line feeds.
Long, repeated mappings such as builtin operations and feature status should live in TOML and be rendered or checked from that structured source.

## Example strategy

### One source of truth

Published snippets must originate in compiling fixtures rather than being copied independently into MDX.
The build should either import source regions directly or verify extracted snippets against their owning files.

Create three documentation fixtures:

1. `tour-minimal` for the two-constructor orientation;
2. `tour-imp` for the monotonically accumulated IMP chapters;
3. `tour-composition` for a multi-package, multi-facet composition example.

The existing M4 source remains the semantic authority for `tour-imp`.
The documentation fixture may split it into modules for pedagogy, but a parity test must compare its collected semantic theory or emitted K with the M4 authority.

### Minimal-theory parity

`tour-minimal` is idiomatic layer 1, while the external M2 Rust fixture is an explicit/reference specimen.
Their source text should not match, but the fixture gate must compare the semantic projection that the page teaches:

- the object sort and membership edges;
- the `foo` and `bar` productions;
- one computation cell initialized to the single item `foo`;
- exactly one `foo => bar` transition;
- the canonical emitted-K sentence multiset;
- `foo -> bar` execution under the pinned M2 consumer; and
- source-map attribution to `tour-minimal`, not copied M2 provenance.

### Positive and negative examples

Each syntax-bearing chapter should have:

- at least one positive compile/check gate;
- at least one focused negative example with a pinned diagnostic class and authored span;
- `krs fmt --check` over authored KRS files;
- an expansion or emission assertion when lowering is the lesson.

The orientation's unordered-rule negative control uses two overlapping `Foo` heads.
The CLI now emits schema-1 analysis code `overlapping-rule-heads` with the exact authored range of the second head, and the focused negative gate rejects diagnostic or range drift.

The first orientation negative matrix should also cover a missing wrapper-free `#[k::cell]`, forbidden initializer control flow, a constructor omitted from the exhaustive precedence chain, and a corrupted rule RHS mapped back to its authored token.

Claims, repeated cells, hooks, and composition require their own positive fixtures because IMP does not cover them all.
One-path reachability must remain marked unqualified until such a fixture passes the intended backend gate.

### Do not fake execution

The current KRS CLI exposes `fmt`, `check`, `expand`, `emit-k`, and `build`.
It does not expose `krs run`.
When the tour shows execution, search, or proof, it must name the generated K/KORE consumer or the checked repository harness instead of inventing a KRS command.

## Vocs implementation

The local Vocs checkout at `/home/sebastiengllmt/git/workspaces/starstream-fv/vocs` is a strong fit for the first site:

- it supports MDX, navigation, code groups, callouts, steps, search, and static generation;
- the checked-out V2 branch includes experimental Rust Twoslash backed by rust-analyzer;
- its Rust transformer can use a selected Cargo manifest, which suits documentation fixtures;
- its Shiki pipeline can focus, highlight, diff, and collapse relevant source lines.

The Vocs checkout is heavily in progress, so the integration must pin a reproducible commit or package artifact before the documentation site becomes a release gate.
Do not make the KRS repository depend on an unrecorded mutable symlink.
The initial inspected pin is Vocs commit `4d36250650f46aaef319c14f74aeea47279dd036` with Vocs 2.8.5 and `@vocs/twoslash-rust` 0.1.0; selection of that pin is provisional until the fail-closed spike passes.

### Proposed site layout

The bootstrap selected a standalone top-level `docs-site/` application with:

```text
docs-site/
  package.json
  tsconfig.json
  vocs.config.ts
  scripts/
  src/
    pages/
    snippets/
```

It remains outside the root Cargo workspace, which currently includes only `crates/*`.
The authoritative Rust examples live in standalone fixtures under `tests/`; the site mirrors their named source regions and fails when a mirror is stale.

### Rust Twoslash boundary

Use Rust Twoslash for ordinary Rust-visible positions such as imports, sort aliases, constructor fields, and generated item types.
Do not treat Twoslash as the semantic validator for KRS macro islands.
The KRS collector, compiler, formatter, and existing LSP probes remain authoritative for rule-table, cell-record, map, sequence, and term-island semantics.

For each code block, choose one of:

- ordinary highlighted Rust for a conceptual excerpt;
- Rust Twoslash for rustc/rust-analyzer-visible behavior;
- a checked fixture plus captured output for KRS semantic behavior;
- an explicit generated-output block for layer 2, K, IR, or diagnostics.

### Avoid an interactive playground in v1

Browser execution would require shipping or remotely hosting a large, pinned K toolchain and resolving backend capability and resource limits.
The first version should favor deterministic examples, expandable generated artifacts, and trace visualizations.
An interactive runner is a later product decision, not a documentation bootstrap requirement.

## Build roadmap

### Phase 0: freeze the curriculum ledger

Deliverables:

- review and accept `tour.toml` as the coverage contract;
- decide which unqualified features are promoted by new tests and which remain on the boundaries page;
- assign an owner and positive evidence target to every `current` and `qualified` concept;
- add a check that all concept IDs are unique, prerequisites resolve, chapters exist, and every chapter order is unique.

Exit gate:

- the adversarial review has no unclassified current public macro, attribute, builtin family, CLI command, or configuration shape.

### Phase 1: build executable teaching fixtures

Deliverables:

- minimal theory fixture;
- a structural parity gate showing that the minimal fixture has the same sort edges, terminals, initial configuration, and `foo -> bar` transition as the M2 authority;
- split IMP teaching fixture with semantic parity to M4;
- multi-package composition fixture;
- authored token, `owise`, stable symbol, nested/repeated cell, Bytes/List/Set, typed-hook, and claim variants not naturally covered by IMP;
- focused negative examples for the major Rust/KRS semantic boundaries.

Exit gate:

- fixtures pass Cargo checking, KRS checking, formatting, deterministic collection, and the proportional emission/backend gates recorded beside each example.

### Phase 2: bootstrap Vocs

Deliverables:

- pinned Vocs dependency or commit;
- site package, navigation, theme, search, and deployment-neutral build;
- Rust Twoslash configured against the documentation Cargo manifest;
- source-region or snippet-verification pipeline;
- CI jobs for site build, links, snippets, Twoslash cache generation, and KRS fixture gates.
- a negative-control Rust block whose intentional error fails CI;
- an unavailable or broken Rust-Twoslash binary test that fails CI rather than warning and skipping;
- cache invalidation that includes the selected Cargo manifest, lockfile, tool versions, and relevant source inputs;
- a manifest strategy that preserves relative path dependencies;
- an explicit probe of proc-macro expansion and generated KRS item visibility.

Exit gate:

- the site builds offline from declared inputs after caches and pinned dependencies are prepared;
- no page contains an unverified KRS code block.
- Rust-Twoslash spawn failure, nonzero exit, invalid output, diagnostics, and missing binaries are fatal in CI;
- fixture `cargo check` remains authoritative even if Rust Twoslash succeeds.

### Phase 3: publish the orientation and IMP spine

Deliverables:

- Start here pages;
- all Build IMP pages;
- applicability and failure pages;
- the complete IMP capstone;
- one readable-to-expanded-to-K walkthrough.

Exit gate:

- a new reader can reproduce a checked and emitted IMP definition by following the pages in order;
- the capstone remains semantically equivalent to the M4 authority.

### Phase 4: publish static semantics and verification

Deliverables:

- functions, equations, priorities, aliases, contexts, and simplifiers;
- reachability claim pages and proof-capability matrix;
- distinct outcome examples for undefined partial functions, stuck states, explicit traps, and backend rejections.

Exit gate:

- all M4 static adjunct and proof constructs are indexed and positively linked from the tour;
- no page implies that `Option`, host Boolean evaluation, or Rust function execution models K partiality or symbolic conditions.

### Phase 5: publish scale, composition, and reference

Deliverables:

- bounded nested/repeated-cell walkthrough;
- builtin catalog generated from or checked against the registry;
- composition and stable-identity walkthrough;
- macro, attribute, pattern, CLI, artifact, and diagnostic references;
- current coverage summaries for KWasm, KMIR, and KEVM generated from or checked against `semantics/coverage.toml`.

Exit gate:

- every `current`, `qualified`, and `reference` concept in `tour.toml` has a published destination;
- large-port pages state their incomplete status and adapter boundaries.

### Phase 6: harden the documentation release gate

Deliverables:

- broken-link and orphan-page checks;
- concept-to-page coverage check;
- stale-source detection for snippets and generated artifacts;
- accessibility and mobile-navigation pass;
- search-term audit for K terminology and Rust analogies;
- version banner and compatibility matrix tied to `Krs.lock`.

Exit gate:

- changing an author-facing macro, CLI command, builtin registry member, or feature status fails a documentation check until the ledger and affected pages are reviewed.

## Review questions requiring a human decision

The build can begin with the defaults below, but these choices should be confirmed before Phase 2 ends:

1. Is the primary audience strictly Rust-literate semantics authors, or must the tour teach the required Rust subset too?
   Default: assume comfortable Rust reading, explain macro-specific deviations only.
2. Should the published site present K terminology immediately or reveal it after the first theory?
   Default: name K concepts immediately and pair each with a plain-language gloss.
3. Should generated K be a recurring second tab or appear only in lowering/reference pages?
   Default: show it on the first occurrence of each sentence kind, then link to expansion views.
4. Is documentation released with KRS itself or continuously from the main branch?
   Default: version the language pages with KRS and allow unversioned design-history material separately.
5. Should unqualified one-path claims be promoted for v1 of the tour?
   Default: keep them visibly unqualified until a positive end-to-end fixture exists.

## Current implementation status

The complete linear tour is authored at all 17 canonical chapter routes, followed by a generated-gloss five-minute synthesis.
Five dedicated documentation fixtures cover the minimal theory, the byte-identical M4 IMP capstone and chapter slices, deterministic two-package composition with dual cfg-value artifacts, authored negative diagnostics, and proof/static outcome evidence.
The IMP gate also derives a checked readable → explicit → descriptor → emitted-K walkthrough from one rule.

The focused negative matrix pins overlap, missing-cell, initializer-control-flow, exhaustive-precedence, and rule-result failures to authored tokens.
Static/proof documentation includes a backend × claim-form capability matrix and four separately owned outcomes.
KWasm, KMIR, and KEVM summaries are generated from `semantics/coverage.toml`, while the release baseline is generated from `Krs.lock`.

The production gate now covers the curriculum, reviewed public surfaces, complete page graph and anchors, generated artifacts, terminology, gloss keyboard/mobile/reduced-motion contracts, all documentation fixtures, TypeScript, and Vocs production output.
A CI workflow reconstructs the pinned native-frontend workspace before running the same gate.

Residual work is explicit rather than silently passing:

1. pinned execution for `tour-minimal` remains capability-gated rather than mandatory on every machine;
2. Rust Twoslash remains supplementary and disabled by default because upstream still hides generated procedural-macro symbols;
3. one-path claims and simplification priority remain unqualified pending positive end-to-end fixtures; and
4. a real-browser assistive-technology pass should complement the checked component/CSS accessibility contract before a public release.

The full-tour-first sequencing is enforced in primary navigation; future edits to the five-minute synthesis should continue to derive unfamiliar-term disclosure from the canonical ledger.
