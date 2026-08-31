# Coverage review

## Review method

The first inventory was produced by a Sol lead coordinating two Terra scouts.
One scout traced public compiler and test surfaces; the other traced normative syntax, examples, and pedagogical dependencies.
The lead reconciled both reports against the current semantics ports and their coverage ledger.

A separate Sol pass then reviewed the resulting `tour.toml` and `roadmap.md` adversarially.
The review looked for current constructs that were absent, planned constructs presented as current, incorrect teaching dependencies, stale sources, and examples whose claimed tool workflow does not exist.

## Findings incorporated before adversarial review

### The historical result syntax is not tour syntax

`draft/readability/result/README.md` says its specimens do not compile and are superseded.
The plan now uses `draft/readability/spec/` for idiomatic syntax and M4 for executable evidence.

### Repeated cells are not wholly unsupported

The current parser and KEVM port support nested repeated cells with `multiplicity = "*"` and `cell_type = "Bag" | "List" | "Map" | "Set"`.
The ledger marks that bounded form `qualified` and separately marks optional cells and other multiplicities unsupported.

### Numeric priority is not a transition-rule ordering mechanism

Readable transition rules are unordered; overlap is a static error and `owise` is the explicit fallback form.
The public `#[k::priority(N)]` helper is for equations, while simplifiers have their own optional `#[k::simplification(priority = N)]` payload.
Simplification priority remains marked unqualified until a positive authored macro fixture joins its parser and lowering evidence.

### The CLI does not run object programs

The current commands are `fmt`, `check`, `expand`, `emit-k`, and `build`.
Execution, search, and proof examples must identify the generated K/KORE consumer or the repository harness and must not invent `krs run`.

### Large ports are qualification evidence, not completeness claims

KWasm, KMIR, and KEVM remain incremental ports.
The plan treats `semantics/coverage.toml` as the status authority and uses small extracts only for language-scale constructs.

### One-path claims lack the same positive evidence as all-path claims

The claim grammar accepts `one_path`, but scouting found no positive end-to-end specimen comparable to M4's all-path corpus.
The ledger marks it `unqualified` until a fixture establishes the intended backend path.

### Rust Twoslash is not yet a fail-closed documentation gate

The inspected Vocs pin can warn and skip missing tools, ignore subprocess failures or diagnostics, reuse an incomplete cache key, break relative Cargo paths in temporary projects, and disable proc-macro expansion.
Phase 2 now requires negative controls for every failure class and keeps fixture `cargo check` authoritative.

## Mechanical audit

The current ledger parses as TOML and has:

- 17 uniquely ordered chapters;
- 68 unique concepts;
- only declared status and coverage values;
- only existing chapter and prerequisite references;
- no prerequisite assigned to a later chapter;
- 135 evidence paths, all present in the working tree.

The public procedural-macro facade was compared with the ledger and planned reference index.
Every public macro or attribute entry point is routed to a narrative concept or the required macro index.

## Adversarial disposition

The following rules are release blockers for the eventual tour:

1. No page may source idiomatic syntax from `draft/readability/result/`.
2. No planned semantic-gap item may be shown as supported without current public API and positive evidence.
3. Every qualified feature must state its exact supported shape beside the first example.
4. Every KRS code block must be backed by a compiling fixture or a deliberate pinned negative fixture.
5. Rust Twoslash may demonstrate Rust-visible behavior but may not substitute for KRS semantic collection and lowering.
6. No example may imply source-ordered rule selection, host execution of builtin calls, `Option`-style partiality, or a `krs run` command.
7. The feature index and limitations page must be generated from or mechanically checked against `tour.toml`.

## Residual risks for implementation

- A documentation-specific IMP split could drift semantically from M4 unless parity is a build gate.
- A mutable local Vocs symlink would make the site non-reproducible; the dependency must be pinned.
- Rust Twoslash has less visibility inside KRS token-tree islands than ordinary rust-analyzer positions.
- Backend availability is distinct from source acceptance and must remain visible in example metadata.
- Open design questions must be linked from the boundaries page rather than silently answered by tutorial prose.

## First-slice audit

The independent follow-up audit accepted the ledger's completeness and dependency ordering, then tightened the executable contracts for the opening pages:

- `tour-minimal` is explicitly a scaffolded idiomatic whole-definition preview; each previewed construct is still introduced formally in its later chapter;
- its parity gate now has a concrete semantic projection, emitted-K, execution, and source-provenance contract;
- configuration metadata is split between fixed leaf cells and nested-cell fields;
- authored traps are documented as ordinary object-language states rather than a special KRS construct;
- composition and explicit-layer claims cite positive end-to-end fixtures; and
- the unordered-rule negative control requires a structured overlap diagnostic with an authored span rather than stderr matching.

The integrated implementation audit accepted that work as a planning and bootstrap slice rather than a release-ready site.
The minimal fixture now loads the M2 source for the bounded sort/terminal/configuration/transition projection and verifies authored `sources.json` attribution, but pinned backend execution is still capability-gated and did not run locally.
The site now carries a Bun lockfile, and a clean frozen install, TypeScript check, and full Vocs production build pass with the pinned Waku compatibility version.
Rust Twoslash remains opt-in: the preflight is fail-closed and resolves the same package binary as Vocs, but the current upstream transformer still disables the procedural-macro expansion required by the generated-symbol probe.

## Full-tour and synthesis audit

A second Sol-led, Terra-executed audit reviewed the completed 17-route tour for API accuracy and pedagogical coverage before the five-minute synthesis was promoted.
It found and the implementation corrected:

- hook signature validation is now assigned to post-collection Definition-IR checking, while unknown hook paths remain macro-expansion errors;
- `--package-id` is documented as a root-only disambiguator;
- public-symbol, cross-family grammar, anonymous-value, Boolean-disjunction, configuration-variable, formatting, and fallback spellings are indexed exactly;
- token and typed-hook examples now come from the compiling positive macro fixture;
- the site gate now compiles that fixture, the M1 base/root composition packages, and KEVM in addition to the minimal and M4 fixtures; and
- all canonical pages declare their ledger concepts, while the checker also compares the public macro and builtin-operation exports with the language reference.

The five-minute page was changed only after those corrections.
Its 14 required concepts, one-sentence hover/focus glosses, and canonical destinations are generated from `tour.toml`.
Publication fails if the synthesis marker, component annotations, generated data, sidebar state, or destination pages drift.

The post-audit production gate passes curriculum validation, route/link checks, snippet freshness, five compiler-backed fixture checks, TypeScript checking, and a full Vocs build.
The subsequent completion pass added dedicated `tour-imp` and `tour-composition` gates, a complete IMP capstone and checked four-layer lowering walkthrough, a five-case authored-span negative matrix, generated port summaries, proof-capability evidence, page-graph and generated-artifact freshness checks, a `Krs.lock` compatibility baseline, terminology and component-accessibility audits, public-surface review pins, and CI.
The overlap diagnostic is now structured as `overlapping-rule-heads` and selects exactly the second authored head.

Residual limitations remain visible: minimal-theory backend execution is capability-gated, Rust Twoslash cannot yet see proc-macro-generated symbols, one-path claims and simplification priority remain unqualified, and the automated gloss checks do not replace a final real-browser assistive-technology review.

## Final release audit

A final Sol-led adversarial pass found four release gaps and one sequencing inconsistency, all closed before the final gate:

- the CI workflow now uses Bun 1.3.13's actual `bun install --cwd …` and `bun run --cwd …` argument order;
- the reference and claims chapters state that `id!`, `bytes!`, and `or_bool!` are claim-only and that `anonymous!` is subject-only;
- the orientation chapter now includes a source-synced rule excerpt, its checked emitted transition, and the owning fixture command;
- the composition fixture emits with and without `tour_mode=extended` and requires the cfg-gated production only in the configured artifact; and
- the primary navigation and narrative links put the five-minute synthesis after all 17 canonical chapters, with a checker that prevents it moving earlier.

The cfg evidence exposed and fixed a compiler integration defect: the generated collector's Cargo process did not run from the directory containing its generated `.cargo/config.toml`, so Cargo ignored KRS cfg rustflags.
The composition gate is now the regression test for that behavior.
