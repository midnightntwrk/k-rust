# KRS authoring surface — normative spec

**This folder is the implemented outcome of the readability investigation (`draft/readability/`, docs 00–16, concluded 2026-08-21).**
If you are extending the authoring layer, this folder is the contract; read the sibling deliberation documents only to chase a rationale citation.
They record superseded intermediate forms and are not implementation instructions.

## The deliverable

`imp.rs` is the compiling layer-1 **authoring surface**.
It expands deterministically through `krs expand` to the exact layer-2 **reference surface** in `imp.expanded.rs`, and the M4 gate proves that this route drives the same K semantics as the reference IMP definition.
`krs fmt` is the co-delivered formatter that enforces the canonical authoring layout from F1/F5–F7.

| File | Status | Role |
|---|---|---|
| [`imp.rs`](imp.rs) | **normative, implemented** | the authoring surface that authors write and review |
| [`imp.expanded.rs`](imp.expanded.rs) | **generated reference** | the byte-exact reviewed `krs expand` projection |
| [`decisions.md`](decisions.md) | **normative** | every settled decision as an implementable rule (A architecture, B sorts, C grammar, D configuration, E rules, F tooling) |
| [`open-questions.md`](open-questions.md) | **normative** | what is deliberately undecided — surface these, never resolve them silently |

Precedence on conflict: `imp.rs` > `decisions.md` > everything else.
A conflict is a bug in this folder and must not be interpreted around.

## Implementation status

The readable IMP surface is implemented in `crates/krs-macros`, `crates/krs-syntax`, `crates/krs-compiler`, `crates/krs-fmt`, and `crates/krs-cli`.
The production acceptance specimen is `tests/m4/rust-definition/src/imp.rs`.

- `k::sorts!` generates the selected `<Sort>Sort` membership trait plus the short `Term<dyn <Sort>Sort>` alias, with bracket and membership declarations from B1–B4.
- The syntax-first grammar surface, exhaustive enum precedence chains, derived formats, and named strictness from C1–C10 compile and lower through M4.
- Wrapper-free configuration uses an explicit `#[k::cell]` marker on every leaf field; the expansion injects `Cell`/`KCell`, and the init function supplies configuration variables and the main computation input.
- `k::rules!` supports the complete `for Sort` and `for Machine` IMP forms, block-local constructor imports, inferred and narrowed binders, splice/erase results, clause labels, and deterministic layer-2 expansion.
- `k::builtin::map::update` and its alias-safe facade are implemented.
- `krs fmt` provides Rustfmt-first elide/splice formatting, whole-table alignment, one-cell-per-line machine records, trivia preservation, Cargo-workspace discovery, `--stdin`, `--check`, unified diffs, editor integration, idempotence, and Rustfmt-fixpoint enforcement.
- Semantic lowering rejects overlapping readable rules after sort inference with a deterministic, cross-table, sort-aware pattern-unification diagnostic.

The only unresolved IMP formatter presentation choice is the trailing-clause-comment policy: aligned comment column or fixed two-space gutter.
Both behaviors have stable snapshots; `aligned` is the current provisional default pending the explicit decision in `open-questions.md` §4.
Two representative readable KWasm integer slices are qualified: wraparound arithmetic first exposed ordinary fixed-leaf-cell rewrites, while guarded unsigned division and traps required no additional authoring syntax.
Further qualification must target genuinely unsupported language-scale dimensions such as locals, structured control flow, memory, or multiplicity without reopening implemented IMP decisions or silently resolving `open-questions.md`.

## Acceptance oracles

- **Expansion fidelity**: `krs expand` on the M4 `imp.rs` produces `imp.expanded.rs` byte-for-byte, and the resolved IR / emitted `.k` matches the reference route.
  The emitted `.k` is checked mechanically against `inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics/{expr,calc,imp}.k` for all 27 rules, labels, strictness, formats, bracket, and both precedence chains.
  The recorded deliberate divergence is that the 18 eval clauses acquire labels `[eval-neg]`… that K's `expr.k` lacks.
- **The four method gates** (F3): LSP goldens, byte-exact provenance
  re-parse, frozen `ProvenanceRole` seam, stable identities.
- **Formatter invariants** (F1): `krs_fmt` is idempotent, output re-parses, the ordered comment and DSL token payloads survive, `rustfmt(krs_fmt(x)) == krs_fmt(x)`, the readable corpus is fixed, and label-renaming edit stability is pinned.
- **Cross-language qualification**: `tests/kwasm/verify.py` pins the external KWasm revision and source mapping, deterministically compiles the readable and expanded Rust routes, compiles emitted K, executes both value and trap outcomes, and closes a native claim.
- **Density**: `imp.rs` contains 139 non-comment, nonblank lines against K's 108 (~1.3× K).
  A construct change that materially regresses this ratio requires an explicit decision.

## Expansion synchronization

`imp.expanded.rs` is synchronized byte-for-byte with `tests/m4/goldens/imp.expanded.rs`.
The M4 gate performs two live expansions, compares them to each other and to that golden, and separately compiles the same bytes as `tests/m4/expanded-definition/src/imp.rs`.
Any readable-surface change must regenerate all three projections in one reviewed change.

## Where the history lives

Deliberation and evidence: `draft/readability/` docs 00–16 (index in its
README) and `draft/readability/result/README.md` (the round-by-round
record; the `[rN]` tags cited by `decisions.md` and the specimen banners
resolve there). Superseded specimens (`result/imp.rs`,
`imp_sort_aliases.rs`, `imp_round6.rs`, `imp_round9.rs`) exist for
comparison only — this folder's `imp.rs` supersedes all of them.
