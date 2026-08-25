# KRS authoring surface — normative spec

**This folder is the settled outcome of the readability investigation
(`draft/readability/`, docs 00–16, concluded 2026-08-21). If you are here
to build, this folder is sufficient: do not read the sibling deliberation
docs except to chase a rationale citation.** They record how the design
was reached, including many superseded intermediate forms; treating them
as instructions will mislead you.

## The deliverable

Make `imp.rs` (in this folder) real: a layer-1 **authoring surface** of
attribute macros and function-like macros such that this file compiles,
expands deterministically (`krs expand`) to the layer-2 **reference
surface** shown in `imp.expanded.rs` (the shape of today's hand-written
`tests/m4/rust-definition/src/imp.rs`), and drives the same K-parity
oracle. Plus one co-deliverable: **`krs fmt`**, the formatter that
enforces the surface's canonical layout (decision F1).

| File | Status | Role |
|---|---|---|
| [`imp.rs`](imp.rs) | **normative** | the target authoring surface — what authors write; the acceptance specimen |
| [`imp.expanded.rs`](imp.expanded.rs) | reference | what it expands to (see "Known deltas" below) |
| [`decisions.md`](decisions.md) | **normative** | every settled decision as an implementable rule (A architecture, B sorts, C grammar, D configuration, E rules, F tooling) |
| [`open-questions.md`](open-questions.md) | **normative** | what is deliberately undecided — surface these, never resolve them silently |

Precedence on conflict: `imp.rs` > `decisions.md` > everything else. A
conflict is a bug in this folder — report it rather than interpreting
around it.

## What exists today vs. what to build

Grounded in the real implementation (`crates/krs-macros`, `crates/krs-syntax`,
`crates/krs-compiler`). Already real, keep the spelling: `#[k::constructors]`
enums, the variant strictness helpers, the `cells!`/`map!` grammars, the
attribute-argument forms, the collector's provenance re-parse, the m1 LSP
oracle. To build (decision IDs from `decisions.md`):

1. **`k::sorts!`** with `impl` membership lines, bracket attribute,
   generated trait + alias pairs (B1–B4); sort recognition in
   rule-parsing becomes name-resolution-based, not `Term<…>`
   token-shape-based (B2 — prototype-gated, r3 caveat).
2. **Grammar surface**: syntax-first attribute as driver (C3), the
   enum-level `#[k::precedence(…)]` chain with total membership checking
   (C7), template-spacing-derived pretty-print + `#[k::format]` (C5),
   bare/field-list strictness (C6).
3. **Wrapper-free configuration**: injectable `Cell`/`KCell`, `#[k::cell]`
   leaves, init-fn-derived config vars (D1–D2; open-questions §11 on the
   leaf discriminator).
4. **`k::rules!`** — the core: `for Sort;` k-head anchoring with framed
   tail, splice/erase right-hand forms, block-local `use`, clause-derived
   labels, occurrence-based sort inference + `where` narrowing, the
   `for Machine` cell-record form, expansion to independent framed
   two-sided `#[k::rule]` fns (E1–E8). Prerequisite: head resolution for
   `use Family::*;` globs (block-local and module-scope; today variant
   re-imports are rejected as rule heads — there is a negative fixture).
5. **`map::update`** and the `k::builtin::map` facade (open-questions
   §16 — build work).
6. **`krs fmt`** per F1/F5–F7 / doc 16 §Verdict. Its layout-independent
   krs-syntax trivia facade and source APIs are implemented; renderer and
   CLI integration remain.
7. **Diagnostics**: the fail-fast set (F4) and the overlap diagnostic
   (F2; mechanism open — open-questions §5).

Suggested order: (1)–(3) are contained macro/collector work; (4) is the
substantial piece and gates on the head-resolution prerequisite; (6)'s
renderer can build on the delivered trivia/source-API foundation; nothing
blocks on (7)'s open mechanism beyond emitting *some* overlap error.

## Acceptance oracles

- **Expansion fidelity**: `krs expand` on `imp.rs` produces the reference
  surface — `imp.expanded.rs` in shape (see deltas below), and the
  resolved IR / emitted `.k` must match what today's hand-written M4 port
  produces. The emitted `.k` is checked against the original
  `inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics/{expr,calc,imp}.k`
  — full K parity of all 27 rules, labels, strictness, formats, bracket,
  and both precedence chains was verified by hand in round 6 and must
  hold mechanically. (One recorded deliberate divergence: the 18 eval
  clauses acquire labels `[eval-neg]`… that K's expr.k lacks.)
- **The four method gates** (F3): LSP goldens, byte-exact provenance
  re-parse, frozen `ProvenanceRole` seam, stable identities.
- **Formatter invariants** (F1): `krs_fmt` idempotent, output re-parses,
  `rustfmt(krs_fmt(x)) == krs_fmt(x)`, `imp.rs` here is a fixed point.
- **Density**: `imp.rs` is 308 raw / ~129 code lines against K's 108 —
  the surface exists to hold roughly that ratio (~1.2× K). A construct
  change that regresses it materially needs a decision, not a commit.

## Known deltas between `imp.rs` and `imp.expanded.rs`

`imp.expanded.rs` was written against the round-1/2 baseline and is
normative **in shape, not byte-for-byte** (recorded in the result
README's round-6 corrections): clause-derived labels mean the expansion
of this `imp.rs` emits e.g. `pub fn r#while` with no `label =` argument
where the file shows `pub fn while_loop` + `label = "while"`; rule heads
are enum-qualified (`Op::…`) under the round-4 enum families; precedence
expands to per-variant `group = …` + chain blocks per C7. When the
expansion is implemented, regenerate this file from `imp.rs` and make it
the golden.

## Where the history lives

Deliberation and evidence: `draft/readability/` docs 00–16 (index in its
README) and `draft/readability/result/README.md` (the round-by-round
record; the `[rN]` tags cited by `decisions.md` and the specimen banners
resolve there). Superseded specimens (`result/imp.rs`,
`imp_sort_aliases.rs`, `imp_round6.rs`, `imp_round9.rs`) exist for
comparison only — this folder's `imp.rs` supersedes all of them.
