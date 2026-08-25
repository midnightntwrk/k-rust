# Readability proposals

> **Concluded 2026-08-21 — the design is settled. If you are here to
> BUILD, go to [`spec/`](spec/README.md) and stop reading this folder:
> it contains the normative specimen, the decision register, and the
> open-questions list, and is self-sufficient. Everything below is the
> deliberation record — rationale on citation, not instructions.**

How to close the readability gap between KRS and K itself, using the M4 IMP
port (`tests/m4/rust-definition/src/imp.rs`, 522 lines) versus the original
K IMP definition (`inspirations/runtimeverification/imp-semantics/.../
{expr,calc,imp}.k`, 145 lines) as the running specimen.

**The organizing distinction** (see [08-surface-strategy](08-surface-strategy.md)):
a DSL has two artifacts to improve — **(1) the authoring surface itself**
and **(2) the code it compiles into** (the explicit reference surface). The
M4 port collapses them into one file, which is why its readability problems
are ambiguous between "the DSL is bad" and "we are authoring directly in
the compilation target." The proposals split cleanly along that line:
(2)-improvements are conservative compiler engineering that can start now;
(1)-improvements are language design, corpus-gated by the **macro
ergonomics study** `draft/design.md` already schedules, and every one is
defined by its expansion to unchanged (2) descriptors — valid Rust outer
syntax, identical resolved IR, stable identities and spans, deterministic
`krs expand` reference form.

Reading order: 00 (diagnosis) → 08 (surface strategy) → proposals 01–05 →
06 (comparison and phasing); 07 is supporting evidence.

## Contents

| Doc | Layer | Subject | Verdict argued |
|---|---|---|---|
| [00-problem-analysis](00-problem-analysis.md) | — | Where the 3.6× blowup actually comes from — five distinct causes, with measurements | diagnosis |
| [01-mechanical-cleanups](01-mechanical-cleanups.md) | mostly (2) | Path noise (incl. the wrapper-check bug forcing `k::configuration::KCell`), unused-import hack, strictness defaults, subsort compression | bug-class items now; default-style items are strategy-dependent |
| [02-grammar-colocation](02-grammar-colocation.md) | 02a: (2); 02b: (1) | Kill the `group`-string three-way join: merged precedence block (02a), precedence tiers inside `#[k::constructors]` enums (02b), diagnostics (02c) | 02b corpus-gated; 02a only under a single-surface strategy |
| [03-rule-framing](03-rule-framing.md) | (1) | Implicit frames (03a/b), binder inference (03c), K-style in-place `=>` rewrite inside `cells!` (03d) — expanding to fully-framed (2) rules | build in the (1) track; 03d behind LSP goldens |
| [04-rule-families](04-rule-families.md) | (1) | `k::rules!` — one named line per simple term rewrite; K's table-reading property with real Rust paths | corpus-gated |
| [05-k-mirror-dsl](05-k-mirror-dsl.md) | (1), overreached | The maximal K-in-a-macro option — and the useful inversion: promote generated `.k` to a first-class review view (05b) | reject DSL; adopt 05b tooling |
| [06-comparison](06-comparison.md) | — | All proposals on the same specimens, architecture scorecard, phased recommendation | ~200 lines for IMP (1.4× K, from 3.6×) |
| [07-prior-art](07-prior-art.md) | — | Lessons from egg/egglog, Verus/Flux/Creusot/Prusti/Kani, darling, thiserror, ungrammar — what transfers and what warns | supporting evidence |
| [08-surface-strategy](08-surface-strategy.md) | — | The (1)-vs-(2) divide: classification of every proposal, the strategy decision, and how each track is tackled | recommend two-surface strategy |
| [09-rule-prior-art](09-rule-prior-art.md) | — | Targeted survey for the configuration-rule redesign (Rust rule DSLs, hand-written abstract machines, Redex/Maude/DynSem, ascent DX) | feeds `result/` round 5 |
| [10-first-principles](10-first-principles.md) | — | The end state (`result/imp_round6.rs`) stated and justified from first principles for a Rust developer with no K background; backend-seam jargon inventoried as explicit carve-outs | the justification test itself surfaced the round-7 deltas listed in its §9 |
| [11-variant-group-prior-art](11-variant-group-prior-art.md) | — | Targeted survey: has any Rust library annotated *groups* of enum variants? (sticky markers, container member-lists, macro separators, language-level rejections) | feeds `result/` round 9: container-level chain over positional markers |
| [12-machine-rules-pin](12-machine-rules-pin.md) | (1) | The `for Machine` rule form — agreed critique, candidate replacements, reviewer's `match (k, env)` counter-sketch, and the questions a redesign must answer | **resolved**: keep candidate A; readability reframed as a formatting problem (see 14 §Verdict, 15) |
| [13-multicell-rule-prior-art](13-multicell-rule-prior-art.md) | — | Targeted evidence for the doc-12 follow-up: Verus `state_machine!` (direction 2, shipped), verified rustc facts (RFC 2584 / E0797 / E0529 / E0416 / let-chains), tuple-match census (unattested), `env[name]` lowering evidence, K-corpus cell-count measurements | feeds the doc-12 session; trailing-clause direction strongly favored |
| [14-multicell-candidates](14-multicell-candidates.md) | (1) | The doc-13 evidence rendered as a **choice menu**: six concrete forms (A status quo, B `Machine{..}`/`..pre`, C trailing clauses, D C+`env[name]`, E keyword clauses, F `match (k, env)`) all on the same `var`/`assign` specimens, plus a KMIR 11-cell width stress test | **A chosen** (truest to mechanism); readability = formatting; C/D recorded as fallback |
| [15-formatter-pin](15-formatter-pin.md) | tooling | **PINNED**: enforced canonical layout for `k::rules!` bodies — the bet behind keeping candidate A; known rustfmt facts, survey questions (verusfmt/leptosfmt/dioxus-autofmt leads), provenance gates | **resolved by 16**: `krs fmt` after verusfmt; layout design + provenance checks stay open as design inputs |
| [16-formatter-prior-art](16-formatter-prior-art.md) | tooling | The doc-15 survey: dedicated macro-DSL formatters (verusfmt/leptosfmt/dioxus/Slint + the ascent counterfactual), the rustfmt/rust-analyzer substrate (braced-body fixpoint characterized; extension points confirmed dead), CI/version-skew patterns, idempotence-as-runtime-invariant | **decided: build `krs fmt` after verusfmt** — adopted wholesale + five deviations fixing its gaps (krs-syntax as parser, `--stdin`, in-workspace, runtime idempotence, cargo-metadata discovery); C/D fallback released |

## Method

The proposals are grounded in a mechanical inventory of the current
implementation (macro expansions in `crates/krs-macros/src/expand.rs`, the
shared parsers in `crates/krs-syntax`, the collector's source re-parse in
`crates/krs-compiler/src/collect.rs`, the m1 LSP oracle, and the r1–r12
investigation records under `draft/investigations/`). Feasibility claims
cite file/line; the four recurring gates any new surface must pass are:

1. rustc/rust-analyzer visibility (charter §"What 'like Rust' means";
   operationally `tests/m1/tools/lsp_probe.py`);
2. the collector's re-parse of authored source with byte-exact provenance
   anchors;
3. the `ProvenanceRole` catalog as a frozen protocol seam;
4. stable item identity (no span-derived nonces in anything authors reorder).

## Headline findings

- The deepest issue is structural, not cosmetic: KRS currently has one
  surface doing two jobs. The costs that dominate (rule scaffolding like
  `pub fn done`, per-production ceremony) are *constitutive* of a good
  compilation target and therefore only fixable by building a genuine
  authoring layer above it; the costs that are fixable in place are mostly
  bug-class (08).
- The worst single noise source (`k: k::configuration::KCell(...)` twice per
  rule) is not a design decision: the `cells!` parser already accepts bare
  `KCell`, and only the generated `use`-position wrapper check forces the
  crate-rooted spelling. One-line fix class.
- The precedence/associativity disconnection the corpus complains about is a
  string join that K expresses positionally; enums (already supported via
  `#[k::constructors]`) are ordered and closed, so position can carry tiers
  exactly as K's `>` does, without reopening the r2 open-sorts decision.
- Every rule in imp.rs pays identical "frame rent" (`state @ ..`/`..state`,
  `tail @ ..`/`..tail`); K frames implicitly because framing is what a rule
  *is*. In the authoring layer the frames can be omitted and inserted by
  expansion — the explicit frames remain, canonically, in the reference
  form, so no information is lost anywhere.
- The 18 expression rules are the largest near-duplicate block; a named
  one-line-per-rule family form recovers K's table readability while keeping
  per-rule identity, which r3's DSL rejection was protecting.
- The maximal "just embed K" option fails four architectural gates at once
  and was already rejected (r3/r4) — but its goal is served cheaply by
  rendering the existing generated `.k` as a linked review view.
- Prior art is unanimous on two points (07): no Rust verification/DSL tool
  has achieved IDE support inside embedded non-Rust expressions (which
  vindicates the charter's "stay Rust-shaped" bet and hardens the LSP gate
  on 03d/04), and mature tools (Verus, Flux) converged on shipping *dual*
  surfaces — a compact form and an explicit form — which is exactly the
  reference-vs-ergonomic layering design.md already specifies.
