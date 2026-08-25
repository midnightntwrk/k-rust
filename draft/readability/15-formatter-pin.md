# 15: PINNED — enforced formatting for `k::rules!` bodies

**Status: RESOLVED 2026-08-21 — survey run and decision made: build
`krs fmt` after verusfmt.** See
[16-formatter-prior-art](16-formatter-prior-art.md) §Verdict for the
decision (what is adopted from verusfmt wholesale, and the five
deliberate deviations that fix its documented gaps). The bet below
pays; candidate A's condition is satisfiable. Questions 1/2/4 answered
in doc 16; questions 3 (canonical layout design — now sharpened by a
column-alignment requirement, 16 §I) and 5 (provenance/span safety)
remain open as design inputs to `krs fmt`, plus a new urgent item: the
krs-syntax public-API/trivia decision (16 §I).

Original pin (2026-08-21): the doc-12 question resolved (see
[14-multicell-candidates](14-multicell-candidates.md) §Verdict): the
multi-cell rule form stays the anonymous cell record (candidate A),
**conditional on an enforced canonical layout** — the review judged its
readability failure to be a layout problem, not a syntax problem.
Whether/how to enforce macro-body formatting was unexplored; the
prior-art survey below was to run in a fresh session.

## The bet being made

Multi-line A (one cell per line) reads well; one-line A does not. rustfmt
will neither produce nor maintain the multi-line layout, so without a
formatter the layout is a convention that rots. If enforced formatting is
viable, A wins on fidelity-to-mechanism; if it is a mess, fall back to
doc 14's C/D (evidence in doc 13 unchanged).

## What is already established (do not re-derive)

- **rustfmt categorically never formats brace-delimited macro bodies** —
  maintainer-confirmed (09 §D, from the ascent deep dive). ascent ships a
  nightly-only fmt config and has an open "hard to contribute" issue
  about it. rust-analyzer applies one blanket `macro` token treatment
  inside.
- Corollary already relied on: rustfmt's non-formatting is what
  *preserves* the hand-laid tables in `result/imp_round9.rs` (result
  README, "What writing it out surfaced" item 4). Preservation ≠
  enforcement — that item's open "formatting policy" question folds into
  this pin.
- The krs collector already re-parses authored source with byte-exact
  provenance anchors (README §Method gate 2) — a formatter that rewrites
  author bytes interacts with provenance and span-stability gates and
  must be checked against them.
- `crates/krs-syntax` already owns a real parser for `cells!`/`map!`/
  rule bodies — a `krs fmt` need not invent a second grammar; formatter
  as a consumer of krs-syntax keeps one grammar (the ungrammar lesson,
  07 §8).

## Questions the survey must answer

1. **Who has shipped a dedicated macro formatter, and how does it feel?**
   Leads to verify (unverified, from memory — confirm existence, health,
   mechanism, adoption): **verusfmt** (standalone formatter for the
   `verus!{}` block — most relevant: Verus is doc 13 §A's headline
   precedent and hit this exact problem), **leptosfmt** (`view!`),
   **dioxus autofmt**, **genemichaels** (whole-file formatter that
   attempts macro bodies), rustfmt's own `skip_macro_invocations` /
   macro-handling internals, **prettyplease** (as an emit-side layout
   engine). For each: how it integrates (`cargo fmt` replacement?
   wrapper? editor?), whether it is check-mode/CI-capable, idempotence
   story, and user complaints.
2. **Delivery mechanism for KRS**: standalone `krs fmt` (wrapping
   rustfmt for the non-macro remainder?) vs formatting via the LSP
   (range formatting inside macro bodies — interacts with the m1
   LSP-golden gate) vs CI check only. Does any rustfmt plugin/extension
   point exist (believed: no — verify)?
3. **Canonical layout design** (separate from mechanism): one cell per
   line; placement of `=>`, `where`, the result record; alignment
   policy; the collapse rule (when a rule is legal as a one-liner —
   single-cell table clauses must stay one-liners); stability under
   small edits; behavior on comments inside rule bodies.
4. **Enforcement path**: format-on-save feasibility inside macro bodies;
   CI `--check`; interaction with `#[rustfmt::skip]` already used on the
   enum tables (02b item — same policy decision, one answer for both).
5. **Provenance/span safety**: verify reformatting does not break the
   collector's byte-exact anchors or stable identities (gates 2 and 4 in
   the README method list).

## Seed corpus for the survey session

Read first: 14 §Verdict (the decision and target layout sketch), 09 §D
(the rustfmt/ascent facts), result README item 4 (the `#[rustfmt::skip]`
policy note), 07 §2 (LSP reality inside macros). The specimens to format:
`result/imp_round9.rs`'s three `k::rules!` tables plus doc 14's KMIR
11-cell stress-test rule rewritten in form A.
