# The two-surface divide: improving the DSL vs improving what it compiles into

Every embedded DSL has two distinct artifacts, and they should be improved
in different ways:

1. **The authoring surface** — the DSL itself: what humans and agents write
   and read day to day.
2. **The compilation target** — what the DSL expands into: explicit,
   regular, the thing tools, audits, and diffs consume.

In KRS terms these are design.md's layer 3 (ergonomic surface) and layer 2
(explicit reference surface), with the IR below both. design.md *defines*
the layers, but the M4 port collapses them: `imp.rs` is simultaneously what
you author and what the machinery consumes — there is no more-explicit form
behind it short of the IR. Every complaint in the problem analysis (00) is
therefore ambiguous between two different diagnoses: "the authoring surface
is bad" and "**we are authoring directly in the compilation target**."

This document disambiguates every proposal in the folder, because the two
diagnoses call for different treatments — and because polishing (2) is
wasted effort in exactly the places where (1) is going to take over.

## The two surfaces have opposite virtues

| | (1) authoring surface | (2) reference surface |
|---|---|---|
| optimizes for | reading/writing effort, locality | explicitness, regularity, auditability |
| redundancy | noise — eliminate it | often information — keep it |
| defaults & inference | good: compact | bad: canonical form spells everything |
| plurality of spellings | tolerable with style guidance | exactly one canonical spelling |
| how it changes | language design; corpus-gated | compiler engineering; conservative |
| primary readers | authors, reviewers | `krs expand` users, auditors, diff tools, agents debugging a lowering |

The two review examples, restated in these terms:

- **`pub fn done` is only really fixable in (1).** The fn-item ceremony is
  *constitutive* of (2): r3 chose the refutable-function shape precisely
  for explicit pre/post structure and independent item identity. Polishing
  (2) — proposal 01 — takes `done` from 12 lines to 10. Reaching 4 lines
  (03a–c) or 2 lines (03d) requires constructs that are not the reference
  shape anymore, i.e. a genuine (1). No amount of (2)-polish gets there,
  and it shouldn't: those lines are (2) doing its job.
- **Some pure-readability polish of (2) stops mattering once (1) exists.**
  Strictness defaults, the merged precedence block, implied supertrait
  impls — all worth having if humans keep authoring in (2), all marginal if
  humans author in (1) and meet (2) mainly through `krs expand` and audits,
  where explicitness is the point.

## Classification of the proposals

| Item | Layer | Notes |
|---|---|---|
| 01.1 wrapper-check fix (bare `KCell`) | neutral | compiler bug fix; benefits any surface that lowers through the rule expansion |
| 01.2 absorb `#[allow(unused_imports)]` | (2) | expansion hygiene of the reference surface |
| 01.3 strictness defaults | **(1)-style default applied to (2)** | strategy-dependent — see below |
| 01.4 unquoted group idents | (2) | small consistency polish |
| 01.5 lint hygiene | (2) | expansion hygiene |
| 01.6 subsort compression | split | the `k::subsorts!` block is a (1) construct; "implied supertrait impls" loosens (2) — strategy-dependent |
| 02a merged precedence block | (2) | polish; subsumed by 02b under a two-surface strategy |
| 02b enum precedence tiers | **(1)** | new authoring construct expanding to constructor + chain descriptors |
| 02c unused-group/adjacency diagnostics | neutral | diagnostics serve both surfaces |
| 03a/b implicit frames | **(1)** | *reclassified* — see next section |
| 03c binder inference | **(1)** | same |
| 03d in-place `=>` rewrite | **(1)** | unambiguously an authoring construct |
| 04 `k::rules!` families | **(1)** | unambiguously an authoring construct |
| 05 K-mirror DSL | (1), overreached | a (1) that abandons the charter; rejected |
| 05b K-review view | output tooling | operates on the *further* compilation output (`.k`); orthogonal to both |
| 07's darling/diagnostic adoptions | neutral | error quality serves both surfaces |

## The reclassification dissolves a real design tension

Proposal 03 originally argued that frame bindings (`state @ ..`/`..state`)
are "syntactic rent" and should be *removed*, and then had to argue against
the deviation ledger's demand that framing stay visible. Under the
two-surface divide that argument was misdirected — it was an argument about
(2) that should have been an argument about (1):

- In **(2)**, the frames stay, explicitly, always. That is (2) being
  canonical and honest; the ledger is satisfied by construction.
- In **(1)**, the frames are omitted and the expansion *inserts* them.
  `krs expand` shows the framed form.

Nothing is removed anywhere; explicitness is relocated to the layer whose
job it is. The same resolution applies to `result = KResult` defaults
(01.3), binder sort inference (03c), and implied supertrait impls (01.6):
each was framed as "loosening the surface" and each becomes uncontroversial
the moment it is a (1) spelling with an explicit (2) expansion. The
proposals' honesty caveats should be read with this correction.

The practical implication for implementation is sharp: **these features
should be built as expansion-time desugarings to the unchanged explicit
descriptors — never as new permissiveness in the reference parsers.** The
reference grammar (`krs-syntax` as consumed by the collector's re-parse)
stays strict; the ergonomic forms are separate entry points that produce
reference-form descriptors. This also keeps the collector's
byte-exact-anchor architecture stable: (2)'s parsers don't grow modes.

## The strategy decision this forces

**D: what is the primary authoring surface?**

- **Strategy A — single surface.** Keep polishing (2) until it is pleasant
  enough to author in. All of 01 + 02a matter; 03/04 would have to be
  *changes to* (2), each one eroding its canonical, fully-explicit
  character; and `done`-class rules floor at ~4 lines with the erosion, ~10
  without.
- **Strategy B — two surfaces.** Build (1) (02b + 03 + 04) as the default
  spelling for definitions; freeze (2) as the explicit, canonical,
  machine-facing form; polish (2) only where bug-class (01.1, 01.2, 01.5)
  or diagnostic (02c, darling).

**Recommendation: Strategy B.** Reasons:

- The problem analysis shows the dominant readability costs (rule
  scaffolding, per-production ceremony) are constitutive of (2), not
  incidental — Strategy A cannot reach K-competitive density without
  compromising (2)'s reason to exist.
- design.md already leans this way: the reference form "need not be the
  dominant spelling in a large semantics" (§"Surface layers and ergonomic
  macros").
- Prior art converged on it (07 §3): Verus and Flux both ended up with a
  compact authoring form and an explicit form, on purpose.
- The workspace's spec-driven goal wants (2) stable, regular, and
  machine-legible for oracles and diffing, while humans review at higher
  density — with 05b's K-view as the densest reading layer of all.

Costs, stated honestly: two surfaces to specify, test, and teach; dialect
risk inside (1) (mitigated by style guidance and by `krs fmt`-style
canonicalization *within* each layer); and each (1) construct pays the
standard expansion-contract engineering (collector arm, provenance roles,
LSP goldens) — which is exactly why (1) constructs are corpus-gated and
(2) fixes are not.

One audience note for the corpus study: this workspace's premise is that
agents implement and humans review. Agents tolerate (2)'s verbosity better
than humans do (it is regular), but (1) still pays for them — fewer tokens,
fewer degrees of freedom to get wrong — and it pays most for the human
reviewer. The study should measure both: agent edit accuracy in (1) vs (2),
and human review effort.

## How each track is tackled

**Track (2) — compiler engineering, start now, no corpus gate:**
01.1, 01.2, 01.5, 02c, darling-grade diagnostics,
`#[diagnostic::on_unimplemented]`. Then *define canonical (2)*: `krs
expand` output becomes the format authority for the reference surface, and
the M4 port stays as the (2) corpus and equivalence baseline. (2) changes
after that point are conservative by policy.

**Track (1) — language design, through the ergonomics study design.md
already schedules:** 02b, 03a–d, 04 as candidate constructs, each defined
*by its expansion* to (2). First deliverable: the M4 IMP port rewritten in
(1) as a second corpus file compiled against the same oracle — the
line-count and diff-legibility comparison in 06 then becomes an executable
artifact rather than an estimate. Gates: identical resolved IR to the (2)
form, LSP goldens, corpus evidence on a non-IMP slice.

**Deprioritized under Strategy B:** 01.3, 01.6's implied-impls variant, and
02a as (2) changes. If any of them return, they return as (1) spellings.
(01.4 survives as a trivial consistency fix; 01.6's `subsorts!` block moves
into Track (1)'s candidate list.)

**Orthogonal, start anytime:** 05b (K-review view over the emitted `.k`).
