# Side-by-side comparison and recommendation

All proposals rendered on the same specimens, then scored against the
architecture and phased.

## Specimen 1: the `[done]` rule

**K** (imp.k:37) — 1 line:

```k
rule [done]: <k> { } => .K ... </k>
```

**Current KRS** (imp.rs:510-522) — 12 lines:

```rust
#[k::rule(label = "done")]
pub fn done(
    cells! {
        k: k::configuration::KCell(EmptyBlock(), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(..tail),
        ..state
    }
}
```

**After 01 (path fix)** — 10 lines, same shape.

**After 01 + 03a–c** — 4 lines:

```rust
#[k::rule(label = "done")]
pub fn done(cells! { k: KCell(EmptyBlock(), ..) }: Machine) -> Machine {
    cells! { k: KCell(..) }
}
```

**After 01 + 03d** — 2 lines:

```rust
#[k::rule(label = "done")]
pub fn done(cells! { k: KCell(EmptyBlock() => (), ..) }: Machine) {}
```

## Specimen 2: the `[assign]` rule

**K** (calc.k:32-34) — 3 lines:

```k
rule [assign]:
  <k> X = V:Value ; => .K ... </k>
  <env> E => E [ X <- V ] </env>
```

**Current KRS** (imp.rs:409-425) — 17 lines. **After 01 + 03a–c** — 12
lines (pre/post form). **After 01 + 03d** — 7 lines:

```rust
#[k::rule]
pub fn assign(
    cells! {
        k: KCell(Assign(name, value) => (), ..),
        env: Cell(e => map![e [ name <- value ]]),
    }: Machine,
) {}
```

The remaining gap to K is Rust item ceremony (`#[k::rule]`, `pub fn`,
`: Machine`, `{}`) — the tokens that buy item identity, cargo/rustdoc/
rust-analyzer integration, and the explicit rule/configuration types. That
residue is the price of the project's premise and is fine.

## Specimen 3: the operator grammar (14 productions)

| Surface | Lines | Precedence readable by | Grammar join |
|---|---|---|---|
| K (expr.k:13-32) | 20 | vertical position | none needed |
| Current KRS (imp.rs:45-162) | 117 | 3-way string join | `group` strings ×14 + 2 blocks |
| 01 only (defaults) | ~95 | 3-way string join | unchanged |
| 02a (merged block) | ~90 | 2-way string join | `group` strings ×14 + 1 block |
| **02b (enum tiers)** | **~50** | **vertical position** | **none needed** |

## Specimen 4: the 18 evaluation rules

Current 89 lines of fn scaffolding → proposal 04's table form, 28 lines, one
rule per line, arrows in a column. K's equivalent block (expr.k:41-64) is 24
lines. Parity, effectively.

## Whole-definition estimate

Composing 01 + 02a/b + 03a–d + 04 over imp.rs (same theory, same rules, same
labels):

| Section | Current | Composed proposals |
|---|---|---|
| header/imports | 14 | ~6 |
| sorts + subsorts | 30 | ~12 |
| operator grammar (+prec/assoc) | 118 | ~50 |
| stmt grammar (+prec/assoc) | 92 | ~45 |
| configuration + init | 22 | ~18 |
| expression rules | 89 | ~28 |
| control-flow rules | 148 | ~40 |
| **total** | **522** (measured) | **~200** (estimated) |

K is 145 lines for the same content. **~1.4× K, down from 3.6×**, while every
declaration stays a navigable Rust item. Below ~1.4× the remaining cost is
Rust's own item syntax, which is the part the charter deliberately keeps.

## Architecture scorecard

Gates from the internals inventory: (A) rustc/rust-analyzer visibility and
the m1 LSP goldens; (B) collector re-parse arm + byte-exact anchors; (C)
`ProvenanceRole` catalog extension; (D) stable item identity (no span
nonces); (E) IR untouched; (F) consistency with prior decisions (r2–r5,
charter, design.md ergonomic-macro contract).

| Proposal | A | B | C | D | E | F |
|---|---|---|---|---|---|---|
| 01 cleanups | unaffected | trivial | none | unaffected | yes | yes |
| 02a merged precedence | unaffected | small | none | nonce issue unchanged | yes | yes |
| 02b enum tiers | unaffected (attrs are r-a's best case) | moderate | small | **improves** (path-derived tier ids) | yes | yes (extends existing `constructors`) |
| 03a/b implicit frames | unaffected | small | none | unaffected | yes | yes (frames stay in `cells!`) |
| 03c binder inference | removes some rustc-checked params (modest loss) | small | none | unaffected | yes | debatable — annotation-as-docs |
| 03d in-place `=>` | **must re-verify LSP goldens** | moderate | moderate | unaffected | yes | tension with r3's pre/post shape; sanctioned by semantic-gaps "local rewrite" row |
| 04 rule families | **must verify r-a on fn-like macro input** | moderate | moderate | yes (named clauses) | yes | scoped to dodge r3's DSL objections |
| 05 K-mirror | fails | fails | fails | fails | yes | rejected by r3/r4 |
| 05b K-view tooling | n/a | n/a | n/a | n/a | n/a | composes existing emit + source map |

On gate A, prior art (07) sets the ceiling: no tool in the Rust
verification/DSL ecosystem has achieved completion or reliable goto-def
inside embedded non-Rust expressions — rust-analyzer's input-token
heuristics are the best that exists, they are strongest for attribute-macro
inputs, and sub-spans inside string literals are impossible on stable. So
03d and 04 can at best *match* today's island tooling, never exceed it, and
the m1 LSP goldens are the arbiter of whether they match it.

## Recommended phasing

The phasing follows the two-track split in 08: reference-surface fixes are
compiler engineering with no corpus gate; authoring-layer constructs are
language design gated by the ergonomics study. It assumes 08's recommended
two-surface strategy; the single-surface alternative is noted where it
differs.

- **Track (2), now — bug-class and diagnostics, no design debate.** 01.1
  (wrapper-check fix that unlocks bare `KCell`), 01.2 (absorb the
  unused-import hack), 01.5 (lint hygiene), 02c's unused-group warning.
  Add from prior art (07): darling-grade attribute diagnostics
  (multi-error, sub-attribute spans, did-you-mean) and
  `#[diagnostic::on_unimplemented]` on the sort traits — error-quality
  wins with no surface change — plus a golden test for the
  field-rename-vs-syntax-template desync path. Then declare (2) canonical:
  `krs expand` output is the format authority, the M4 port is the (2)
  corpus, and further (2) changes are conservative by policy.
- **Track (1), the ergonomics study proper — corpus-gated per design.md.**
  03a–c (implicit frames + binder inference), 02b (enum tiers), 04 (rule
  families), 01.6's `subsorts!` block — each defined by its expansion to
  the unchanged explicit (2) form. First deliverable: the M4 IMP port
  rewritten in the (1) constructs as a second definition compiled against
  the same oracle, turning this document's ~200-line estimate into a
  measured artifact. Validate on a KWasm or KMIR slice before freezing.
  Measure: line counts, the LSP goldens, agent edit accuracy in (1) vs
  (2), and a "diff legibility" check (does adding one production/rule
  produce a one-hunk diff?).
- **Track (1), empirically gated tail.** 03d (in-place rewrite) only if the
  LSP goldens hold with `=>` in the islands and the corpus shows the
  two-shape split (in-place vs pre/post) reads well.
- **Only under a single-surface strategy** (i.e. if 08's recommendation is
  rejected and humans keep authoring in (2)): 01.3 (strictness defaults),
  01.4 (ident groups), 01.6's implied supertrait impls, 02a (merged
  precedence block). These polish the form that the (1) constructs would
  otherwise stop humans from writing.
- **In parallel, independent of all of the above:** 05b — surface the
  generated `.k` as a first-class review view with source-map hyperlinks.
  It delivers K-density reading immediately and de-risks every other
  decision by making the lowering visible.

## What "done" looks like

The end state this folder argues for: a Rust file where the grammar reads
top-to-bottom like K's syntax block (02b), simple rewrites read as a table
of arrows (04), configuration rules read as framed one-sided rewrites (03),
nothing is spelled twice (01), and any reviewer one keystroke away from the
K rendering of whatever they're looking at (05b) — with `krs expand`
guaranteeing that every compact spelling has an explicit reference form, as
design.md already requires.
