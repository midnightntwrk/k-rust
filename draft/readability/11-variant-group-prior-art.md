# Prior art for annotating groups of enum variants (round-9 research)

Companion to [09-rule-prior-art](09-rule-prior-art.md). Triggered by a
review critique of the round-8 tier notation: `#[k::precedence(left)]` on
the first variant of a group misreads as a per-variant fact about that
variant ("Mul is left-precedence") rather than as opening a block that
spans the following variants and orders it against other blocks. Since
Rust attributes attach to single items, the question surveyed here is:
has anyone found a clean notation for annotating *groups/runs/blocks* of
enum variants? Condensed from three research passes (derive-macro
ecosystem, language-level proposals, macro-DSL tier notations); claims
marked "verified" were checked against source, not docs.

## Taxonomy of shapes found

- **(a)** per-variant explicit annotation
- **(b)** per-variant with run scope ("applies until the next marker")
- **(c)** container-level annotation referencing member names
- **(d)** positional separator in a macro body
- **(e)** container→all-members default with per-item override (very
  common; distinct from a run — listed only to avoid false positives)

## A. The sticky-marker club — shape (b) — has two shipped members

- **LALRPOP** is the closest precedent to the round-8 design, and its
  exact semantics (verified in `normalize/precedence/mod.rs`) differ in
  the one way that matters: `#[precedence(level="1")]` states an
  **absolute level**, so any annotated alternative reads correctly in
  isolation; un-annotated alternatives inherit both level and assoc from
  the previous one; grouping is by **level value, not adjacency** (levels
  are sorted/deduped; non-contiguous runs with the same number merge).
  Footgun (verified, code comment): a new `#[precedence]` **resets assoc
  to the default** (`FullyAssoc`) instead of inheriting — the reset the
  round-6 fused-argument design already avoids. Prevalidation requires
  the first alternative to be annotated and rejects assoc on level 0.
- **nom-derive `#[nom(SetEndian(expr))]`** — the only run-scoped
  attribute in any Rust *derive* macro found. Three design choices worth
  copying if a marker survives: (1) the sticky attribute has a
  **distinct, imperative name** (`SetEndian`) from the per-item one
  (`BigEndian`), so it cannot misread as a per-item fact; (2) docs state
  "including it, until changed" explicitly; (3) per-item always
  overrides the run. It is the only one of ~30 nom attributes with run
  scope.
- **binserde `#[binserde(index = n)]`** ("moves the field and all
  following fields…") is documented and marked **not implemented** —
  the idea proposed and then dropped.
- **clap is the cautionary counterexample.** The builder has exactly
  this stickiness (`next_help_heading` / `next_display_order`, verified
  in `command.rs::arg_internal`: `get_or_insert` + auto-increment, with
  `None` clearing the marker). The **derive deliberately declined to
  expose it as a positional field attribute** (clap-rs/clap#3269;
  codegen emits it only in the `Kind::Flatten` arm) — sectioning is
  routed through `flatten` + a nested struct instead. A mainstream crate
  judged attribute scope depending on source position too ambiguous.
- **egglog**: base syntax tags each rule with `:ruleset NAME` per item;
  the tutorial calls that "tedious and error-prone" verbatim, and the
  fix (`egglog-experimental`) is a **wrapping container**,
  `(with-ruleset optimization (rewrite …) (rule …))` — a shipped project
  retreating from per-item group tags to a container form.

## B. Container-level member lists — shape (c) — exist and check names

The only shape with a hard stale-name story:

- **subenum**: enum-level `#[subenum(Tree, Edible)]` declares the group
  universe; per-variant `#[subenum(Tree)]` names memberships. Groups are
  by name, not adjacency; undeclared group names are caught.
- **bitflags**: composite flags reference member names
  (`const AB = Self::A.bits() | Self::B.bits();`) with real path
  resolution — stale names are hard compile errors.
- **Bevy system sets**: the enum declares names; a *separate ordered
  expression* declares the relation with real paths:
  `(GameSystems::Input, GameSystems::Update, GameSystems::Render).chain()`
  — literally an `A > B > C` ordering spelled as a tuple of idents.
- clap's `ArgGroup::new("g").args(["a", "b"])` is the string-typed
  version (builder only, debug-asserted at runtime, not compile-checked).
- No crate was found embedding an `A > B > C` operator DSL over variant
  names inside an attribute — that spelling would be novel, though its
  ingredients (idents in attributes, chain grammar) are all established.

## C. The language will not help

Attributes over ranges of items were proposed twice and rejected:
rust-lang/rfcs#1991 ("Blocks for items") and internals.rust-lang.org
t/14483 ("Item blocks"), both the brace-wrapped shape, the decisive
objection being that braces imply a scope that isn't one.
`stmt_expr_attributes` (still unstable) covers expressions/statements, a
different axis. **No pre-RFC anywhere proposes the sticky
"applies-until-next-marker" model as Rust syntax** — LALRPOP and
nom-derive implement it privately because no group form exists.

Two adjacent language facts: duplicate explicit discriminants are a
hard error, so tiers cannot be encoded as `Mul = 1, Div = 1`; and
`derive(PartialOrd/Ord)` already gives variant declaration order
semantic weight with no annotation at all — the strongest in-language
precedent *for* positional semantics, recorded here as the
counter-argument to this doc's synthesis.

Also relevant: Rust does not allow macro invocations in enum-variant
position, so an egglog-style wrapper (`tier!(left { … })`) cannot live
inside a `#[k::constructors]` enum — a wrapper would force the whole
grammar into a function-like macro, trading away attribute-on-real-enum
visibility (C1). A container-level attribute naming its members is the
attribute-space analogue of the wrapper shape.

## D. Macro-DSL tier notations — shape (d) and friends

- **rust-peg `precedence!{}`**: `--` separates tiers (loosest→tightest);
  associativity is encoded by `@` placement (`x:(@) "+" y:@` = left).
  Purely positional, no keywords or numbers.
- **pest `PrattParser`**: `.op(infix(add, Left) | infix(sub, Left))
  .op(infix(mul, Left))` — tier membership via `|`, level via call
  order (first = lowest), associativity per-op, no integers, stale
  `Rule::` names caught by the type system. The cleanest tier notation
  found — but it lives in expression space.
- **lelwel**: the alternation bar itself is the tier separator; branch
  order in the top-level alternation is binding power (first =
  tightest). Associativity is factored out entirely into a separate
  container-level token list (`right '^' '=';`, default left) — a split
  of *order* (implicit, adjacency, unannotated) from *associativity*
  (one declaration per exception) that dissolves the marker problem by
  never needing a marker.
- **yacc lineage (grmtools, pomelo)**: `%left '+' '-'` lines, one per
  tier, level = line index (verified in grmtools `test_precs`); rules
  carry only `%prec` overrides — declaration table separate from rules.
- **chumsky pratt / rust-sitter / ISLE / `pratt` crate**: bare integers,
  higher = tighter, source order irrelevant — shape (a).
- **egg `define_language!`**: no precedence construct at all; relies on
  declaration order only for parse fallback.

**Direction is genuinely inconsistent across tools** — pest, yacc,
pomelo, rust-peg order first→loosest; lelwel, K, LALRPOP (low level =
tight) order first→tightest; the integer crates make order irrelevant.
There is no convention to conform to; whatever KRS picks must be stated
loudly on the attribute rustdoc and pinned with a fixture (this was
already a round-6 open question).

## E. Negatives (for coverage claims)

No grouping or run mechanism of any kind: serde, strum, derive_more,
parse-display, num_enum (value-ranges only, over discriminants),
enum-kinds, logos, packed_struct (its own examples repeat the endian
annotation on consecutive fields — the exact case a sticky marker would
collapse, and they chose repetition), modular-bitfield, bitfield-struct,
bilge, binrw, deku (its "all former fields" `ctx` is value flow, not
attribute inheritance), zerocopy, bytemuck, binary-layout (hoists
would-be separators into a macro-header parameter), confique, config-rs,
figment, bpaf, structopt, argh, gumdrop, pest-ast/pest_typed, plex.
GitHub code search for "applies to all following variants" /
"range of variants" language:rust: zero relevant hits.

## Synthesis

1. **(a) per-item explicit is the overwhelming ecosystem default**; its
   cost is repetition, its benefit is that every line reads correctly in
   isolation — exactly the property the round-9 critique demands.
2. **(b) sticky markers are a two-member club** (LALRPOP, nom-derive),
   and the recorded retreats from the shape (clap #3269, egglog
   `with-ruleset`, binserde's unbuilt attribute) all moved to container
   or explicit forms. If a marker is kept anyway: copy LALRPOP's
   absolute levels (annotated lines read standalone; adjacency stops
   being semantic) and nom-derive's state-change naming.
3. **(c) container-level member lists are the only shape with hard
   stale-name checking**, and the natural fit for an ordered relation
   (Bevy's `.chain()`). Applied to KRS this is an enum-level
   `#[k::precedence((Neg, Not) > left (Mul, Div) > …)]` in the existing
   chain grammar: same line budget as one marker per tier, the whole
   hierarchy visible in one expression (K's actual virtue), exhaustive
   missing/duplicate-variant diagnostics (closing cause 2's "diff looks
   complete" hole with an error instead of a convention), variant order
   demoted to presentation (killing the silent-reorder footgun and its
   golden test), and one chain grammar for both intra-family (on-enum)
   and cross-family (freestanding) precedence. Costs: variant names
   spelled twice; rename refactors don't rewrite attribute tokens
   (staleness is an expansion-time error, same status as syntax
   templates). The minimal-change fallback if the marker is kept:
   combine both mitigations — an imperative/stateful name with clap's
   `next_` flavor (`#[k::next_precedence(left)]`) or LALRPOP's absolute
   level (`#[k::precedence(level = 2, left)]`). A third hybrid, from
   lelwel's order/associativity split: bare markers carrying only the
   boundary, with associativity declared once at the enum level — the
   marker then has only one job left to misread. (Related LALRPOP
   nuance: its reset-assoc-at-each-new-level rule, called a footgun
   above, is also a deliberate guard against stale assoc leaking across
   a boundary — the fused-argument design gets the guard for free.)
   The yacc/pomelo form is worth noting as (c)+(d) at once: one ordered
   line per tier, each an associativity keyword followed by its member
   list — it reads as a block because the keyword *opens* the line and
   members follow it, never because a member is annotated. That is
   exactly the reading order the on-enum chain attribute reproduces.
4. **(d) positional separators exist only in macro bodies** (rust-peg,
   lelwel), never in attribute space, and Rust rejected the language
   feature that would allow them; wrappers can't enter variant position.
