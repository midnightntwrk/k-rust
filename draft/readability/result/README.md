# Result: the M4 IMP port rendered on the two-surface design

> **Superseded for building purposes by [`../spec/`](../spec/README.md)
> (2026-08-21): `spec/imp.rs` is round 9 plus the resolved machine-rules
> verdict (candidate A, doc 14) and supersedes every variant below. This
> folder remains the round-by-round decision record that `spec/decisions.md`
> cites (`[rN]` tags resolve here).**

This folder makes the readability proposals *visible*: it is the M4 IMP port
hand-rewritten as the pair of artifacts that [08-surface-strategy](../08-surface-strategy.md)
argues for, so the proposals can be judged by looking at the end result
instead of prose. **Nothing here compiles** — these files mock constructs
that do not exist yet (`#[k::tier]`, `k::rules!`, `k::subsorts!`, in-place
`=>`, implicit frames, the round-2 revisions below). Where a construct
*does* exist today (`#[k::constructors]`, variant strictness helpers, the
`cells!`/`map!` grammars, the attribute arguments), the spelling follows the
real parsers.

| File | Layer | Role |
|---|---|---|
| [`imp.rs`](imp.rs) | (1) authoring surface | what humans and agents write and review |
| [`imp_sort_aliases.rs`](imp_sort_aliases.rs) | (1) variant | accumulates rounds 3–5 (sort aliases, co-located statement family, rule tables), kept separate for side-by-side comparison |
| [`imp_round6.rs`](imp_round6.rs) | (1) variant | rounds 3–8: the round-6 revisions (consistency fixes, wrapper-free configuration, defined rule headers), the round-7 amendments surfaced by [10-first-principles](../10-first-principles.md), and the round-8 legibility fixes (`tightest`/`looser` markers, `impl` membership lines) |
| [`imp_round9.rs`](imp_round9.rs) | (1) variant, current best | rounds 3–9: round 6–8 plus the round-9 precedence chain (enum-level member-list chain replacing positional tier markers); the `for Machine` table is unchanged pending [12-machine-rules-pin](../12-machine-rules-pin.md) |
| [`imp.expanded.rs`](imp.expanded.rs) | (2) reference surface | what `imp.rs` expands to — the deterministic `krs expand` rendering |

The third layer already exists and needs no mock: the emitted `.k` (proposal
05b's review view) is, for this definition, essentially the original
`expr.k`/`calc.k`/`imp.k` under `inspirations/runtimeverification/imp-semantics/`.
Reading order for an evaluation session: K original → `imp.rs` → the same
section of `imp.expanded.rs` → the same section of today's
`tests/m4/rust-definition/src/imp.rs` (which the expanded file deliberately
reproduces almost verbatim).

## Line counts (measured on these files)

| Surface | raw | code-only* |
|---|---|---|
| K original (expr.k + calc.k + imp.k) | 145 | 108 |
| current M4 port (`imp.rs`, authored = reference) | 522 | 429 |
| **proposed authoring surface** (`imp.rs` here) | 343 | **184** |
| variant, rounds 3–5 (`imp_sort_aliases.rs`) | 294 | 136 |
| variant, rounds 6–8 (`imp_round6.rs`) | 389 | 125 |
| **variant, rounds 6–9** (`imp_round9.rs`) | 308 | **129** |
| its expansion (`imp.expanded.rs` here) | 538 | 380 |

\* non-blank, non-comment lines. The authoring file carries ~110 lines of
banner comments written *for this evaluation* (proposal citations, expansion
notes); a real definition would keep the doc comments but not those, so
code-only is the honest density number. It undercuts 06's ~200-line
estimate: **~1.7× K by code lines (from ~4×), while the explicit form —
unchanged in shape from today's port — remains fully available behind
`krs expand`.**

## Construct map

| In `imp.rs` | Proposal | Expansion (in `imp.expanded.rs`) |
|---|---|---|
| `use k::configuration::{Cell, KCell};` + bare `KCell` | 01.1 (bug-class fix) | crate-rooted paths |
| no `#[allow(unused_imports)]` preamble | 01.2 | (absent) |
| bare `#[k::strict]` / `#[k::seqstrict]` | 01.3 as layer-1 spelling | `sequence = [..], result = KResult` spelled out |
| `group = stmt` (ident) | 01.4 as layer-1 spelling | `group = "stmt"` |
| no clippy `#[allow]` on the init impl | 01.5 | injected by the expansion |
| `k::subsorts! { Int: Value; … }` | 01.6 | the four-impl groups of today's port |
| `k::precedence! { stmt > right seq_stmt }` | 02a as layer-1 spelling | separate `precedence!` + `associativity!` blocks |
| `#[k::tier(left)]` markers in `enum Op` | 02b | per-variant `group = "op_tierN"` + chain blocks with path-derived (nonce-free) tier identities |
| unmentioned cells omitted | 03a | `state @ ..` / `..state` frames |
| bare `..` computation/map tails | 03b | `tail @ ..` / `..tail`, `rest @ ..` |
| binders undeclared unless narrowing | 03c | explicit typed leading parameters |
| `Pattern => term` inside `cells!`, fn body `{}` | 03d | two-sided pre/post rules |
| `k![a, b]` on the arrow's right | 03d (extension, round 1) | multiple leading `KCell` items |
| `()` on the arrow's right = K's `.K` | 03d (spelling settled, round 1) | the item removed from the `KCell` result |
| `k::rules! { for …; use Op::*; name: pat => term; }` | 04 | 18 independent `#[k::rule]` fns named by clause |
| `#[k::syntax(Stmt = "…", group = stmt, avoid)]` leads every production | r2a | `#[k::constructor(sort = …, syntax = …, group = "…", avoid = true, format = …)]` |
| no format attr where template spacing suffices | r2b | derived `format = "…"` materialized |
| `#[k::format("{first}%n{second}")]` named layout templates | r2b | same named form, printed explicitly |
| `map::update(e, k, v)` | r2c | same (the `e [ k <- v ]` sugar is removed from the language) |
| `map![k -> v, ..]` entries; `=>` reserved for rewrites | r2d | same separator |

Retained as-is per 01.7: `Term<dyn …>` and explicit `label = "if-true"`
attributes. `IfThenElse`'s pretty-print keeps the same compromise as the
current port: K's `% ` escape after the `)` is treated as a plain space.

## Round 2: revisions from review

Three questions from review, and how the files now answer them.

**1. Is `map![e [ name <- value ]]` intuitive for Rust developers?**
No — it was K's `E[X <- V]` sugar transliterated, and it was the only place
the definition invented bracket syntax instead of using the file's own
idiom. The fix follows the pattern already on the page: builtins are term
*functions* (`int::add(lhs, rhs)`, not K's `X +Int Y`), so the map update is
now `map::update(e, name, value)` — named `update` after the persistent-map
convention (`im`-style crates), since it is a functional update returning a
new map, not std's mutating `insert`. The `[ <- ]` production is removed
from the term grammar entirely, in both layers. Method-call sugar
(`e.update(name, value)`) would read even more like Rust but requires
sort-directed receiver resolution in the term grammar; deferred — if it
comes, it should come for `int::`/`bool::` too, uniformly.

**2. The syntax template is buried mid-attribute — how do we make the
grammar scannable?**
Solved structurally rather than by line-wrapping convention: the production
attribute now *leads with the syntax*, in K's own reading order
(`syntax Stmt ::= "…" [attributes]` becomes
`#[k::syntax(Stmt = "…", group = stmt, avoid)]`), and it is always the
item's first attribute. Every production therefore starts with the same
short prefix followed by the template, and a grammar section scans as a
column of templates — see the statement section of `imp.rs`. The
`format = …` argument no longer competes for space on that line: it moved
to its own optional `#[k::format]` attribute (and mostly disappeared — see
next item). The rejected easier fix, keeping `#[k::constructor]` and asking
authors to wrap `syntax` onto its own line, gives a similar scan column but
puts the key information at a convention-dependent position; making it
positional-in-the-attribute makes the convention unbreakable.
Implementation note: as the first attribute, `#[k::syntax]` becomes the
proc-macro driver for struct productions (the role `#[k::constructor]`
plays today); on enum variants it stays an inert helper of
`#[k::constructors]` — same name, same shape, sort omitted because the enum
states it.

**3. Is `format = "%1%n%2"` right, or should it be an `impl Display`
idiom?**
`impl Display` is the wrong tool for a reason worth writing down: the
format must be declarative *data*, because it lowers to K's `format(...)`
attribute for oracle parity and must be statically checkable against the
production (arbitrary code can be neither). But the review instinct was
right that the K spelling was bad, and it exposed a redundancy: for most
productions the format is *already determined by the syntax template's own
spacing* (`"-{value}"` says "no space"; `"{name} = {value};"` says
everything `"%1 %2 %3%4"` said). So: the template's spacing is now the
pretty-print default, and an explicit `#[k::format("…")]` exists only for
real layout — written as the same named-placeholder template plus K's
layout codes (`%n` newline, `%i`/`%d` indent/dedent), e.g.
`"{{%i%n{body}%d%n}}"` for `Block`. Positional `%N` codes are gone from
both layers (K's codes are generated at `.k` emission). Net effect on IMP:
nine format attributes become two (`Sequence`, `Block`).

## Round 3: sort aliases (`imp_sort_aliases.rs`, first revision)

The variant file answers the review question "do we benefit from
`Term<dyn …>` everywhere?" by showing the alternative. In `imp.rs`,
`Term<dyn …>` appears 45 times on 34 of 184 code lines (~18%), dominating
exactly the section we compressed hardest — every operator-table line is
half sort spelling. The variant splits each sort's two jobs across two
names, giving the good name to the frequent job:

```rust
k::sorts! { …; Expr; Value: Expr + KResult; Stmt; }
// per sort:  pub trait ExprSort {}                 (membership — rare)
//            pub type Expr = Term<dyn ExprSort>;   (the type — frequent)
```

so fields, binders, config cells, and the `rules!` header write `Expr`,
`Stmt`, `Value` — `Mul { lhs: Expr, rhs: Expr }` reads like an ordinary
Rust AST — while `Term<Id>` survives only where the term-vs-value
distinction is real (a term of the builtin sort Id vs `Id` the map-key
type). Line *count* barely moves (184 → 181; the win is width: ~8% fewer
code characters, concentrated in the grammar tables), honesty relocates as
usual (hover on `Expr` shows the aliased type; the expansion spells the
traits, e.g. `#[k::subsort] impl ValueSort for Int {}`).

Costs, honestly: two names per sort, with the `-Sort` suffix appearing in
the reference surface's impls and bounds; and the one architectural change
— sort recognition in the rule parser/collector becomes name-resolution-
based instead of matching the `Term<…>` token shape, so it is
prototype-gated like 03d. To be checked in the prototype rather than
assumed: that no other part of the semantic layer depends on the `Term`
shape in pattern positions.

## Round 4: the co-located statement family (`imp_sort_aliases.rs`, second revision)

Review asked why `While`, `Block`, etc. are disjoint code blocks when K
co-locates the whole statement grammar in one syntax block. Answer: there
is no DSL reason — one-item-per-production is constitutive of the
*reference* surface (stable identity, per-production provenance anchors),
and the baseline mock kept structs in layer 1 partly to display both
styles and partly to dodge `Stmt::While`-qualified rule heads. Neither is
a real advantage, and `enum Stmt { If {…}, While {…} }` is how a Rust
developer writes an AST anyway. So the variant now renders statements the
same way as `Op`: one `#[k::constructors]` enum where adjacency continues
a tier and `#[k::tier(right)]` before `Sequence` *is* calc.k's
`syntax priority stmt > seq-stmt` — the `group = stmt` strings and the
freestanding `k::precedence!` block are gone entirely. Variants keep
doc comments, `avoid`, syntax-first attributes, and formats; the expansion
is unchanged in kind (per-variant descriptors plus generated tier groups,
exactly as `Op` expands).

Two decisions this forced, recorded here:

- **Naming.** The sort owns the `Stmt` name (trait in the baseline, alias
  in this variant), and Rust puts traits, aliases, and enums in one
  namespace — so the family enum cannot also be `Stmt`. Convention
  adopted: a natural family name when one exists (`Op`), otherwise
  `<Sort>Syntax` (here `StmtSyntax`), mirroring K's `IMP-SYNTAX` modules.
  The name is low-traffic: it appears on the enum and in one `use`.
- **Head resolution.** Unqualified heads (`While(…)` not
  `StmtSyntax::While(…)`) in the control-flow rules require
  `use self::StmtSyntax::*;` to be honored for rule heads — proposal 04's
  resolution extension applied at module scope. Today variant re-imports
  are rejected as rule heads (there is a negative fixture), so this is a
  prerequisite, not a nicety.

Revised style guidance (supersedes the earlier "enum for operator tables,
structs for statement-shaped grammars"): **the enum family is the default
for all grammars; per-production structs are the exception**, reserved for
productions that need standalone Rust type identity or their own rustdoc
page. The baseline `imp.rs` intentionally still shows the struct style for
comparison.

Cumulative effect on the variant: 164 code lines (baseline `imp.rs` 184,
K 108 — 1.5× K), and the whole grammar now reads top-to-bottom in K's
order with zero string joins.

## Round 5: configuration rules as match-style tables (`imp_sort_aliases.rs`, third revision)

Review verdict on the remaining fn/`cells!` rules: the table form "looks
cute, but as soon as cells are involved it devolves into an unreadable
mess" — with the `while` rule (9 lines for a one-line rewrite) as the
specimen. First-principles decomposition of that mess: (1) wrong construct
— a macro in fn-parameter-pattern position with an empty body is not a
shape any Rust developer has seen; (2) wrong depth — the payload sits four
nesting levels down, where Rust's own pattern→result construct (the match
arm) puts it at depth one; (3) wrong ontology — `if_true`, `if_false`,
`if_else`, and `while` are pure term rewrites that inherited `<k>` wrappers
from imp.k's style; (4) wrong vocabulary — the k cell is a *sequence*, and
Rust's sequence pattern is the slice pattern, not a call-shaped
`KCell(…)`.

A four-survey prior-art pass (Rust rule DSLs; hand-written abstract
machines in Rust; semantics frameworks beyond K; ascent's real-world DX)
is condensed in [09-rule-prior-art](../09-rule-prior-art.md). It confirmed
the direction unanimously and sharpened it: Redex's context-closure lets a
rule table be *headed by* its context, so with `for Stmt in k;` the right
side may splice a sequence (`k![s1, s2]`) or erase (`()`), and **seven of
the nine control-flow rules become cell-free one-liners** — only `var` and
`assign` genuinely touch more than the k head. No other framework puts the
rewrite arrow inside the matched context (K's own rationale for it is
concurrency read-sets, not readability), which demotes 03d's in-place
arrow from default to special-purpose.

The round-5 form, from the variant file:

```rust
k::rules! {
    for Stmt in k;
    r#while: While(c, s) => IfThen(c, Block(Sequence(s, While(c, s))));
    done:    EmptyBlock() => ();
    …
}

k::rules! {
    for Machine;
    assign: { k: [Assign(name, value), ..], env: e }
         => { k: [..], env: map::update(e, name, value) }
        where value: Value;
    …
}
```

Decisions recorded:

- **Unordered, with a static overlap diagnostic** (Cranelift ISLE's
  posture) — never smlang's silent first-wins. Clauses expand to
  independent named rules, exactly as `k::rules!` already promises.
- **Labels default to the clause name** with `_` → `-`; raw identifiers
  (`r#while`) cover K labels that are Rust keywords. All nine explicit
  `label = …` attributes disappeared.
- **Slice patterns are evocative, not literal, Rust**: by-value slice
  patterns on `Vec` are illegal (E0508), so the macro desugars them — the
  same status as the rest of the rule grammar, stated rather than hidden.
  Head-at-front (`[head, ..]`) matches K's cons-like k cell, not a Rust
  `Vec` stack (`[.., top]`) — a documented mental-model note.
- **`where` clauses carry sort narrowing** (K's `X:Id`/`V:Value`), flat at
  one indent level, ascent-style — the table form's replacement for the fn
  form's leading typed parameters.
- **The fn/`cells!` form is now purely the reference surface** (and the
  graduation target for rules that outgrow `pattern => result + where`).
  The `cells!` island no longer appears in the variant at all.

Cumulative effect: the variant is **136 code lines (1.26× K's 108)**, the
`while` rule is 1 line against K's 1 (from 9), and the baseline `imp.rs`
retains the round-1/2 forms for comparison. The expansion story is
unchanged: every clause expands to the framed two-sided fn rules shown in
`imp.expanded.rs`.

## Round 6: audit, prior art for the rest of the surface, configuration (`imp_round6.rs`)

Round 5's prior-art pass ([09-rule-prior-art](../09-rule-prior-art.md))
covered only the rule surface. Round 6 ran three investigations over
everything else: (a) a mechanical consistency + Rust-legality audit of
`imp_sort_aliases.rs` against its own stated rules; (b) a prior-art survey
of the *grammar* surface (LALRPOP, rust-peg, pest, rust-sitter,
parse-display, rustc's AST conventions); (c) an idiom audit of the
configuration/init/builtins sections, grounded in the real implementation
(`crates/krs/src/lib.rs`, `crates/krs-syntax/src/{configuration,initializer}.rs`).
`imp_round6.rs` is rounds 3–5 plus what survived. **129 code lines (1.19×
K's 108)**, widest line under 100 columns.

### What the survey *validated* (kept, now with evidence)

- **Positional `#[k::tier]` over numeric levels.** rust-peg's `precedence!`
  (`--` separators) and pest's `PrattParser` (`.op()` order) are purely
  positional; LALRPOP's `#[precedence(level="N")]` turns out to be
  KRS's design in disguise — un-annotated alternatives inherit the previous
  level and associativity, and the collected levels are `sort`ed and
  `dedup`ed, so the number carries nothing position doesn't. Only
  rust-sitter is purely numeric (inherited from tree-sitter's C API).
  Fusing associativity into the tier marker also avoids LALRPOP's
  reset-to-default footgun (`#[assoc]` silently resets at each new level).
  Mitigation for the reorder hazard: tiers are always visible in the
  expansion (`group = "op_tierN"`) and the emitted `.k` — add a reorder
  golden test. Direction (first tier = tightest, matching K and LALRPOP,
  *inverse* of pest/rust-peg) must be documented loudly.
- **Std format-string escaping.** `"{{{body}}}"`/`"{{}}"` are byte-for-byte
  what `format!` prints and what `parse-display` (the nearest relative:
  one `#[display("{a}__{b}")]` template deriving both Display and FromStr)
  accepts. Inventing a KRS escape would create a dialect. Adopt
  parse-display's *documentation* discipline instead: one "deviations from
  `std::format!`" table, plus a did-you-mean-`{{` diagnostic. Constraints
  never move inside `{}` (parse-display layers its `regex` as a sibling
  field attribute — the KRS analog, the sort, is already the field type).
- **`strict`/`seqstrict` names.** No Rust attribute precedent exists for
  declaring evaluation order, so a rename invents rather than conforms; the
  surrounding vocabulary (`bracket`, `avoid`, `format`, `group`) is already
  uniformly K's, and a half-translated vocabulary is worse than a
  consistent foreign one. Discoverability spend goes to rustdoc on the
  attributes ("`seqstrict` = left-to-right, like Rust's own operand order;
  `strict` = any order, the freedom Rust does not give you").
- **`k::sorts!`/`k::subsorts!` spelling.** `Value: Expr + KResult` is
  Rust's supertrait syntax with `trait`/`{}` elided (direction correct in
  both languages); `Int: Value` reads as a bound, the reading
  `static_assertions::assert_impl_all!(u32: Copy, Send)` established.
  The two-block split mirrors `trait`/`impl`. Keep.
- **`Cell` the name, and lowercase builtin modules.** The std `Cell` clash
  is a hard `E0252`, never silent; the whole API and the committed
  multiplicity family (`OptionalCell`, `SetCells`, …) are cell-shaped; K's
  word is *cell*. And `int::add` is structurally `std::str::from_utf8`
  (a module namespacing distinct nominal operation types), not the
  deprecated `std::i32::MAX` (a module existing to hold two constants) —
  `use k::builtin::bool;` coexisting with primitive `bool` verified clean
  on rustc 1.97. One guard to add: a test that no `k::builtin::bool`/`int`
  item name collides with an inherent item of the primitive (on collision
  the module wins silently). `Int::add` associated fns were verified
  *feasible* (fn items carry distinct `TypeId`s, cross-crate inherent
  impls on the alias work) but rejected: probe rewrite, `E0116` asymmetry
  for user sorts, and it makes term constructors look like ordinary fns.
- **K parity of the whole variant file.** All 27 rules, all labels
  (`r#while` → `while`), all strictness annotations, all nine formats, the
  bracket, and both precedence chains verified against expr.k/calc.k/imp.k
  with no discrepancies.

### What changed (r6a–r6i, details in the file header)

- **r6a** — the evocative-Rust deviations are now a stated four-item
  contract (positional constructor application, non-linear binders, slice
  patterns, result-side `..`). The audit found the first two undocumented;
  converting instead of documenting would cost +55/+75 columns on
  `if_else`/`r#while` (named-field `r#while` measures 147 columns) and
  forfeit the round-5 headline. `EmptyBlock` becomes a zero-field *tuple*
  variant so `EmptyBlock()` is legal Rust at every use site, unchanged.
- **r6b** — the round-3 narrowing rule was violated 16× by the expression
  table as stated; restated as inference-from-all-occurrences (K's own
  behavior), literals self-narrowing, explicit `where` only where inference
  fails or where narrowing separates overlapping clauses. The four `Eq`/`Ne`
  clauses now carry `where lhs: Bool, rhs: Bool` etc. — without them the
  promised overlap diagnostic fires on the definition itself and
  `eval_bool_eq` on Ints builds an ill-sorted term.
- **r6c** — `for Sort;` is *defined* as K rule completion (anchored at the
  computation-cell head, tail framed); round 5's `in k` is gone. The file
  and this README had contradicted each other on what the two headers
  meant, and the "unanchored context-closure" reading would admit rewrites
  the K oracle does not perform (inside unheated subterms, inside stored
  env values) — an oracle-parity hazard. Corrected count: four of the nine
  control-flow rules are pure term rewrites; `step`/`block`/`done` are
  one-liners that use the anchor's splice/erase forms.
- **r6d** — `Term<…>` leaves layer 1 entirely. Round 3 kept `Term<Id>`
  "where the distinction is real: the Map key" — exactly where it failed
  to typecheck (`Term<Id>` key vs `Map<Id, _>`). Closed builtin sorts are
  self-denoting in layer 1; the expansion spells `Term<Id>`.
- **r6e** — `#[k::strict(sequence = [lhs])]` contradicted itself (`strict`
  = unordered, `sequence` = ordered). Now K-parity field lists:
  `#[k::strict(lhs)]`, `#[k::seqstrict(lhs, rhs)]`, bare = all fields.
  `result = KResult` stays hoisted on `#[k::constructors]`.
- **r6f** — `<Sort>Syntax` naming kept; the survey's `StmtKind`
  soft-recommendation is rejected. Criterion note: the decider is neither
  fidelity to the original K nor any external codebase — it is fit with
  this design's own first principles. KRS chose open sorts (the r2
  decision: traits plus subsort impls, constructors addable from any
  module), so a production enum is one *contribution* to a sort, never
  its definition. rustc's `Kind` names the opposite thing — the
  exhaustive discriminated union that *is* the type — so the familiarity
  it buys (via `io::ErrorKind` it reaches every Rust developer, and the
  wrapper-around-shapes relationship genuinely matches) comes at the cost
  of teaching the one wrong assumption the open-sort model must undo:
  `Op` is already, deliberately, not all of `Expr`, and IMP's own `Stmt`
  productions span two source modules. `Syntax` names what the enum is —
  concrete syntax contributed to the sort. Natural family names (`Op`)
  still win when they exist; the rustc precedent stays recorded as the
  counter-argument.
- **r6g** — wrapper-free configuration, 19 → 11 code lines. Grounded in
  the implementation: `Cell`/`KCell` are `PhantomData` markers
  (`Cell::new` discards its argument), `KCell`'s generic admits only
  `KSequence`, so both are injectable; `#[k::cell]` becomes mandatory on
  leaf fields (today it is optional metadata — the *type* is the marker),
  or the collector resolves leaf-vs-nested by TypeId. Config-var names
  derive from init parameters (`pgm` → `$PGM`), `main` defaults to the
  variable initializing the computation cell (100% hit rate on IMP, M3B,
  M3C, KMIR); `#[k::config_var]` survives as override and
  `parser_module` carrier. The init *fn* stays — KMIR (12 cells, 1 config
  var, 11 constant initializers, `fresh::<Int>()`) cannot live in
  attributes and stay rustc-checked. Payoff scales: ~7 tokens on IMP, 24
  `Cell<…>`/`Cell::new(…)` occurrences on KMIR.
- **r6h** — `use` is block-local in every `k::rules!`; the module-scope
  variant glob is gone (two families sharing a variant name would be a
  hard ambiguity at module scope).
- **r6i** — rule binders are K-style metavariables by stated convention
  (the round-5 width numbers quietly depended on this: descriptive names
  push `r#while` to 105 columns).

### Corrections to earlier rounds' claims (audit findings)

- Round 3's density figure: `Term<dyn …>` appears **42 times on 30 of
  184 code lines (~16%)**, not "45 on 34 (~18%)".
- §"What writing it out surfaced" item 7 is stale for the variants:
  `[done]` is 1 line, and no rule in the round-5/6 files wraps (widest
  content line 85 columns — under the metavariable convention above).
- "The expansion story is unchanged" (round 5) is not literally true:
  clause-derived labels mean the expansion emits `pub fn r#while` with no
  `label =` argument, where `imp.expanded.rs` (the *baseline's* expansion)
  shows `pub fn while_loop` + `label = "while"`. Claim narrowed: the
  expansion is unchanged *in shape* (framed two-sided fn rules).
- The stale open question "whether `var`'s narrowing should be inferable
  from the env map's key sort" is closed: the k-cell occurrence alone gives
  only `KItem`, so it is a real narrowing under r6b, kept explicit.
- The 18 expression clauses acquire labels (`[eval-neg]`, …) that K's
  expr.k does not have — a deliberate divergence of the emitted `.k` from
  the original, recorded here.
- `imp-verification.k` (the `[simplification]` inequality rules and the
  regex `token` production) remains inexpressible on this surface — out of
  scope for the IMP specimen, but it is the next thing a reader looks for.

## Round 7: amendments from the first-principles write-up

[10-first-principles](../10-first-principles.md) restates the round-6 end
state with full justification for a K-naive Rust developer, under the rule
that "the original K does it this way" never counts as justification. The
write-up (its §9) plus review surfaced three amendments, applied in place
to `imp_round6.rs` (now rounds 3–7, **128 code lines**):

1. **Framework sorts are imported, not declared.** `KItem;`/`KResult;`
   left `k::sorts!` — they are framework concepts every definition would
   re-declare identically (`KItem` was in fact unused; `KResult` arrives
   by `use k::KResult;` and is still extended through the `Value` bound).
   The sorts block now declares only the language's own categories.
2. **`result = KResult` carries its gloss at the use site**: it defines
   "evaluated" for the strictness attributes (a subterm is done once it
   reaches that sort). In the real surface this becomes attribute
   rustdoc; in the mock it is the section comment.
3. **`#[k::bracket("(", ")")]` replaces `#[k::bracket("({value})")]`.**
   Review datum: the template form read as opaque even to project
   members — its hole named no declared field, the only placeholder in
   the language not checked against a declaration. Spelling the two
   delimiters directly says exactly what the construct means ("this sort
   may be wrapped in these delimiters for grouping; no node is created")
   and removes the magic name. Convention: bracket delimiters are tight
   (no spaces) in the pretty-print default.

## Round 8: two legibility fixes from review

Review criterion (the same one that retired the bracket template in round
7): a construct a K-naive reader cannot decode on its face fails,
whatever its pedigree. Two failed. The variant is now **125 code lines
(1.16× K's 108)**.

1. **`#[k::tier]` → `#[k::precedence]` / `#[k::precedence(left)]`.**
   "Tier" named neither the domain nor the direction, so the marker was
   undecodable on its face. The first attempt in this round encoded the
   direction in the names (`#[k::tightest]` / `#[k::looser(left)]`);
   review verdict: "`looser` makes absolutely zero sense" — invented
   ordering words read as gibberish, while `precedence` is the domain
   word with fifty years of lineage (yacc's `%left`/`%right`, LALRPOP's
   `#[precedence]`+`#[assoc]`) that any grammar author recognizes
   instantly. A recognized word half-implied beats an invented word
   fully-specified. Landed design: each `#[k::precedence(..)]` marker
   opens a group binding weaker than the one before; unmarked adjacent
   variants join the current group; the argument is associativity
   (`left`/`right`, yacc's meaning); the first marker is required
   (LALRPOP's prevalidation) and carries a `// tightest` comment by
   convention. Two residual ambiguities are accepted and assigned to
   attribute rustdoc rather than the name: the marker sets the relation
   *between groups*, not the precedence of the variant it sits on, and
   `left` means left-associative. No clash with the layer-2
   `k::precedence!` chain block: on enum variants the marker is an
   inert helper consumed by `#[k::constructors]`, never resolved as a
   macro. The generated cross-reference identities (`op_tierN`) keep
   their name — "tier" remains the internal/prose word.
2. **`k::subsorts!` folded into `k::sorts!` as `impl` lines**,
   superseding round 6's "keep the two-block split" verdict. The split
   was defended because identically-shaped lines with two meanings must
   not share a block — an argument that dissolves once membership lines
   carry the `impl` keyword: `impl Value for Int, Bool;` is elided Rust
   impl syntax (exactly what it expands to), unambiguous next to
   declarations. The payoff is the reading K's `syntax Value ::= Int |
   Bool` had and the terse edge list (`Int: Value;`) lost: membership is
   grouped by the sort being populated and sits directly under that
   sort's declaration — "a Value is an Int or a Bool" — instead of an
   inverted per-member assertion the reader must flip. A comma list is
   one impl per type in the (unchanged) expansion
   (`#[k::subsort] impl ValueSort for Int {}`). Blocks stay colocatable:
   a feature module can carry a `k::sorts!` of only `impl` lines — K's
   `syntax Expr ::= Id` living in the calc module.

## Round 9: the precedence chain; the rule-table redesign pinned

Review critique of the round-8 markers, sharper than round 8's own fix:
`#[k::precedence(left)]` on `Mul` reads as a per-variant fact about `Mul`
("Mul uses left-precedence"), not as opening a block that spans the
following variants — Rust attributes attach to single items, so the
scoping convention (unmarked adjacency joins the group) is unguessable on
its face. Round 8 fixed the *word*; this is the same criterion applied to
the *scoping*.

A three-pass ecosystem survey
([11-variant-group-prior-art](../11-variant-group-prior-art.md)) found:
sticky run-scoped attributes exist in exactly two shipped designs
(LALRPOP alternatives — mitigated by absolute level numbers; nom-derive
`SetEndian` — mitigated by imperative naming) against three recorded
retreats from the shape (clap #3269 shipped stickiness in its builder
and refused it in the derive; egglog replaced per-item ruleset tags with
a `with-ruleset` container after calling them "tedious and error-prone";
binserde documented and never implemented one); container-level member
lists (subenum, bitflags, bevy `.chain()`) are the only shape with a
hard stale-name story; attributes spanning sibling ranges were proposed
to the language twice and rejected; and macro wrappers cannot enter
enum-variant position, so a true block form is unavailable.

**Landed design (r9): the enum-level precedence chain.** One attribute
on the enum states the whole hierarchy in the same chain grammar as the
freestanding `k::precedence!` block; elements are parenthesized member
lists, optionally prefixed by associativity (`left`/`right`; bare =
non-associative) and an optional group name (`stmt (…) > right
seq_stmt (…)` — calc.k's priority line verbatim; `left`/`right` are
reserved in the name position). Decisive properties, matching the
reviewer's acceptance condition (fail-fast sync):

- **Exhaustive, local checking**: the attribute sees the full variant
  list in its own token stream, so missing, unknown (did-you-mean), and
  duplicate names are hard expansion-time errors — the marker design
  can never check membership because any variant is trivially "in"
  whatever block precedes it. Misplaced-insertion changes from a silent
  wrong-tier join to impossible.
- **Direction is in the operator**: `>` reads "binds tighter than";
  no first-is-tightest position convention to document.
- **Line budget is a wash**: the markers cost one line per tier already;
  measured 125 → 129 code lines (chains cost +4 net for both enums).
- **Variant order becomes purely presentational** — the reorder footgun
  and its golden test disappear; blank-line grouping is kept aligned
  with the chain for scanning only.
- Layer 2 unchanged: per-variant `group = …` plus the two freestanding
  blocks, generated (`op_tierN`) or author-named identities; the
  freestanding chain block survives as the names-only case of the same
  grammar for cross-family precedence.

Recorded fallback preferences from review, if markers ever return: the
marker must sit on its own line (never sharing a line with the syntax
attribute), and explicit block shapes are preferred over adjacency —
which, wrappers being impossible in variant position, itself argues for
the chain. Survey-backed marker mitigations (absolute levels; `next_`
imperative naming; lelwel's order/assoc split) are recorded in doc 11.

**Pinned in the same round:** the `for Machine` rule-table critique (no
Rust idiom matches the anonymous cell record; the for-Sort/for-Machine
mechanism cliff has no K counterpart — K's cell-less/cell-ful
distinction is gradual). Both reviewer and analysis agree it is the
weakest remaining construct; candidate replacements (typed `Machine`
struct patterns, trailing cell clauses, expression-position cell reads
`env[name]`, and the reviewer's tuple-scrutinee `match (k, env)`
counter-sketch) plus the questions a redesign must answer are parked in
[12-machine-rules-pin](../12-machine-rules-pin.md) for a dedicated
follow-up session. `imp_round9.rs` keeps the round-6 form with a NOTE
marker at the block.

## What writing it out surfaced (and where each stands)

1. **Resolved (round 2): the `=>` pun in `[var]`.** The 03d rewrite arrow
   and `map!`'s maplit-style entry separator were the same token with
   opposite meanings on adjacent lines. Decision: `=>` belongs to rewrites
   alone — `pattern => term` reads as a Rust match arm, which is the right
   association — and map entries spell `k -> v`. A rewrite inside a `map!`
   pattern is thereby unambiguous too.

2. **Resolved (round 1, now recorded as decisions): 03d's missing
   right-hand forms.** `[step]` and `[block]` rewrite one k-cell item into
   *two*; the arrow's right side accepts the existing `k!` sequence grammar
   (`k![first, second]`). "Rewrites to nothing" is `()` (Rust's unit as
   K's `.K`).

3. **Narrowing binders are semantics, not documentation.** `[assign]` must
   keep `value: Term<dyn Value>`: inference from the `Assign` field would
   yield `Expr` and the rule would fire before the value is evaluated. The
   style rule (now stated in the file): the explicit parameter is
   *required* whenever the binder's sort is narrower than the field's —
   it is K's `V:Value`.

4. **The 02b table layout fights rustfmt.** The one-line
   `#[k::syntax(…)] #[k::strict]` pairs that make the enum read as a table
   get exploded by default formatting; the mock uses `#[rustfmt::skip]` on
   the enum. `k::rules!` and `cells!` bodies are macro token trees rustfmt
   leaves alone, so the other tables are safe. A real adoption needs a
   formatting policy here.

5. **The two grammar styles coexist — and the style rule was revised in
   round 4.** The baseline `imp.rs` shows `Op` as a tiered enum next to
   `Stmt` as per-production structs; the variant file shows the all-enum
   form. Current guidance (see §"Round 4"): enum families by default,
   structs only for productions needing standalone type identity. Both
   forms depend on 04's head-resolution extension (`use Op::*;` in
   `k::rules!`, `use self::StmtSyntax::*;` at module scope) which does not
   exist today.

6. **The expanded file confirms 08's central claim by inspection.** Its
   rule and grammar sections reproduce today's
   `tests/m4/rust-definition/src/imp.rs` nearly verbatim (modulo `Op::`
   heads, generated tier groups, and the round-2 map/format spellings).
   The reference surface we would "generate" is the file we currently
   hand-write — we are authoring in the compilation target, and the layer
   split costs no new explicit form because it already exists.

7. **Residual density gap to K is Rust item ceremony, as predicted.**
   `[done]` is 2 lines against K's 1; the remaining tokens (`#[k::rule]`,
   `pub fn`, `: Machine`, `{}`) buy item identity and tooling and are the
   part the charter keeps. Some of K's remaining edge is metavariable
   brevity (`C`, `S1`) — with descriptive Rust binder names, three of the
   nine control-flow rules still need wrapping under 100 columns even in
   the compact form.

## Open questions deliberately left visible

- Method-call term syntax (`e.update(name, value)`) as uniform sugar over
  the builtin function style — deferred, and policy-blocked beyond
  deferral: r10 rules out anything depending on Rust trait resolution
  (K functions are partial/symbolic; K's Booleans are not short-circuit),
  so it would need a closed sort-directed method table, giving up the
  rename-safe TypeId identity.
- Tier-group naming for cross-family references (`op_tier1` is the
  generated identity; 02b also allows naming a tier explicitly with
  `group = ident` when another module must refer to it). Round 6 note:
  this is strictly better than LALRPOP's positionally-derived `Expr1`/
  `Expr2` names, which silently retarget under insertion.
- Default associativity of a bare `#[k::tier]`: LALRPOP defaults to
  fully-associative (what iterated unary `-`/`!` needs), K's bare `>` is
  non-associative. Pick, document on the attribute, add a fixture.
- `ExprSort` trait suffix vs a generated `mod sort { trait Expr }`
  (Rust's own two-things-one-name answer, `fmt::Result`-style, giving
  `impl sort::Value for Int {}`). Decide before the reference surface's
  shape freezes. Related: sealing sorts against out-of-definition
  `impl ValueSort for MyType {}` (the `sealed` crate's technique drops
  onto `#[k::sort]`/`#[k::subsort]` directly).
- ~~`<Sort>Kind` vs `<Sort>Syntax`~~ — closed in r6f: under KRS's own
  open-sort model an enum is a contribution to a sort, not its
  definition, so the exhaustiveness-connoting `Kind` misdescribes the
  construct; `Syntax` stays, despite the rustc familiarity precedent.
- The leaf-vs-nested cell discriminator once wrappers are injected (r6g):
  mandatory `#[k::cell]`/`#[k::cells]` attributes (contained parser
  change) vs collector-side TypeId resolution (cleaner, real work).
- A `const`-initializer alternative to the init fn
  (`k::config_vars! { main PGM: Stmt; … }` + `const MACHINE: Machine`) —
  more K-faithful ($PGM as a name in a term), fully rustc-checked, but a
  new construct; sketch only. Field default values (`field: T = expr`)
  verified still unstable (E0658, #132162), not an option.
- Exact-parity handling of K's `% ` format escape (currently: plain space,
  same compromise as the M4 port).
- Formatting policy for the 02b enum table (`#[rustfmt::skip]` vs accepting
  the taller one-attribute-per-line layout). Note rustfmt never formats
  brace-macro bodies, so the `k::rules!` and grammar tables keep their
  layout for free.
- The overlap diagnostic for rule tables: decided in posture (ISLE-style,
  never first-wins), open in mechanism — and round 6 sharpened the spec:
  it must be *cross-table* (a `for Machine` rule can overlap a `for Stmt`
  rule at the k head) and *sort-aware* (`where` narrowing is what makes
  the `Eq`/`Ne` clauses disjoint), so it is not a purely syntactic check.
- Whether `{ .. }` in a cell position is a tail-only map pattern or an
  all-framed cell record — not currently exercised; the grammar should
  rule on it.
- `k::builtin::map` does not exist yet in the facade; `map::update` needs
  building, with the `pub use Update as update;` dual-namespace pattern
  the TypeId probe requires.
- Two grammar-surface conventions to write into the style guide: bracket
  templates use the fixed hole name `{value}`; and the file-level policy
  for doc comments on rule clauses (the control-flow table documents every
  clause, the eval table none — semantic steps vs self-evident table).
