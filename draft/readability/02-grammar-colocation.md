# Proposal 02: Co-locate the grammar (kill the three-way string join)

**Target: Cause 2 (precedence/associativity disconnection) and Cause 1
(per-production volume).** The K reader sees an operator grammar as one
ordered block where adjacency = tier, `>` = priority, and `left:` = tier
associativity. KRS currently reconstructs that structure from a string join
across `group = "..."` attributes, a `precedence!` block, and an
`associativity!` block. Three sub-proposals, independently adoptable, in
increasing ambition.

## 02a. One ordering block: fold associativity into `precedence!`

Cheapest possible fix, no new concepts. Today (imp.rs:151-162):

```rust
k::precedence! {
    prefix > multiplicative > additive > comparison > equality > conjunction > disjunction
}

k::associativity! {
    left: multiplicative;
    left: additive;
    left: comparison;
    left: equality;
    left: conjunction;
    left: disjunction;
}
```

Proposed — annotate the chain elements directly:

```rust
k::precedence! {
    prefix
        > left multiplicative
        > left additive
        > left comparison
        > left equality
        > left conjunction
        > left disjunction
}
```

12 lines → 8, but the line count is not the point: **the two facts about
`additive` now live in one place**, and a tier cannot be registered for
precedence while forgetting its associativity. `associativity!` remains for
the cases with no chain (`right seq_stmt` in a one-group module) or is kept
as `k::precedence! { right seq_stmt }` for a single-element "chain".

Implementation: pure extension of the chain parser
(`crates/krs-syntax/src/grammar.rs:1061-1070`); the expansion emits exactly
the same two descriptor kinds as today (one `Precedence`, one `Associativity`
descriptor set), so IR, collector, and emission are untouched except for the
collector's re-parse arm learning the new chain grammar. The span-derived
item-name nonce issue (`expand.rs:4708-4720`) is unchanged in kind: moving
the block still reorders emitted sentences without changing relations.

## 02b. Precedence tiers inside `#[k::constructors]` enums (the main move)

`#[k::constructors(sort = S)]` already exists and is the natural batch form:
one enum, one variant per production, each with a `#[k::syntax("...")]`
helper (`crates/krs-macros/src/expand.rs:3450-3602`). The enum becomes a
closed sort subsorted into the open `S`, and variant identity is fully
rustc-real. What it *lacks* is the grammar structure: today every variant
would still name a string group, joined to distant chain blocks.

Proposal: variants are already **ordered** and the enum is already
**closed** — use position, exactly like K's syntax block. A `#[k::tier]`
marker on a variant opens a new (weaker) precedence tier containing that
variant and the following ones; the marker carries the tier's associativity:

```rust
use k::Term;

#[k::constructors(sort = Expr, result = KResult)]
pub enum Op {
    #[k::tier]                                    // tightest tier
    #[k::syntax("-{value}")] #[k::strict]
    Neg { value: Term<dyn Expr> },
    #[k::syntax("!{value}")] #[k::strict]
    Not { value: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} * {rhs}")] #[k::seqstrict]
    Mul { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} / {rhs}")] #[k::seqstrict]
    Div { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} + {rhs}")] #[k::seqstrict]
    Add { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} - {rhs}")] #[k::seqstrict]
    Sub { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} >= {rhs}")] #[k::seqstrict]
    Ge { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} > {rhs}")] #[k::seqstrict]
    Gt { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} <= {rhs}")] #[k::seqstrict]
    Le { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} < {rhs}")] #[k::seqstrict]
    Lt { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} == {rhs}")] #[k::seqstrict]
    Eq { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} != {rhs}")] #[k::seqstrict]
    Ne { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} && {rhs}")] #[k::strict(sequence = [lhs])]
    And { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} || {rhs}")] #[k::strict(sequence = [lhs])]
    Or { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
}
```

~50 lines replacing 117 (with proposal 01's strictness defaults), no group
strings anywhere, and the whole operator hierarchy reads top-to-bottom
tightest-to-loosest — the same reading order as K's `>` chains. "Does `+`
bind tighter than `==`?" is answered by vertical position.

The reading is *structurally* faithful to expr.k:15-32: K's block is
`> left: Expr "*" Expr | Expr "/" Expr > left: ...`, and this enum is the
same list with `#[k::tier(left)]` playing `> left:` and variant adjacency
playing `|`.

### Expansion contract

Everything lowers to descriptors that already exist:

- per-variant Constructor + Production, exactly as `#[k::constructors]` does
  today;
- one generated group per tier with a **stable, position-independent
  identity** derived from the enum's item path plus tier ordinal
  (`op::tier0`, `op::tier1`, …) — unlike the freestanding chain blocks whose
  item names embed a span-derived nonce (`expand.rs:4708-4720`), so
  reformatting the enum cannot perturb emitted sentence order;
- one Precedence chain descriptor over those groups, and one Associativity
  descriptor per tier that declares `left`/`right`/`non_associative`.

`krs expand` renders the reference surface: the structs-equivalent
constructor list plus explicit `precedence!`/`associativity!` blocks. This
meets the design.md ergonomic-macro contract clause by clause — the tier
marker does not infer away any distinction; it *relocates* declarations the
author currently writes by string join.

An explicit `group = ident` on a variant remains legal and additive: it
names the tier so that *other* items (a struct-form production in another
part of the module, or a raw chain block relating this grammar to another
family's) can reference it. Cross-family precedence — e.g. imp.rs's
`stmt > seq_stmt` across separately declared productions — keeps using the
freestanding block; 02b removes the *intra-family* join, which is where the
bulk of the strings live.

### What must be built

1. Variant helper attributes `#[k::tier]`, `#[k::strict]`, `#[k::seqstrict]`
   parsed and stripped by the enum expansion (today only `#[k::syntax]` is;
   `crates/krs-syntax/src/enum_constructor.rs:312-334`). While in there, fix
   the hard-coded `k::`-only helper match (`enum_constructor.rs:388-394`) so
   renamed facades work.
2. A matching arm in the collector's re-parse walker
   (`crates/krs-compiler/src/collect.rs`, `collect_invocations`) plus new
   `ProvenanceRole` variants for tier markers — the standard cost of any new
   surface form (constraint §4.2/§4.3 of the internals inventory).
3. Semantic-layer nothing: tiers arrive as ordinary groups/chains.

One boundary this proposal deliberately respects (from the prior-art survey,
07 §1): the compression comes from relocating *item-level* structure —
tiers, adjacency — not from enriching the `syntax = "..."` template strings.
Sub-spans inside string literals are impossible on stable Rust, so anything
moved *into* a string is permanently invisible to IDE tooling; KRS's
templates are tolerable only because expansion-time validation catches
template↔field desync (a rust-analyzer field rename leaves the string stale
but produces a compile error, not silent breakage — worth a golden test).

### The closedness question, answered honestly

Enums are closed; K sorts are open. This proposal does **not** reopen enums —
it leans on the design already in place (`draft/investigations/r2-open-sorts.md`):
the *sort* `Expr` stays an open trait, and each module contributes closed
families into it. That is also how real K modules behave in practice: expr.k
contributes its operator block, calc.k adds `Expr ::= Id` separately. A new
module adds a new enum (or struct) subsorted into `Expr`; it never needs to
edit `Op`. Charter success criterion #3 (extension without editing the parent
module) is preserved.

The residual cost: rules cannot match "any `Op`" exhaustively-by-variant and
get Rust exhaustiveness help, and a production's rule references spell
`Op::Mul { .. }` instead of `Mul { .. }`. The second point matters for
readability of the *rules*; `use Op::*;`-style variant imports are rejected
today as rule heads (negative fixture: `use Enum::Variant as X` aliases),
so 02b should be accompanied by teaching rule-head resolution to accept
plain re-imported variant names — or the eval-rule families in proposal 04,
which name heads once each and make the qualification harmless.

## 02c. If structs stay: adjacency lint instead of relocation

Minimal alternative for taste or for grammars where per-production structs
are preferred (doc comments per production, `#[k::symbol]` pins, etc.):
keep everything as today but require — with a compiler diagnostic, not a
convention — that the `precedence!`/`associativity!` blocks for a group
appear in the same module as the productions of that group. This does not
shorten anything; it bounds the search radius when reading. Worth having as
a diagnostic regardless of 02a/02b, since dangling groups are already
detected (`DanglingProductionGroup`, `crates/krs-ir/src/semantic.rs:1775`)
but *unreferenced* constructor groups are accepted silently today (no
unused-group diagnostic exists) — the silent half of the join should warn.

## Recommendation

Surface classification (08): 02a modifies the *reference* surface, 02b is
an *authoring-layer* construct, 02c is layer-neutral diagnostics.

Adopt 02c's unused-group warning independently — diagnostics serve both
surfaces. Build 02b behind the ergonomics-study gate and validate it on the
IMP grammar plus one open-grammar corpus slice (KWasm instructions) before
freezing — that is exactly the corpus-evidence bar design.md sets. 02a is
worth doing only under a single-surface strategy: it polishes the reference
form that 02b's tier markers stop humans from writing. Under 08's
recommended two-surface strategy, skip 02a and keep the separate
`precedence!`/`associativity!` blocks as the canonical expansion target.
