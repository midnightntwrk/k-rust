# Proposal 04: Rule families — one line per simple term rewrite

**Target: Cause 3 as it appears in bulk term rules.** imp.rs spends 89 lines
(285–373) on 18 rules whose entire content is "this constructor rewrites to
this builtin application":

```rust
#[k::rule]
pub fn eval_add(Add { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::add(lhs, rhs)
}
```

× 18, where the only varying tokens are the head, the field list, and the
builtin. K writes each as one line (`rule X + Y => X +Int Y`), and the K
*block* of them reads as a table — the eye scans the column of arrows. The
KRS spelling hides the one interesting token per rule inside a wall of
identical `pub fn … Term<dyn Expr> …` scaffolding.

## The proposed form

A `k::rules!` item macro; each clause is one named rule:

```rust
k::rules! {
    for Term<dyn Expr>;

    eval_neg:     Neg { value }            => int::sub(0, value);
    eval_not:     Not { value }            => bool::not(value);

    eval_add:     Add { lhs, rhs }         => int::add(lhs, rhs);
    eval_sub:     Sub { lhs, rhs }         => int::sub(lhs, rhs);
    eval_mul:     Mul { lhs, rhs }         => int::mul(lhs, rhs);
    eval_div:     Div { lhs, rhs }         => int::div(lhs, rhs);

    eval_ge:      Ge { lhs, rhs }          => int::ge(lhs, rhs);
    eval_gt:      Gt { lhs, rhs }          => int::gt(lhs, rhs);
    eval_le:      Le { lhs, rhs }          => int::le(lhs, rhs);
    eval_lt:      Lt { lhs, rhs }          => int::lt(lhs, rhs);

    eval_bool_eq: Eq { lhs, rhs }          => bool::eq(lhs, rhs);
    eval_int_eq:  Eq { lhs, rhs }          => int::eq(lhs, rhs);
    eval_bool_ne: Ne { lhs, rhs }          => bool::ne(lhs, rhs);
    eval_int_ne:  Ne { lhs, rhs }          => int::ne(lhs, rhs);

    and_true:     And { lhs: true, rhs }   => rhs;
    and_false:    And { lhs: false, .. }   => false;
    or_true:      Or  { lhs: true, .. }    => true;
    or_false:     Or  { lhs: false, rhs }  => rhs;
}
```

89 lines → 28, and the block regains K's table-reading property while using
only KRS's existing pattern and term grammars: the left side is exactly the
rule-subject grammar (`crates/krs-syntax/src/rule.rs:793-830` — native
pattern or `term!` payload, unchanged), the right side is exactly the
restricted term-expression grammar. Nothing stringly: every head and builtin
is a real path.

Design points, each mapped to an existing constraint:

- **Names are mandatory.** `eval_add:` is not decoration — it is the item
  identity. This keeps the charter's "one rule = one independently named
  clause" (r3's accepted design) and gives each clause a stable
  `StableItemId` (`block module path` + clause name), avoiding the
  span-derived nonce problem that afflicts the anonymous grammar blocks
  (`crates/krs-macros/src/expand.rs:4708-4720`). Reordering or reformatting
  clauses changes nothing, satisfying charter success criterion #2. A
  `label = "…"` attribute per clause covers K-parity labels with hyphens.
- **The subject sort is stated once** (`for Term<dyn Expr>;`) instead of 36
  times. Clauses whose sorts differ go in separate blocks — a block is a
  family, not a container.
- **Per-clause attributes ride along** where needed:
  `#[k::requires(int::ne(denominator, 0))] eval_div: …;` — same attribute
  grammar, applied to a clause instead of a fn.
- **Unordered semantics are preserved by construction**: clauses expand to
  exactly the descriptor set of 18 separate `#[k::rule]` fns; there is no
  ordered-match reading to be tempted by, and the overlapping `Eq`/`Ne`
  pairs (bool vs int) sit adjacently *without* implying priority — same as
  today.
- **`krs expand` shows the reference form**: the 18 explicit fns. Contract
  satisfied.

## Why this is *not* the rejected rule DSL

r3 rejected "a dedicated `k::rule!` DSL" for the general case
(`draft/investigations/r3-rule-surface.md:232-235`): opaque token trees, a
second item grammar, loss of fn/pattern/attribute cues. Three things are
different here:

1. **Scope.** This form is only for term rules — subject pattern, arrow,
   result term. Configuration rules, requires-heavy rules, and claims keep
   the fn form (or proposal 03's). The moment a rule needs more than
   `pattern => term` plus a requires, it graduates to a fn.
2. **No new inner grammar.** Both sides reuse grammars that already exist
   and are already island-parsed in fn-form rules; the block adds only
   `name: … => …;` framing.
3. **The tooling loss is bounded and testable.** In fn-form term rules,
   the pattern and body are *already* consumed before rustc
   (`expand.rs:1550-1800` — rustc checks only `TypeId`-level path
   existence); rust-analyzer features come from input-token indexing, which
   applies to function-like macro inputs as well. The LSP goldens
   (`tests/m1/tools/lsp_probe.py`) are the gate, exactly as for 03d — with
   the honest caveat that *attribute* macro inputs are the case r-a handles
   best today, so this needs to be measured, not assumed.

The residual real cost: clause names are not `fn` items, so "find all rules"
by grepping `fn ` no longer works, and doc comments per clause need
supporting in the block grammar (they should be — the imp.rs rules carry
useful doc comments).

Prior art brackets this design from both sides (07). egg's `rewrite!` shows
the arrow-table form is the natural notation for rewrite systems — and shows
the failure mode to avoid: its patterns are strings, so pattern variables
get no tooling at all; `k::rules!` takes the shape but keeps both sides as
real KRS grammars over real paths. Verus and Flux show the endgame of
having two spellings for one construct: it is the convergent design in this
space, provided style guidance says when each applies (here: block for
`pattern => term` (+ requires), fn for everything else).

## Interaction with proposal 02b

If the operator grammar becomes an `Op` enum, heads are spelled
`Op::Add { lhs, rhs }`. In the fn form that qualification is one more noise
token per rule; in the table form it is absorbed by column alignment — or
avoided entirely by allowing `use Op::*;`-style resolution inside the block
(today variant aliases are rejected as rule heads; the block, which controls
its own name resolution pass in the semantic layer anyway, is the natural
place to permit it).

## Implementation cost

The standard new-surface triple: a `krs-syntax` block parser (shared by
macro and collector per the re-parse architecture,
`crates/krs-compiler/src/collect.rs:2296-2960`), a `collect_invocations`
arm, and `ProvenanceRole` coverage for clause name / pattern / result
positions. Descriptor, semantic, lowering, and emission layers are untouched
— clauses arrive as ordinary rule descriptors.

## Recommendation

Adopt behind the ergonomics-study gate, after 01/02a/03a-b. It is the
cheapest of the ambitious proposals (no IR impact, no new semantics, no
change to existing forms) and it attacks the single largest block of
near-duplicate lines in the corpus. Gate on the LSP goldens and on one
question the corpus must answer: how many real rules stay simple enough for
the table? In IMP it is 18 of 27; if KMIR/KWasm slices show similar ratios,
the form pays for itself.
