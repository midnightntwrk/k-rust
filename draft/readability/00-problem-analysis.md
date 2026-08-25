# Why the current surface is hard to read

This document diagnoses *precisely where* the readability gap between KRS and
K comes from, using the M4 IMP port as the specimen. The numbered proposals in
this folder each attack one or more of the causes named here; the comparison
document scores them against each other.

Specimen files:

- K oracle: `inspirations/runtimeverification/imp-semantics/.../expr.k`,
  `calc.k`, `imp.k` — **145 lines** total (including blanks and comments).
- KRS port: `krs/tests/m4/rust-definition/src/imp.rs` — **522 lines** for the
  same theory (the M3C control-flow slice layered over the expression and
  calculation theory).

A 3.6× line blowup understates the problem, because the K lines are also
individually far closer to the mathematical content. The gap has five
distinct causes, and they need different fixes.

## Cause 1: one production = one struct + attribute block (grammar volume)

One K production line:

```k
syntax Expr ::= Expr "+" Expr [seqstrict]
```

becomes six KRS lines:

```rust
#[k::constructor(sort = Expr, syntax = "{lhs} + {rhs}", group = "additive")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Add {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}
```

The K line carries five facts: sort, arity, concrete syntax, strictness, and
(via block position) precedence and associativity. The KRS form carries the
same facts but *repeats* what K states once positionally:

- The child sorts appear twice each (`{lhs}`/`{rhs}` in the template, then
  `Term<dyn Expr>` per field).
- The strictness attribute re-lists the field names (`sequence = [lhs, rhs]`)
  and the result sort (`result = KResult`), which for a whole definition is
  almost always the same value.
- Every production restates `sort = Expr` even when fifteen consecutive
  productions share the sort.
- Field names (`lhs`, `rhs`) are invented per production even when they carry
  no information beyond position. K needs no names at all for these; the KRS
  names then propagate into the syntax template and strictness attributes.

IMP's operator grammar is 14 productions: **20 lines of K (precedence and
associativity included), 117 lines of KRS** (imp.rs:45–162, including the
separate `precedence!`/`associativity!` blocks) — and every one of those KRS
productions is structurally identical modulo the operator string and group
name.

## Cause 2: precedence and associativity are spatially disconnected

K's grammar block *is* the precedence declaration: `>` separates priority
tiers, `left:`/`right:` prefixes tiers, and membership in a tier is literal
adjacency. The reader sees the whole operator hierarchy in one screenful, and
cannot state a production without simultaneously stating its precedence.

KRS splits this one concept across three places:

1. a `group = "additive"` string inside each constructor attribute,
2. a `k::precedence! { prefix > multiplicative > ... }` invocation possibly
   hundreds of lines away,
3. a `k::associativity! { left: additive; ... }` invocation somewhere else
   again.

Three consequences:

- **Reading**: to answer "does `+` bind tighter than `==`?" the reader must
  find and join three declarations by a string key.
- **Writing**: a new production must pick a group name and remember to
  register it in two other macros; nothing co-located reminds the author.
- **Reviewing**: a diff adding a production looks complete even when the
  precedence registration is missing.

This is the clearest instance of the general disease: **facts that K states
by position, KRS states by string-keyed cross-reference.**

## Cause 3: rule scaffolding drowns the rewrite

The K rule

```k
rule [done]: <k> { } => .K ... </k>
```

is one line: pattern, arrow, result, frame (`...`). The KRS form is twelve:

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

Separable noise sources, worst first:

- **Path noise.** `k::configuration::KCell(...)` is 24 characters of module
  path around a one-letter cell name, written twice per rule. The K
  equivalent is `<k>`/`</k>`. Nothing about the semantics requires the full
  path; it is an import-discipline choice.
- **Explicit frames that K makes implicit.** `tail @ ..` + `..tail` and
  `state @ ..` + `..state` appear in *every single rule* in imp.rs. In K,
  `...` inside a cell and the absence of other cells express the same thing
  with zero named bindings. When a construct appears in 100% of rules with
  identical spelling, it is syntactic rent, not information. (The bindings do
  make the frame explicit — a charter value — but the charter also says a
  compact spelling is wrong only when it *hides a distinction the author
  needs to notice*. A frame that is always present and never varies is not
  such a distinction.)
- **Pre/post duplication.** The unchanged parts of the configuration are
  written in both the parameter pattern and the result expression. K writes
  only the changed part (`{ } => .K`) *inside* the context, once.
- **Variable pre-declaration.** Every variable used in the pattern must also
  be declared as a preceding `fn` parameter with its sort
  (`first: Term<dyn Stmt>, second: Term<dyn Stmt>,`). K infers variable
  sorts from use. This doubles the mention count of every rule variable and
  pushes the actual rewrite further from the `fn` keyword.
- **Signature ceremony.** `pub fn done(...) -> Machine` adds tokens carrying
  no semantic content (rules are not callable; `-> Machine` is determined by
  the parameter; `pub` is meaningless for a rule's semantics).

For the simple expression rules the same pattern recurs in miniature:
`pub fn eval_add(Add { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
int::add(lhs, rhs) }` (3 lines + attribute) versus `rule X + Y => X +Int Y`
(1 line). Here the overhead ratio is lower but the *token* ratio is still
~4×, and 18 such rules in a row make imp.rs's midsection a wall of
near-identical function headers in which the one varying token (`int::add`
vs `int::sub`) is optically buried.

## Cause 4: type-noise in recurring positions

`Term<dyn Expr>` appears 50 times in imp.rs, `Term<dyn Stmt>` 15 times.
The `dyn` keyword — pure mechanism, meaningless to a semanticist — appears
87 times. `k::configuration::` appears 25 times. `KCell`'s type is spelled
`k::configuration::KCell<k::builtin::KSequence>` in the configuration.

None of these spellings is wrong, but the *default* spelling of the most
common concept in the language should be its shortest, and here it is close
to its longest. Compare how K spells its most common concept — a sort
position — as a bare capitalized word.

## Cause 5: bookkeeping the object language forces on the host

Smaller irritants, listed for completeness:

- `#[allow(unused_imports)] use k::{cells, map};` with an explanatory comment
  about compiler-owned islands — leaked implementation detail.
- `impl KItem for Int {} impl KResult for Int {} impl Expr for Int {}` plus
  `#[k::subsort] impl Value for Int {}` — four impls to state
  `syntax Value ::= Int` plus two membership facts (K: 2 short lines for both
  Int and Bool).
- `group = "seq_stmt"` with a comment apologizing that groups must be
  Rust-identifier-shaped while K's group was `seq-stmt`.
- `format = "%1 %2%3%4 %5"` strings copied verbatim from K, including a
  comment noting one K format string is not even expressible.
- `#[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]` on
  the configuration impl — host-language lint pressure on non-host code.

## What is *not* wrong

To keep the proposals honest, the things the current surface gets right and
must not lose:

- **Every name resolves.** `Add`, `Expr`, `int::add` are real items; go-to-def,
  find-references, and rename work. This is the project's core bet and no
  proposal may break it for *declarations* (charter: name compatibility).
- **Rules are visibly rules.** `#[k::rule]` marks relational, unordered
  clauses; nothing pretends to be ordinary Rust control flow (charter:
  semantic honesty).
- **The pre/post structure is genuinely function-shaped** — pattern in,
  term out — which is the right Rust analogy for a rewrite.
- **Explicitness where K is implicit is sometimes a feature**: `result =
  KResult` on strictness, named rule labels, and explicit `#[k::subsort]`
  edges surface real semantic content that K hides in defaults. Proposals
  should compress *repetition*, not *distinctions* — the design doc's
  ergonomic-macro contract (design.md §"Surface layers and ergonomic
  macros") already draws exactly this line.

## Summary of causes → proposals

| # | Cause | Attacked by |
|---|-------|-------------|
| 1 | Per-production struct + attribute volume | 02 (enum tiers), 01 (attribute defaults) |
| 2 | String-keyed precedence/associativity disconnection | 02 (co-located grammar) |
| 3 | Rule scaffolding: paths, frames, pre/post duplication, variable pre-declaration | 01 (path fix), 03 (framing + in-place rewrite), 04 (rule families) |
| 4 | `Term<dyn …>` / path noise | 01 (mechanical cleanups) |
| 5 | Host-language bookkeeping leaks | 01 (mechanical cleanups) |

Proposal 05 (a full K-mirror DSL) is assessed and mostly rejected; 06 compares
everything side by side and states a phased recommendation.

## The diagnosis behind the diagnosis: one surface doing two jobs

A caveat that reframes the whole table (expanded in 08): imp.rs is a single
surface serving simultaneously as *the DSL people author in* and as *the
explicit form the DSL compiles into*. The five causes split along that
line. Causes 4 and 5 (and parts of 1) are defects of the compilation
target — fixable in place by conservative compiler work. But the dominant
costs — rule scaffolding (cause 3) and production ceremony (cause 1) — are
largely *constitutive* of a good explicit target: r3 chose the fn-item
shape for rules precisely to make pre/post structure and item identity
explicit. Those costs cannot be polished away from the target without
eroding what the target is for; they can only be removed by giving authors
a distinct layer that expands into it. `pub fn done` is the canonical
example: cleanups take it from 12 lines to 10; only an authoring-layer
construct reaches 4 or 2. So "what is not wrong" above should be read
per-surface: explicitness is a virtue of the target that the authoring
layer is free to compress, because the expansion preserves it.
