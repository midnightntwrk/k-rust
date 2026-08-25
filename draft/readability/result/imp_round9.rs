//! IMP authoring surface, **round-9 variant**.
//!
//! Same definition as `imp_round6.rs` (rounds 3–8; see its header for the
//! accumulated rationale), revised by the round-9 review of the precedence
//! notation. One change:
//!
//!   [r9] **Positional tier markers → an enum-level precedence chain.**
//!        Review datum: `#[k::precedence(left)]` on the first variant of a
//!        group misreads as a per-variant fact ("`Mul` uses
//!        left-precedence"). Rust attributes attach to single items, so a
//!        marker cannot say "opens a block spanning the following
//!        variants" on its face, and the adjacency convention (unmarked
//!        variants join the current group) is unguessable — the same
//!        on-its-face criterion that drove rounds 7–8, one level deeper.
//!        The ecosystem survey (11-variant-group-prior-art.md) found
//!        sticky markers in exactly two shipped designs (LALRPOP
//!        alternatives, nom-derive `SetEndian`) against three recorded
//!        retreats from the shape (clap #3269, egglog `with-ruleset`,
//!        binserde's unimplemented attribute), and found that
//!        container-level member lists are the only shape with a hard
//!        stale-name story (subenum, bitflags, bevy `.chain()`).
//!
//!        Landed design: one enum-level attribute states the whole
//!        hierarchy, in the same chain grammar as the freestanding
//!        `k::precedence!` block. A chain element is a parenthesized
//!        member list, optionally preceded by an associativity keyword
//!        (`left`/`right`; bare = non-associative, K's bare `>`) and an
//!        optional group name for the emitted grammar and cross-family
//!        references. `>` reads "binds tighter than" — direction lives in
//!        the operator, not in a position convention. Sync is fail-fast
//!        at expansion: the attribute sees the full variant list in the
//!        same token stream, so every variant must appear exactly once —
//!        missing, unknown (with did-you-mean), and duplicate names are
//!        hard errors, a total check the marker design could never make
//!        (any variant is trivially "in" whatever block precedes it).
//!        Variant order in the enum body is now purely presentational;
//!        the silent-reorder footgun and its golden test disappear.
//!        rustfmt leaves custom attribute token streams alone, so the
//!        multi-line chain layout is stable without `#[rustfmt::skip]`
//!        (the enum body keeps its skip for the attribute-pair-per-line
//!        table, as before).
//!
//!        Layer 2 is unchanged: per-variant `group = …` arguments plus
//!        freestanding `precedence!`/`associativity!` blocks, with
//!        generated (`op_tier0`…) or author-named (`stmt`, `seq_stmt`)
//!        group identities. The freestanding `k::precedence!` block
//!        remains for cross-family chains, now as the degenerate
//!        names-only case of the same grammar.
//!
//! The round-9 review's second finding (the `for Machine` rule table) is
//! deliberately NOT addressed here — pinned in 12-machine-rules-pin.md
//! for a follow-up session; the `k::rules!` sections below are unchanged
//! from round 6.

use k::KResult;
use k::builtin::{Bool, Id, Int, KSequence, Map, bool, int, map};

// ---------------------------------------------------------------------------
// Sorts (expr.k EXPR-SYNTAX)
//
// One entry per sort; each generates a membership trait (`ExprSort`) and a
// type alias for the frequent spelling (`type Expr = Term<dyn ExprSort>;`).
// Supertrait bounds are written on the sort names. [r3] Framework sorts
// (`KResult`, the evaluated-value sort) are imported, not declared. [r7]
// `#[k::bracket]` gives the sort's grouping delimiters: `(e)` parses as
// plain `e` and creates no node. [r7] `impl` lines declare membership of
// existing types, under the sort they populate. [r8]
// ---------------------------------------------------------------------------

k::sorts! {
    #[k::bracket("(", ")")]
    Expr;
    impl Expr for Id;           // a bare identifier is an expression

    Value: Expr + KResult;
    impl Value for Int, Bool;   // a value is an integer or a boolean

    Stmt;
}

// ---------------------------------------------------------------------------
// Expression grammar (expr.k:13-32)
//
// The precedence chain above the enum states the whole operator hierarchy
// in one expression: `>` reads "binds tighter than", an associativity
// keyword prefixes its group (bare = non-associative), and every variant
// must appear exactly once — missing, unknown, and duplicate names are
// expansion-time errors, so the chain cannot drift out of sync with the
// variants. [r9] Variant order and blank-line grouping below are
// presentation only, kept aligned with the chain for scanning.
// Bare `#[k::strict]`/`#[k::seqstrict]` cover all fields; a field list
// (`#[k::strict(lhs)]`) restricts them — K's `strict(1)` with names. [r6e]
// `result = KResult` defines "evaluated" for those attributes: a subterm
// is done once it reaches that sort. [r7]
// ---------------------------------------------------------------------------

#[k::constructors(sort = Expr, result = KResult)]
#[k::precedence(
    (Neg, Not)              // binds tightest
    > left (Mul, Div)
    > left (Add, Sub)
    > left (Ge, Gt, Le, Lt)
    > left (Eq, Ne)
    > left (And)
    > left (Or)
)]
#[rustfmt::skip] // keep the table layout: one production per line pair
pub enum Op {
    #[k::syntax("-{value}")] #[k::strict]
    Neg { value: Expr },
    #[k::syntax("!{value}")] #[k::strict]
    Not { value: Expr },

    #[k::syntax("{lhs} * {rhs}")] #[k::seqstrict]
    Mul { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} / {rhs}")] #[k::seqstrict]
    Div { lhs: Expr, rhs: Expr },

    #[k::syntax("{lhs} + {rhs}")] #[k::seqstrict]
    Add { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} - {rhs}")] #[k::seqstrict]
    Sub { lhs: Expr, rhs: Expr },

    #[k::syntax("{lhs} >= {rhs}")] #[k::seqstrict]
    Ge { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} > {rhs}")] #[k::seqstrict]
    Gt { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} <= {rhs}")] #[k::seqstrict]
    Le { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} < {rhs}")] #[k::seqstrict]
    Lt { lhs: Expr, rhs: Expr },

    #[k::syntax("{lhs} == {rhs}")] #[k::seqstrict]
    Eq { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} != {rhs}")] #[k::seqstrict]
    Ne { lhs: Expr, rhs: Expr },

    #[k::syntax("{lhs} && {rhs}")] #[k::strict(lhs)]
    And { lhs: Expr, rhs: Expr },

    #[k::syntax("{lhs} || {rhs}")] #[k::strict(lhs)]
    Or { lhs: Expr, rhs: Expr },
}

// ---------------------------------------------------------------------------
// Statement grammar (calc.k CALC-SYNTAX + imp.k IMP-SYNTAX)
//
// One co-located family. [r4] The chain here names its groups (`stmt`,
// `seq_stmt`): an ident before a member list names that group for the
// emitted grammar and for cross-family chains — this is calc.k's
// `syntax priority stmt > seq-stmt` verbatim. [r9] (`left`/`right` are
// reserved words in this position; a group may not be named either.)
// `<Sort>Syntax` is the default family name when no natural name (like
// `Op`) exists. [r6f]
// ---------------------------------------------------------------------------

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(
    stmt (Assign, IfThenElse, IfThen, While, Block, EmptyBlock)
    > right seq_stmt (Sequence)
)]
#[rustfmt::skip] // keep the table layout: one production per line pair
pub enum StmtSyntax {
    #[k::syntax("{name} = {value};")] #[k::strict(value)]
    Assign { name: Id, value: Expr },

    /// Dangling else: `avoid` makes the parser prefer the `IfThen` reading.
    #[k::syntax("if ({condition}) {then_branch} else {else_branch}", avoid)]
    #[k::strict(condition)]
    IfThenElse { condition: Expr, then_branch: Stmt, else_branch: Stmt },

    #[k::syntax("if ({condition}) {body}")]
    IfThen { condition: Expr, body: Stmt },

    /// Deliberately not strict: the `[while]` rule unfolds the loop instead.
    #[k::syntax("while ({condition}) {body}")]
    While { condition: Expr, body: Stmt },

    #[k::syntax("{{{body}}}")] #[k::format("{{%i%n{body}%d%n}}")]
    Block { body: Stmt },

    // Zero-field tuple variant on purpose: `EmptyBlock()` is then a legal
    // Rust pattern *and* constructor at every use site. [r6a fix]
    #[k::syntax("{{}}")]
    EmptyBlock(),

    #[k::syntax("{first} {second}")] #[k::format("{first}%n{second}")]
    Sequence { first: Stmt, second: Stmt },
}

// ---------------------------------------------------------------------------
// Configuration (calc.k:22-24)
//
// A `#[k::cell]` field is a leaf cell; the computation cell is the one of
// sort `KSequence`. Wrappers (`Cell<…>`, `KCell`) belong to the expansion.
// Config-var names derive from the init parameters (`pgm` → `$PGM`), and
// the variable that initializes the computation cell is `main`. [r6g]
// ---------------------------------------------------------------------------

/// The oracle's fixed two-cell calculation state.
#[k::configuration]
pub struct Machine {
    /// K's computation cell: the continuation, head-first.
    #[k::cell(color = "green")]
    pub k: KSequence,
    #[k::cell(color = "yellow")]
    pub env: Map<Id, Value>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt, env: Map<Id, Value>) -> Self {
        Self { k: k![pgm], env }
    }
}

// ---------------------------------------------------------------------------
// Expression rules (expr.k EXPR-RULES)
//
// `for Expr;` anchors every clause at the head of the computation cell —
// K's completion of a cell-less rule — with the tail framed. [r6c]
// Binder sorts are inferred from all occurrences, including the builtins on
// the right; the `Eq`/`Ne` clauses carry the `where` narrowing that is the
// only thing separating them. [r6b] The block expands to 18 independent
// `#[k::rule]` fns named by clause; `use` is block-local. [04, r6h]
// ---------------------------------------------------------------------------

k::rules! {
    for Expr;
    use Op::*;

    eval_neg:     Neg { value }           => int::sub(0, value);
    eval_not:     Not { value }           => bool::not(value);

    eval_add:     Add { lhs, rhs }        => int::add(lhs, rhs);
    eval_sub:     Sub { lhs, rhs }        => int::sub(lhs, rhs);
    eval_mul:     Mul { lhs, rhs }        => int::mul(lhs, rhs);
    eval_div:     Div { lhs, rhs }        => int::div(lhs, rhs);

    eval_ge:      Ge { lhs, rhs }         => int::ge(lhs, rhs);
    eval_gt:      Gt { lhs, rhs }         => int::gt(lhs, rhs);
    eval_le:      Le { lhs, rhs }         => int::le(lhs, rhs);
    eval_lt:      Lt { lhs, rhs }         => int::lt(lhs, rhs);

    eval_bool_eq: Eq { lhs, rhs }         => bool::eq(lhs, rhs)  where lhs: Bool, rhs: Bool;
    eval_int_eq:  Eq { lhs, rhs }         => int::eq(lhs, rhs)   where lhs: Int,  rhs: Int;
    eval_bool_ne: Ne { lhs, rhs }         => bool::ne(lhs, rhs)  where lhs: Bool, rhs: Bool;
    eval_int_ne:  Ne { lhs, rhs }         => int::ne(lhs, rhs)   where lhs: Int,  rhs: Int;

    and_true:     And { lhs: true, rhs }  => rhs;
    and_false:    And { lhs: false, .. }  => false;
    or_true:      Or { lhs: true, .. }    => true;
    or_false:     Or { lhs: false, rhs }  => rhs;
}

// ---------------------------------------------------------------------------
// Control flow (calc.k CALC + imp.k IMP)
//
// Same anchoring as above [r6c]: the header sort constrains the pattern;
// the right side is a Stmt, a spliced sequence (`k![…]` — K's `~>`), or
// `()` (K's `.K`). Clauses are unordered and expand to independent named
// rules — overlap is a diagnostic, never first-wins; labels default to the
// clause name with `_` → `-` (`r#while` names the K label `while`). [r5]
// ---------------------------------------------------------------------------

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    /// Expose the right-associated statement pair as K sequencing.
    step:     Sequence(s1, s2) => k![s1, s2];

    /// Select the branch of an evaluated conditional.
    if_true:  IfThenElse(true, s1, _)  => s1;
    if_false: IfThenElse(false, _, s2) => s2;

    /// Normalize the no-else form with an explicit empty branch.
    if_else:  IfThen(c, s) => IfThenElse(c, s, EmptyBlock());

    /// Unfold one loop test without making the constructor strict.
    r#while:  While(c, s) => IfThen(c, Block(Sequence(s, While(c, s))));

    /// Expose a nonempty block body followed by an empty block.
    block:    Block(s) => k![s, EmptyBlock()];

    /// Remove an empty block from the computation cell.
    done:     EmptyBlock() => ();
}

// The two rules that touch more than the k head match the machine itself.
// NOTE [r9]: this form is under active redesign — see
// 12-machine-rules-pin.md for the critique (no Rust idiom matches the
// anonymous cell record; the for-Sort/for-Machine split is a mechanism
// cliff K does not have) and the candidate replacements. Kept as-is from
// round 6 until that follow-up session.
k::rules! {
    for Machine;
    use StmtSyntax::Assign;

    /// Replace an identifier at the head of `k` with its mapped value.
    var: {
           k: [name, ..],
           env: { name -> value, .. }
        } => {
            k: [value, ..]
        }
        where name: Id;

    /// Consume a value assignment and update the environment map.
    assign:
        {
            k: [Assign(name, value), ..],
            env: e
        } => {
            k: [..],
            env: map::update(e, name, value)
        }
        where value: Value;
}
