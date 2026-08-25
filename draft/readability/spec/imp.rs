//! IMP authoring surface — **normative specimen**.
//!
//! This file is the settled target of the readability investigation: what a
//! human (or agent) writes and reviews once the layer-1 authoring surface
//! exists. It is `result/imp_round9.rs` with the one pinned section
//! resolved (the `for Machine` rule table — candidate A, decided
//! 2026-08-21; see `decisions.md` §E7). It does not compile today: see
//! `README.md` for the build gap list. The `[rN]`/`[…]` tags in section
//! banners resolve in `decisions.md`.
//!
//! Reference points: the original K definition is
//! `inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics/{expr,calc,imp}.k`
//! (145 raw / 108 code lines); this file is 1.2× K by code lines. Its
//! expansion target is `imp.expanded.rs` (layer 2, the reference surface —
//! today's `tests/m4/rust-definition/src/imp.rs` shape).

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
// keyword prefixes its group (bare = no associativity constraint, K's
// bare `>` — the unary tier needs `!!x` to nest), and every variant
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
// `syntax priority stmt > seq-stmt` verbatim. [r9] (`left`/`right`/
// `non_assoc` are reserved words in this position; a group may not be
// named any of them.) The bare `stmt` group is deliberate: statements
// nest inside statements, so it must carry no associativity constraint.
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

// ---------------------------------------------------------------------------
// Machine rules (calc.k:28-34)
//
// The two rules that touch more than the k head match the machine itself:
// an anonymous cell record that mirrors the `Machine` configuration struct
// and the layer-2 expansion nearly 1:1 — candidate A of the 2026-08-21
// review, decided [E7]. Convention: a cell named in the pattern but absent
// from the result is unchanged (framed) [E7]. Layout: multi-line, one cell
// per line — enforced by `krs fmt` [F1]; single-cell table clauses above
// stay one-liners. Exact placement and whole-table alignment are settled
// by [F5]; this is the normative rendering of the 14 §Verdict sketch.
// ---------------------------------------------------------------------------

k::rules! {
    for Machine;
    use StmtSyntax::Assign;

    /// Replace an identifier at the head of `k` with its mapped value.
    var: {
        k: [name, ..],
        env: { name -> value, .. },
    } => {
        k: [value, ..],
    }
    where name: Id;

    /// Consume a value assignment and update the environment map.
    assign: {
        k: [Assign(name, value), ..],
        env: e,
    } => {
        k: [..],
        env: map::update(e, name, value),
    }
    where value: Value;
}
