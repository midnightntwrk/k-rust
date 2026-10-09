//! Restating IMP, the comparison for the local-rewrite fixture (KF-011).
//!
//! This is `tests/imp`'s readable IMP: `var` and `assign` restate the before
//! and after of each cell they touch. `assign` writes the environment with
//! `map::update`, which adds a variable that is not declared yet; the
//! single-body `assign` of the local-rewrite fixture requires the key.

use k::KResult;
use k::builtin::{Bool, Id, Int, KSequence, Map, bool, int, map};

k::sorts! {
    #[k::bracket("(", ")")]
    Expr;
    impl Expr for Id;

    Value: Expr + KResult;
    impl Value for Int, Bool;

    Stmt;
}

#[k::constructors(sort = Expr, result = KResult)]
#[k::precedence(
    (Neg, Not)
    > left (Mul, Div)
    > left (Add, Sub)
    > left (Ge, Gt, Le, Lt)
    > left (Eq, Ne)
    > left (And)
    > left (Or)
)]
#[rustfmt::skip]
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

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(
    stmt (Assign, IfThenElse, IfThen, While, Block, EmptyBlock)
    > right seq_stmt (Sequence)
)]
#[rustfmt::skip]
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

    #[k::syntax("{{}}")]
    EmptyBlock(),

    #[k::syntax("{first} {second}")] #[k::format("{first}%n{second}")]
    Sequence { first: Stmt, second: Stmt },
}

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
        Self { k: k::k![pgm], env }
    }
}

k::rules! {
    for Expr;
    use Op::*;

    eval_neg    : Neg { value }          => int::sub(0, value);
    eval_not    : Not { value }          => bool::not(value);

    eval_add    : Add { lhs, rhs }       => int::add(lhs, rhs);
    eval_sub    : Sub { lhs, rhs }       => int::sub(lhs, rhs);
    eval_mul    : Mul { lhs, rhs }       => int::mul(lhs, rhs);
    eval_div    : Div { lhs, rhs }       => int::div(lhs, rhs);

    eval_ge     : Ge { lhs, rhs }        => int::ge(lhs, rhs);
    eval_gt     : Gt { lhs, rhs }        => int::gt(lhs, rhs);
    eval_le     : Le { lhs, rhs }        => int::le(lhs, rhs);
    eval_lt     : Lt { lhs, rhs }        => int::lt(lhs, rhs);

    eval_bool_eq: Eq { lhs, rhs }        => bool::eq(lhs, rhs) where lhs: Bool, rhs: Bool;
    eval_int_eq : Eq { lhs, rhs }        => int::eq(lhs, rhs)  where lhs: Int, rhs: Int;
    eval_bool_ne: Ne { lhs, rhs }        => bool::ne(lhs, rhs) where lhs: Bool, rhs: Bool;
    eval_int_ne : Ne { lhs, rhs }        => int::ne(lhs, rhs)  where lhs: Int, rhs: Int;

    and_true    : And { lhs: true, rhs } => rhs;
    and_false   : And { lhs: false, .. } => false;
    or_true     : Or { lhs: true, .. }   => true;
    or_false    : Or { lhs: false, rhs } => rhs;
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    /// Expose the right-associated statement pair as K sequencing.
    step    : Sequence(s1, s2)         => k::k![s1, s2];

    /// Select the true branch of an evaluated conditional.
    if_true : IfThenElse(true, s1, _)  => s1;
    /// Select the false branch of an evaluated conditional.
    if_false: IfThenElse(false, _, s2) => s2;

    /// Normalize the no-else form with an explicit empty branch.
    if_else : IfThen(c, s)             => IfThenElse(c, s, EmptyBlock());

    /// Unfold one loop test without making the constructor strict.
    r#while : While(c, s)              => IfThen(c, Block(Sequence(s, While(c, s))));

    /// Expose a nonempty block body followed by an empty block.
    block   : Block(s)                 => k::k![s, EmptyBlock()];

    /// Remove an empty block from the computation cell.
    done    : EmptyBlock()             => ();
}

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
