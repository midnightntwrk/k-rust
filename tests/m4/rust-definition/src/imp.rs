//! Readable Rust-authored definition of the complete M4 IMP language.
//!
//! This is the production form of the semantics in the upstream `expr.k`,
//! `calc.k`, and `imp.k` modules. The object-language declarations stay visible
//! to rustc and rust-analyzer while KRS owns the symbolic rule bodies.

use k::KResult;
use k::builtin::{Bool, Id, Int, KSequence, Map, bool, int};
// The rule-table parser consumes this operation before rustc sees a call.
#[allow(unused_imports)]
use k::builtin::map;

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

    /// Deliberately not strict: the `while` rule unfolds the loop.
    #[k::syntax("while ({condition}) {body}")]
    While { condition: Expr, body: Stmt },

    #[k::syntax("{{{body}}}")] #[k::format("{{%i%n{body}%d%n}}")]
    Block { body: Stmt },

    #[k::syntax("{{}}")]
    EmptyBlock(),

    #[k::syntax("{first} {second}")] #[k::format("{first}%n{second}")]
    Sequence { first: Stmt, second: Stmt },
}

/// The fixed two-cell calculation state from `calc.k`.
#[k::configuration]
pub struct Machine {
    /// Computation cell, with the next IMP item at the head.
    #[k::cell(color = "green")]
    pub k: KSequence,
    /// Identifier-to-evaluated-value environment.
    #[k::cell(color = "yellow")]
    pub env: Map<Id, Value>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt, env: Map<Id, Value>) -> Self {
        Self {
            k: k::k![pgm],
            env,
        }
    }
}

k::rules! {
    for Expr;
    use Op::*;

    eval_neg:     Neg { value }          => int::sub(0, value);
    eval_not:     Not { value }          => bool::not(value);

    eval_add:     Add { lhs, rhs }       => int::add(lhs, rhs);
    eval_sub:     Sub { lhs, rhs }       => int::sub(lhs, rhs);
    eval_mul:     Mul { lhs, rhs }       => int::mul(lhs, rhs);
    eval_div:     Div { lhs, rhs }       => int::div(lhs, rhs);

    eval_ge:      Ge { lhs, rhs }        => int::ge(lhs, rhs);
    eval_gt:      Gt { lhs, rhs }        => int::gt(lhs, rhs);
    eval_le:      Le { lhs, rhs }        => int::le(lhs, rhs);
    eval_lt:      Lt { lhs, rhs }        => int::lt(lhs, rhs);

    eval_bool_eq: Eq { lhs, rhs }        => bool::eq(lhs, rhs) where lhs: Bool, rhs: Bool;
    eval_int_eq:  Eq { lhs, rhs }        => int::eq(lhs, rhs)  where lhs: Int,  rhs: Int;
    eval_bool_ne: Ne { lhs, rhs }        => bool::ne(lhs, rhs) where lhs: Bool, rhs: Bool;
    eval_int_ne:  Ne { lhs, rhs }        => int::ne(lhs, rhs)  where lhs: Int,  rhs: Int;

    and_true:     And { lhs: true, rhs } => rhs;
    and_false:    And { lhs: false, .. } => false;
    or_true:      Or { lhs: true, .. }   => true;
    or_false:     Or { lhs: false, rhs } => rhs;

    /// A missing environment binding makes this rule inapplicable.
    var: name => value
        where name: Id,
              value: Value,
              have env[name => let value];
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    /// Expose a right-associated statement pair as K sequencing.
    step:     Sequence(s1, s2) => k::k![s1, s2];

    #[k::rule(label = "if-true")]
    if_true:  IfThenElse(true, then_branch, _)  => then_branch;
    #[k::rule(label = "if-false")]
    if_false: IfThenElse(false, _, else_branch) => else_branch;

    #[k::rule(label = "if-else")]
    if_else:  IfThen(condition, body) => IfThenElse(condition, body, EmptyBlock());

    /// Unfold one loop test without making the constructor strict.
    #[k::rule(label = "while")]
    r#while:  While(condition, body) =>
        IfThen(condition, Block(Sequence(body, While(condition, body))));

    #[k::rule(label = "block")]
    block:    Block(body) => k::k![body, EmptyBlock()];
    #[k::rule(label = "done")]
    done:     EmptyBlock() => ();

    /// Consume a value assignment and update the environment simultaneously.
    assign: Assign(name, value) => ()
        where value: Value,
              update env = map::update(env, name, value);
}
