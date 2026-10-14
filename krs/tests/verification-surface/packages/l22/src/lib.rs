//! K tutorial lesson 1.22's language (KF-039): assignments to `$`-variables
//! in a store, sequencing, a strict `if`, and a strict `<`, plus `div`, which
//! evaluates only for a nonzero divisor, and the partial function `pf`,
//! defined on positive integers. Its claims and lemmas live in the
//! `krs-verification-surface-l22-verification` package, which adds the
//! `$`-identifier token to its definition, as upstream IMP-VERIFICATION does.
//! The `krs-verification-surface-l22-lesson` package takes the other route: it
//! holds only a spec module, which declares the token itself.

use k::builtin::{Id, Int, KSequence, Map, int, map};
use k::{KResult, Term};

k::sorts! {
    Exp;
    impl Exp for Id;
    Value: Exp + KResult;
    impl Value for Int, k::builtin::Bool;
    Stmt;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Lt, Div))]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("{lhs} < {rhs}")] #[k::seqstrict]
    Lt { lhs: Exp, rhs: Exp },
    #[k::syntax("div({lhs}, {rhs})")] #[k::seqstrict]
    Div { lhs: Exp, rhs: Exp },
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Assign, If) > right (Seq))]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("{name} = {value};")] #[k::strict(value)]
    Assign { name: Id, value: Exp },
    #[k::syntax("if ({condition}) {then_branch} else {else_branch}")]
    #[k::strict(condition)]
    If { condition: Exp, then_branch: Stmt, else_branch: Stmt },
    #[k::syntax("{first} {second}")]
    Seq { first: Stmt, second: Stmt },
}

/// A partial function, defined on positive integers only.
#[k::function(partial, sort = Int, syntax = "pf({value})")]
pub struct Pf {
    pub value: Term<Int>,
}

/// `pf(x)` is `x` when `x` is positive, and undefined otherwise.
#[k::equation]
#[k::requires(int::gt(value, 0))]
fn pf_positive(k::term![Pf(value)]: Term<Int>) -> Term<Int> {
    value
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub store: Map<Id, Value>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt, store: Map<Id, Value>) -> Self {
        Self {
            k: k::k![pgm],
            store,
        }
    }
}

k::rules! {
    for Exp;
    use Op::*;

    eval_lt: Lt { lhs, rhs } => int::lt(lhs, rhs);
}

/// `div(a, b)` evaluates only when the divisor is not zero.
#[k::rule(label = "eval-div")]
#[k::requires(int::ne(rhs, 0))]
fn eval_div(lhs: Term<Int>, rhs: Term<Int>, k::term![Op::Div(lhs, rhs)]: Term<Exp>) -> Term<Exp> {
    int::div(lhs, rhs)
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    step    : Seq(s1, s2)      => k::k![s1, s2];
    if_true : If(true, s1, _)  => s1;
    if_false: If(false, _, s2) => s2;
}

k::rules! {
    for Machine;
    use StmtSyntax::Assign;

    /// Read a variable as the lesson does, `STORE [ X ]`.
    var: {
        k: [name, ..],
        store: s,
    } => {
        k: [k::project!(Value, map::get(s, name)), ..],
        store: s,
    }
    where name: Id;

    assign: {
        k: [Assign(name, value), ..],
        store: s,
    } => {
        k: [..],
        store: map::update(s, name, value),
    }
    where value: Value;
}
