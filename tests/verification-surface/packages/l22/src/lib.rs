//! K tutorial lesson 1.22's language (KF-039): assignments to `$`-variables
//! in a store, sequencing, a strict `if`, and a strict `<`, plus `div`, which
//! evaluates only for a nonzero divisor, and the partial function `pf`,
//! defined on positive integers. Its claims and lemmas live in the
//! `krs-verification-surface-l22-verification` package, which adds the
//! `$`-identifier token to its definition, as upstream IMP-VERIFICATION does.
//!
//! The `LESSON-SPEC` spec module below takes the other route: it declares the
//! token itself, so the token is part of the proof input only and `kompile`
//! never sees it, and its claim writes `$n` bare.

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

/// A lesson's proof module that needs `$` identifiers only in its claims.
#[k::spec_module(name = "LESSON-SPEC", imports = [crate])]
mod lesson_spec {
    use super::{Int, Machine, Map, StmtSyntax, Term, map};

    /// Every `$`-prefixed identifier, for this module's claims only.
    #[k::token(regex = r"\$[a-zA-Z0-9_]+")]
    pub type DollarId = k::builtin::Id;

    /// `$n = n; $m = m;` stores both values under their names.
    #[k::claim(all_paths, label = "dollar-assign")]
    fn dollar_assign(
        n: Term<Int>,
        m: Term<Int>,
        s: Term<Map>,
        k::cells! {
            k: k::configuration::KCell(
                StmtSyntax::Seq(
                    StmtSyntax::Assign(k::id!("$n"), n),
                    StmtSyntax::Assign(k::id!("$m"), m),
                ),
                tail @ ..
            ),
            store: k::configuration::Cell(s),
            state @ ..
        }: Machine,
    ) -> Machine {
        k::cells! {
            k: k::configuration::KCell(..tail),
            store: k::configuration::Cell(map::update(
                map::update(s, k::id!("$n"), n),
                k::id!("$m"),
                m,
            )),
            ..state
        }
    }
}
