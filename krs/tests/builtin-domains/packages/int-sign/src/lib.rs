//! Negative Int literals (KF-006): the sign belongs to the literal.
//!
//! `-1` is one K `Int` token in equation heads, readable patterns, results, and
//! programs; a literal is a value and can be matched. `int::div` truncates like
//! Rust's `/`, shown on the four sign combinations of 7 and 3.

use k::builtin::{Bool, Int, KSequence, int};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence(left (Div))]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("{lhs} / {rhs}")] #[k::seqstrict]
    Div { lhs: Exp, rhs: Exp },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

/// `int::div` on program values, including negative ones.
#[k::function(total, sort = Int, syntax = "quot({a}, {b})")]
pub struct Quot {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn quot(k::term![Quot(a, b)]: Term<Int>) -> Term<Int> {
    int::div(a, b)
}

/// The sign of an Int, with `-1` matched as a literal.
#[k::function(total, sort = Int, syntax = "sgn({value})")]
pub struct Sgn {
    pub value: Term<Int>,
}

#[k::equation]
fn sgn_minus_one(k::term![Sgn(-1)]: Term<Int>) -> Term<Int> {
    -1
}

#[k::requires(int::lt(value, -1))]
#[k::equation]
fn sgn_negative(k::term![Sgn(value)]: Term<Int>) -> Term<Int> {
    -1
}

#[k::requires(int::eq(value, 0))]
#[k::equation]
fn sgn_zero(k::term![Sgn(value)]: Term<Int>) -> Term<Int> {
    0
}

#[k::requires(int::gt(value, 0))]
#[k::equation]
fn sgn_positive(k::term![Sgn(value)]: Term<Int>) -> Term<Int> {
    1
}

k::rules! {
    for Exp;
    use Op::*;

    div_by_minus_one: Div { lhs, rhs: -1 } => int::sub(0, lhs) where lhs: Int;
    div_by_one      : Div { lhs, rhs: 1 }  => lhs              where lhs: Int;
}
