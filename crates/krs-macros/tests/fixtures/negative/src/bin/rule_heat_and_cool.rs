use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;
use renamed_krs::builtin::int::Int;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Num {
    pub value: Term<Int>,
}

#[constructor(sort = Expr)]
pub struct Wrap {
    pub inner: Term<dyn Expr>,
}

#[rule(heat, cool, hole = h)] //~ ERROR a rule is a heating step or a cooling step, not both; write `heat` or `cool`
fn invalid(Wrap { inner: h }: Term<dyn Expr>) -> Term<dyn Expr> {
    h
}

fn main() {}
