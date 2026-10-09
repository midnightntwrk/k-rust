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

#[rule(hole = h)] //~ ERROR `hole` and `result` are keys of a heat or cool rule; add `heat` or `cool`
fn invalid(Wrap { inner: h }: Term<dyn Expr>) -> Term<dyn Expr> {
    h
}

fn main() {}
