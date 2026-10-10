use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;
use renamed_krs::builtin::int::Int;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Num {
    pub value: Term<Int>,
}

#[constructor(sort = Expr)]
pub struct Wrap {
    pub inner: Term<dyn ExprSort>,
}

#[rule(hole = h)] //~ ERROR `hole` and `result` are keys of a heat or cool rule; add `heat` or `cool`
fn invalid(Wrap { inner: h }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    h
}

fn main() {}
