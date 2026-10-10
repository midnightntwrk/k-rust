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

#[rule(heat)] //~ ERROR a heat or cool rule names the subterm it moves with `hole = x`, K's HOLE; bind `x` on the left side
fn invalid(Wrap { inner: h }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    h
}

fn main() {}
