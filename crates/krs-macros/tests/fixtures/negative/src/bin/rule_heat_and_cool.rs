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

#[rule(heat, cool, hole = h)] //~ ERROR a rule is a heating step or a cooling step, not both; write `heat` or `cool`
fn invalid(Wrap { inner: h }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    h
}

fn main() {}
