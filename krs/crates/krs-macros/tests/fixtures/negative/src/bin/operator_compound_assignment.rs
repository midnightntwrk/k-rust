use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;
use renamed_krs::builtin::int::Int;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Counter {
    pub value: Term<Int>,
}

#[rule]
fn bump(Counter { value }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Counter { value: value += 1 } //~ ERROR `+=` assigns, and a term has nothing to assign to; write the value `a + b`
}

fn main() {}
