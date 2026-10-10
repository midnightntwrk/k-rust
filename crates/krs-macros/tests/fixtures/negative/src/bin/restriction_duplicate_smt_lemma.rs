use krs_macros::{constructor, equation, sort};
use renamed_krs::Term;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Done;

#[equation(smt_lemma, smt_lemma)] //~ ERROR duplicate argument `smt_lemma`
fn invalid(Done: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Done
}

fn main() {}
