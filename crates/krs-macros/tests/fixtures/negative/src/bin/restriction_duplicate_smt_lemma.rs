use krs_macros::{constructor, equation, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Done;

#[equation(smt_lemma, smt_lemma)] //~ ERROR duplicate argument `smt_lemma`
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    Done
}

fn main() {}
