use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Done;

#[rule]
#[renamed_krs::requires(true)]
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    Done
}

fn main() {}
