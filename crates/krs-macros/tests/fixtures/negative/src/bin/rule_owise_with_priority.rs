use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Done;

#[rule(owise, priority = 40)] //~ ERROR owise is priority 200; write one of them
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    Done
}

fn main() {}
