use krs_macros::{constructor, simplification, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Done;

#[simplification(owise)] //~ ERROR a simplification has its own `priority = N`, a simplifier hint; owise has no meaning there
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    Done
}

fn main() {}
