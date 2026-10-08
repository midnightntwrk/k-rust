use krs_macros::{alias, constructor, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Done;

#[alias(priority = 40)] //~ ERROR static rules have no priority
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    Done
}

fn main() {}
