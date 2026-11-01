use krs_macros::{alias, constructor, sort};
use renamed_krs::Term;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Done;

#[alias(priority = 40)] //~ ERROR a static production's clauses rewrite each of its applications into one term
fn invalid(Done: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Done
}

fn main() {}
