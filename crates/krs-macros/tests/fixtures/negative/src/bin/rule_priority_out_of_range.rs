use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Done;

#[rule(priority = 255)] //~ ERROR k-rust ranks rule priorities 0..=254
fn invalid(Done: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Done
}

fn main() {}
