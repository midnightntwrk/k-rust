use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Done;

#[rule]
#[renamed_krs::requires(true)] //~ ERROR a rule condition must be an object-Bool term constructor, not a host literal
fn invalid(Done: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Done
}

fn main() {}
