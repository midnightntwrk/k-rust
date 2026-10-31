use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Done;

#[rule(owise, priority = 40)] //~ ERROR owise applies where no other rule or equation applies, which no priority orders; write one of them
fn invalid(Done: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Done
}

fn main() {}
