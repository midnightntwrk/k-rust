use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Done;

#[rule]
#[renamed_krs::exists(x: renamed_krs::builtin::int::Int)] //~ ERROR an existential must occur in the rule's result or ensures condition
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    Done
}

fn main() {}
