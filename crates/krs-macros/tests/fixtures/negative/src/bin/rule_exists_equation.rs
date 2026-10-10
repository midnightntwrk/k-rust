use krs_macros::{constructor, equation, sort};
use renamed_krs::Term;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Done;

#[equation]
#[renamed_krs::exists(x: renamed_krs::builtin::int::Int)] //~ ERROR existential results and ensures are allowed on claims and transition rules, not on equations, simplifications, or aliases
fn invalid(Done: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    x
}

fn main() {}
