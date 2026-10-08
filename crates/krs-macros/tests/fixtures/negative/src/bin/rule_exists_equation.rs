use krs_macros::{constructor, equation, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Done;

#[equation]
#[renamed_krs::exists(x: renamed_krs::builtin::int::Int)] //~ ERROR existential results and ensures are allowed on claims and transition rules, not on equations, simplifications, or aliases
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    x
}

fn main() {}
