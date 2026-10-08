use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;
use renamed_krs::builtin::int::Int;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Done;

#[constructor(sort = Expr)]
pub struct Num {
    pub value: Term<Int>,
}

#[rule]
#[renamed_krs::fresh(value: Int)] //~ ERROR a fresh value cannot be matched: it does not exist until the step happens, so it cannot also be a pattern binding; rename it
fn invalid(Num { value }: Term<dyn Expr>) -> Term<dyn Expr> {
    Num { value }
}

fn main() {}
