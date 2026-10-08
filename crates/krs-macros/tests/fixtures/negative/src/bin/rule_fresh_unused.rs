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
#[renamed_krs::fresh(n: Int)] //~ ERROR a fresh binder must occur in the rule's result or ensures condition
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    Done
}

fn main() {}
