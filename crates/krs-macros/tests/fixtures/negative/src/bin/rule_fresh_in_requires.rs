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
#[renamed_krs::requires(renamed_krs::builtin::int::gt(n, 0))]
#[renamed_krs::fresh(n: Int)] //~ ERROR a fresh value cannot occur in `requires`: the step allocates it only after deciding to apply
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    Num { value: n }
}

fn main() {}
