use krs_macros::{constructor, equation, sort};
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

#[equation]
#[renamed_krs::fresh(n: Int)] //~ ERROR fresh values are drawn from the generated counter only by a transition step of the configuration; `#[k::fresh]` is not allowed on an equation, simplification, alias, claim, context alias, or anywhere rule
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    Num { value: n }
}

fn main() {}
