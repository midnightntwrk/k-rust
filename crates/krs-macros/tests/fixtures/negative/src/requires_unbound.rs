use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Guarded {
    pub value: Term<renamed_krs::builtin::int::Int>,
}

#[rule]
#[renamed_krs::requires(renamed_krs::builtin::int::gt(unbound, 0))]
fn invalid(Guarded { value }: Term<dyn Expr>) -> Term<dyn Expr> {
    Guarded { value }
}

fn main() {}
