use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Guarded {
    pub value: Term<renamed_krs::builtin::int::Int>,
}

#[rule]
fn invalid(Guarded { value }: Term<dyn Expr>) -> Term<dyn Expr> {
    Guarded { value: post } //~ ERROR cannot find type `post`
}

fn main() {}
