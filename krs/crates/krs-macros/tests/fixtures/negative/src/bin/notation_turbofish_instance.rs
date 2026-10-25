use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;
use renamed_krs::builtin::int::Int;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Guarded {
    pub value: Term<Int>,
}

#[rule]
#[renamed_krs::requires(value.eq::<K, Int>(1))] //~ ERROR the turbofish of a method call names one builtin domain by its bare name
fn guarded(Guarded { value }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Guarded { value }
}

fn main() {}
