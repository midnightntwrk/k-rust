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
#[renamed_krs::requires(value.lt(1))] //~ ERROR a method call names its builtin domain in a turbofish: write `lt::<Int>`, `lt::<String>`, or `lt::<Float>`
fn guarded(Guarded { value }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Guarded { value }
}

fn main() {}
