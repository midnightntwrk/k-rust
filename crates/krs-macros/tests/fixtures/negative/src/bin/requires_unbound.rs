use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Guarded {
    pub value: Term<renamed_krs::builtin::int::Int>,
}

#[rule]
#[renamed_krs::requires(renamed_krs::builtin::int::gt(unbound, 0))] //~ ERROR cannot find type `unbound`
fn invalid(Guarded { value }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Guarded { value }
}

fn main() {}
