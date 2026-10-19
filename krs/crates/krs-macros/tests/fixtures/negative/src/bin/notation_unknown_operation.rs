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
#[renamed_krs::requires(value.concat::<Int>(1))] //~ ERROR the builtin module `int` has no operation `concat`; `concat::<String>` or `concat::<Bytes>` exist
fn guarded(Guarded { value }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Guarded { value }
}

fn main() {}
