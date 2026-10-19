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
#[renamed_krs::requires(value.lt::<Nat>(1))] //~ ERROR `Nat` is not a builtin domain; a method call names `Int`, `Bool`, `String`, `Float`, `Bytes`, or `K`
fn guarded(Guarded { value }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Guarded { value }
}

fn main() {}
