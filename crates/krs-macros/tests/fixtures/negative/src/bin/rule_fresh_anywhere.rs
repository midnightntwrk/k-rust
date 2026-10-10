use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;
use renamed_krs::builtin::int::Int;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Done;

#[constructor(sort = Expr)]
pub struct Num {
    pub value: Term<Int>,
}

#[rule(anywhere)]
#[renamed_krs::fresh(n: Int)] //~ ERROR fresh values are drawn from the generated counter only by a transition step of the configuration; `#[k::fresh]` is not allowed on an equation, simplification, alias, claim, context, context alias, anywhere rule, or heat or cool rule
fn invalid(Done: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Num { value: n }
}

fn main() {}
