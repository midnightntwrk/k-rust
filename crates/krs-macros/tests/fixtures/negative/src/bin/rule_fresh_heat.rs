use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;
use renamed_krs::builtin::int::Int;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Num {
    pub value: Term<Int>,
}

#[constructor(sort = Expr)]
pub struct Wrap {
    pub inner: Term<dyn Expr>,
}

#[rule(heat, hole = h)]
#[renamed_krs::fresh(n: Int)] //~ ERROR fresh values are drawn from the generated counter only by a transition step of the configuration; `#[k::fresh]` is not allowed on an equation, simplification, alias, claim, context alias, anywhere rule, or heat or cool rule
fn invalid(Wrap { inner: h }: Term<dyn Expr>) -> Term<dyn Expr> {
    Num { value: n }
}

fn main() {}
