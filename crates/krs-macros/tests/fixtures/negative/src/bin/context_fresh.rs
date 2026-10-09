use krs_macros::{constructor, context, sort};
use renamed_krs::Term;
use renamed_krs::builtin::int::Int;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Wrap {
    pub inner: Term<dyn Expr>,
}

#[context(hole = h)]
#[renamed_krs::fresh(n: Int)] //~ ERROR fresh values are drawn from the generated counter only by a transition step of the configuration; `#[k::fresh]` is not allowed on an equation, simplification, alias, claim, context, context alias, anywhere rule, or heat or cool rule
fn invalid(Wrap { inner: h }: Term<dyn Expr>) {}

fn main() {}
