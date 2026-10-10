use krs_macros::{constructor, context, sort};
use renamed_krs::Term;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Wrap {
    pub inner: Term<dyn ExprSort>,
}

#[context(hole = h)]
fn invalid(Wrap { inner: h }: Term<dyn ExprSort>) -> Term<dyn ExprSort> { //~ ERROR a context returns `()`: it says where evaluation may happen and has no after-state; K turns it into a heat rule and a cool rule
    h
}

fn main() {}
