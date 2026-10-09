use krs_macros::{constructor, context, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Wrap {
    pub inner: Term<dyn Expr>,
}

#[context(hole = h)]
fn invalid(Wrap { inner: h }: Term<dyn Expr>) -> Term<dyn Expr> { //~ ERROR a context returns `()`: it says where evaluation may happen and has no after-state; K turns it into a heat rule and a cool rule
    h
}

fn main() {}
