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

#[rule(heat, hole = h, priority = 10)] //~ ERROR a heat or cool rule is ordered by its hole: K adds `requires notBool isKResult(HOLE)` to heating and `requires isKResult(HOLE)` to cooling; it takes no `owise`, `priority`, `nondet`, or `anywhere`
fn invalid(Wrap { inner: h }: Term<dyn Expr>) -> Term<dyn Expr> {
    h
}

fn main() {}
