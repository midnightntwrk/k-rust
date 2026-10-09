use krs_macros::{constructor, context, sort};
use renamed_krs as k;
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Pair {
    pub left: Term<dyn Expr>,
    pub right: Term<dyn Expr>,
}

#[constructor(sort = Expr)]
pub struct Wrap {
    pub inner: Term<dyn Expr>,
}

#[context(hole = h)]
fn invalid(
    k::term![Pair {
        left: k::rewrite!(h => Wrap { inner: h }),
        right: k::rewrite!(g => Wrap { inner: g }), //~ ERROR a context rewrites at most its hole, once: `k::rewrite!(h => f(h))`, K's `HOLE => f(HOLE)`
    }]: Term<dyn Expr>,
) {
}

fn main() {}
