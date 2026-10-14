use krs_macros::{constructor, context, sort};
use renamed_krs as k;
use renamed_krs::Term;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Pair {
    pub left: Term<dyn ExprSort>,
    pub right: Term<dyn ExprSort>,
}

#[constructor(sort = Expr)]
pub struct Wrap {
    pub inner: Term<dyn ExprSort>,
}

#[context(hole = h)]
fn invalid(
    k::term![Pair {
        left: k::rewrite!(h => Wrap { inner: h }),
        right: k::rewrite!(g => Wrap { inner: g }), //~ ERROR a context rewrites at most its hole, once: `k::rewrite!(h => f(h))`, K's `HOLE => f(HOLE)`
    }]: Term<dyn ExprSort>,
) {
}

fn main() {}
