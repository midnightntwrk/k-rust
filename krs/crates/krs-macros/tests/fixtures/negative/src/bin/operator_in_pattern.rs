use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct Check;

#[rule]
fn check(term![Check(n + 1)]: Term<dyn Expr>) -> Term<dyn Expr> { //~ ERROR `+` is not a pattern: a pattern writes a builtin operation as its call, `int::add(..)`, `string::concat(..)`, or `float::add(..)`
    term![n]
}

fn main() {}
