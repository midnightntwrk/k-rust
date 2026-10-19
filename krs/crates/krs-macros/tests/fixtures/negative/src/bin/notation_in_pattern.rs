use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct Check;

#[rule]
fn check(term![Check(a && b)]: Term<dyn Expr>) -> Term<dyn Expr> { //~ ERROR `&&` is not a pattern: a left-hand side matches `bool::and_then` only as the call `bool::and_then(..)`
    term![a]
}

fn main() {}
