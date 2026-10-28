use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct Dup;
struct Pair;

#[rule]
fn dup(term![Dup(a)]: Term<dyn Expr>) -> Term<dyn Expr> {
    term![Pair(p @ a, a)] //~ ERROR `name @ pattern` (K's #as) names the term a pattern matched
}

fn main() {}
