use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct Dup;
struct Pair;

#[rule]
fn dup(term![Dup(ref p @ Pair(a, b))]: Term<dyn Expr>) -> Term<dyn Expr> { //~ ERROR K's #as binds the matched term itself; remove `ref`
    term![Pair(p, Pair(b, a))]
}

fn main() {}
