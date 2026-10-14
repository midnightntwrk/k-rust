//@ check-pass
use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct Dup;
struct Pair;

#[rule]
fn dup(term![Dup(p @ Pair(a, b))]: Term<dyn Expr>) -> Term<dyn Expr> {
    term![Pair(p, Pair(b, a))]
}

fn main() {}
