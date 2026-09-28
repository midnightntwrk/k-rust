//@ check-pass
use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct Pair;

#[rule]
fn duplicate(term![Pair(value, value)]: Term<dyn Expr>) -> Term<dyn Expr> {
    term![Pair]
}

fn main() {}
