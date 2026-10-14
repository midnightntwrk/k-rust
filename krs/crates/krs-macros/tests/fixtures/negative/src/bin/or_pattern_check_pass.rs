//@ check-pass
use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct First;
struct Pair;
struct Red;
struct Green;

#[rule]
fn first(term![First(Pair(x, Red()) | Pair(x, Green()))]: Term<dyn Expr>) -> Term<dyn Expr> {
    term![x]
}

fn main() {}
