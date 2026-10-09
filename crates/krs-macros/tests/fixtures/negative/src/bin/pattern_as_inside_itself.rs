use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct Dup;
struct Pair;

#[rule]
fn dup(term![Dup(p @ Pair(p, _))]: Term<dyn Expr>) -> Term<dyn Expr> { //~ ERROR an alias cannot occur inside its own subpattern
    term![Pair]
}

fn main() {}
