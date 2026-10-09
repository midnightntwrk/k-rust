use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct Dup;

#[rule]
fn dup(term![Dup(p @ ..)]: Term<dyn Expr>) -> Term<dyn Expr> { //~ ERROR a `..` remainder binds only inside a sequence, collection or cells! pattern
    term![Dup]
}

fn main() {}
