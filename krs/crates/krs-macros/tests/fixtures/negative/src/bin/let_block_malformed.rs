use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct Second;
struct Pair;

#[rule]
fn second(term![Second(p)]: Term<dyn Expr>) -> Term<dyn Expr> {
    let Pair(_, y) = p;
    y; //~ ERROR a term block is `let pattern = term;`* followed by one result term (K's #let)
}

fn main() {}
