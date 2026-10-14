use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct First;
struct Pair;

#[rule]
fn first(term![First(Pair(x, _) | Pair(_, y))]: Term<dyn Expr>) -> Term<dyn Expr> { //~ ERROR variable `x` is not bound in all alternatives
    term![x]
}

fn main() {}
