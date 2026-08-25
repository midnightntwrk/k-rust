use language_host::{self as k, Term};

trait Expr {}
struct Pair;

#[k::rule]
fn duplicate(k::term![Pair(value, value)]: Term<dyn Expr>) -> Term<dyn Expr> {
    k::term![Pair]
}

fn main() {}

