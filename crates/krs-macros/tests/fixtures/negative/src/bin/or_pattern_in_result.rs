use krs_macros::{rule, term};
use renamed_krs::Term;

trait Expr {}
struct Dup;
struct Red;
struct Green;

#[rule]
fn dup(term![Dup(a)]: Term<dyn Expr>) -> Term<dyn Expr> {
    term![Red() | Green()] //~ ERROR `|` is a pattern alternative; for Bool disjunction use bool::or or k::or_bool!
}

fn main() {}
