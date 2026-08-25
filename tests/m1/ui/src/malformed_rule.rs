use language_host::{self as k, Term};

trait Expr {}
struct Start;

#[k::rule]
fn broken(Start: Term<dyn Expr>) -> Term<dyn Expr> {
    Start + Start
}

fn main() {}

