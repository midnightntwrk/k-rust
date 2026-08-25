use krs_macros::rule;
use renamed_krs::Term;

trait Expr {}
struct Start;

#[rule]
fn operator(Start: Term<dyn Expr>) -> Term<dyn Expr> {
    Start + Start
}

fn main() {}
