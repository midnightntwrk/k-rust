use krs_macros::rule;
use renamed_krs::Term;

trait Expr {}
struct Start;

#[rule]
fn operator(Start: Term<dyn Expr>) -> Term<dyn Expr> {
    Start + Start //~ ERROR the root must be a named path
}

fn main() {}
