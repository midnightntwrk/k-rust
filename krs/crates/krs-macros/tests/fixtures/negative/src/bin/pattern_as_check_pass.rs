//@ check-pass
use krs_macros::{rule, term};
use renamed_krs as k;

renamed_krs::sorts! {
    Expr;
}

#[k::constructors(sort = Expr, reference)]
pub enum ExprSyntax {
    Dup { pair: k::Term<dyn ExprSort> },
    Pair { left: k::Term<dyn ExprSort>, right: k::Term<dyn ExprSort> },
}
use ExprSyntax::*;

#[rule]
fn dup(term![Dup(p @ Pair(a, b))]: k::Term<dyn ExprSort>) -> k::Term<dyn ExprSort> {
    term![Pair(p, Pair(b, a))]
}

fn main() {}
