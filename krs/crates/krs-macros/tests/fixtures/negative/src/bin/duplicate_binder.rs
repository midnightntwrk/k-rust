//@ check-pass
use krs_macros::{rule, term};
use renamed_krs as k;

renamed_krs::sorts! {
    Expr;
}

#[k::constructors(sort = Expr, reference)]
pub enum ExprSyntax {
    Pair { left: k::Term<dyn ExprSort>, right: k::Term<dyn ExprSort> },
}
use ExprSyntax::*;

#[rule]
fn duplicate(term![Pair(value, value)]: k::Term<dyn ExprSort>) -> k::Term<dyn ExprSort> {
    term![value]
}

fn main() {}
