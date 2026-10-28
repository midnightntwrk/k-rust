//@ check-pass
use krs_macros::{rule, term};
use renamed_krs as k;

renamed_krs::sorts! {
    Expr;
}

#[k::constructors(sort = Expr, reference)]
pub enum ExprSyntax {
    First { pair: k::Term<dyn ExprSort> },
    Pair { left: k::Term<dyn ExprSort>, right: k::Term<dyn ExprSort> },
    Red,
    Green,
}
use ExprSyntax::*;

#[rule]
fn first(term![First(Pair(x, Red()) | Pair(x, Green()))]: k::Term<dyn ExprSort>) -> k::Term<dyn ExprSort> {
    term![x]
}

fn main() {}
