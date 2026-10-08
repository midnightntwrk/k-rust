use krs_macros::{constructor, rule, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Done;

#[rule(priority = 255)] //~ ERROR k-rust ranks rule priorities 0..=254
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    Done
}

fn main() {}
