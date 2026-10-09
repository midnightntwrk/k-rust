use krs_macros::{constructor, simplification, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Done;

#[simplification(symbolic())] //~ ERROR `symbolic()` lists no binder; write bare `symbolic` to restrict every binder
fn invalid(Done: Term<dyn Expr>) -> Term<dyn Expr> {
    Done
}

fn main() {}
