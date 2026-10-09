use krs_macros::{constructor, context, sort};
use renamed_krs::Term;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Wrap {
    pub inner: Term<dyn Expr>,
}

#[context(label = "wrap-inner")] //~ ERROR missing
fn invalid(Wrap { inner: h }: Term<dyn Expr>) {}

fn main() {}
