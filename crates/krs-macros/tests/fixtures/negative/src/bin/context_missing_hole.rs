use krs_macros::{constructor, context, sort};
use renamed_krs::Term;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Wrap {
    pub inner: Term<dyn ExprSort>,
}

#[context(label = "wrap-inner")] //~ ERROR missing
fn invalid(Wrap { inner: h }: Term<dyn ExprSort>) {}

fn main() {}
