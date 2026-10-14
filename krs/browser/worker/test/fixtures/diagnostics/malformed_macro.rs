#[k::sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = k::Term<dyn ExprSort>;

// `syntax` is present, but the required `sort = ...` argument is absent.
#[k::constructor(syntax = "broken")]
pub struct Broken;

fn main() {}
