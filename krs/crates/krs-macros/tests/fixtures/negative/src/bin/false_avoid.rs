use renamed_krs as k;

#[k::sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = k::Term<dyn ExprSort>;

#[k::constructor(sort = Expr, syntax = "bad", avoid = false)] //~ ERROR `avoid` must be the Rust Boolean literal `true`
pub struct Bad;

fn main() {}
