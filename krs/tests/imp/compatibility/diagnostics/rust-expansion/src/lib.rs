#[k::sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = k::Term<dyn ExprSort>;

// The exact malformed token is `syntax`; `sort = ...` is required.
#[k::constructor(syntax = "broken")]
pub struct Broken;
