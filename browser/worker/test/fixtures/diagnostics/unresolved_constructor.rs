#[k::sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = k::Term<dyn ExprSort>;

// The first diagnostic selects `missing`; a generated reference check also
// reports the complete macro invocation through rustc's expansion metadata.
#[k::constructor(sort = missing::Expr, syntax = "broken")]
pub struct Broken;

fn main() {}
