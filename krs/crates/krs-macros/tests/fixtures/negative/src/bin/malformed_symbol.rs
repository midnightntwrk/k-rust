#[renamed_krs::symbol("")] //~ ERROR invalid explicit stable symbol
#[renamed_krs::sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

fn main() {}
