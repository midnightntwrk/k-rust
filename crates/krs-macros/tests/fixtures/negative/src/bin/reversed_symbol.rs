#[renamed_krs::sort(alias = Expr)]
#[renamed_krs::symbol("api::Expr")] //~ ERROR #[k::symbol] must appear before the symbol-bearing KRS declaration attribute
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

fn main() {}
