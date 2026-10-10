#[renamed_krs::symbol("api::Expr")]
#[renamed_krs::symbol("api::OtherExpr")]
#[renamed_krs::sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>; //~ ERROR duplicate #[k::symbol] attribute

fn main() {}
