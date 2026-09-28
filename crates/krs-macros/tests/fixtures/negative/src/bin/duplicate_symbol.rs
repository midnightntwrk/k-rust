#[renamed_krs::symbol("api::Expr")]
#[renamed_krs::symbol("api::OtherExpr")]
#[renamed_krs::sort]
pub trait Expr {} //~ ERROR duplicate #[k::symbol] attribute

fn main() {}
