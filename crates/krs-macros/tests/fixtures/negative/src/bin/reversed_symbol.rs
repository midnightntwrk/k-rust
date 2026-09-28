#[renamed_krs::sort]
#[renamed_krs::symbol("api::Expr")] //~ ERROR #[k::symbol] must appear before the symbol-bearing KRS declaration attribute
pub trait Expr {}

fn main() {}
