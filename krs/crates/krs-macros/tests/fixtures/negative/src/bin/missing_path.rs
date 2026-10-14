use krs_macros::{constructor, sort};

#[sort(alias = Expr)]
trait ExprSort {} type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = missing::Expr)] //~ ERROR cannot find module or crate `missing`
struct Broken;

fn main() {}
