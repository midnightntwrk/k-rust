use krs_macros::{constructor, sort};

#[sort]
trait Expr {}

#[constructor(sort = missing::Expr)] //~ ERROR cannot find module or crate `missing`
struct Broken;

fn main() {}
