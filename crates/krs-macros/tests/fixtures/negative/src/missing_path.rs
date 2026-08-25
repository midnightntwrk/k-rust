use krs_macros::{constructor, sort};

#[sort]
trait Expr {}

#[constructor(sort = missing::Expr)]
struct Broken;

fn main() {}
