use renamed_krs as k;

#[k::sort]
pub trait Expr {}

#[k::constructor(sort = Expr, syntax = "bad", avoid = false)]
pub struct Bad;

fn main() {}
