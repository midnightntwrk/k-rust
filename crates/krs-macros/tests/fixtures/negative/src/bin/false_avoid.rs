use renamed_krs as k;

#[k::sort]
pub trait Expr {}

#[k::constructor(sort = Expr, syntax = "bad", avoid = false)] //~ ERROR `avoid` must be the Rust Boolean literal `true`
pub struct Bad;

fn main() {}
