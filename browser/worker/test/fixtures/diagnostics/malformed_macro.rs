#[k::sort]
pub trait Expr {}

// `syntax` is present, but the required `sort = ...` argument is absent.
#[k::constructor(syntax = "broken")]
pub struct Broken;

fn main() {}
