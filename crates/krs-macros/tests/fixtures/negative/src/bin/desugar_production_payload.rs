use krs_macros::{constructor, sort};

#[sort]
pub trait Stmt {}

#[constructor(sort = Stmt, syntax = "skip")]
#[renamed_krs::desugar(unbound_variables = [x])] //~ ERROR unknown argument `unbound_variables`
pub struct Skip;

fn main() {}
