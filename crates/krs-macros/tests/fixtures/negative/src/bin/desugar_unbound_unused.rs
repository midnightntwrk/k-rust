use krs_macros::{constructor, desugar, sort};
use renamed_krs::Term;

#[sort]
pub trait Stmt {}

#[constructor(sort = Stmt, syntax = "skip")]
#[renamed_krs::desugar]
pub struct Skip;

#[constructor(sort = Stmt, syntax = "nop")]
pub struct Nop;

#[desugar(unbound_variables = [other, _])] //~ ERROR `_` is listed in `unbound_variables`, but the result has no `_`; list `_` only for a result with wildcards
fn skip(Skip: Term<dyn Stmt>) -> Term<dyn Stmt> {
    Nop
}

fn main() {}
