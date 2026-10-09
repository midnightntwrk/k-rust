use krs_macros::{alias, constructor, sort};
use renamed_krs::Term;

#[sort]
pub trait Stmt {}

#[constructor(sort = Stmt, syntax = "skip")]
#[renamed_krs::alias]
pub struct Skip;

#[constructor(sort = Stmt, syntax = "nop")]
pub struct Nop;

#[alias(unbound_variables = [x])] //~ ERROR unbound_variables applies only to desugar clauses: write it in the `#[k::desugar(..)]` of a clause fn, `#[k::desugar(unbound_variables = [x, _])]`
fn skip(Skip: Term<dyn Stmt>) -> Term<dyn Stmt> {
    Nop
}

fn main() {}
