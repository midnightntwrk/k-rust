use krs_macros::{constructor, desugar, sort};
use renamed_krs::Term;

#[sort]
pub trait Stmt {}

#[constructor(sort = Stmt, syntax = "skip")]
#[renamed_krs::desugar]
pub struct Skip;

#[constructor(sort = Stmt, syntax = "nop")]
pub struct Nop;

#[desugar(recursive)] //~ ERROR recursion is a property of the production: write `recursive` on the production's `#[k::alias]` or `#[k::desugar]` marker, and a plain marker on its clauses
fn skip(Skip: Term<dyn Stmt>) -> Term<dyn Stmt> {
    Nop
}

fn main() {}
