use krs_macros::{constructor, desugar, sort};
use renamed_krs::Term;

#[sort(alias = Stmt)]
pub trait StmtSort {} pub type Stmt = renamed_krs::Term<dyn StmtSort>;

#[constructor(sort = Stmt, syntax = "skip")]
#[renamed_krs::desugar]
pub struct Skip;

#[constructor(sort = Stmt, syntax = "nop")]
pub struct Nop;

#[desugar(recursive)] //~ ERROR recursion is a property of the production: write `recursive` on the production's `#[k::alias]` or `#[k::desugar]` marker, and a plain marker on its clauses
fn skip(Skip: Term<dyn StmtSort>) -> Term<dyn StmtSort> {
    Nop
}

fn main() {}
