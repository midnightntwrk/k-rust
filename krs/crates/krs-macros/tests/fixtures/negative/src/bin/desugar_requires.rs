use krs_macros::{constructor, desugar, sort};
use renamed_krs::Term;

#[sort(alias = Stmt)]
pub trait StmtSort {} pub type Stmt = renamed_krs::Term<dyn StmtSort>;

#[constructor(sort = Stmt, syntax = "skip")]
#[renamed_krs::desugar]
pub struct Skip;

#[constructor(sort = Stmt, syntax = "nop")]
pub struct Nop;

#[desugar]
#[renamed_krs::requires(true)] //~ ERROR a desugar clause has no `#[k::requires]`: K rewrites the definition and the program with it once, before anything runs, so there is nothing to test a condition against
fn skip(Skip: Term<dyn StmtSort>) -> Term<dyn StmtSort> {
    Nop
}

fn main() {}
