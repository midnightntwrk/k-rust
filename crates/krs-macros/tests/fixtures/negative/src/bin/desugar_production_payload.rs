use krs_macros::{constructor, sort};

#[sort(alias = Stmt)]
pub trait StmtSort {} pub type Stmt = renamed_krs::Term<dyn StmtSort>;

#[constructor(sort = Stmt, syntax = "skip")]
#[renamed_krs::desugar(unbound_variables = [x])] //~ ERROR unbound_variables applies only to desugar clauses: write it in the `#[k::desugar(..)]` of a clause fn, `#[k::desugar(unbound_variables = [x, _])]`
pub struct Skip;

fn main() {}
