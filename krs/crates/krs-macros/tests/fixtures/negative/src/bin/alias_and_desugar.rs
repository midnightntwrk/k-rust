use krs_macros::{constructor, sort};

#[sort(alias = Stmt)]
pub trait StmtSort {} pub type Stmt = renamed_krs::Term<dyn StmtSort>;

#[constructor(sort = Stmt, syntax = "skip")]
#[renamed_krs::alias]
#[renamed_krs::desugar] //~ ERROR a production is an alias or a desugar, not both: `alias` also prints backwards, `desugar` only expands
pub struct Skip;

fn main() {}
