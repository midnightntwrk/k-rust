use krs_macros::{constructor, desugar, sort};
use renamed_krs::Term;

#[sort(alias = Stmt)]
pub trait StmtSort {} pub type Stmt = renamed_krs::Term<dyn StmtSort>;

#[constructor(sort = Stmt, syntax = "skip")]
#[renamed_krs::desugar]
pub struct Skip;

#[constructor(sort = Stmt, syntax = "nop")]
pub struct Nop;

#[desugar(unbound_variables = [other, _])] //~ ERROR `_` is listed in `unbound_variables`, but the result has no `_`; list `_` only for a result with wildcards
fn skip(Skip: Term<dyn StmtSort>) -> Term<dyn StmtSort> {
    Nop
}

fn main() {}
