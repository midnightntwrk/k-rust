use krs_macros::{constructor, desugar, sort};
use renamed_krs::Term;

#[sort(alias = Stmt)]
pub trait StmtSort {} pub type Stmt = renamed_krs::Term<dyn StmtSort>;

#[constructor(sort = Stmt, syntax = "twice {body}")]
#[renamed_krs::desugar]
pub struct Twice {
    pub body: Term<dyn StmtSort>,
}

#[constructor(sort = Stmt, syntax = "{first} {second}")]
pub struct Seq {
    pub first: Term<dyn StmtSort>,
    pub second: Term<dyn StmtSort>,
}

#[desugar(unbound_variables = [body])] //~ ERROR `body` is bound by the pattern; `unbound_variables` lists only result names the pattern does not bind
fn twice(Twice { body }: Term<dyn StmtSort>) -> Term<dyn StmtSort> {
    Seq { first: body, second: body }
}

fn main() {}
