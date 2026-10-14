use renamed_krs as k;

#[k::sort(alias = Stmt)]
pub trait StmtSort {} pub type Stmt = k::Term<dyn StmtSort>;

#[k::constructor(sort = Stmt, syntax = "bad", avoid = true, prefer = true)] //~ ERROR `prefer` must be omitted: a production is either preferred or avoided, not both
pub struct Bad;

fn main() {}
