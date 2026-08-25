use language_host as k;

trait Expr {}

#[k::constructor(sort = Expr)]
trait NotAStruct {}

fn main() {}

