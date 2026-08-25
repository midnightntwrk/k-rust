use language_host as k;

#[k::sort]
trait Expr {}

#[k::constructor(sort = missing::Expr)]
struct Broken;

fn main() {}

