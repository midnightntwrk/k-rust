use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::*;
    bad: Add { lhs: k::is!(Int, x), rhs } => rhs; //~ ERROR `k::is!` and `k::project!` are function calls and cannot be matched
}

fn main() {}
