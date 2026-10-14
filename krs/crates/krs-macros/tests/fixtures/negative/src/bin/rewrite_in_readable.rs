use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::*;
    bad: Add { lhs: k::rewrite!(x => y), rhs } => rhs; //~ ERROR `k::rewrite!` is reference-only
}

fn main() {}
