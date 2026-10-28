use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::*;
    bad: Add { lhs: k::matches!(x, Pair(_, _)), rhs } => rhs; //~ ERROR `k::matches!` (K's :=K) is a Bool test of a bound term
}

fn main() {}
