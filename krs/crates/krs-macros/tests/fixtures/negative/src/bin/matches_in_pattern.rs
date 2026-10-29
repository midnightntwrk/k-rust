use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::*;
    bad: Add { lhs: k::matches!(x, Pair(_, _)), rhs } => rhs; //~ ERROR `k::matches!` (K's :=K) computes a Bool by matching a term
}

fn main() {}
