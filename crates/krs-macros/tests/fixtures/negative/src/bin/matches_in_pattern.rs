use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::*;
    bad: Add { lhs: k::matches!(x, Pair(_, _)), rhs } => rhs; //~ ERROR `k::matches!` is a Bool test (K's :=K); it cannot appear on a left-hand side or inside a pattern
}

fn main() {}
