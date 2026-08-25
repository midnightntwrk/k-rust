use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::*;
    bad: Add { lhs, .. } => lhs where absent: Int;
}

fn main() {}
