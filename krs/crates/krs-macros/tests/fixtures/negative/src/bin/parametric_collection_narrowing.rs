use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::*;
    bad: Add { lhs, .. } => lhs where lhs: List<BusCycle>; //~ ERROR a `where` narrowing tests only the sort `List` and cannot constrain its elements
}

fn main() {}
