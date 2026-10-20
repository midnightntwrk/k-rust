use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::*;
    bad: Add { lhs, .. } => lhs where lhs: List<BusCycle>; //~ ERROR K's `List` sort is not parametric, so a `where` narrowing tests the sort `List`
}

fn main() {}
