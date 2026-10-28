use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::*;
    bad: Add { lhs: k::rewrite!(x => y), rhs } => rhs; //~ ERROR a rule with a result already states the whole after-state
}

fn main() {}
