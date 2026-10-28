use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::*;
    bad: Add { lhs: k::is!(Int, x), rhs } => rhs; //~ ERROR `k::is!` and `k::project!` compute from a term, and a pattern matches terms as they are
}

fn main() {}
