use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::Add;
    bad: Add(lhs, rhs) => lhs;
}

fn main() {}
