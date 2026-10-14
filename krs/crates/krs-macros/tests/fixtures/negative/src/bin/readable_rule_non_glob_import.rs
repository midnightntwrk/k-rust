use renamed_krs as k;

k::rules! {
    for Expr;
    use Op::Add; //~ ERROR only `use Enum::*;` imports
    bad: Add(lhs, rhs) => lhs;
}

fn main() {}
