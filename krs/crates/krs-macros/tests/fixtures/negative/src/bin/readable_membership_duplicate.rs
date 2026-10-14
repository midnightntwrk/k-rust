use renamed_krs as k;
use renamed_krs::builtin::Int;

k::sorts! {
    Expr;
    impl Expr for Int;
    impl Expr for Int; //~ ERROR duplicate readable membership relation `relative:Int -> relative:Expr`
}

fn main() {}
