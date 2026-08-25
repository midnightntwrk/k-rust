extern crate renamed_krs as k;

pub struct Expr;

k::rules! {
    for Expr;
    bad: Wrap(value) => k![value, ..tail];
}

fn main() {}
