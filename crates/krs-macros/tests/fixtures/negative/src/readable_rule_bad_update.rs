extern crate renamed_krs as k;

pub struct Expr;

k::rules! {
    for Expr;
    bad: Wrap(value) => value
        where update env = map::update(other, value, value);
}

fn main() {}
