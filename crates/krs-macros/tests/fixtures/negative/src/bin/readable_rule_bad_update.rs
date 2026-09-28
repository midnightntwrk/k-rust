extern crate renamed_krs as k;

pub struct Expr;

k::rules! {
    for Expr;
    bad: Wrap(value) => value
        where update env = map::update(other, value, value); //~ ERROR update base must be the cell `env`
}

fn main() {}
