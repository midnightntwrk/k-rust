extern crate renamed_krs as k;

pub struct Expr;

k::rules! {
    for Expr;
    legacy: Wrap(key) => value
        where have env[key => let value];
}

fn main() {}
