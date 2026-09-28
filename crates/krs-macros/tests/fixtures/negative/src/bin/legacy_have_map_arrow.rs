extern crate renamed_krs as k;

pub struct Expr;

k::rules! {
    for Expr;
    legacy: Wrap(key) => value
        where have env[key => let value]; //~ ERROR `=>` is reserved for rewrites; map entries use `->`
}

fn main() {}
