extern crate renamed_krs as k;

pub struct Expr;

k::rules! {
    for Expr;
    duplicate: Wrap(value) => value
        where have env[value -> let first],
              have env[value -> let second]; //~ ERROR duplicate extra-cell mention `env`
}

fn main() {}
