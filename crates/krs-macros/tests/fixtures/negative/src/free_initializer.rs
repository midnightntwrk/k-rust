use krs_macros::{init, k};

struct Foo;

#[init]
fn init() -> Self {
    Self {
        k: renamed_krs::configuration::KCell::new(k![Foo]),
    }
}

fn main() {}
