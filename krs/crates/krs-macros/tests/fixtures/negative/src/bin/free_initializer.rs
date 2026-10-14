use krs_macros::{init, k};

struct Foo;

#[init]
fn init() -> Self { //~ ERROR cannot find type `Self`
    Self {
        k: renamed_krs::configuration::KCell::new(k![Foo]),
    }
}

fn main() {}
