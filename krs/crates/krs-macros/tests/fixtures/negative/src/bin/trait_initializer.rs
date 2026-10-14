use krs_macros::{init, k};

struct Foo;
struct Machine {
    k: renamed_krs::configuration::KCell<renamed_krs::builtin::KSequence>,
}

trait Initializes {
    fn init() -> Self;
}

impl Initializes for Machine {
    #[init] //~ ERROR method `__krs_initializer_payload` is not a member of trait `Initializes`
    fn init() -> Self {
        Self {
            k: renamed_krs::configuration::KCell::new(k![Foo]),
        }
    }
}

fn main() {}
