use krs_macros::{configuration, init, k};

struct Foo;

#[configuration(root = "machine")]
struct Machine {
    k: renamed_krs::configuration::KCell<renamed_krs::builtin::KSequence>,
}

impl Machine {
    #[init]
    fn init() -> Self {
        Self {
            k: renamed_krs::configuration::KCell::new(k![Foo]),
        }
    }

    #[init]
    fn init() -> Self {
        Self {
            k: renamed_krs::configuration::KCell::new(k![Foo]),
        }
    }
}

fn main() {}
