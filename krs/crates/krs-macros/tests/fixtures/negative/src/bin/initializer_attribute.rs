use krs_macros::{configuration, init, k};

struct Foo;

#[configuration(root = "machine")]
struct Machine {
    k: renamed_krs::configuration::KCell<renamed_krs::builtin::KSequence>,
}

impl Machine {
    /// Documentation is accepted.
    #[init]
    #[inline] //~ ERROR an initializer accepts only doc comments and `allow`, `expect`, `warn`, `deny`, and `cfg` attributes
    fn init() -> Self {
        Self {
            k: renamed_krs::configuration::KCell::new(k![Foo]),
        }
    }
}

fn main() {}
