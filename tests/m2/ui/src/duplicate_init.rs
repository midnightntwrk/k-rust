use language_host as k;

struct Foo;

#[k::configuration(root = "machine")]
struct Machine {
    k: k::configuration::KCell<k::builtin::KSequence>,
}

impl Machine {
    #[k::init]
    fn init() -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![Foo]),
        }
    }

    #[k::init]
    fn init() -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![Foo]),
        }
    }
}

fn main() {}

