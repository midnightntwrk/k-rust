use language_host as k;

struct Foo;

#[k::configuration(root = "machine")]
struct Machine {
    k: k::configuration::KCell<k::builtin::KSequence>,
}

impl Machine {
    #[k::init]
    fn init() -> Self {
        let forbidden_host_statement = Foo;
        Self {
            k: k::configuration::KCell::new(k::k![forbidden_host_statement]),
        }
    }
}

fn main() {}

