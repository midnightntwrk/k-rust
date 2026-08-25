use language_host as k;

#[k::configuration(root = "machine")]
struct Machine {
    k: k::configuration::KCell<k::builtin::KSequence>,
    extra: k::configuration::KCell<k::builtin::KSequence>,
}

fn main() {}

