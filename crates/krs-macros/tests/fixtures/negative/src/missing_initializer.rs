use krs_macros::configuration;

#[configuration(root = "machine")]
struct Machine {
    k: renamed_krs::configuration::KCell<renamed_krs::builtin::KSequence>,
}

fn main() {}
