use krs_macros::configuration;

#[configuration(root = "machine")] //~ ERROR no associated function or constant named `__krs_initializer_payload`
struct Machine {
    k: renamed_krs::configuration::KCell<renamed_krs::builtin::KSequence>,
}

fn main() {}
