use krs_macros::configuration;

#[configuration(root = "machine")]
struct Machine { //~ ERROR configuration `Machine` has no `#[k::init]` initializer
    k: renamed_krs::configuration::KCell<renamed_krs::builtin::KSequence>,
}

fn main() {}
