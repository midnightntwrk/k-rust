use renamed_krs as k;
use renamed_krs::KResult;

#[k::token(regex = r"w[a-z]*")]
pub struct Word(pub String);

// A membership line places `Word` below `Value` and the parents `Value` has
// in this block; `KResult` is the framework's and takes its own line.
k::sorts! {
    Value: KResult;
    impl Value for Word; //~ ERROR [krs::expand::sort-membership] `Word` is not a member of the K sort `KResult`
}

fn main() {}
