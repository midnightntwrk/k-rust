//@ check-pass
//! Code that rustc checks receives the calls that notation denotes,
//! qualified by the renamed facade, without an imported builtin module.
use renamed_krs::builtin::bool::Bool;

#[renamed_krs::configuration(root = "machine")]
pub struct Machine {
    pub k: renamed_krs::configuration::KCell<renamed_krs::builtin::KSequence>,
}

impl Machine {
    #[renamed_krs::init]
    pub fn init(ready: Bool) -> Self {
        Self {
            k: renamed_krs::configuration::KCell::new(renamed_krs::k![
                ready.not::<Bool>(),
                ready && ready
            ]),
        }
    }
}

fn main() {
    let (ready, armed) = (Bool, Bool);
    let _ = || renamed_krs::term![ready || armed];
    let _ = || renamed_krs::term![armed.eq::<K>(ready)];
}
