//@ check-pass
//! Code that rustc checks receives each operator as a call of its facade
//! marker, qualified by the renamed facade, so rustc reads no Rust operator
//! on the authoring markers and needs no imported builtin module.
use renamed_krs::builtin::bool::Bool;
use renamed_krs::builtin::int::Int;

#[renamed_krs::configuration(root = "machine")]
pub struct Machine {
    pub k: renamed_krs::configuration::KCell<renamed_krs::builtin::KSequence>,
    pub count: renamed_krs::configuration::Cell<Int>,
}

impl Machine {
    #[renamed_krs::init]
    pub fn init(ready: Bool, start: Int) -> Self {
        Self {
            k: renamed_krs::configuration::KCell::new(renamed_krs::k![!ready, ready == !ready]),
            count: renamed_krs::configuration::Cell::new(-start * 2 + 1),
        }
    }
}

fn main() {
    let (ready, armed) = (Bool, Bool);
    let (left, right) = (Int, Int);
    let _ = || renamed_krs::term![!ready != (armed == ready)];
    let _ = || renamed_krs::term![(left & 15) + (right & 15) > 15];
    let _ = || renamed_krs::term![-left << 2 >> right ^ !left];
}
