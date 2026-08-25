use krs_macros::{cells, rule};
use renamed_krs::Term;
use renamed_krs::builtin::{Id, KSequence};
use renamed_krs::configuration::KCell;

#[renamed_krs::configuration]
pub struct Machine {
    pub k: KCell<KSequence>,
}

impl Machine {
    #[renamed_krs::init]
    fn init() -> Self {
        Self {
            k: KCell::new(renamed_krs::k![.K]),
        }
    }
}

#[rule]
fn bad(
    value: Term<Id>,
    cells! {
        k: KCell(value, tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: KCell(value, ..state),
        ..state
    }
}

fn main() {}
