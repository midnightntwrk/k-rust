use krs_macros::{cells, k, rule};
use renamed_krs::Term;
use renamed_krs::builtin::{Id, KSequence};
use renamed_krs::configuration::{Cell, KCell};

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
        k: Cell(k![value, tail @ ..]), //~ ERROR cell wrapper and rule state family disagree
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: Cell(k![value, ..tail]),
        ..state
    }
}

fn main() {}
