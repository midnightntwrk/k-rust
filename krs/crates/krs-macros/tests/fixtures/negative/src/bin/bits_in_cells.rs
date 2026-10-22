use krs_macros::{cells, rule};
use renamed_krs::Term;
use renamed_krs::builtin::{Int, KSequence};
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
fn decode(
    n: Term<Int>,
    cells! {
        k: KCell(renamed_krs::bits!("1_"), tail @ ..), //~ ERROR `k::bits!` is a pattern
        state @ ..
    }: Machine,
) -> Machine {
    cells! { k: KCell(n, ..tail), ..state }
}

fn main() {}
