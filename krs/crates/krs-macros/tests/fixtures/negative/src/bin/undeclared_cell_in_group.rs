use krs_macros::{cells, rule};
use renamed_krs::Term;
use renamed_krs::builtin::{Int, KSequence};
use renamed_krs::configuration::{Cell, KCell};

#[renamed_krs::cell]
pub struct Frame {
    #[renamed_krs::cell]
    pub ret: Int,
}

#[renamed_krs::configuration]
pub struct Machine {
    pub k: KCell<KSequence>,
    #[renamed_krs::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[renamed_krs::init]
    fn init() -> Self {
        Self {
            k: KCell::new(renamed_krs::k![.K]),
            frame: Frame { ret: 0 },
        }
    }
}

// `ret` is a cell of the group `Frame`, not of `Machine`: it is written
// `Frame::ret`.
#[rule]
fn reset(
    n: Term<Int>,
    cells! {
        k: KCell(n, tail @ ..),
        ret: Cell(_), //~ ERROR [krs::expand::undeclared-cell] `Machine` declares no cell of this name
        state @ ..
    }: Machine,
) -> Machine {
    cells! { k: KCell(..tail), ..state }
}

fn main() {}
