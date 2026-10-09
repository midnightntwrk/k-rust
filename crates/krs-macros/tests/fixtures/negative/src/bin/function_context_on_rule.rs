use krs_macros::{cells, rule, term};
use renamed_krs::Term;
use renamed_krs::builtin::{Int, KSequence};
use renamed_krs::configuration::{Cell, KCell};

trait Expr {}
struct ReadBar;

#[renamed_krs::configuration]
pub struct Machine {
    pub k: KCell<KSequence>,
    pub bar: Cell<Int>,
}

impl Machine {
    #[renamed_krs::init]
    fn init() -> Self {
        Self {
            k: KCell::new(renamed_krs::k![.K]),
            bar: Cell::new(0),
        }
    }
}

#[rule]
fn read_bar(
    b: Term<Int>,
    term![ReadBar()]: Term<dyn Expr>,
    cells! { //~ ERROR a configuration context belongs only on #[k::equation] (K's [[ ]] function context)
        bar: Cell(b),
        ..
    }: Machine,
) -> Term<dyn Expr> {
    b
}

fn main() {}
