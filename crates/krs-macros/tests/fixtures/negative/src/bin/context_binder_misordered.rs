use krs_macros::{cells, constructor, context, sort};
use renamed_krs::Term;
use renamed_krs::builtin::KSequence;
use renamed_krs::configuration::KCell;

#[sort]
pub trait Expr {}

#[constructor(sort = Expr)]
pub struct Pair {
    pub left: Term<dyn Expr>,
    pub right: Term<dyn Expr>,
}

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

#[context(hole = h)]
fn invalid(
    h: Term<dyn Expr>, //~ ERROR typed term parameters must declare every term binder of the subject and function context, in first-occurrence order (hole binders included; `_`, remainders, HERE, instance labels and local binders excluded)
    e: Term<dyn Expr>,
    cells! { k: KCell(Pair { left: e, right: h }, tail @ ..), state @ .. }: Machine,
) {
}

fn main() {}
