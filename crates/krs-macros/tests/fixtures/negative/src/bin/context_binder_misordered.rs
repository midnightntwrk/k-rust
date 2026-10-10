use krs_macros::{cells, constructor, context, sort};
use renamed_krs::Term;
use renamed_krs::builtin::KSequence;
use renamed_krs::configuration::KCell;

#[sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = renamed_krs::Term<dyn ExprSort>;

#[constructor(sort = Expr)]
pub struct Pair {
    pub left: Term<dyn ExprSort>,
    pub right: Term<dyn ExprSort>,
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
    h: Term<dyn ExprSort>, //~ ERROR typed term parameters must declare every term binder of the subject and function context, in first-occurrence order (hole binders included; `_`, remainders, HERE, instance labels and local binders excluded)
    e: Term<dyn ExprSort>,
    cells! { k: KCell(Pair { left: e, right: h }, tail @ ..), state @ .. }: Machine,
) {
}

fn main() {}
