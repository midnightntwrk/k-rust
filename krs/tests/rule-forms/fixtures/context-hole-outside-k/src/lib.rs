//! A context's hole lies in the computation cell: heating moves it to the
//! front of `k`.

use k::builtin::{Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Inc, Wrap) > left (Add))]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("++ {target}")]
    Inc { target: Exp },
    #[k::syntax("wrap({inner})")]
    Wrap { inner: Exp },
    #[k::syntax("{lhs} + {rhs}")]
    Add { lhs: Exp, rhs: Exp },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub focus: Exp,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp, focus: Exp) -> Self {
        Self {
            k: k::k![pgm],
            focus,
        }
    }
}

#[k::context(hole = h)]
fn focus_operand(
    h: Exp,
    k::cells! {
        k: k::configuration::KCell(Op::Wrap(_), ..),
        focus: k::configuration::Cell(h),
        state @ ..
    }: Machine,
) {
}
