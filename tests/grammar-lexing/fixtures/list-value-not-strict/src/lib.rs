//! Only a strict syntactic list admits a subsort, its value list: `Exps` is
//! not strict, so `Vals` cannot join it.

use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    Val: Exp + KResult;
    impl Val for Int;
    impl Exps for Vals;
    impl KResult for Vals;
}

#[k::syntax_list(separator = ",")]
pub enum Exps {
    Cons { head: Exp, tail: Exps },
    Nil(),
}

#[k::syntax_list(separator = ",")]
pub enum Vals {
    Cons { head: Val, tail: Vals },
    Nil(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exps) -> Self {
        Self { k: k::k![pgm] }
    }
}
