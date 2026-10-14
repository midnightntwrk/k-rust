//! A value list is a result of its strict list: without
//! `impl KResult for Vals`, an evaluated `Exps` would be heated forever.

use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    Val: Exp + KResult;
    impl Val for Int;
    impl Exps for Vals;
}

#[k::syntax_list(separator = ",", result = KResult)]
pub enum Exps {
    #[k::seqstrict]
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
