//! `name @ pattern` binds only on a left-hand side: K's #as is LHS-only.

use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    impl Exp for Int;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Pair, Dup))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("pair({fst}, {snd})")]
    Pair { fst: Exp, snd: Exp },
    #[k::syntax("dup({e})")]
    Dup { e: Exp },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    dup_pair: Dup(a) => Pair(p @ a, a);
}
