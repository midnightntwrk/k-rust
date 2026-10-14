//! An `smt_lemma` simplification in a spec module, where kore-exec would ignore it.

use k::builtin::{Id, Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Var))]
pub enum ExpSyntax {
    #[k::syntax("var({name})")]
    Var { name: Id },
}

#[k::function(total, sort = Int, smtlib = "probeH", syntax = "h({value})")]
pub struct H {
    pub value: Term<Int>,
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

#[k::spec_module(imports = [crate])]
mod proofs {
    use super::{H, Int, Term, int};

    #[k::simplification(smt_lemma)]
    fn h_lemma(k::term![H(x)]: Term<Int>) -> Term<Int> {
        int::add(x, 1)
    }
}
