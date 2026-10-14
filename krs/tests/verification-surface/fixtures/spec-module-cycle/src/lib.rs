//! Two spec modules import each other.

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

#[k::spec_module(name = "FIRST-SPEC", imports = [crate, second])]
mod first {}

#[k::spec_module(name = "SECOND-SPEC", imports = [first])]
mod second {}
