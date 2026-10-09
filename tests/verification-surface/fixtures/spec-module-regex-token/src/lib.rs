//! A regex token in a spec module: only the definition declares regex tokens.

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
    #[k::token(regex = r"\$[a-z]+")]
    pub type DollarId = k::builtin::Id;
}
