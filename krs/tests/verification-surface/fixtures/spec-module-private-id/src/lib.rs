//! A spec-module claim names `$x`. The definition's `$` token alias is not
//! `pub`, so its token is K `private` and the spec module, which imports the
//! definition, does not see it: no token production the module sees lexes `$x`.

use k::builtin::{Id, Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[allow(dead_code)]
#[k::token(regex = r"\$[a-zA-Z0-9_]+")]
type DollarId = Id;

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
    use super::{ExpSyntax, Machine};

    #[k::claim(all_paths, label = "var-stays")]
    pub fn var_stays(
        k::cells! { k: k::configuration::KCell(ExpSyntax::Var(k::id!("$x")), tail @ ..), state @ .. }: Machine,
    ) -> Machine {
        k::cells! { k: k::configuration::KCell(ExpSyntax::Var(k::id!("$x")), ..tail), ..state }
    }
}
