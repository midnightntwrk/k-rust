//! A simplification lemma in a spec module that names a private production.
//!
//! `H` is not `pub`, so K declares it `private` in this package's module.
//! Rust lets the child spec module name it, but K parses the spec module with
//! its own grammar, which leaves imported private syntax out (KF-045).

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

#[k::function(total, sort = Int, syntax = "h({value})")]
struct H {
    value: Term<Int>,
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

    #[k::simplification]
    fn h_lemma(k::term![H(x)]: Term<Int>) -> Term<Int> {
        int::add(x, 1)
    }
}
