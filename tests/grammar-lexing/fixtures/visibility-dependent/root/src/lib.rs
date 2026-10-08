//! A dependent that names the base package's private production: rustc
//! rejects the path (E0603), so the rule never reaches K.

use base::{Exp, ExpSyntax};
use k::builtin::KSequence;

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

    unwrap: Inc { value } => base::Helper::Wrap { value };
}
