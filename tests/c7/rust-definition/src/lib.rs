//! Minimal readable definition distinguishing bare and explicit associativity.

use k::builtin::{Bool, KSequence};

k::sorts! {
    Probe;
    impl Probe for Bool;
}

#[k::constructors(sort = Probe, result = k::KResult)]
#[k::precedence(
    (Not)
    > non_assoc equality (Eq)
)]
pub enum ProbeSyntax {
    #[k::syntax("!{value}")]
    Not { value: Probe },
    #[k::syntax("{lhs} == {rhs}")]
    Eq { lhs: Probe, rhs: Probe },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Probe) -> Self {
        Self { k: k![pgm] }
    }
}
