//! Peano natural numbers: one sort and its constructors, and no rules.

// [!region definition]
use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Nat: KItem;
}

#[k::constructors(sort = Nat, result = KResult)]
#[k::precedence((Zero, Succ))]
pub enum NatSyntax {
    #[k::syntax("zero")]
    Zero(),
    #[k::syntax("s({n})")]
    Succ { n: Nat },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Nat) -> Self {
        Self { k: k::k![pgm] }
    }
}
// [!endregion definition]
