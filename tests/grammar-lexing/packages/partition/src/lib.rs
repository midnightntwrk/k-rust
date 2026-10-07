//! Program-syntax partition fixture.
//!
//! `pub` productions are program syntax and land in `KRS-PART-SYNTAX`.
//! The `internal` family `Aux` is usable by rules but not by programs.
//! With `int-literals = "unsigned"`, a program's `-1` is `Neg(1)`, while the
//! rules can still write signed literals because `KRS-PART` imports `INT`.

use k::KResult;
use k::builtin::{Bool, Int, KSequence, bool, int};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Neg) > left (And))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("-{value}")] #[k::strict]
    Neg { value: Exp },
    #[k::syntax("{lhs} && {rhs}")] #[k::strict]
    And { lhs: Exp, rhs: Exp },
}

/// Rule machinery that programs cannot contain.
#[k::constructors(sort = Exp, result = KResult, internal)]
#[k::precedence((Inc))]
pub enum Aux {
    #[k::syntax("#inc({value})")]
    Inc { value: Exp },
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

    and: And { lhs, rhs } => bool::and(lhs, rhs)                    where lhs: Bool, rhs: Bool;
    neg: Neg { value }    => Aux::Inc { value: int::sub(0, value) } where value: Int;
}

k::rules! {
    for Exp;
    use Aux::*;

    inc: Inc { value } => int::add(value, 1) where value: Int;
}
