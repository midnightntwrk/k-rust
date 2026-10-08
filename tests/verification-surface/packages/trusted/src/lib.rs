//! Trusted claims: an axiom that splits a proof.
//!
//! `helper(I)` has no rules, so the program `call(I)` steps to `helper(I)`
//! and stops there. The claim `helper-axiom` is `trusted`: the prover
//! assumes `helper(I)` reaches `I +Int 1` without proving it, like `unsafe`
//! in Rust or `assume` in Verus. With that assumption `call-spec` is proved:
//! one step reaches `helper(I)`, and the trusted claim finishes the proof.
//! `krs prove` reports `call-spec` proven and `helper-axiom` trusted, never
//! proven, and every prove run and Haskell build warns about the assumption.
//!
//! Use a trusted claim to split a proof into parts, never to make one pass:
//! nothing checks that the axiom holds.

use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Call, Helper))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("call({value})")] Call { value: Int },
    #[k::syntax("helper({value})")] Helper { value: Int },
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

/// `call(I)` delegates to `helper(I)`, which no rule defines.
#[k::rule(label = "call")]
fn call(k::term![ExpSyntax::Call { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Helper(value)
}

/// Assumed without proof: `helper(I)` reaches `I +Int 1`.
#[k::claim(all_paths, label = "helper-axiom", trusted)]
pub fn helper_axiom(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Helper(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(int::add(i, 1), ..tail), ..state }
}

/// Proved: `call(I)` reaches `I +Int 1`, through the trusted `helper-axiom`.
#[k::claim(all_paths, label = "call-spec")]
pub fn call_spec(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Call(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(int::add(i, 1), ..tail), ..state }
}
