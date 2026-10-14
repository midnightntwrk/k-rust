//! The trusted fixture without `helper-axiom` (an ablation).
//!
//! Nothing says what `helper(I)` reaches, so `call-spec` stops at
//! `helper(I)` and is not proved, natively or by `kprove`: the trusted claim
//! is what made the proof go through.

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

/// Not provable: `call(I)` stops at `helper(I)`.
#[k::claim(all_paths, label = "call-spec")]
pub fn call_spec(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Call(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(int::add(i, 1), ..tail), ..state }
}
