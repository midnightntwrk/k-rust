//! `==K`, `=/=K`, and `#if` from K's `K-EQUAL` module (KF-024), after K's
//! tutorial `1_basic/18`.
//!
//! `kequal::ite` is K's sort-parametric function `#if c #then t #else e #fi`,
//! not control flow: k-rust evaluates both branches and Java K's LLVM backend
//! only the taken one, so every program below keeps both branches defined,
//! except `go()`, which pins that difference.

use k::KResult;
use k::builtin::{Bool, Int, KSequence, kequal};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((If, Same, Differ, Pick, Go))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("if ({condition}) {then} else {otherwise}")] #[k::strict(condition)]
    If { condition: Exp, then: Exp, otherwise: Exp },
    #[k::syntax("same({lhs}, {rhs})")]
    Same { lhs: Exp, rhs: Exp },
    #[k::syntax("differ({lhs}, {rhs})")]
    Differ { lhs: Exp, rhs: Exp },
    #[k::syntax("pick({condition})")] #[k::strict]
    Pick { condition: Exp },
    #[k::syntax("go()")]
    Go(),
}

/// A function with no equations: undefined on every argument.
#[k::function(partial, sort = Int, syntax = "undef()")]
pub struct Undef {}

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

    /// `#if` at the rule's sort Exp: the instance is Exp.
    if_eval: If { condition: b, then: e1, otherwise: e2 } => kequal::ite(b, e1, e2)               where b: Bool;
    /// Syntactic equality of the unevaluated operand terms.
    same   : Same { lhs, rhs }                            => kequal::eq(lhs, rhs);
    differ : Differ { lhs, rhs }                          => kequal::ne(lhs, rhs);
    /// Two Int branches at an Exp position: the instance is Int, then injected.
    pick   : Pick { condition: b }                        => kequal::ite(b, 1, 2)                 where b: Bool;
    /// The untaken branch is undefined: Java K's LLVM backend never evaluates it.
    go     : Go()                                         => kequal::ite(true, 1, crate::Undef());
}
