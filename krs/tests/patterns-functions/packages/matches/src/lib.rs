//! `k::matches!(t, P)`: K's `P :=K T` (KF-031).
//!
//! `k::matches!` is an object-language Bool that is true when `t` matches the
//! Rust pattern `P`. K writes the pattern first, `( pair ( _ , _ ) :=K E:Exp )`,
//! always parenthesised, and compiles it to a generated function. The
//! pattern's names are local binders: they bind inside the pattern only.
//!
//! - `isPair(pair(1, 2))` is `true` and `isPair(3)` is `false`, by two
//!   readable clauses whose guards are `k::matches!` and its negation;
//! - `twin(pair(1, 1))` is `true` and `twin(pair(1, 2))` is `false`: the
//!   local binder `x` occurs twice, so both components must be equal;
//! - `boxed(pair(pair(1, 2), pair(1, 2)))` is `true` and
//!   `boxed(pair(pair(1, 2), pair(2, 1)))` is `false`: in a guard,
//!   `p @ Pair(_, _)` names the first component, which the second must equal
//!   (K rejects `#as` in a right-hand side, so `@` stays in conditions);
//! - `known(unit())` is `true` and `known(3)` is `false`, by alternatives.

use k::KResult;
use k::Term;
use k::builtin::bool::{self, Bool};
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((IsPair, Pair, Unit, Boxed))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("isPair({e})")]
    IsPair { e: Exp },
    #[k::syntax("pair({fst}, {snd})")]
    Pair { fst: Exp, snd: Exp },
    #[k::syntax("unit()")]
    Unit(),
    #[k::syntax("boxed({e})")]
    Boxed { e: Exp },
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

/// Whether a term is a pair of two equal components.
#[k::function(total, sort = Bool, syntax = "twin({e})")]
pub struct Twin {
    pub e: Term<Exp>,
}

/// `twin(E)` is `( pair ( X:Exp , X:Exp ) :=K E:Exp )`.
#[k::equation]
fn twin(k::term![Twin(e)]: Term<Bool>) -> Term<Bool> {
    k::matches!(e, ExpSyntax::Pair(x, x))
}

/// Whether a term is a pair or the unit.
#[k::function(total, sort = Bool, syntax = "known({e})")]
pub struct Known {
    pub e: Term<Exp>,
}

/// `known(E)` is `( ( pair ( _ , _ ) #Or unit ( ) ) :=K E:Exp )`.
#[k::equation]
fn known(k::term![Known(e)]: Term<Bool>) -> Term<Bool> {
    k::matches!(e, ExpSyntax::Pair(_, _) | ExpSyntax::Unit())
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    /// `requires ( pair ( _ , _ ) :=K E:Exp )`.
    #[k::requires(k::matches!(e, Pair(_, _)))]
    is_pair : IsPair { e } => true;
    /// `requires notBool ( pair ( _ , _ ) :=K E:Exp )`, K's `:/=K`.
    #[k::requires(bool::not(k::matches!(e, Pair(_, _))))]
    not_pair: IsPair { e } => false;
    /// `p @ ..` names the first component, which the second must equal.
    #[k::requires(k::matches!(e, Pair(p @ Pair(_, _), p)))]
    boxed   : Boxed { e }  => true;
    #[k::requires(bool::not(k::matches!(e, Pair(p @ Pair(_, _), p))))]
    unboxed : Boxed { e }  => false;
}
