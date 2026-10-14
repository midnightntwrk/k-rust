//! `let` blocks: K's `#let P = A #in B` (KF-032).
//!
//! A Rust block in a term position, `{ let P = A; B }`, binds the pattern `P`
//! to the term `A` in the result `B`. K writes it
//! `( #let P = A #in B )`, always parenthesised, and defines it as
//! `#fun(P => B)(A)`: a generated one-equation function applied to `A`. The
//! pattern's names are local binders, visible in the pattern and the rest of
//! the block.
//!
//! - `swap(pair(1, 2))` is `pair(2, 1)` by a readable clause whose result is
//!   a block, and `swapPair(pair(1, 2))` is `pair(2, 1)` by an equation whose
//!   body has a `let` statement;
//! - `scale(3)` is `12` by two ascribed lets, `let m: Int = e;` and
//!   `let n: Int = int::add(m, 1);`, which nest to the right;
//! - `shadow(1)` is `pair(pair(1, 1), 1)`: a `let` that shadows the rule's
//!   `e` binds a distinct variable, and the outer `e` keeps its value;
//! - `positive(5)` is `1` by a rule whose condition is a block;
//! - a refutable pattern that fails makes the term undefined, where rustc
//!   would have rejected the program: `swap(3)` and `swapPair(3)` (the value
//!   is no pair) and `scale(pair(1, 2))` (the value is no `Int`).

use k::KResult;
use k::Term;
use k::builtin::KSequence;
use k::builtin::int::{self, Int};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Swap, Pair, Shadow, Positive))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("swap({e})")]
    Swap { e: Exp },
    #[k::syntax("pair({fst}, {snd})")]
    Pair { fst: Exp, snd: Exp },
    #[k::syntax("shadow({e})")]
    Shadow { e: Exp },
    #[k::syntax("positive({e})")]
    Positive { e: Exp },
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

/// The components of a pair, swapped.
#[k::function(partial, sort = Exp, syntax = "swapPair({e})")]
pub struct SwapPair {
    pub e: Term<Exp>,
}

/// `swapPair(P) => ( #let pair ( X , Y ) = P #in pair ( Y , X ) )`.
#[k::equation]
fn swap_pair(k::term![SwapPair(p)]: Term<Exp>) -> Term<Exp> {
    let ExpSyntax::Pair(x, y) = p;
    ExpSyntax::Pair(y, x)
}

/// `m * (m + 1)` for an `Int` value.
#[k::function(partial, sort = Int, syntax = "scale({e})")]
pub struct Scale {
    pub e: Term<Exp>,
}

/// Two ascribed lets: `( #let M:Int = E #in ( #let N:Int = M +Int 1 #in .. ) )`.
#[k::equation]
fn scale(k::term![Scale(e)]: Term<Int>) -> Term<Int> {
    let m: Int = e;
    let n: Int = int::add(m, 1);
    int::mul(n, m)
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    /// `( #let pair ( X , Y ) = E #in pair ( Y , X ) )`.
    swap    : Swap { e }     => { let Pair(x, y) = e; Pair(y, x) };
    /// The inner `e` is a new variable; the outer `e` is unaffected.
    shadow  : Shadow { e }   => Pair({ let e = Pair(e, e); e }, e);
    /// A block as a condition.
    #[k::requires({ let m: Int = e; int::gt(m, 0) })]
    positive: Positive { e } => 1;
}
