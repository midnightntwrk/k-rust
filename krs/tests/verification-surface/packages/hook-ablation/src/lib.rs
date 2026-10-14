//! The hook fixture with `smtlib` in place of `smt_hook` (ablation).
//!
//! `smtlib = "myAbs"` only gives the function a name in Z3: Z3 sees an
//! uninterpreted symbol, so `myAbs(I) >=Int 0` may be false for all it
//! knows, and the claim `abs-nonneg` is not provable.

use k::builtin::{Bool, Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
    impl Exp for Bool;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Go))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("go({value})")] Go { value: Int },
}

/// An absolute value Z3 knows only by name.
#[k::function(total, sort = Int, syntax = "myAbs({value})", smtlib = "myAbs")]
pub struct MyAbs {
    pub value: Term<Int>,
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

/// `go(I)` asks whether `myAbs(I)` is nonnegative.
#[k::rule(label = "go")]
fn go(k::term![ExpSyntax::Go { value }]: Term<Exp>) -> Term<Exp> {
    int::ge(MyAbs(value), 0)
}

/// Not provable: Z3 does not know what `myAbs` computes.
#[k::claim(all_paths, label = "abs-nonneg")]
pub fn abs_nonneg(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Go(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(true, ..tail), ..state }
}
