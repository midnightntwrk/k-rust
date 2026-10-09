//! Handing a simplification to Z3 as an axiom.
//!
//! `h_lemma` is still `concrete(x)`, so the prover does not rewrite `h(I)`;
//! with `smt_lemma`, Z3 also receives `probeH(x) = x + 1` for every `x`, an
//! unchecked axiom, and proves `probeH(I) > 3` from `I > 2`. Both claims are
//! proved. Z3 sees `h` only because it declares `smtlib`.

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

/// A function Z3 sees as the uninterpreted symbol `probeH`; it has no equation.
#[k::function(total, sort = Int, syntax = "h({value})", smtlib = "probeH")]
pub struct H {
    pub value: Term<Int>,
}

/// `h(x) = x +Int 1`: rewritten when `x` is ground, and a Z3 axiom always.
#[k::simplification(concrete(x), smt_lemma)]
fn h_lemma(k::term![H(x)]: Term<Int>) -> Term<Int> {
    int::add(x, 1)
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

/// `go(I)` asks whether `h(I)` exceeds 3.
#[k::rule(label = "go")]
fn go(k::term![ExpSyntax::Go { value }]: Term<Exp>) -> Term<Exp> {
    int::gt(H(value), 3)
}

/// A ground argument: `h(5)` is `6`.
#[k::claim(all_paths, label = "go-concrete")]
pub fn go_concrete(
    k::cells! { k: k::configuration::KCell(ExpSyntax::Go(5), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(true, ..tail), ..state }
}

/// A symbolic argument above 2: `h(I)` is `I +Int 1`, above 3.
#[k::claim(all_paths, label = "go-symbolic")]
#[k::requires(int::gt(i, 2))]
pub fn go_symbolic(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Go(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(true, ..tail), ..state }
}
