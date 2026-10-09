//! `name @ pattern`: K's `#as` (KF-029).
//!
//! In a left-hand side, `p @ Pair(a, b)` matches what `Pair(a, b)` matches and
//! also binds `p` to the whole matched term, as Rust's `@` does. K writes the
//! name last, `( pair(A, B) #as P:Exp )`, and the alias is the matched term
//! itself (a conjunction of patterns), so a result may reuse it without
//! rebuilding it. Like `tail @ ..`, the binder comes first.
//!
//! - `dup(pair(1, 2))` is `pair(pair(1, 2), pair(2, 1))`, by a readable clause;
//! - `wrap(pair(1, 2))` is `pair(1, pair(1, 2))`, by a `cells!` rule whose
//!   binder list declares the alias before the binders inside it;
//! - `rest(cons(1, cons(2, nil)))` is `cons(2, nil)` and `rest(cons(1, nil))`
//!   is `nil`, by an equation that aliases the tail it returns and an `owise`
//!   fallback.

use k::KResult;
use k::Term;
use k::builtin::{Bool, Int, KSequence};

k::sorts! {
    Exp;
    Seq: Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Pair, Dup, Wrap))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("pair({fst}, {snd})")]
    Pair { fst: Exp, snd: Exp },
    #[k::syntax("dup({e})")]
    Dup { e: Exp },
    #[k::syntax("wrap({e})")]
    Wrap { e: Exp },
}

#[k::constructors(sort = Seq, result = KResult)]
#[k::precedence((Cons, Nil))]
#[rustfmt::skip]
pub enum SeqSyntax {
    #[k::syntax("cons({head}, {tail})")]
    Cons { head: Exp, tail: Seq },
    #[k::syntax("nil")]
    Nil(),
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

/// The list without its first element.
#[k::function(total, sort = Seq, syntax = "rest({s})")]
pub struct Rest {
    pub s: Term<Seq>,
}

/// `rest(cons(_, ( cons(_, _) #as More:Seq )))` is `More:Seq`.
#[k::equation]
fn rest_long(
    k::term![Rest(SeqSyntax::Cons(_, more @ SeqSyntax::Cons(_, _)))]: Term<Seq>,
) -> Term<Seq> {
    more
}

#[k::equation(owise)]
fn rest_short(k::term![Rest(_)]: Term<Seq>) -> Term<Seq> {
    SeqSyntax::Nil()
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    /// `dup(( pair(A, B) #as P ))` reuses the matched pair.
    dup_pair: Dup(p @ Pair(a, b)) => Pair(p, Pair(b, a));
}

/// The binder list declares the alias `p`, then `a`, in first-occurrence
/// order; `_` is not a binder.
#[k::rule(label = "wrap-pair")]
pub fn wrap_pair(
    p: Exp,
    a: Exp,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Wrap(p @ ExpSyntax::Pair(a, _)), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Pair(a, p), ..tail),
        ..state
    }
}
