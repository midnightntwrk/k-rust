//! K's generated sort predicates and projections (KF-013).
//!
//! K generates, for every sort `S`, the total predicate `isS` and the partial
//! projection `project:S`. `k::is!(S, t)` is `isS(T)`, a Bool a rule can
//! compute with; `k::project!(S, t)` is `{T}:>S`, which has no value when `t`
//! is not an `S`. Neither is ever matched: a typed binder or `where t: S`
//! restricts what a rule matches instead.
//!
//! - `chk(5)` is `true`; `chk(box(1))` is stuck, because its guard fails;
//! - `prj(4)` is `5`; `prj(true)` and `unbox(box(true))` are undefined: Java
//!   K's LLVM backend aborts the run and k-rust yields `#Bottom`;
//! - `isval(3)` is `1` and `isval(box(3))` is `0`, by the user sort `Value`;
//! - `nth(1)` projects a list lookup with exactly one cast;
//! - `kind(7)` is `1` and `kind(box(7))` is `0`, by an equation whose result is
//!   a sort test.

use k::KResult;
use k::Term;
use k::builtin::{Bool, Int, KSequence, bool, int, kequal, list};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Chk, Boxed, Unbox, Prj, IsVal, Nth))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("chk({value})")]
    Chk { value: Exp },
    #[k::syntax("box({e})")]
    Boxed { e: Exp },
    #[k::syntax("unbox({e})")]
    Unbox { e: Exp },
    #[k::syntax("prj({e})")]
    Prj { e: Exp },
    #[k::syntax("isval({e})")]
    IsVal { e: Exp },
    #[k::syntax("nth({i})")]
    Nth { i: Exp },
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

/// Whether `e` is an Int, as an equation's result.
#[k::function(total, sort = Int, syntax = "kind({e})")]
pub struct Kind {
    pub e: Term<Exp>,
}

#[k::equation]
fn kind(k::term![Kind(e)]: Term<Int>) -> Term<Int> {
    kequal::ite(k::is!(Int, e), 1, 0)
}

/// `chk(e)` is `isKResult(E)` when `e` is an Int or a Bool.
#[k::rule]
#[k::requires(bool::or(k::is!(Int, x), k::is!(Bool, x)))]
fn chk(k::term![ExpSyntax::Chk { value: x }]: Term<Exp>) -> Term<Exp> {
    k::is!(KResult, x)
}

/// `{E}:>Int +Int 1`.
#[k::rule]
fn unbox(
    k::term![ExpSyntax::Unbox {
        e: ExpSyntax::Boxed { e }
    }]: Term<Exp>,
) -> Term<Exp> {
    int::add(k::project!(Int, e), 1)
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    prj      : Prj { e }   => int::add(k::project!(Int, e), 1);
    #[k::requires(k::is!(Value, e))]
    isval_yes: IsVal { e } => 1;
    #[k::requires(bool::not(k::is!(Value, e)))]
    isval_no : IsVal { e } => 0;
    /// The list lookup keeps its `KItem` result, so the term has one cast.
    nth      : Nth { i }   => k::project!(Int, list::get(list::concat(list::item(10), list::item(20)), i)) where i: Int;
}
