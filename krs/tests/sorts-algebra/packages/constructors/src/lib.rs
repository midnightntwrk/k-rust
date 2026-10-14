//! Sort-parametric constructors (KF-027): K's `syntax {S} S ::= wrap(S)`.
//!
//! A parametric constructor is a value-building schema: `wrap(v(7))` is a
//! `Val` and `wrap(done(7))` a `Done`, each instance solved from the
//! argument. A rule head fixes its instance with a turbofish.
//!
//! - `go(7)` is `v(-8)`: `go` builds `wrap(v(7))`, at `Val`, and a rule on
//!   `Wrap::<Val>` rewrites it;
//! - `fin(7)` is `done(7)`: `fin` builds `wrap(done(7))`, at `Done`, and a rule
//!   on `Wrap::<Done>` unwraps it.

use k::builtin::{Int, KSequence, int};
use k::{KResult, Term};

k::sorts! {
    Pgm;
    Val: Pgm + KResult;
    Done: Pgm + KResult;
}

/// `wrap(x)` has the sort of `x`.
#[k::constructor(sort = S, syntax = "wrap({inner})")]
pub struct Wrap<S: ?Sized> {
    pub inner: Term<S>,
}

#[k::constructors(sort = Val, result = KResult)]
#[k::precedence((V))]
#[rustfmt::skip]
pub enum ValSyntax {
    #[k::syntax("v({n})")]
    V { n: Int },
}

#[k::constructors(sort = Done, result = KResult)]
#[k::precedence((Finished))]
#[rustfmt::skip]
pub enum DoneSyntax {
    #[k::syntax("done({n})")]
    Finished { n: Int },
}

#[k::constructors(sort = Pgm, result = KResult)]
#[k::precedence((Go, Fin))]
#[rustfmt::skip]
pub enum PgmSyntax {
    #[k::syntax("go({n})")]
    Go { n: Int },
    #[k::syntax("fin({n})")]
    Fin { n: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Pgm) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::rules! {
    for Pgm;
    use PgmSyntax::*;

    /// `wrap` at `Val`, solved from its argument.
    go : Go(n)  => crate::Wrap { inner: crate::ValSyntax::V(n) };
    /// `wrap` at `Done`, solved from its argument.
    fin: Fin(n) => crate::Wrap { inner: crate::DoneSyntax::Finished(n) };
}

/// `wrap(v(N))` becomes `v(N - 15)`: a head at `Val`.
#[k::rule(label = "unwrap-val")]
fn unwrap_val(
    k::term![Wrap::<dyn ValSort> {
        inner: ValSyntax::V(n)
    }]: Term<Val>,
) -> Term<Val> {
    ValSyntax::V(int::sub(n, 15))
}

/// `wrap(D)` at `Done` becomes `D`.
#[k::rule(label = "unwrap-done")]
fn unwrap_done(k::term![Wrap::<dyn DoneSort> { inner: d }]: Term<Done>) -> Term<Done> {
    d
}
