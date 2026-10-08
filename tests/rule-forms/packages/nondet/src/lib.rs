//! Intended nondeterminism and the overlap check.
//!
//! K does not forbid overlapping rules; KRS reports two rules that can apply
//! to one configuration at one priority, because in Rust two arms matching
//! one input are usually a mistake. `nondet = toss` declares that `heads` and
//! `tails` overlap on purpose: `krun` takes one, and search finds both.
//!
//! - `toss` reaches `heads` and `tails`;
//! - `add(inc, dbl)` is bare `#[k::strict]`, so K may evaluate either operand
//!   first: with `-cCOUNTER=1` the counter ends at 4 (`inc` first) or 3;
//! - `div` and `div_zero` overlap on their pattern, but their guards
//!   `rhs != 0` and `rhs == 0` are literal complements, so they need no group.

use k::KResult;
use k::Term;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Toss, Heads, Tails, Inc, Dbl, Add, Div, DivByZero))]
#[rustfmt::skip]
pub enum Syntax {
    #[k::syntax("toss")] Toss(),
    #[k::syntax("heads")] Heads(),
    #[k::syntax("tails")] Tails(),
    #[k::syntax("inc")] Inc(),
    #[k::syntax("dbl")] Dbl(),
    #[k::syntax("add({lhs}, {rhs})")] #[k::strict]
    Add { lhs: Exp, rhs: Exp },
    #[k::syntax("div({lhs}, {rhs})")] #[k::strict]
    Div { lhs: Exp, rhs: Exp },
    #[k::syntax("divByZero")] DivByZero(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub counter: Int,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Exp,
        #[k::config_var(name = "COUNTER")] counter: Int,
    ) -> Self {
        Self {
            k: k::k![pgm],
            counter,
        }
    }
}

k::rules! {
    for Exp;
    use Syntax::*;

    #[k::rule(nondet = toss)]
    heads: Toss() => Heads();
    #[k::rule(nondet = toss)]
    tails: Toss() => Tails();
}

k::rules! {
    for Machine;
    use Syntax::*;

    inc: {
        k: [Inc(), ..],
        counter: c
    } => {
        k: [0, ..],
        counter: int::add(c, 1)
    };
    dbl: {
        k: [Dbl(), ..],
        counter: c
    } => {
        k: [0, ..],
        counter: int::mul(c, 2)
    };
    add: {
        k: [Add { lhs, rhs }, ..],
        counter: c
    } => {
        k: [c, ..],
        counter: c
    }
    where lhs: Int, rhs: Int;
}

#[k::rule]
#[k::requires(int::ne(rhs, 0))]
fn div(k::term![Syntax::Div { lhs, rhs }]: Term<Exp>) -> Term<Exp> {
    int::div(lhs, rhs)
}

#[k::rule]
#[k::requires(int::eq(rhs, 0))]
fn div_zero(k::term![Syntax::Div { lhs: _, rhs }]: Term<Exp>) -> Term<Exp> {
    k::term![Syntax::DivByZero()]
}
