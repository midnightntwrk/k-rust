//! Function contexts: equations that read the configuration (KF-025).
//!
//! An equation may end with a second parameter, a `k::cells!` pattern over
//! the configuration struct framed by an anonymous `..`. It is K's function
//! context, `rule [[ barPlus ( N ) => B +Int N ]] <bar> B </bar> ..`: the
//! function reads the cells of the configuration it is evaluated in. The
//! caller never passes the configuration; K adds a hidden argument to the
//! function and threads it through every function that needs it. The context
//! is read-only: an equation returns a term, never the configuration.
//!
//! - `readBar()` is `43`: a rule on the computation cell calls `barPlus(1)`,
//!   whose equation reads `<bar> 42 </bar>` and requires `<baz> 0 </baz>`;
//! - `readTwice()` is `86`: it calls `barTwice(1)`, a function with no context
//!   of its own whose equation calls `barPlus` twice, so K threads the
//!   configuration through `barTwice` too.

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
#[k::precedence((ReadBar, ReadTwice))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("readBar()")]
    ReadBar(),
    #[k::syntax("readTwice()")]
    ReadTwice(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub bar: Int,
    #[k::cell]
    pub baz: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            bar: 42,
            baz: 0,
        }
    }
}

/// `n` plus the value of the `<bar>` cell.
#[k::function(total, sort = Int, syntax = "barPlus({n})")]
pub struct BarPlus {
    pub n: Term<Int>,
}

/// `[[ barPlus ( N ) => B +Int N ]] <bar> B </bar> <baz> 0 </baz> requires 0 <=Int B`.
#[k::requires(int::le(0, b))]
#[k::equation]
fn bar_plus(
    n: Term<Int>,
    b: Term<Int>,
    k::term![BarPlus(n)]: Term<Int>,
    k::cells! {
        bar: k::configuration::Cell(b),
        baz: k::configuration::Cell(0),
        ..
    }: Machine,
) -> Term<Int> {
    int::add(b, n)
}

/// `barPlus(n) + barPlus(n)`: no context of its own, but it calls `barPlus`.
#[k::function(total, sort = Int, syntax = "barTwice({n})")]
pub struct BarTwice {
    pub n: Term<Int>,
}

#[k::equation]
fn bar_twice(k::term![BarTwice(n)]: Term<Int>) -> Term<Int> {
    int::add(BarPlus(n), BarPlus(n))
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    read : ReadBar()   => crate::BarPlus(1);
    twice: ReadTwice() => crate::BarTwice(1);
}
