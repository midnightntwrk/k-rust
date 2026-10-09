//! Strict syntactic lists that evaluate to completion (KF-020), after K's
//! `Vals` idiom in the PL tutorial's SIMPLE:
//!
//! ```k
//! syntax Exps ::= List{Exp, ","} [seqstrict]
//! syntax Vals ::= List{Val, ","}
//! syntax Exps ::= Vals
//! syntax KResult ::= Vals
//! ```
//!
//! `Exps` is a `seqstrict` list, so a call evaluates its arguments left to
//! right. `impl Exps for Vals` makes the value list `Vals` the one subsort a
//! strict list admits; KRS gives both lists K's `overload` key, so an
//! evaluated argument list is a `Vals`, which is a `KResult`, and the call's
//! own strictness stops heating it. `tick` returns the counter and
//! increments it, so `f(tick, tick, tick)` sees `1, 2, 3` and `digits`
//! reads them as `123`; right-to-left evaluation would give `321`.

use k::KResult;
use k::Term;
use k::builtin::{Id, Int, KSequence, int};

k::sorts! {
    Exp;
    Val: Exp + KResult;
    impl Val for Int;
    impl Exps for Vals;
    impl KResult for Vals;
}

/// Call arguments, evaluated left to right.
#[k::syntax_list(separator = ",", result = KResult)]
pub enum Exps {
    #[k::seqstrict]
    Cons {
        head: Exp,
        tail: Exps,
    },
    Nil(),
}

/// Evaluated call arguments.
#[k::syntax_list(separator = ",")]
pub enum Vals {
    Cons { head: Val, tail: Vals },
    Nil(),
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Tick, Call))]
#[rustfmt::skip]
pub enum Syntax {
    #[k::syntax("tick")] Tick(),
    #[k::syntax("{callee}({args})")] #[k::strict(args)]
    Call { callee: Id, args: Exps },
}

/// Reads a list of digits as a decimal number, most significant first.
#[k::function(partial, sort = Int, syntax = "digits({values}, {acc})")]
pub struct Digits {
    pub values: Term<Vals>,
    pub acc: Term<Int>,
}

#[k::equation]
fn digits_done(acc: Term<Int>, k::term![Digits(Vals::Nil(), acc)]: Term<Int>) -> Term<Int> {
    acc
}

#[k::equation]
fn digits_more(
    digit: Term<Int>,
    rest: Term<Vals>,
    acc: Term<Int>,
    k::term![Digits(Vals::Cons(digit, rest), acc)]: Term<Int>,
) -> Term<Int> {
    Digits(rest, int::add(int::mul(acc, 10), digit))
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
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            counter: 1,
        }
    }
}

k::rules! {
    for Machine;
    use Syntax::*;

    tick: {
        k: [Tick(), ..],
        counter: c
    } => {
        k: [c, ..],
        counter: int::add(c, 1)
    };
}

k::rules! {
    for Exp;
    use Syntax::*;

    call: Call { callee: _, args } => crate::Digits(args, 0) where args: Vals;
}
