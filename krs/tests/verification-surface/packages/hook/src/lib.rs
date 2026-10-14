//! SMT translations: a function Z3 understands without any equation.
//!
//! Z3 knows Int arithmetic but not your functions. `myAbs` has no equation;
//! its `smt_hook` gives it a meaning in Z3's language, SMT-LIB, where
//! `{value}` stands for the argument. The rule `go(I) => myAbs(I) >=Int 0`
//! leaves a Boolean only Z3 can decide, and with the hook it can: the claim
//! `abs-nonneg` is proved. Concrete execution cannot evaluate `myAbs`, so
//! every build warns about each function that only Z3 can evaluate.
//!
//! `clampSub` shows that placeholders follow field names, not positions: its
//! template names `value` before `low`, and K's `smt-hook` gets `#2` before
//! `#1`. Nothing checks a template against equations: like `smtlib`, it is
//! trusted.

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

/// The absolute value, defined only for Z3.
#[k::function(total, sort = Int, syntax = "myAbs({value})", smt_hook = "(ite (< {value} 0) (- 0 {value}) {value})")]
pub struct MyAbs {
    pub value: Term<Int>,
}

/// `value - low`, or 0 below `low`; the template reads the fields out of order.
#[k::function(total, sort = Int, syntax = "clampSub({low}, {value})", smt_hook = "(ite (< {value} {low}) 0 (- {value} {low}))")]
pub struct ClampSub {
    pub low: Term<Int>,
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

/// Proved by Z3 through the hook: `myAbs(I) >=Int 0` holds for every `I`.
#[k::claim(all_paths, label = "abs-nonneg")]
pub fn abs_nonneg(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Go(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(true, ..tail), ..state }
}
