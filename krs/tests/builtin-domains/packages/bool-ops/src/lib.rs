//! Builtin BOOL operations: one function and one equation per operation.

use k::builtin::{Bool, KSequence, bool};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool;
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

/// `bool::not`, `notBool`.
#[k::function(total, sort = Bool, syntax = "not({a})")]
pub struct Not {
    pub a: Term<Bool>,
}

#[k::equation]
fn not(k::term![Not(a)]: Term<Bool>) -> Term<Bool> {
    bool::not(a)
}

/// `bool::and`, `andBool`.
#[k::function(total, sort = Bool, syntax = "and({a}, {b})")]
pub struct And {
    pub a: Term<Bool>,
    pub b: Term<Bool>,
}

#[k::equation]
fn and(k::term![And(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::and(a, b)
}

/// `bool::or`, `orBool`.
#[k::function(total, sort = Bool, syntax = "or({a}, {b})")]
pub struct Or {
    pub a: Term<Bool>,
    pub b: Term<Bool>,
}

#[k::equation]
fn or(k::term![Or(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::or(a, b)
}

/// `bool::xor`, `xorBool`.
#[k::function(total, sort = Bool, syntax = "xor({a}, {b})")]
pub struct Xor {
    pub a: Term<Bool>,
    pub b: Term<Bool>,
}

#[k::equation]
fn xor(k::term![Xor(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::xor(a, b)
}

/// `bool::implies`, `impliesBool`.
#[k::function(total, sort = Bool, syntax = "implies({a}, {b})")]
pub struct Implies {
    pub a: Term<Bool>,
    pub b: Term<Bool>,
}

#[k::equation]
fn implies(k::term![Implies(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::implies(a, b)
}

/// `bool::and_then`, `andThenBool` (not `Option::and_then`).
#[k::function(total, sort = Bool, syntax = "andThen({a}, {b})")]
pub struct AndThen {
    pub a: Term<Bool>,
    pub b: Term<Bool>,
}

#[k::equation]
fn and_then(k::term![AndThen(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::and_then(a, b)
}

/// `bool::or_else`, `orElseBool`.
#[k::function(total, sort = Bool, syntax = "orElse({a}, {b})")]
pub struct OrElse {
    pub a: Term<Bool>,
    pub b: Term<Bool>,
}

#[k::equation]
fn or_else(k::term![OrElse(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::or_else(a, b)
}

/// `bool::eq`, `==Bool`.
#[k::function(total, sort = Bool, syntax = "eq({a}, {b})")]
pub struct Eq {
    pub a: Term<Bool>,
    pub b: Term<Bool>,
}

#[k::equation]
fn eq(k::term![Eq(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::eq(a, b)
}

/// `bool::ne`, `=/=Bool`.
#[k::function(total, sort = Bool, syntax = "ne({a}, {b})")]
pub struct Ne {
    pub a: Term<Bool>,
    pub b: Term<Bool>,
}

#[k::equation]
fn ne(k::term![Ne(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::ne(a, b)
}
