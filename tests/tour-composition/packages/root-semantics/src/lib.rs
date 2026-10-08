//! Composition example. This package's only KRS implementation dependency is
//! the renamed `language-host` facade.

use k::Term;
use k::builtin::KSequence;
use language_host as k;

#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait KResult: KItem {}

#[k::sort]
pub trait Expr: KItem {}

#[k::sort]
pub trait Value: Expr + KResult {}

#[k::symbol("tour::RootCommon")]
#[k::sort]
pub trait Common: KItem {}

#[k::symbol("tour::RootSame")]
#[k::constructor(sort = Common, syntax = "same-root")]
pub struct Same;

#[cfg(tour_mode = "extended")]
#[k::constructor(sort = Common, syntax = "extended-root")]
pub struct Extended;

#[k::constructor(sort = Expr, syntax = "pair({first},{second})")]
pub struct Pair {
    pub first: Term<dyn Expr>,
    pub second: Term<dyn Expr>,
}

#[k::constructor(sort = Expr, syntax = "wrap({value})")]
pub struct Wrap {
    pub value: Term<dyn Expr>,
}

#[k::constructor(sort = Value, syntax = "value-node")]
pub struct ValueNode;

// `native_swap` and `macro_swap` spell one rule two ways and overlap on purpose.
#[k::rule(nondet = swap_forms)]
pub fn native_swap(Pair { first, second }: Term<dyn Expr>) -> Term<dyn Expr> {
    Pair {
        first: second,
        second: first,
    }
}

#[k::rule(nondet = swap_forms)]
pub fn macro_swap(k::term![Pair { first, second }]: Term<dyn Expr>) -> Term<dyn Expr> {
    k::term![Pair {
        first: second,
        second: first
    }]
}

#[k::rule]
pub fn cross_package(
    semantic_base::Same: Term<dyn semantic_base::Common>,
) -> Term<dyn semantic_base::Common> {
    semantic_base::Same
}

#[allow(dead_code)]
#[must_use]
pub fn standalone_term(value: Term<dyn Expr>) -> Term<dyn Expr> {
    k::term![Wrap { value }]
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![Same] }
    }
}
