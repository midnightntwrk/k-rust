//! Composition example. This package's only KRS implementation dependency is
//! the renamed `language-host` facade.

use k::builtin::KSequence;
use k::{KItem, KItemSort, KResult, KResultSort, Term};
use language_host as k;

#[k::sort(alias = Expr, parents = [KItem])]
pub trait ExprSort: KItemSort {}
pub type Expr = Term<dyn ExprSort>;

#[k::sort(alias = Value, parents = [Expr, KResult])]
pub trait ValueSort: ExprSort + KResultSort {}
pub type Value = Term<dyn ValueSort>;

#[k::symbol("tour::RootCommon")]
#[k::sort(alias = Common, parents = [KItem])]
pub trait CommonSort: KItemSort {}
pub type Common = Term<dyn CommonSort>;

#[k::symbol("tour::RootSame")]
#[k::constructor(sort = Common, syntax = "same-root")]
pub struct Same;

#[cfg(tour_mode = "extended")]
#[k::constructor(sort = Common, syntax = "extended-root")]
pub struct Extended;

#[k::constructor(sort = Expr, syntax = "pair({first},{second})")]
pub struct Pair {
    pub first: Term<dyn ExprSort>,
    pub second: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "wrap({value})")]
pub struct Wrap {
    pub value: Term<dyn ExprSort>,
}

#[k::constructor(sort = Value, syntax = "value-node")]
pub struct ValueNode;

// `native_swap` and `macro_swap` spell one rule two ways and overlap on purpose.
#[k::rule(nondet = swap_forms)]
pub fn native_swap(Pair { first, second }: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    Pair {
        first: second,
        second: first,
    }
}

#[k::rule(nondet = swap_forms)]
pub fn macro_swap(k::term![Pair { first, second }]: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
    k::term![Pair {
        first: second,
        second: first
    }]
}

#[k::rule]
pub fn cross_package(
    semantic_base::Same: Term<dyn semantic_base::CommonSort>,
) -> Term<dyn semantic_base::CommonSort> {
    semantic_base::Same
}

#[must_use]
pub fn standalone_term(value: Term<dyn ExprSort>) -> Term<dyn ExprSort> {
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
