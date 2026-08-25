//! Positive M1 surface. This package's only KRS implementation dependency is
//! the renamed `language-host` facade.

use language_host as k;
use k::Term;

#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait KResult: KItem {}

#[k::sort]
pub trait Expr: KItem {}

#[k::sort]
pub trait Value: Expr + KResult {}

#[k::sort]
pub trait Common: KItem {}

#[k::constructor(sort = Common, syntax = "same-root")]
pub struct Same;

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

#[k::rule]
pub fn native_swap(Pair { first, second }: Term<dyn Expr>) -> Term<dyn Expr> {
    Pair {
        first: second,
        second: first,
    }
}

#[k::rule]
pub fn macro_swap(k::term![Pair { first, second }]: Term<dyn Expr>) -> Term<dyn Expr> {
    k::term![Pair {
        first: second,
        second: first
    }]
}

#[k::rule]
pub fn zero_bindings(nested::Done: Term<dyn Expr>) -> Term<dyn Expr> {
    nested::Done
}

#[k::rule]
pub fn ordinal_gap(
    k::term![Pair {
        first: 日本,
        second: nested::Done,
    }]: Term<dyn Expr>,
) -> Term<dyn Expr> {
    k::term![nested::Keep { value: 日本, marker: nested::Done }]
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

pub mod nested {
    use super::{Expr, KItem, Term, k};

    #[k::sort]
    pub trait Common: KItem {}

    #[k::constructor(sort = Common, syntax = "same-root-nested")]
    pub struct Same;

    #[k::constructor(sort = Expr, syntax = "done")]
    pub struct Done;

    #[k::constructor(sort = Expr, syntax = "keep({value},{marker})")]
    pub struct Keep {
        pub value: Term<dyn Expr>,
        pub marker: Term<dyn Expr>,
    }
}

