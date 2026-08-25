//! Intended Rust-authored surface for the M3D static and verification forms.
//!
//! This crate is deliberately ahead of the public `k` facade and must remain
//! an always-on compile failure until the requested sentence kinds land.

#[path = "../../src/m3c.rs"]
mod inherited;

pub use inherited::*;

use k::Term;
use k::builtin::{Bool, Int, bool, int};

// `function` must register a functional production, including its declared
// totality, result sort, concrete syntax, and stable K symbol identity.
#[k::function(total, sort = Int, syntax = "#m3dTotal({value})")]
pub struct M3dTotal {
    pub value: Term<Int>,
}

#[k::function(partial, sort = Int, syntax = "#m3dPositive({value})")]
pub struct M3dPositive {
    pub value: Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#m3dPriority({value})")]
pub struct M3dPriority {
    pub value: Term<Int>,
}

/// Oracle rule `[m3d-total]`.
#[k::equation]
fn m3d_total(k::term![M3dTotal(value)]: Term<Int>) -> Term<Int> {
    int::add(value, 1)
}

/// Oracle rule `[m3d-positive]`.
#[k::requires(int::le(0, value))]
#[k::equation]
fn m3d_positive(k::term![M3dPositive(value)]: Term<Int>) -> Term<Int> {
    value
}

/// Oracle rule `[m3d-priority-zero]`.
#[k::priority(40)]
#[k::equation]
fn m3d_priority_zero(k::term![M3dPriority(0)]: Term<Int>) -> Term<Int> {
    111
}

/// Oracle rule `[m3d-priority-fallback]`.
#[k::priority(80)]
#[k::equation]
fn m3d_priority_fallback(k::term![M3dPriority(_)]: Term<Int>) -> Term<Int> {
    222
}

// The production and its expansion clause are both visibly static aliases.
#[k::constructor(sort = Expr, syntax = "m3dZero")]
#[k::alias]
pub struct M3dZero;

/// Oracle rule `[m3d-zero-alias]`.
#[k::alias]
fn m3d_zero_alias(k::term![M3dZero]: Term<dyn Expr>) -> Term<dyn Expr> {
    0
}

// `site` denotes the complete production instance at HERE, not merely the
// selected argument hole. The tail and sibling cells remain framed.
#[k::context_alias(name = m3d_eval, here = site)]
fn m3d_eval(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: Machine,
) {
}

#[k::constructor(sort = Expr, syntax = "m3dTwice({value})")]
#[k::seqstrict(using = m3d_eval, sequence = [value], result = KResult)]
pub struct M3dTwice {
    pub value: Term<dyn Expr>,
}

/// Oracle rule `[m3d-twice]`; use in `int::add` refines `value` to `Int`.
#[k::rule]
fn m3d_twice(k::term![M3dTwice(value)]: Term<dyn Expr>) -> Term<dyn Expr> {
    int::add(value, value)
}

// The four rules imported by IMP-VERIFICATION are simplifier lemmas rather
// than executable transitions or ordinary function equations.
#[k::simplification]
fn normalize_gt(k::term![int::gt(lhs, rhs)]: Term<Bool>) -> Term<Bool> {
    int::lt(rhs, lhs)
}

#[k::simplification]
fn normalize_ge(k::term![int::ge(lhs, rhs)]: Term<Bool>) -> Term<Bool> {
    int::le(rhs, lhs)
}

#[k::simplification]
fn normalize_not_lt(
    k::term![bool::not(int::lt(lhs, rhs))]: Term<Bool>,
) -> Term<Bool> {
    int::le(rhs, lhs)
}

#[k::simplification]
fn normalize_not_le(
    k::term![bool::not(int::le(lhs, rhs))]: Term<Bool>,
) -> Term<Bool> {
    int::lt(rhs, lhs)
}

// Five concrete claims cover every authored adjunct form. Labels are explicit
// so Rust item names remain freely refactorable without changing K identity.
#[k::claim(all_paths, label = "total-equation")]
fn total_equation(
    k::cells! {
        k: k::configuration::KCell(M3dTotal(4), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(5, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "partial-equation")]
fn partial_equation(
    k::cells! {
        k: k::configuration::KCell(M3dPositive(7), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(7, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "explicit-priority")]
fn explicit_priority(
    k::cells! {
        k: k::configuration::KCell(M3dPriority(0), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(111, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "static-alias")]
fn static_alias(
    k::cells! {
        k: k::configuration::KCell(M3dZero, tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(0, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "context-alias")]
fn context_alias(
    k::cells! {
        k: k::configuration::KCell(M3dTwice(Add(1, 2)), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(6, ..tail),
        ..state
    }
}

// These are the two upstream IMP claims whose current reference notation is
// unambiguous and does not require concrete Id tokens or non-element binders.
#[k::claim(all_paths, label = "addition-1")]
fn addition_one(
    k::cells! {
        k: k::configuration::KCell(Add(3, 4), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(7, ..tail),
        ..state
    }
}

#[k::requires(int::eq(n, 4))]
#[k::claim(all_paths, label = "addition-var")]
fn addition_var(
    k::cells! {
        k: k::configuration::KCell(Add(3, n), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(7, ..tail),
        ..state
    }
}
