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
#[k::function(total, sort = Int, syntax = "#addOne({value})")]
pub struct AddOne {
    pub value: Term<Int>,
}

#[k::function(partial, sort = Int, syntax = "#nonnegativeIdentity({value})")]
pub struct NonnegativeIdentity {
    pub value: Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#priorityChoice({value})")]
pub struct PriorityChoice {
    pub value: Term<Int>,
}

/// Oracle rule `[add-one]`.
#[k::equation]
fn add_one(k::term![AddOne(value)]: Term<Int>) -> Term<Int> {
    int::add(value, 1)
}

/// Oracle rule `[nonnegative-identity]`.
#[k::requires(int::le(0, value))]
#[k::equation]
fn nonnegative_identity(k::term![NonnegativeIdentity(value)]: Term<Int>) -> Term<Int> {
    value
}

/// Oracle rule `[priority-choice-zero]`.
#[k::priority(40)]
#[k::equation]
fn priority_choice_zero(k::term![PriorityChoice(0)]: Term<Int>) -> Term<Int> {
    111
}

/// Oracle rule `[priority-choice-fallback]`.
#[k::priority(80)]
#[k::equation]
fn priority_choice_fallback(k::term![PriorityChoice(_)]: Term<Int>) -> Term<Int> {
    222
}

// The production and its expansion clause are both visibly static aliases.
#[k::constructor(sort = Expr, syntax = "zeroAlias")]
#[k::alias]
pub struct ZeroAlias;

/// Oracle rule `[zero-alias]`.
#[k::alias]
fn zero_alias(k::term![ZeroAlias]: Term<dyn Expr>) -> Term<dyn Expr> {
    0
}

// `site` denotes the complete production instance at HERE, not merely the
// selected argument hole. The tail and sibling cells remain framed.
#[k::context_alias(name = operand_eval, here = site)]
fn operand_eval(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: Machine,
) {
}

#[k::constructor(sort = Expr, syntax = "double({value})")]
#[k::seqstrict(using = operand_eval, sequence = [value], result = KResult)]
pub struct Double {
    pub value: Term<dyn Expr>,
}

/// Oracle rule `[double]`; use in `int::add` refines `value` to `Int`.
#[k::rule]
fn double(k::term![Double(value)]: Term<dyn Expr>) -> Term<dyn Expr> {
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
        k: k::configuration::KCell(AddOne(4), tail @ ..),
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
        k: k::configuration::KCell(NonnegativeIdentity(7), tail @ ..),
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
        k: k::configuration::KCell(PriorityChoice(0), tail @ ..),
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
        k: k::configuration::KCell(ZeroAlias, tail @ ..),
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
        k: k::configuration::KCell(Double(Add(1, 2)), tail @ ..),
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
