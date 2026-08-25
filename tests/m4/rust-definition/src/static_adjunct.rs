//! M3D's separately identified static stress surface.
//!
//! These declarations exercise functions, equations, equation priority,
//! aliases, and named contexts. They are intentionally not upstream IMP.

use k::Term;
use k::builtin::{Int, int};

use crate::{Expr, Machine};

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

#[k::equation]
fn m3d_total(k::term![M3dTotal(value)]: Term<Int>) -> Term<Int> {
    int::add(value, 1)
}

#[k::requires(int::le(0, value))]
#[k::equation]
fn m3d_positive(k::term![M3dPositive(value)]: Term<Int>) -> Term<Int> {
    value
}

#[k::priority(40)]
#[k::equation]
fn m3d_priority_zero(k::term![M3dPriority(0)]: Term<Int>) -> Term<Int> {
    111
}

#[k::priority(80)]
#[k::equation]
fn m3d_priority_fallback(k::term![M3dPriority(_)]: Term<Int>) -> Term<Int> {
    222
}

#[k::constructors(sort = Expr, result = k::KResult)]
#[k::precedence((M3dZero, M3dTwice))]
pub enum StaticExpr {
    #[k::syntax("m3dZero")]
    #[k::alias]
    M3dZero(),

    #[k::syntax("m3dTwice({value})")]
    #[k::seqstrict(using = m3d_eval)]
    M3dTwice { value: Expr },
}

#[k::alias]
fn m3d_zero_alias(k::term![StaticExpr::M3dZero]: Term<Expr>) -> Term<Expr> {
    0
}

#[k::context_alias(name = m3d_eval, here = site)]
fn m3d_eval(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: Machine,
) {
}

#[k::rule]
fn m3d_twice(k::term![StaticExpr::M3dTwice(value)]: Term<Expr>) -> Term<Expr> {
    int::add(value, value)
}
