//! Separately identified static-semantics stress surface.
//!
//! These declarations exercise functions, equations, equation priority,
//! aliases, and named contexts. They are intentionally not upstream IMP.

use k::Term;
use k::builtin::{Int, int};

use crate::{Expr, Machine};

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

#[k::equation]
fn add_one(k::term![AddOne(value)]: Term<Int>) -> Term<Int> {
    int::add(value, 1)
}

#[k::requires(int::le(0, value))]
#[k::equation]
fn nonnegative_identity(k::term![NonnegativeIdentity(value)]: Term<Int>) -> Term<Int> {
    value
}

#[k::equation(priority = 40)]
fn priority_choice_zero(k::term![PriorityChoice(0)]: Term<Int>) -> Term<Int> {
    111
}

#[k::equation(priority = 80)]
fn priority_choice_fallback(k::term![PriorityChoice(_)]: Term<Int>) -> Term<Int> {
    222
}

#[k::constructors(sort = Expr, result = k::KResult)]
#[k::precedence((ZeroAlias, Double))]
pub enum StaticExpr {
    #[k::syntax("zeroAlias")]
    #[k::alias]
    ZeroAlias(),

    #[k::syntax("double({value})")]
    #[k::seqstrict(using = operand_eval)]
    Double { value: Expr },
}

#[k::alias]
fn zero_alias(k::term![StaticExpr::ZeroAlias]: Term<Expr>) -> Term<Expr> {
    0
}

#[k::context_alias(name = operand_eval, here = site)]
fn operand_eval(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: Machine,
) {
}

#[k::rule]
fn double(k::term![StaticExpr::Double(value)]: Term<Expr>) -> Term<Expr> {
    int::add(value, value)
}
