//! Equation scans: the outcome of one equation attempt, the scan of one priority group, and the
//! priority loop over the groups a term theory offers a term.

use std::sync::Arc;

use crate::{
    rule::{RewriteRule, Theory, applicable_groups, term_index},
    term::Term,
};

use super::{ConditionIndeterminacy, Simplification, SimplifyResult};

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum IndeterminateEquation {
    Block,
    Continue,
}

pub(super) enum TheoryScan {
    /// The result of the equation that applied, and that equation.
    Applied(Simplification, Arc<RewriteRule>),
    Blocked,
    /// No equation applied, but some equation was set aside for a reason other than a failed
    /// match (see [`GroupScan::NotCacheable`]); the term is not a fixed point to record.
    NotCacheable,
    /// Every equation offered the term failed to match it.
    NotApplicable,
}

/// The priority loop of a term theory: scan the groups `theory` offers `term` in priority order,
/// trying each equation with `attempt`, until one applies or a group blocks the scan.
///
/// ```toml algorithm-site
/// id = "backend.simplify.term"
/// role = "part"
/// sites = ["scan_theory", "scan_group"]
/// ```
pub(super) fn scan_theory(
    theory: &Theory,
    indeterminate_equation: IndeterminateEquation,
    term: &Term,
    mut attempt: impl FnMut(&Arc<RewriteRule>) -> SimplifyResult<EquationAttempt<Simplification>>,
) -> SimplifyResult<TheoryScan> {
    let groups = applicable_groups(theory, &term_index(term));
    let mut blocked = false;
    let mut not_cacheable = false;
    for rules in groups.values() {
        match scan_group(rules, |rule| {
            Ok(match attempt(rule)? {
                EquationAttempt::Applied(result) => {
                    EquationAttempt::Applied((result, Arc::clone(rule)))
                }
                EquationAttempt::NotApplicable => EquationAttempt::NotApplicable,
                EquationAttempt::ContextDependent => EquationAttempt::ContextDependent,
                EquationAttempt::Unused => EquationAttempt::Unused,
                EquationAttempt::Indeterminate(reason) => EquationAttempt::Indeterminate(reason),
            })
        })? {
            GroupScan::Applied((result, rule)) => return Ok(TheoryScan::Applied(result, rule)),
            GroupScan::Blocked if indeterminate_equation == IndeterminateEquation::Block => {
                // A rule at this priority may apply after the symbolic subject becomes more
                // concrete. Function evaluation must preserve the application and must not fall
                // through to an owise or otherwise lower-priority equation.
                return Ok(TheoryScan::Blocked);
            }
            GroupScan::Blocked => blocked = true,
            GroupScan::NotCacheable => not_cacheable = true,
            GroupScan::NotApplicable => {}
        }
    }
    Ok(if blocked {
        TheoryScan::Blocked
    } else if not_cacheable {
        TheoryScan::NotCacheable
    } else {
        TheoryScan::NotApplicable
    })
}

pub(super) enum EquationAttempt<T> {
    NotApplicable,
    /// The equation is inapplicable under the current path condition, but may apply if the same
    /// term is simplified under different assumptions. Unlike `Indeterminate`, this does not
    /// block lower-priority equations in the current scan.
    ContextDependent,
    /// The equation's left-hand side matched, or its shape keeps the evaluator from using it as
    /// a term rewrite, and the evaluator does not use it on this term: a `concrete` or
    /// `symbolic` attribute rejected the binding, the match bound a variable outside the
    /// left-hand side, or the right-hand side is a predicate. These are choices of when the
    /// evaluator uses an equation, not of what the definition means: the equation still holds,
    /// so the term may equal its right-hand side. Like `ContextDependent`, this lets
    /// lower-priority equations of the scan fire and keeps the term out of the evaluated cache.
    Unused,
    Indeterminate(ConditionIndeterminacy),
    Applied(T),
}

pub(super) enum GroupScan<T> {
    Applied(T),
    Blocked,
    /// No equation applied, and some equation was `ContextDependent` or `Unused`: the scan's
    /// answer may differ under another path condition, or an equation that matched was set aside,
    /// so the term must not be recorded as a fixed point.
    NotCacheable,
    NotApplicable,
}

pub(super) fn scan_group<R, T>(
    rules: &[Arc<R>],
    mut attempt: impl FnMut(&Arc<R>) -> SimplifyResult<EquationAttempt<T>>,
) -> SimplifyResult<GroupScan<T>> {
    let mut indeterminate = false;
    let mut not_cacheable = false;
    for rule in rules {
        match attempt(rule)? {
            EquationAttempt::Applied(result) => return Ok(GroupScan::Applied(result)),
            EquationAttempt::Indeterminate(_reason) => indeterminate = true,
            EquationAttempt::ContextDependent | EquationAttempt::Unused => not_cacheable = true,
            EquationAttempt::NotApplicable => {}
        }
    }
    Ok(if indeterminate {
        GroupScan::Blocked
    } else if not_cacheable {
        GroupScan::NotCacheable
    } else {
        GroupScan::NotApplicable
    })
}
