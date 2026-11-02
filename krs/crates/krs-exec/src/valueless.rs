//! A run's path conditions over terms with no value.
//!
//! A run starts from a variable-free state, which is one state, and the backend decides every
//! step on it but one whose rule's condition reads a term the backend cannot evaluate. On a
//! variable-free state that is a ground application no equation evaluates: a function applied
//! where its equations give it no value, as the function KRS lifts from a `k::matches!` is where
//! the test has none (`k::matches!(k::project!(Int, a), 1)` at `a = true`). The backend keeps
//! that step's outcomes apart, each under a condition over the term: that it is defined and is
//! what the rule's condition needs, or that it is not. A function's application has a value only
//! where an equation gives it one, so the term has none, and a condition that reads a term with
//! no value does not hold: where a construct has no value, the sentence does not apply. The
//! outcome whose condition gives the term a value is therefore no state of the run, and the one
//! whose condition denies it one is the state the run reached.

use k_rust::kore::{ast::Pattern, walk};

use crate::values::strip_injections;

/// What a leaf's condition says once every term the backend could not evaluate is read as having
/// no value ([module docs](self)).
#[derive(Debug, PartialEq)]
pub(crate) enum Reading<'a> {
    /// The condition holds: the leaf is `configuration`, and its condition read `undecided`.
    Holds {
        configuration: &'a Pattern,
        undecided: Vec<&'a Pattern>,
    },
    /// The condition gives a term with no value a value: the leaf denotes no state.
    Fails,
    /// The condition is not one this reading decides.
    Open,
}

/// The reading of `state`, a configuration conjoined with its path condition.
pub(crate) fn read(state: &Pattern) -> Reading<'_> {
    let mut conjuncts = Vec::new();
    conjoined(state, &mut conjuncts);
    let (predicates, configurations): (Vec<_>, Vec<_>) = conjuncts
        .into_iter()
        .partition(|conjunct| is_predicate(conjunct));
    let [configuration] = configurations.as_slice() else {
        return Reading::Open;
    };
    let mut undecided = Vec::new();
    let mut verdict = Some(true);
    for predicate in predicates {
        match holds(predicate, &mut undecided) {
            Some(true) => {}
            Some(false) => return Reading::Fails,
            None => verdict = None,
        }
    }
    match verdict {
        Some(_) => Reading::Holds {
            configuration,
            undecided,
        },
        None => Reading::Open,
    }
}

fn conjoined<'a>(pattern: &'a Pattern, out: &mut Vec<&'a Pattern>) {
    match pattern {
        Pattern::And { arguments, .. } => {
            for argument in arguments {
                conjoined(argument, out);
            }
        }
        other => out.push(other),
    }
}

/// Whether `pattern` is a predicate: a matching-logic connective over predicates, or `#Ceil`,
/// `#Equals`, `#In`, `#Top` or `#Bottom`.
fn is_predicate(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::Ceil { .. }
        | Pattern::Floor { .. }
        | Pattern::Equals { .. }
        | Pattern::In { .. } => true,
        Pattern::Not { argument, .. } => is_predicate(argument),
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
            arguments.iter().all(is_predicate)
        }
        _ => false,
    }
}

/// Whether `predicate` holds where each term the backend left undecided has no value, `None`
/// where this reading does not decide it; each such term goes to `undecided`.
///
/// - `#Ceil(t)` does not hold: a run's backend discharges the definedness of every term it
///   evaluates, so the obligation it left is on a term it could not, which has no value.
/// - `{v #Equals t}` with `v` a domain value does not hold: the backend compares values, so `t`
///   is a term it could not evaluate, which has no value and so equals none.
/// - `#Not`, `#And`, `#Or`, `#Top` and `#Bottom` are read as written.
fn holds<'a>(predicate: &'a Pattern, undecided: &mut Vec<&'a Pattern>) -> Option<bool> {
    match predicate {
        Pattern::Top { .. } => Some(true),
        Pattern::Bottom { .. } => Some(false),
        Pattern::Ceil { argument, .. } => {
            note(undecided, argument);
            Some(false)
        }
        Pattern::Equals { left, right, .. } => {
            let other = match (is_value(left), is_value(right)) {
                (true, false) => right,
                (false, true) => left,
                _ => return None,
            };
            note(undecided, other);
            Some(false)
        }
        Pattern::Not { argument, .. } => holds(argument, undecided).map(|holds| !holds),
        Pattern::And { arguments, .. } => {
            let mut all = Some(true);
            for argument in arguments {
                match holds(argument, undecided) {
                    Some(true) => {}
                    Some(false) => return Some(false),
                    None => all = None,
                }
            }
            all
        }
        Pattern::Or { arguments, .. } => {
            let mut any = Some(false);
            for argument in arguments {
                match holds(argument, undecided) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => any = None,
                }
            }
            any
        }
        _ => None,
    }
}

fn is_value(pattern: &Pattern) -> bool {
    matches!(strip_injections(pattern), Pattern::DomainValue { .. })
}

fn note<'a>(undecided: &mut Vec<&'a Pattern>, term: &'a Pattern) {
    if !undecided.contains(&term) {
        undecided.push(term);
    }
}

/// Adds to `out` each function application in `configuration` that occurs in one of `read`, the
/// terms a leaf's condition read, outermost first: on a run's variable-free state the backend
/// left it unevaluated, so it has no value.
pub(crate) fn read_applications(
    configuration: &Pattern,
    read: &[Pattern],
    is_function: &dyn Fn(&str) -> bool,
    out: &mut Vec<Pattern>,
) {
    if let Pattern::Application { symbol, .. } = configuration
        && is_function(&symbol.name)
        && read.iter().any(|term| occurs(configuration, term))
    {
        if !out.contains(configuration) {
            out.push(configuration.clone());
        }
        return;
    }
    for child in walk::children(configuration) {
        read_applications(child, read, is_function, out);
    }
}

/// Whether `term` occurs in `pattern`.
fn occurs(term: &Pattern, pattern: &Pattern) -> bool {
    pattern == term
        || walk::children(pattern)
            .into_iter()
            .any(|child| occurs(term, child))
}
