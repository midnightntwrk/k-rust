//! Terms with no value in a run's states, and the path conditions over them.
//!
//! A function has a value only where its definition gives it one. For a partial function whose
//! definition is its equations alone (declared neither `total` nor hooked, with no `smt-hook` or
//! `smtlib`, as the function KRS lifts from a static result's `k::matches!` is), that is where an
//! equation applies. A ground application of such a function, whose arguments are values, is
//! decided by matching and by conditions over values, so where the backend left it unevaluated
//! no equation applies, and the application has no value: a *witness* here. Every other term the
//! backend left unevaluated may have one: a symbolic term (an existential's `?V`) stands for
//! values the run has not fixed, a `total` function has a value at every argument even where no
//! equation names it, and a hook the backend does not evaluate can have one.
//!
//! Every symbol is strict, so a term that holds a witness has no value either: a state that holds
//! one has none, and a predicate that asserts its value (`#Ceil(t)`, `{v #Equals t}` with `v` a
//! value) does not hold. A rule's condition that reads a term with no value does not hold, so the
//! backend's outcome of the step where it holds is no state, and the outcome where it does not
//! is the state the run reached ([`read`]). A predicate over a term that is neither a value nor a
//! witness is not decided here: such a split is the definition's, and a run reports it rather
//! than choosing an outcome.

use k_rust::kore::{ast::Pattern, walk};

/// The heads a reading of a state asks about.
pub(crate) trait Heads {
    /// Whether `symbol` is a partial function whose definition is its equations alone.
    fn is_equational_partial(&self, symbol: &str) -> bool;
    /// Whether `symbol` builds a value from values: a free constructor, a sort injection, or a
    /// builtin collection's unit, element or concatenation.
    fn is_data(&self, symbol: &str) -> bool;
}

/// Whether `pattern` is a value: a domain value, or data over values.
pub(crate) fn is_value(pattern: &Pattern, heads: &dyn Heads) -> bool {
    match pattern {
        Pattern::DomainValue { .. } => true,
        Pattern::Application { symbol, arguments } => {
            heads.is_data(&symbol.name)
                && arguments.iter().all(|argument| is_value(argument, heads))
        }
        _ => false,
    }
}

/// Whether `pattern` is a witness: a partial function, defined by its equations alone, applied
/// to values ([module docs](self)).
fn is_witness(pattern: &Pattern, heads: &dyn Heads) -> bool {
    matches!(
        pattern,
        Pattern::Application { symbol, arguments }
            if heads.is_equational_partial(&symbol.name)
                && arguments.iter().all(|argument| is_value(argument, heads))
    )
}

/// Adds to `out` each witness `pattern` holds, outermost first, each once.
pub(crate) fn witnesses<'a>(pattern: &'a Pattern, heads: &dyn Heads, out: &mut Vec<&'a Pattern>) {
    if is_witness(pattern, heads) {
        if !out.contains(&pattern) {
            out.push(pattern);
        }
        return;
    }
    for child in walk::children(pattern) {
        witnesses(child, heads, out);
    }
}

/// A state split into its configuration and its path condition's conjuncts.
pub(crate) struct Split<'a> {
    /// The configuration, where the state has exactly one conjunct that is no predicate.
    pub(crate) configuration: Option<&'a Pattern>,
    /// The predicates conjoined with it.
    pub(crate) predicates: Vec<&'a Pattern>,
}

/// `state`, a configuration conjoined with its path condition, split.
pub(crate) fn split(state: &Pattern) -> Split<'_> {
    let mut conjuncts = Vec::new();
    conjoined(state, &mut conjuncts);
    let (predicates, configurations): (Vec<_>, Vec<_>) = conjuncts
        .into_iter()
        .partition(|conjunct| is_predicate(conjunct));
    Split {
        configuration: match configurations.as_slice() {
            [configuration] => Some(configuration),
            _ => None,
        },
        predicates,
    }
}

/// What a leaf's path condition says, read with the witnesses as having no value.
#[derive(Debug, PartialEq)]
pub(crate) enum Reading<'a> {
    /// Every predicate holds.
    Holds,
    /// A predicate does not hold: the leaf denotes no state.
    Fails,
    /// No predicate fails, and some are not decided here; `over` are the terms they read that
    /// are not values (the undecided predicate itself where it reads none).
    Open { over: Vec<&'a Pattern> },
}

/// The reading of `predicates`; each witness a decided predicate read goes to `read`.
pub(crate) fn read<'a>(
    predicates: &[&'a Pattern],
    heads: &dyn Heads,
    read: &mut Vec<&'a Pattern>,
) -> Reading<'a> {
    let mut over = Vec::new();
    for predicate in predicates {
        let mut open = Vec::new();
        match holds(predicate, heads, read, &mut open) {
            Some(true) => {}
            Some(false) => return Reading::Fails,
            None if open.is_empty() => note(&mut over, vec![*predicate]),
            None => note(&mut over, open),
        }
    }
    if over.is_empty() {
        Reading::Holds
    } else {
        Reading::Open { over }
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
/// `#Floor`, `#Equals`, `#In`, `#Top` or `#Bottom`.
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

/// Whether `predicate` holds, `None` where the reading does not decide it; the witnesses a
/// decided predicate read go to `read`, and the terms an undecided one read to `over`.
///
/// - `#Ceil(t)` does not hold where `t` holds a witness, and holds where `t` is a value.
/// - `{a #Equals b}` does not hold where one side holds a witness and the other is a value, which
///   has one; it holds where both are the same value.
/// - `#Not`, `#And`, `#Or`, `#Top` and `#Bottom` are read as written; anything else is undecided.
fn holds<'a>(
    predicate: &'a Pattern,
    heads: &dyn Heads,
    read: &mut Vec<&'a Pattern>,
    over: &mut Vec<&'a Pattern>,
) -> Option<bool> {
    match predicate {
        Pattern::Top { .. } => Some(true),
        Pattern::Bottom { .. } => Some(false),
        Pattern::Ceil { argument, .. } => {
            let mut found = Vec::new();
            witnesses(argument, heads, &mut found);
            if !found.is_empty() {
                note(read, found);
                Some(false)
            } else if is_value(argument, heads) {
                Some(true)
            } else {
                note(over, vec![argument]);
                None
            }
        }
        Pattern::Equals { left, right, .. } => {
            for (side, other) in [(left, right), (right, left)] {
                let mut found = Vec::new();
                witnesses(side, heads, &mut found);
                if !found.is_empty() && is_value(other, heads) {
                    note(read, found);
                    return Some(false);
                }
            }
            if is_value(left, heads) && left == right {
                return Some(true);
            }
            let open = [left.as_ref(), right.as_ref()]
                .into_iter()
                .filter(|side| !is_value(side, heads))
                .collect();
            note(over, open);
            None
        }
        Pattern::Not { argument, .. } => holds(argument, heads, read, over).map(|holds| !holds),
        Pattern::And { arguments, .. } => {
            let mut all = Some(true);
            for argument in arguments {
                match holds(argument, heads, read, over) {
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
                match holds(argument, heads, read, over) {
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

fn note<'a>(out: &mut Vec<&'a Pattern>, terms: Vec<&'a Pattern>) {
    for term in terms {
        if !out.contains(&term) {
            out.push(term);
        }
    }
}

/// Whether `pattern` holds a variable.
pub(crate) fn is_symbolic(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Variable(_)) || walk::children(pattern).into_iter().any(is_symbolic)
}
