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

use k_rust::backend::{SuccessorCandidate, SuccessorReading};
use k_rust::kore::{
    ast::{Pattern, Variable, VariableKind},
    walk,
};

/// The heads a reading of a state asks about.
pub(crate) trait Heads {
    /// Whether `symbol` is a partial function whose definition is its equations alone.
    fn is_equational_partial(&self, symbol: &str) -> bool;
    /// Whether `symbol` builds a value from values: a free constructor, a sort injection, or a
    /// builtin collection's unit, element or concatenation.
    fn is_data(&self, symbol: &str) -> bool;
}

/// A run's reading of the candidates of a stop rule's step, for the backend
/// ([`SuccessorReading`]): a candidate whose path condition does not hold, read with the
/// witnesses as having no value ([`read`]), denotes no state, as a leaf whose condition does not
/// hold is no state of the run (`one_path`). Where the run so far left a hook unevaluated,
/// nothing is decided to have no value ([`Undecided`]), as the run's leaves are then read, and
/// every candidate stays a successor.
pub(crate) struct Successors<'a>(pub(crate) &'a dyn Heads);

impl SuccessorReading for Successors<'_> {
    fn denotes_no_state(&self, candidate: &SuccessorCandidate<'_>) -> bool {
        if candidate.hooks_unevaluated() {
            return false;
        }
        let predicates = candidate.path_condition().iter().collect::<Vec<_>>();
        read(&predicates, self.0, &mut Vec::new()) == Reading::Fails
    }
}

/// Heads of which no application is decided to have no value: a run that met a hook the backend
/// did not evaluate reads its leaves with these, since the hook may leave an equation's
/// condition open.
pub(crate) struct Undecided;

impl Heads for Undecided {
    fn is_equational_partial(&self, _: &str) -> bool {
        false
    }

    fn is_data(&self, _: &str) -> bool {
        false
    }
}

/// Whether `pattern` is a value: a domain value, or data over values.
pub(crate) fn is_value(pattern: &Pattern, heads: &dyn Heads) -> bool {
    // A collection is a chain one level per element, so the walk keeps the terms still to read
    // on a stack of its own rather than the thread's.
    let mut pending = vec![pattern];
    while let Some(pattern) = pending.pop() {
        match pattern {
            Pattern::DomainValue { .. } => {}
            Pattern::Application { symbol, arguments } if heads.is_data(&symbol.name) => {
                pending.extend(arguments);
            }
            _ => return false,
        }
    }
    true
}

/// Whether `pattern` has a value at every valuation of its variables: a value, or an element
/// variable, which denotes exactly one value.
fn has_value(pattern: &Pattern, heads: &dyn Heads) -> bool {
    matches!(pattern, Pattern::Variable(variable) if variable.kind == VariableKind::Element)
        || is_value(pattern, heads)
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
///
/// The terms are visited in pre-order, children left to right, below no witness, from a stack
/// of their own: a state's collection is a chain one level per element.
pub(crate) fn witnesses<'a>(pattern: &'a Pattern, heads: &dyn Heads, out: &mut Vec<&'a Pattern>) {
    let mut pending = vec![pattern];
    while let Some(pattern) = pending.pop() {
        if is_witness(pattern, heads) {
            if !out.contains(&pattern) {
                out.push(pattern);
            }
            continue;
        }
        pending.extend(walk::children(pattern).into_iter().rev());
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

/// The configuration of `state` that [`split`] finds, moved out of `state`; `None` where it finds
/// none.
pub(crate) fn into_configuration(state: Pattern) -> Option<Pattern> {
    let mut configurations = Vec::new();
    let mut pending = vec![state];
    while let Some(mut pattern) = pending.pop() {
        if let Pattern::And { arguments, .. } = &mut pattern {
            pending.extend(std::mem::take(arguments).into_iter().rev());
        } else if !is_predicate(&pattern) {
            configurations.push(pattern);
        }
    }
    match <[_; 1]>::try_from(configurations) {
        Ok([configuration]) => Some(configuration),
        Err(_) => None,
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

/// Adds to `out` the conjuncts of `pattern`, left to right, below every `#And`, however deeply
/// the `#And`s nest.
fn conjoined<'a>(pattern: &'a Pattern, out: &mut Vec<&'a Pattern>) {
    let mut pending = vec![pattern];
    while let Some(pattern) = pending.pop() {
        match pattern {
            Pattern::And { arguments, .. } => pending.extend(arguments.iter().rev()),
            other => out.push(other),
        }
    }
}

/// Whether `pattern` is a predicate: a matching-logic connective or quantifier over predicates
/// (the backend states a projection's definedness as `#Exists V . {t #Equals V}`), or `#Ceil`,
/// `#Floor`, `#Equals`, `#In`, `#Top` or `#Bottom`.
fn is_predicate(pattern: &Pattern) -> bool {
    let mut pending = vec![pattern];
    while let Some(pattern) = pending.pop() {
        match pattern {
            Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::Ceil { .. }
            | Pattern::Floor { .. }
            | Pattern::Equals { .. }
            | Pattern::In { .. } => {}
            Pattern::Not { argument, .. } => pending.push(argument),
            Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
                pending.extend(arguments);
            }
            Pattern::Exists { body, .. } | Pattern::Forall { body, .. } => pending.push(body),
            _ => return false,
        }
    }
    true
}

/// Whether `predicate` holds, `None` where the reading does not decide it; the witnesses a
/// decided predicate read go to `read`, and the terms an undecided one read to `over`.
///
/// - `#Ceil(t)` does not hold where `t` holds a witness, and holds where `t` is a value.
/// - `{a #Equals b}` does not hold where one side holds a witness and the other has a value (a
///   value, or an element variable, which denotes one); it holds where both are the same value.
/// - `#Not`, `#And`, `#Or`, `#Top` and `#Bottom` are read as written.
/// - `#Exists V . p` and `#Forall V . p` are read as `p` is: every decision above is made at
///   witnesses and values, which hold no variable, so it is the same at every value of `V`, and
///   every sort has one. The terms an undecided `p` reads that mention `V` are not the run's.
/// - Anything else is undecided.
///
/// The reading recurses once per connective or quantifier of `predicate`, as the definition's
/// conditions nest them; the terms under them, which may hold a collection, are walked from
/// stacks of their own.
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
                if !found.is_empty() && has_value(other, heads) {
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
        Pattern::Exists { variable, body, .. } | Pattern::Forall { variable, body, .. } => {
            let mut open = Vec::new();
            let holds = holds(body, heads, read, &mut open);
            open.retain(|term| !mentions(term, variable));
            note(over, open);
            holds
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

/// Whether `pattern` holds `variable`.
fn mentions(pattern: &Pattern, variable: &Variable) -> bool {
    any_node(
        pattern,
        |node| matches!(node, Pattern::Variable(held) if held == variable),
    )
}

/// Whether `pattern` holds a variable.
pub(crate) fn is_symbolic(pattern: &Pattern) -> bool {
    any_node(pattern, |node| matches!(node, Pattern::Variable(_)))
}

/// Whether some node of `pattern` satisfies `test`, the nodes visited from a stack of the walk's
/// own.
fn any_node(pattern: &Pattern, test: impl Fn(&Pattern) -> bool) -> bool {
    let mut pending = vec![pattern];
    while let Some(pattern) = pending.pop() {
        if test(pattern) {
            return true;
        }
        pending.extend(walk::children(pattern));
    }
    false
}
