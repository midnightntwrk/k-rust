//! Ground analysis of a function's equations on a bounded Int domain.
//!
//! An equation `f(p̄) => r requires φ` applies to the arguments that match
//! `p̄` and make `φ` true. When every equation of a set bounds each Int
//! argument its guard reads to a finite set (a literal, an or-pattern of
//! literals, or top-level conjuncts `c <= x`, `x < c`, `x == c`, which a
//! `k::bits!` template's range is), only finitely many argument vectors can
//! tell the equations apart: the values the equations bound, and one value
//! outside them per argument, which stands for every other (outside, a
//! bounded equation does not apply and an unbounded one does not read the
//! argument). Up to [`POINT_LIMIT`] such vectors, each equation's guard is
//! evaluated on every one, which decides exactly which equations apply
//! where. Two consumers read it: the overlap check of equations at one
//! priority, and the coverage lint of `total` functions.
//!
//! The evaluation is the builtins' definition on literals (`int_facts`),
//! constructors as free terms, `k::matches!` (`P :=K t`) of a value as
//! pattern matching, and total functions by their own equations
//! ([`Evaluator`]), and it decides nothing it is unsure of: a guard that
//! calls a function it cannot evaluate, reads a binder the pattern does not
//! bind, overflows `i128`, or is undefined anywhere (`10 /Int x` at
//! `x == 0`, unless a top-level conjunct is already false there) makes the
//! analysis give up on the whole set, so a consumer reports nothing rather
//! than guess. Matching logic reads an undefined guard as not holding while
//! a short-circuiting backend may read `true orElseBool ⊥` as true; giving
//! up keeps the analysis out of that disagreement.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, GuardMeaning, SemanticId, StableItemId,
};
use krs_ir_levels::{
    IrCondition, SemanticModule, SemanticProduction, SemanticRule, SemanticSortRef as Sort,
    SemanticTerm, SemanticTermKind,
};

use crate::coverage::{
    EquationSignature, Signature, binder_text, checked, display_name, instantiate,
    production_argument_sorts, symbolic_overlap,
};
use crate::int_facts::{IntFact, IntFacts, evaluate_int};

/// The argument vectors one analysis may enumerate.
pub(crate) const POINT_LIMIT: u64 = 1 << 16;

/// An equation as the analysis reads it.
#[derive(Clone, Copy)]
pub(crate) struct EquationView<'a> {
    pub(crate) id: &'a StableItemId,
    /// The arguments of the left-hand side's head application.
    pub(crate) arguments: &'a [SemanticTerm],
    pub(crate) guard: Option<&'a SemanticTerm>,
    pub(crate) result: &'a SemanticTerm,
}

/// What one equation admits at one argument.
#[derive(Clone, Debug)]
enum Admits {
    /// Literals.
    Values(BTreeSet<i128>),
    /// The integers from `.0` to below `.1`, which the guard bounds.
    Range(i128, i128),
    /// Every value: a binder the guard does not read.
    Any,
}

impl Admits {
    fn contains(&self, value: i128) -> bool {
        match self {
            Self::Values(values) => values.contains(&value),
            Self::Range(low, high) => *low <= value && value < *high,
            Self::Any => true,
        }
    }
}

/// One equation, read for evaluation.
struct Prepared<'a> {
    view: EquationView<'a>,
    admits: Vec<Admits>,
    /// Each binder of an Int argument, and the argument it names.
    binders: Vec<(&'a SemanticId, usize)>,
    /// Each binder of a non-Int argument, and the argument it names.
    free: Vec<(&'a SemanticId, usize)>,
    /// The guard's top-level conjuncts.
    conjuncts: Vec<&'a SemanticTerm>,
}

/// The values one argument ranges over.
#[derive(Clone, Debug)]
pub(crate) enum ColumnValues {
    /// An Int argument: the values the equations bound and one outside
    /// them, in the order witnesses prefer (non-negative first,
    /// nearest zero first).
    Int {
        values: Vec<i128>,
        /// The values the equations bound, as sorted disjoint half-open
        /// intervals; `values` is these and one value outside them.
        bounded: Vec<(i128, i128)>,
    },
    /// An argument every equation binds without reading it.
    Free,
}

/// A set of equations whose arguments the analysis can enumerate.
pub(crate) struct Domain<'a> {
    evaluator: &'a Evaluator<'a>,
    equations: Vec<Prepared<'a>>,
    columns: Vec<ColumnValues>,
}

/// One argument vector: the value of each Int argument (a free argument's
/// entry is `0` and means nothing).
pub(crate) type Point = Vec<i128>;

/// The analysis cannot decide some equation on some argument.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Undecided;

/// The value of a ground term.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[expect(
    clippy::large_enum_variant,
    reason = "A constructor term is a value like the others; values are few and short-lived."
)]
pub(crate) enum Ground {
    Int(i128),
    Bool(bool),
    /// A constructor applied to values.
    Term {
        id: StableItemId,
        instance: Vec<Sort>,
        arguments: Vec<Ground>,
    },
    /// The term has no value (a partial operation outside its domain).
    Undefined,
}

/// The values of an equation's binders.
pub(crate) type Environment<'a> = BTreeMap<&'a SemanticId, Ground>;

/// The deepest chain of function calls one evaluation follows.
const CALL_DEPTH: u32 = 64;
/// The function calls one evaluation may make in all.
const CALL_BUDGET: u32 = 4096;

/// A total function's equations, by priority band, lowest first (`owise`
/// is the rank 200, last: no equation beside it is ranked 200 or after,
/// [`first_equation_after_owise`]).
pub(crate) type Bands<'a> = Vec<Vec<EquationView<'a>>>;

/// Evaluates ground terms: builtins on literals, constructors, `P :=K t`
/// once `t` has a value, as pattern matching, and applications of the
/// total functions it holds by their own equations ([`Evaluator::call`]).
pub(crate) struct Evaluator<'a> {
    signature: &'a Signature,
    functions: BTreeMap<&'a StableItemId, Bands<'a>>,
    /// The calls the current evaluation may still make, and its depth.
    budget: Cell<u32>,
    depth: Cell<u32>,
    /// The values of calls already evaluated.
    values: RefCell<BTreeMap<(StableItemId, Vec<Ground>), Ground>>,
}

impl<'a> Evaluator<'a> {
    /// An evaluator of builtins, constructors and `k::matches!` only.
    #[cfg(test)]
    pub(crate) fn new(signature: &'a Signature) -> Self {
        Self::with_functions(signature, BTreeMap::new())
    }

    /// An evaluator that also applies `functions` by their equations.
    pub(crate) fn with_functions(
        signature: &'a Signature,
        functions: BTreeMap<&'a StableItemId, Bands<'a>>,
    ) -> Self {
        Self {
            signature,
            functions,
            budget: Cell::new(CALL_BUDGET),
            depth: Cell::new(0),
            values: RefCell::default(),
        }
    }

    /// The value of `id(arguments)` by the function's own equations: in the
    /// first priority band where an equation applies (its patterns match
    /// and its guard evaluates to `true`), the one value every applying
    /// equation's result evaluates to. `None` (the evaluation cannot tell)
    /// when no equation applies, two applying results differ, any part
    /// cannot be evaluated (a pattern or guard the evaluation does not
    /// read, a guard undefined there, on which a lazy and a strict reading
    /// disagree), or the call depth or the calls run out. Each of those
    /// gives up rather than guess, so a value it returns is the value the
    /// definition states.
    fn call(&self, id: &StableItemId, bands: &Bands<'_>, arguments: Vec<Ground>) -> Option<Ground> {
        let key = (id.clone(), arguments);
        if let Some(value) = self.values.borrow().get(&key) {
            return Some(value.clone());
        }
        if self.depth.get() == 0 {
            self.budget.set(CALL_BUDGET);
        }
        if self.depth.get() >= CALL_DEPTH || self.budget.get() == 0 {
            return None;
        }
        self.budget.set(self.budget.get() - 1);
        self.depth.set(self.depth.get() + 1);
        let value = self.apply(bands, &key.1);
        self.depth.set(self.depth.get() - 1);
        if let Some(value) = &value {
            self.values.borrow_mut().insert(key, value.clone());
        }
        value
    }

    /// See [`Evaluator::call`].
    fn apply(&self, bands: &Bands<'_>, arguments: &[Ground]) -> Option<Ground> {
        for band in bands {
            let mut found: Option<Ground> = None;
            for view in band {
                if view.arguments.len() != arguments.len() {
                    return None;
                }
                let mut environment = Environment::new();
                let mut matched = true;
                for (pattern, value) in view.arguments.iter().zip(arguments) {
                    if !self.bind(pattern, value, &mut environment)? {
                        matched = false;
                        break;
                    }
                }
                if !matched {
                    continue;
                }
                if let Some(guard) = view.guard {
                    let refuted = conjuncts(guard).iter().any(|conjunct| {
                        self.evaluate(conjunct, &environment) == Some(Ground::Bool(false))
                    });
                    if refuted {
                        continue;
                    }
                    match self.evaluate(guard, &environment)? {
                        Ground::Bool(true) => {}
                        Ground::Bool(false) => continue,
                        Ground::Int(_) | Ground::Term { .. } | Ground::Undefined => return None,
                    }
                }
                let result = self.evaluate(view.result, &environment)?;
                if result == Ground::Undefined {
                    return None;
                }
                match &found {
                    None => found = Some(result),
                    Some(other) if *other == result => {}
                    Some(_) => return None,
                }
            }
            if found.is_some() {
                return found;
            }
        }
        None
    }

    /// Matches an equation's argument pattern against a value, binding its
    /// binders: `None` when the evaluation cannot tell.
    fn bind<'p>(
        &self,
        pattern: &'p SemanticTerm,
        value: &Ground,
        environment: &mut Environment<'p>,
    ) -> Option<bool> {
        match pattern.kind() {
            SemanticTermKind::Variable { variable } => {
                if !self.signature.value_in_sort(value, pattern.sort())? {
                    return Some(false);
                }
                Some(bind_name(environment, variable, value))
            }
            SemanticTermKind::As {
                alias,
                pattern: inner,
            } => {
                if !self.bind(inner, value, environment)? {
                    return Some(false);
                }
                Some(bind_name(environment, alias, value))
            }
            SemanticTermKind::Or { alternatives } => {
                // Alternatives bind the same names; two that match with
                // different bindings would be two equations at once.
                let mut chosen: Option<Environment<'p>> = None;
                for alternative in alternatives {
                    let mut candidate = environment.clone();
                    if self.bind(alternative, value, &mut candidate)? {
                        match &chosen {
                            None => chosen = Some(candidate),
                            Some(other) if *other == candidate => {}
                            Some(_) => return None,
                        }
                    }
                }
                match chosen {
                    Some(bound) => {
                        *environment = bound;
                        Some(true)
                    }
                    None => Some(false),
                }
            }
            SemanticTermKind::Application {
                application: ApplicationRef::Declared(id),
                arguments,
                instance,
                ..
            } if self.signature.is_constructor(id) => match value {
                Ground::Term {
                    id: other,
                    instance: other_instance,
                    arguments: values,
                } => {
                    if id != other || instance != other_instance || arguments.len() != values.len()
                    {
                        return Some(false);
                    }
                    for (argument, value) in arguments.iter().zip(values) {
                        if !self.bind(argument, value, environment)? {
                            return Some(false);
                        }
                    }
                    Some(true)
                }
                Ground::Int(_) | Ground::Bool(_) => Some(false),
                Ground::Undefined => None,
            },
            SemanticTermKind::Token { .. } => self.matches(pattern, value),
            _ => None,
        }
    }

    /// The value of a term under an environment, `None` when the analysis
    /// cannot compute it.
    fn evaluate(&self, term: &SemanticTerm, environment: &Environment<'_>) -> Option<Ground> {
        match term.kind() {
            SemanticTermKind::Token { value } => match term.sort() {
                Sort::Builtin(BuiltinSort::Int) => value.parse().ok().map(Ground::Int),
                Sort::Builtin(BuiltinSort::Bool) => match value.as_str() {
                    "true" => Some(Ground::Bool(true)),
                    "false" => Some(Ground::Bool(false)),
                    _ => None,
                },
                _ => None,
            },
            SemanticTermKind::Variable { variable } => environment.get(variable).cloned(),
            SemanticTermKind::Application {
                application: ApplicationRef::Builtin(builtin),
                arguments,
                ..
            } => {
                let values = arguments
                    .iter()
                    .map(|argument| self.evaluate(argument, environment))
                    .collect::<Option<Vec<_>>>()?;
                operation(*builtin, &values)
            }
            SemanticTermKind::Application {
                application: ApplicationRef::Declared(id),
                arguments,
                instance,
                ..
            } if self.signature.is_constructor(id) => {
                let values = arguments
                    .iter()
                    .map(|argument| self.evaluate(argument, environment))
                    .collect::<Option<Vec<_>>>()?;
                // A constructor is strict as every symbol is.
                if values.contains(&Ground::Undefined) {
                    return Some(Ground::Undefined);
                }
                Some(Ground::Term {
                    id: id.clone(),
                    instance: instance.clone(),
                    arguments: values,
                })
            }
            SemanticTermKind::Application {
                application: ApplicationRef::Declared(id),
                arguments,
                ..
            } => {
                let bands = self.functions.get(id)?;
                let values = arguments
                    .iter()
                    .map(|argument| self.evaluate(argument, environment))
                    .collect::<Option<Vec<_>>>()?;
                if values.contains(&Ground::Undefined) {
                    return Some(Ground::Undefined);
                }
                self.call(id, bands, values)
            }
            SemanticTermKind::Matches {
                subject, pattern, ..
            } => match self.evaluate(subject, environment)? {
                Ground::Undefined => Some(Ground::Undefined),
                value => self.matches(pattern, &value).map(Ground::Bool),
            },
            _ => None,
        }
    }

    /// Whether a `k::matches!` pattern matches a value: constructors are
    /// free, so two terms with different heads differ. `None` when the
    /// analysis cannot tell.
    fn matches(&self, pattern: &SemanticTerm, value: &Ground) -> Option<bool> {
        match (pattern.kind(), value) {
            (_, Ground::Undefined) => None,
            (SemanticTermKind::Variable { .. }, _) => {
                self.signature.value_in_sort(value, pattern.sort())
            }
            (SemanticTermKind::Token { value: text }, Ground::Int(number)) => {
                match pattern.sort() {
                    Sort::Builtin(BuiltinSort::Int) => Some(text.parse::<i128>().ok()? == *number),
                    Sort::Builtin(BuiltinSort::Bool) => Some(false),
                    _ => None,
                }
            }
            (SemanticTermKind::Token { value: text }, Ground::Bool(truth)) => {
                match pattern.sort() {
                    Sort::Builtin(BuiltinSort::Bool) => Some((text == "true") == *truth),
                    Sort::Builtin(BuiltinSort::Int) => Some(false),
                    _ => None,
                }
            }
            (SemanticTermKind::Token { .. }, Ground::Term { .. }) => matches!(
                pattern.sort(),
                Sort::Builtin(BuiltinSort::Int | BuiltinSort::Bool)
            )
            .then_some(false),
            (
                SemanticTermKind::Application {
                    application: ApplicationRef::Declared(id),
                    arguments,
                    instance,
                    ..
                },
                _,
            ) if self.signature.is_constructor(id) => match value {
                Ground::Term {
                    id: other,
                    instance: other_instance,
                    arguments: values,
                } => {
                    if id != other || instance != other_instance || arguments.len() != values.len()
                    {
                        return Some(false);
                    }
                    let mut all = Some(true);
                    for (argument, value) in arguments.iter().zip(values) {
                        match self.matches(argument, value) {
                            Some(false) => return Some(false),
                            Some(true) => {}
                            None => all = None,
                        }
                    }
                    all
                }
                _ => Some(false),
            },
            (SemanticTermKind::As { pattern, .. }, _) => self.matches(pattern, value),
            (SemanticTermKind::Or { alternatives }, _) => {
                let mut any = Some(false);
                for alternative in alternatives {
                    match self.matches(alternative, value) {
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
}

/// The top-level conjuncts of a guard.
fn conjuncts(term: &SemanticTerm) -> Vec<&SemanticTerm> {
    if let SemanticTermKind::Application {
        application: ApplicationRef::Builtin(operation),
        arguments,
        ..
    } = term.kind()
        && operation.guard_meaning() == GuardMeaning::Conjunction
        && let [left, right] = arguments.as_slice()
    {
        let mut all = conjuncts(left);
        all.extend(conjuncts(right));
        return all;
    }
    vec![term]
}

/// Whether a term reads a variable.
fn mentions(term: &SemanticTerm, variable: &SemanticId) -> bool {
    match term.kind() {
        SemanticTermKind::Variable { variable: other } => other == variable,
        SemanticTermKind::Token { .. } => false,
        SemanticTermKind::Application { arguments, .. } => arguments
            .iter()
            .any(|argument| mentions(argument, variable)),
        SemanticTermKind::KSequence { items, .. } => {
            items.iter().any(|item| mentions(item, variable))
        }
        SemanticTermKind::As { alias, pattern } => alias == variable || mentions(pattern, variable),
        SemanticTermKind::Or { alternatives } => {
            alternatives.iter().any(|choice| mentions(choice, variable))
        }
        SemanticTermKind::Matches {
            subject, pattern, ..
        } => mentions(subject, variable) || mentions(pattern, variable),
        SemanticTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => mentions(pattern, variable) || mentions(value, variable) || mentions(body, variable),
        SemanticTermKind::Rewrite { from, to } => {
            mentions(from, variable) || mentions(to, variable)
        }
        // Collections and cells: assume they may read it.
        _ => true,
    }
}

fn int_token(term: &SemanticTerm) -> Option<i128> {
    match term.kind() {
        SemanticTermKind::Token { value }
            if matches!(term.sort(), Sort::Builtin(BuiltinSort::Int)) =>
        {
            value.parse().ok()
        }
        _ => None,
    }
}

/// A builtin operation on ground operands: `None` when the analysis cannot
/// compute it.
fn operation(operation: BuiltinOperation, values: &[Ground]) -> Option<Ground> {
    if values.contains(&Ground::Undefined) {
        // Every builtin is strict in matching logic: an undefined operand
        // makes the application undefined.
        return Some(Ground::Undefined);
    }
    let ints = values
        .iter()
        .map(|value| match value {
            Ground::Int(value) => Some(*value),
            _ => None,
        })
        .collect::<Option<Vec<_>>>();
    let bools = values
        .iter()
        .map(|value| match value {
            Ground::Bool(value) => Some(*value),
            _ => None,
        })
        .collect::<Option<Vec<_>>>();
    match (operation.guard_meaning(), bools.as_deref()) {
        (GuardMeaning::Negation, Some([value])) => return Some(Ground::Bool(!value)),
        (GuardMeaning::Conjunction, Some([left, right])) => {
            return Some(Ground::Bool(*left && *right));
        }
        (GuardMeaning::Disjunction, Some([left, right])) => {
            return Some(Ground::Bool(*left || *right));
        }
        (GuardMeaning::Implication, Some([left, right])) => {
            return Some(Ground::Bool(!left || *right));
        }
        (GuardMeaning::Relation(literal), _) => {
            let (first, second) = if literal.swapped {
                (&values[1], &values[0])
            } else {
                (&values[0], &values[1])
            };
            let holds = match (literal.relation, first, second) {
                (BuiltinOperation::IntLess, Ground::Int(left), Ground::Int(right)) => left < right,
                (BuiltinOperation::IntEqual, Ground::Int(left), Ground::Int(right)) => {
                    left == right
                }
                (BuiltinOperation::BoolEqual, Ground::Bool(left), Ground::Bool(right)) => {
                    left == right
                }
                _ => return None,
            };
            return Some(Ground::Bool(holds == literal.positive));
        }
        _ => {}
    }
    let ints = ints?;
    // The partial Int operations outside their domain (domains.md: division
    // by zero, a negative shift, exponent, index or length).
    let undefined = match (operation, ints.as_slice()) {
        (
            BuiltinOperation::IntTDiv
            | BuiltinOperation::IntTMod
            | BuiltinOperation::IntEDiv
            | BuiltinOperation::IntMod,
            [_, divisor],
        ) => *divisor == 0,
        (
            BuiltinOperation::IntShiftLeft
            | BuiltinOperation::IntShiftRight
            | BuiltinOperation::IntPow,
            [_, amount],
        ) => *amount < 0,
        (BuiltinOperation::IntBitRange, [_, index, length]) => *index < 0 || *length < 0,
        (BuiltinOperation::IntSignExtendBitRange, [_, index, length]) => *index < 0 || *length < 1,
        _ => false,
    };
    if undefined {
        return Some(Ground::Undefined);
    }
    evaluate_int(operation, &ints).map(Ground::Int)
}

/// The interval a top-level conjunct bounds a variable to, as an Int fact.
fn bound_fact(
    evaluator: &Evaluator<'_>,
    conjunct: &SemanticTerm,
    names: &[&SemanticId],
) -> Option<IntFact> {
    let SemanticTermKind::Application {
        application: ApplicationRef::Builtin(builtin),
        arguments,
        ..
    } = conjunct.kind()
    else {
        return None;
    };
    let GuardMeaning::Relation(literal) = builtin.guard_meaning() else {
        return None;
    };
    let [first, second] = arguments.as_slice() else {
        return None;
    };
    let (left, right) = if literal.swapped {
        (second, first)
    } else {
        (first, second)
    };
    let is_name = |term: &SemanticTerm| matches!(term.kind(), SemanticTermKind::Variable { variable } if names.contains(&variable));
    let constant = |term: &SemanticTerm| match evaluator.evaluate(term, &BTreeMap::new()) {
        Some(Ground::Int(value)) => Some(value),
        _ => None,
    };
    match (literal.relation, literal.positive) {
        (BuiltinOperation::IntEqual, true) => {
            if is_name(left) {
                constant(right).map(IntFact::Equal)
            } else if is_name(right) {
                constant(left).map(IntFact::Equal)
            } else {
                None
            }
        }
        // `left < right` when positive, `right <= left` otherwise.
        (BuiltinOperation::IntLess, positive) => {
            if is_name(left) {
                let bound = constant(right)?;
                Some(if positive {
                    IntFact::Below(bound)
                } else {
                    IntFact::AtLeast(bound)
                })
            } else if is_name(right) {
                let bound = constant(left)?;
                Some(if positive {
                    IntFact::AtLeast(bound.checked_add(1)?)
                } else {
                    IntFact::Below(bound.checked_add(1)?)
                })
            } else {
                None
            }
        }
        _ => None,
    }
}

/// What a pattern admits at an Int argument, and the names it binds there.
fn int_pattern(term: &SemanticTerm) -> Option<(Option<BTreeSet<i128>>, Vec<&SemanticId>)> {
    match term.kind() {
        SemanticTermKind::Token { .. } => {
            Some((Some(BTreeSet::from([int_token(term)?])), Vec::new()))
        }
        SemanticTermKind::Variable { variable } => Some((None, vec![variable])),
        SemanticTermKind::As { alias, pattern } => {
            let (values, mut names) = int_pattern(pattern)?;
            names.push(alias);
            Some((values, names))
        }
        SemanticTermKind::Or { alternatives } => Some((
            Some(
                alternatives
                    .iter()
                    .map(int_token)
                    .collect::<Option<BTreeSet<_>>>()?,
            ),
            Vec::new(),
        )),
        _ => None,
    }
}

/// Reads one equation, or `None` when the analysis cannot.
fn prepare<'a>(
    evaluator: &Evaluator<'_>,
    view: EquationView<'a>,
    columns: &[Sort],
) -> Option<Prepared<'a>> {
    if view.arguments.len() != columns.len() {
        return None;
    }
    let conjuncts = view.guard.map(conjuncts).unwrap_or_default();
    let reads = |name: &SemanticId| view.guard.is_some_and(|guard| mentions(guard, name));
    let mut admits = Vec::new();
    let mut binders = Vec::new();
    let mut free = Vec::new();
    let mut seen = BTreeSet::new();
    for (index, (argument, sort)) in view.arguments.iter().zip(columns).enumerate() {
        if matches!(sort, Sort::Builtin(BuiltinSort::Int)) {
            let (values, names) = int_pattern(argument)?;
            for name in &names {
                // A binder that occurs twice matches equal subterms only.
                if !seen.insert(*name) {
                    return None;
                }
                binders.push((*name, index));
            }
            admits.push(match values {
                Some(values) => Admits::Values(values),
                None if names.iter().any(|name| reads(name)) => {
                    let mut facts = IntFacts::default();
                    for conjunct in &conjuncts {
                        if let Some(fact) = bound_fact(evaluator, conjunct, &names) {
                            facts.add(fact);
                        }
                    }
                    let (low, high) = facts.bounds()?;
                    Admits::Range(low, high)
                }
                None => Admits::Any,
            });
        } else {
            // A non-Int argument must be a binder of the argument's sort
            // that the guard does not read.
            let SemanticTermKind::Variable { variable } = argument.kind() else {
                return None;
            };
            if argument.sort() != sort || reads(variable) || !seen.insert(variable) {
                return None;
            }
            free.push((variable, index));
            admits.push(Admits::Any);
        }
    }
    Some(Prepared {
        view,
        admits,
        binders,
        free,
        conjuncts,
    })
}

/// The union of the values the equations bound at one Int argument, as
/// sorted disjoint half-open intervals.
fn union(admits: &[&Admits]) -> Vec<(i128, i128)> {
    let mut intervals = Vec::new();
    for admit in admits {
        match admit {
            Admits::Values(values) => {
                intervals.extend(
                    values
                        .iter()
                        .filter_map(|value| Some((*value, value.checked_add(1)?))),
                );
            }
            Admits::Range(low, high) if low < high => intervals.push((*low, *high)),
            Admits::Range(..) | Admits::Any => {}
        }
    }
    intervals.sort_unstable();
    let mut merged: Vec<(i128, i128)> = Vec::new();
    for (low, high) in intervals {
        match merged.last_mut() {
            Some(last) if low <= last.1 => last.1 = last.1.max(high),
            _ => merged.push((low, high)),
        }
    }
    merged
}

/// The smallest non-negative integer outside the intervals, else the
/// greatest negative one.
fn outside(intervals: &[(i128, i128)]) -> Option<i128> {
    let mut candidate = 0_i128;
    for (low, high) in intervals {
        if *low <= candidate && candidate < *high {
            candidate = *high;
        }
    }
    if candidate < i128::MAX {
        return Some(candidate);
    }
    let mut candidate = -1_i128;
    for (low, high) in intervals.iter().rev() {
        if *low <= candidate && candidate < *high {
            candidate = low.checked_sub(1)?;
        }
    }
    Some(candidate)
}

impl<'a> Domain<'a> {
    /// The domain of a set of equations over arguments of `columns`'
    /// sorts, or `None` when some equation is beyond the analysis or the
    /// domain has more than [`POINT_LIMIT`] points.
    pub(crate) fn new(
        evaluator: &'a Evaluator<'a>,
        columns: &[Sort],
        views: &[EquationView<'a>],
    ) -> Option<Self> {
        let equations = views
            .iter()
            .map(|view| prepare(evaluator, *view, columns))
            .collect::<Option<Vec<_>>>()?;
        let mut size = 1_u64;
        let mut values = Vec::new();
        for (index, sort) in columns.iter().enumerate() {
            if !matches!(sort, Sort::Builtin(BuiltinSort::Int)) {
                values.push(ColumnValues::Free);
                continue;
            }
            let admits = equations
                .iter()
                .map(|equation| &equation.admits[index])
                .collect::<Vec<_>>();
            let bounded = union(&admits);
            let mut count = 1_u64;
            for (low, high) in &bounded {
                count = count.saturating_add(u64::try_from(high - low).unwrap_or(u64::MAX));
            }
            size = size.saturating_mul(count);
            if size > POINT_LIMIT {
                return None;
            }
            let outside = outside(&bounded)?;
            let mut points = bounded
                .iter()
                .flat_map(|(low, high)| *low..*high)
                .chain([outside])
                .collect::<Vec<_>>();
            points.sort_by_key(|value| (*value < 0, value.unsigned_abs()));
            values.push(ColumnValues::Int {
                values: points,
                bounded,
            });
        }
        Some(Self {
            evaluator,
            equations,
            columns: values,
        })
    }

    /// The values of each argument.
    pub(crate) fn columns(&self) -> &[ColumnValues] {
        &self.columns
    }

    /// Every argument vector, in the order witnesses prefer.
    pub(crate) fn points(&self) -> impl Iterator<Item = Point> + '_ {
        let sizes = self
            .columns
            .iter()
            .map(|column| match column {
                ColumnValues::Int { values, .. } => values.len(),
                ColumnValues::Free => 1,
            })
            .collect::<Vec<_>>();
        let total = sizes.iter().product::<usize>();
        (0..total).map(move |mut index| {
            let mut point = vec![0; sizes.len()];
            for column in (0..sizes.len()).rev() {
                let position = index % sizes[column];
                index /= sizes[column];
                if let ColumnValues::Int { values, .. } = &self.columns[column] {
                    point[column] = values[position];
                }
            }
            point
        })
    }

    /// The environment of an equation at a point.
    fn environment(&self, equation: usize, point: &[i128]) -> Environment<'a> {
        self.equations[equation]
            .binders
            .iter()
            .map(|(name, column)| (*name, Ground::Int(point[*column])))
            .collect()
    }

    /// Whether an equation applies at a point.
    pub(crate) fn applies(&self, equation: usize, point: &[i128]) -> Result<bool, Undecided> {
        let prepared = &self.equations[equation];
        if prepared
            .admits
            .iter()
            .zip(point)
            .zip(&self.columns)
            .any(|((admits, value), column)| {
                matches!(column, ColumnValues::Int { .. }) && !admits.contains(*value)
            })
        {
            return Ok(false);
        }
        let Some(guard) = prepared.view.guard else {
            return Ok(true);
        };
        let environment = self.environment(equation, point);
        // A false top-level conjunct makes the guard not hold however the
        // others evaluate, even undefined.
        if prepared.conjuncts.iter().any(|conjunct| {
            self.evaluator.evaluate(conjunct, &environment) == Some(Ground::Bool(false))
        }) {
            return Ok(false);
        }
        match self.evaluator.evaluate(guard, &environment) {
            Some(Ground::Bool(holds)) => Ok(holds),
            _ => Err(Undecided),
        }
    }

    /// An equation's result at a point, with its Int binders replaced by
    /// their values and builtins on literals evaluated: a comparison key and
    /// a rendering. `None` when the result has a form the analysis does not
    /// compare.
    pub(crate) fn result(&self, equation: usize, point: &[i128]) -> Option<(String, String)> {
        let prepared = &self.equations[equation];
        let environment = self.environment(equation, point);
        let free = prepared
            .free
            .iter()
            .map(|(name, column)| (*name, *column))
            .collect::<BTreeMap<_, _>>();
        ground_text(self.evaluator, prepared.view.result, &environment, &free)
    }
}

/// Whether a guard holds, exactly, with its Int binders at the given
/// values: `Some(true)` only when it evaluates to `true` (every operation in
/// it then is defined, so a lazy and a strict reading agree), `Some(false)`
/// when it is false or undefined, `None` when the evaluation cannot tell.
pub(crate) fn guard_holds(
    evaluator: &Evaluator<'_>,
    guard: &SemanticTerm,
    environment: &Environment<'_>,
) -> Option<bool> {
    if conjuncts(guard)
        .iter()
        .any(|conjunct| evaluator.evaluate(conjunct, environment) == Some(Ground::Bool(false)))
    {
        return Some(false);
    }
    match evaluator.evaluate(guard, environment)? {
        Ground::Bool(holds) => Some(holds),
        Ground::Undefined => Some(false),
        Ground::Int(_) | Ground::Term { .. } => None,
    }
}

/// The literal a ground Int or Bool term evaluates to, with its Int binders
/// at the given values.
pub(crate) fn ground_literal(
    evaluator: &Evaluator<'_>,
    term: &SemanticTerm,
    environment: &Environment<'_>,
) -> Option<String> {
    match evaluator.evaluate(term, environment)? {
        Ground::Int(value) => Some(value.to_string()),
        Ground::Bool(value) => Some(value.to_string()),
        Ground::Term { .. } | Ground::Undefined => None,
    }
}

/// A term with its Int binders replaced and its ground builtins evaluated:
/// a key in which every binder of a free argument is named by its position,
/// and a rendering.
fn ground_text(
    evaluator: &Evaluator<'_>,
    term: &SemanticTerm,
    environment: &Environment<'_>,
    free: &BTreeMap<&SemanticId, usize>,
) -> Option<(String, String)> {
    if let Some(value) = evaluator.evaluate(term, environment) {
        match value {
            Ground::Int(value) => return Some((value.to_string(), value.to_string())),
            Ground::Bool(value) => return Some((value.to_string(), value.to_string())),
            Ground::Term { .. } | Ground::Undefined => {}
        }
    }
    let list = |terms: &mut dyn Iterator<Item = &SemanticTerm>| {
        let mut keys = Vec::new();
        let mut texts = Vec::new();
        for term in terms {
            let (key, text) = ground_text(evaluator, term, environment, free)?;
            keys.push(key);
            texts.push(text);
        }
        Some((keys.join(", "), texts.join(", ")))
    };
    match term.kind() {
        SemanticTermKind::Variable { variable } => {
            let column = free.get(variable)?;
            Some((format!("${column}"), binder_text(variable)))
        }
        SemanticTermKind::Token { value } => {
            Some((format!("{:?}:{value}", term.sort()), value.clone()))
        }
        SemanticTermKind::Application {
            application,
            arguments,
            instance,
            ..
        } => {
            let (key, text) = match application {
                ApplicationRef::Declared(id) => (format!("{id:?}{instance:?}"), display_name(id)),
                ApplicationRef::Builtin(operation) => {
                    let spec = operation.spec();
                    (
                        format!("{operation:?}"),
                        format!("{}::{}", spec.rust_module, spec.rust_name),
                    )
                }
                ApplicationRef::Generated(generated) => {
                    (format!("{generated:?}"), format!("{generated:?}"))
                }
            };
            let (keys, texts) = list(&mut arguments.iter())?;
            let text = if arguments.is_empty() && matches!(application, ApplicationRef::Declared(_))
            {
                text
            } else {
                format!("{text}({texts})")
            };
            Some((format!("{key}({keys})"), text))
        }
        SemanticTermKind::KSequence { items, .. } => {
            let mut keys = Vec::new();
            let mut texts = Vec::new();
            for item in items {
                let (key, text) = ground_text(evaluator, item, environment, free)?;
                keys.push(key);
                texts.push(text);
            }
            Some((
                format!("seq({})", keys.join(", ")),
                if texts.is_empty() {
                    "k::k![]".to_owned()
                } else {
                    format!("k::k![{}]", texts.join(", "))
                },
            ))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The overlap check of equations

/// Two equations of one function at one priority that apply to one argument
/// and give it different results.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EquationOverlap {
    /// The function, rendered.
    pub(crate) function: String,
    /// The first equation in stable-identity order.
    pub(crate) first: StableItemId,
    /// The second equation in stable-identity order.
    pub(crate) second: StableItemId,
    /// The application both apply to, rendered (`Decode(118)`).
    pub(crate) application: String,
    /// The first and the second equation's result there, rendered.
    pub(crate) results: (String, String),
}

/// An equation with a written `priority = N`, `N` of 200 or more, beside an
/// `owise` equation of its function.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EquationAfterOwise {
    /// The function, rendered.
    pub(crate) function: String,
    /// The `owise` equation.
    pub(crate) owise: StableItemId,
    /// The equation ranked with or after it.
    pub(crate) equation: StableItemId,
    /// That equation's priority.
    pub(crate) priority: u32,
    /// The exact authored range of that priority.
    pub(crate) range: Option<krs_ir::SourceRange>,
}

/// The first function, in declaration order, with an `owise` equation and an
/// equation whose written priority is 200 or more.
///
/// `owise` states that its equation gives the value where no other equation
/// of the function applies, so every other equation is tried before it. A
/// written `priority = N` with `N` of 200 or more orders its equation with or
/// after the `owise` one, the rank 200 that orders `owise` after the default
/// priority: the definition would state two orders between the two.
pub(crate) fn first_equation_after_owise(modules: &[SemanticModule]) -> Option<EquationAfterOwise> {
    function_equations(modules)
        .into_iter()
        .find_map(|(production, _, rules)| {
            let owise = rules.iter().find(|rule| {
                rule.priority()
                    .is_some_and(krs_ir_levels::SemanticRulePriority::is_owise)
            })?;
            let (equation, priority) = rules.iter().find_map(|rule| {
                let priority = rule.priority()?;
                (!priority.is_owise() && priority.value() >= OWISE_RANK).then_some((rule, priority))
            })?;
            Some(EquationAfterOwise {
                function: display_name(production.id()),
                owise: owise.id().clone(),
                equation: equation.id().clone(),
                priority: priority.value(),
                range: priority.origin().origin().exact_authored_range(),
            })
        })
}

/// The rank of an `owise` sentence: after every sentence of the default
/// priority (50).
pub(crate) const OWISE_RANK: u32 = 200;

/// The equations of each function, grouped by the instance their head names.
pub(crate) fn function_equations(
    modules: &[SemanticModule],
) -> Vec<(&SemanticProduction, Vec<Sort>, Vec<&SemanticRule>)> {
    let mut equations = BTreeMap::<&StableItemId, BTreeMap<Vec<Sort>, Vec<&SemanticRule>>>::new();
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        if rule.kind() != krs_ir::SentenceKind::Equation {
            continue;
        }
        if let Some(body) = rule.body()
            && let SemanticTermKind::Application {
                application: ApplicationRef::Declared(head),
                instance,
                ..
            } = body.from().kind()
        {
            equations
                .entry(head)
                .or_default()
                .entry(instance.clone())
                .or_default()
                .push(rule);
        }
    }
    let mut grouped = Vec::new();
    for production in modules.iter().flat_map(SemanticModule::productions) {
        if let Some(instances) = equations.remove(production.id()) {
            for (instance, rules) in instances {
                grouped.push((production, instance, rules));
            }
        }
    }
    grouped
}

/// Binds a pattern's binder to a value, or, when it is already bound (it
/// occurs twice), whether the value is the one bound: constructors are
/// free, so equal values are equal terms and different ones differ.
fn bind_name<'p>(environment: &mut Environment<'p>, name: &'p SemanticId, value: &Ground) -> bool {
    if let Some(bound) = environment.get(name) {
        return bound == value;
    }
    environment.insert(name, value.clone());
    true
}

/// The equations of each total function the evaluator can apply: a
/// non-parametric total function that neither the backend nor the SMT
/// solver defines, all of whose equations the evaluation can read (none
/// reads the configuration or has a matching-logic `requires`). None in a
/// definition with `raw_k!` sentences, which may add equations the
/// evaluation does not see.
pub(crate) fn evaluable_functions(
    modules: &[SemanticModule],
) -> BTreeMap<&StableItemId, Bands<'_>> {
    let mut functions = BTreeMap::new();
    if modules
        .iter()
        .any(|module| !module.raw_sentences().is_empty())
    {
        return functions;
    }
    for (production, instance, rules) in function_equations(modules) {
        if !instance.is_empty() || !production.parameters().is_empty() || !checked(production) {
            continue;
        }
        let Some(views) = rules
            .iter()
            .map(|rule| {
                Some((
                    rule.priority()
                        .map_or(50, krs_ir_levels::SemanticRulePriority::value),
                    equation_view(rule)?,
                ))
            })
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let mut bands = BTreeMap::<u32, Vec<EquationView<'_>>>::new();
        for (priority, view) in views {
            bands.entry(priority).or_default().push(view);
        }
        functions.insert(production.id(), bands.into_values().collect());
    }
    functions
}

/// The view of an equation, or `None` when the analysis cannot read it: it
/// reads the configuration (a function context) or has a matching-logic
/// `requires`.
pub(crate) fn equation_view(rule: &SemanticRule) -> Option<EquationView<'_>> {
    if rule.function_context().is_some() {
        return None;
    }
    let body = rule.body()?;
    let SemanticTermKind::Application { arguments, .. } = body.from().kind() else {
        return None;
    };
    let guard = match rule.requires() {
        None => None,
        Some(IrCondition::Bool(condition)) => Some(condition.term()),
        Some(IrCondition::Predicate(_)) => return None,
    };
    Some(EquationView {
        id: rule.id(),
        arguments,
        guard,
        result: body.to(),
    })
}

/// Renders an argument vector as an application of `head`.
pub(crate) fn render_point(head: &str, domain: &Domain<'_>, point: &[i128]) -> String {
    let arguments = domain
        .columns()
        .iter()
        .zip(point)
        .map(|(column, value)| match column {
            ColumnValues::Int { .. } => value.to_string(),
            ColumnValues::Free => "_".to_owned(),
        })
        .collect::<Vec<_>>();
    format!("{head}({})", arguments.join(", "))
}

/// The first overlap of two equations at one priority whose results differ.
/// Equations at one priority that the analysis can enumerate (see the
/// module documentation) are decided on every argument; the others pair by
/// pair, by unification and the guard decision of the coverage lint
/// (`coverage::overlap`), which reports only an overlap it can exhibit.
/// Results that are identical once the argument is substituted agree, so
/// their overlap is no violation: the equations are confluent there.
pub(crate) fn first_equation_overlap(modules: &[SemanticModule]) -> Option<EquationOverlap> {
    let signature = EquationSignature::new(modules);
    let evaluator = signature.evaluator(modules);
    for (production, instance, rules) in function_equations(modules) {
        let columns = instantiate(
            &production_argument_sorts(production),
            production.parameters(),
            &instance,
        );
        let mut priorities = BTreeMap::<u32, Vec<&SemanticRule>>::new();
        for rule in rules {
            priorities
                .entry(
                    rule.priority()
                        .map_or(50, krs_ir_levels::SemanticRulePriority::value),
                )
                .or_default()
                .push(rule);
        }
        for (_, mut rules) in priorities {
            if rules.len() < 2 {
                continue;
            }
            rules.sort_by(|left, right| left.id().cmp(right.id()));
            let ground = rules
                .iter()
                .map(|rule| equation_view(rule))
                .collect::<Option<Vec<_>>>()
                .ok_or(Undecided)
                .and_then(|views| overlap_among(&evaluator, production, &columns, &views));
            let overlap = match ground {
                Ok(overlap) => overlap,
                Err(Undecided) => symbolic_overlap(&signature, &evaluator, production, &rules),
            };
            if overlap.is_some() {
                return overlap;
            }
        }
    }
    None
}

/// The first overlap among equations at one priority, sorted by identity,
/// or [`Undecided`] when the analysis cannot enumerate them.
fn overlap_among<'a>(
    evaluator: &'a Evaluator<'a>,
    production: &SemanticProduction,
    columns: &[Sort],
    views: &[EquationView<'a>],
) -> Result<Option<EquationOverlap>, Undecided> {
    let domain = Domain::new(evaluator, columns, views).ok_or(Undecided)?;
    for point in domain.points() {
        let mut applying = Vec::new();
        for index in 0..views.len() {
            match domain.applies(index, &point) {
                Ok(true) => applying.push(index),
                Ok(false) => {}
                Err(Undecided) => return Err(Undecided),
            }
        }
        for (position, &first) in applying.iter().enumerate() {
            for &second in &applying[position + 1..] {
                // A result the analysis does not compare cannot be told
                // apart from the other.
                let (Some(left), Some(right)) =
                    (domain.result(first, &point), domain.result(second, &point))
                else {
                    continue;
                };
                // Both equations hold here, evaluated exactly, so the
                // overlap is genuine whatever other points hold.
                if left.0 != right.0 {
                    return Ok(Some(EquationOverlap {
                        function: display_name(production.id()),
                        first: views[first].id.clone(),
                        second: views[second].id.clone(),
                        application: render_point(&display_name(production.id()), &domain, &point),
                        results: (left.1, right.1),
                    }));
                }
            }
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests;
