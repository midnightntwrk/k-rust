//! The overlap check of equations beyond the ground analysis
//! (`equation_domain`): two equations of one function at one priority, pair
//! by pair, by unification of their patterns over the definition's sorts and
//! the guard decision of the coverage lint.
//!
//! Equations `f(p̄) => r requires φ` and `f(q̄) => s requires ψ` both apply to
//! an argument that matches `p̄` and `q̄` and makes `φ` and `ψ` hold. Linear
//! patterns over constructors, literals and sorted binders unify
//! syntactically: a binder matches a constructor or a literal whose values
//! its sort contains, and another binder when the two sorts share a kind of
//! value. When they unify, `φ ∧ ψ` is decided over the guard abstraction
//! ([`decide_counted`]), whose atoms name subterms by their path from the
//! argument list, a frame both equations share, so `x` in one equation and
//! a literal or a binder at the same place in the other are one subject.
//! Validity of `¬φ ∨ ¬ψ` proves the pair disjoint; a refuting valuation is a
//! candidate overlap.
//!
//! A guard's `k::matches!` tests are read as the coverage lint reads them
//! ([`expand`]): each equation becomes one alternative per truth assignment
//! of its tests, with refined patterns and a residual guard, and the terms
//! the tests read that are not binders are virtual columns both equations
//! share. That reading over-approximates where an equation applies, so a
//! pair it proves disjoint is disjoint; it only ever proposes candidates.
//!
//! Only an exact overlap is reported: the candidate's Int values are made
//! concrete, both original guards evaluate to `true` on the concrete
//! argument (a `k::matches!` on a ground term is matching), and the two
//! results, with the argument substituted and builtins on literals
//! evaluated, differ. Anything less (an opaque pattern, a guard neither the
//! reader nor the evaluation can read, a candidate whose guards do not both
//! hold once concrete) reports nothing, as the ground analysis does when it
//! gives up.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{ApplicationRef, BuiltinSort, SemanticId};
use krs_ir_levels::{
    IrCondition, SemanticModule, SemanticProduction, SemanticRule, SemanticSortRef as Sort,
    SemanticTerm, SemanticTermKind,
};
use num_bigint::BigInt;

use super::{
    FUNCTION_VALUATION_BUDGET, Fact, Formula, GuardReader, Head, Path, Pattern, Projections,
    Signature, Test, Verdict, Virtual, argument_alternatives, decide_counted, display_name, expand,
    path_text, pattern_at, snake_case,
};
use crate::equation_domain::{
    Environment, EquationOverlap, Evaluator, Ground, evaluable_functions, ground_literal,
    guard_holds,
};

/// The distinct concrete arguments one pair may try before the check gives
/// up on it.
const CANDIDATE_LIMIT: usize = 64;

/// The sorts and constructors equations are unified over.
pub(crate) struct EquationSignature(Signature);

impl EquationSignature {
    pub(crate) fn new(modules: &[SemanticModule]) -> Self {
        Self(Signature::new(modules))
    }

    /// An evaluator of ground terms over this signature that applies the
    /// total functions of `modules` by their equations.
    pub(crate) fn evaluator<'a>(&'a self, modules: &'a [SemanticModule]) -> Evaluator<'a> {
        Evaluator::with_functions(&self.0, evaluable_functions(modules))
    }
}

/// One alternative of an equation's argument patterns, read for
/// unification.
struct Side<'a> {
    rule: &'a SemanticRule,
    patterns: Vec<Pattern>,
    /// Each binder's path from the argument list.
    paths: BTreeMap<SemanticId, Path>,
    guard: Option<&'a SemanticTerm>,
    /// The guard as the coverage lint reads it, `None` when it cannot.
    read: Option<Read>,
    result: &'a SemanticTerm,
}

/// A guard as the coverage lint reads it.
struct Read {
    formula: Formula,
    projections: Projections,
    tests: BTreeMap<String, Test>,
    virtuals: BTreeMap<String, Virtual>,
}

/// The alternatives of an equation, or `None` when the check cannot read
/// it: a function context, a matching-logic `requires`, too many
/// alternatives, or a binder that occurs twice.
fn sides<'a>(signature: &Signature, rule: &'a SemanticRule) -> Option<Vec<Side<'a>>> {
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
    let mut sides = Vec::new();
    for (patterns, bindings) in argument_alternatives(signature, arguments)? {
        let mut paths = BTreeMap::new();
        for (binder, path) in bindings {
            if paths.insert(binder, path).is_some() {
                return None;
            }
        }
        let read = match guard {
            None => Some(Read {
                formula: Formula::Constant(true),
                projections: Projections::new(),
                tests: BTreeMap::new(),
                virtuals: BTreeMap::new(),
            }),
            Some(term) => {
                let mut reader = GuardReader::new(signature, &paths, None);
                reader.guard(term).map(|formula| Read {
                    formula,
                    projections: reader.projections,
                    tests: reader.tests,
                    virtuals: reader.virtuals,
                })
            }
        };
        sides.push(Side {
            rule,
            patterns,
            paths,
            guard,
            read,
            result: body.to(),
        });
    }
    Some(sides)
}

/// Why two patterns have no unifier the check can use.
enum Stop {
    /// No term matches both.
    Disjoint,
    /// A pattern the check does not decompose.
    Unknown,
}

/// The most specific pattern matching what both patterns match; an Int
/// literal meeting a binder becomes a fact about its path.
#[expect(clippy::too_many_lines, reason = "One case per pair of pattern kinds.")]
fn unify(
    signature: &Signature,
    left: &Pattern,
    right: &Pattern,
    path: &mut Path,
    facts: &mut BTreeMap<String, Fact>,
) -> Result<Pattern, Stop> {
    let covers = |sort: &Sort, head: &Head| signature.binder_covers(sort, head);
    match (left, right) {
        (Pattern::Opaque, _) | (_, Pattern::Opaque) => Err(Stop::Unknown),
        (Pattern::Binder(first), Pattern::Binder(second)) => {
            if signature.is_subsort(first, second) {
                Ok(left.clone())
            } else if signature.is_subsort(second, first)
                || signature
                    .heads(first)
                    .iter()
                    .any(|head| covers(second, head))
            {
                Ok(right.clone())
            } else {
                Err(Stop::Disjoint)
            }
        }
        (Pattern::Binder(sort), constructor @ Pattern::Constructor { id, instance, .. })
        | (constructor @ Pattern::Constructor { id, instance, .. }, Pattern::Binder(sort)) => {
            let head = Head::Constructor {
                id: id.clone(),
                instance: instance.clone(),
            };
            if covers(sort, &head) {
                Ok(constructor.clone())
            } else {
                Err(Stop::Disjoint)
            }
        }
        (Pattern::Binder(binder), literal @ Pattern::Literal { sort, value })
        | (literal @ Pattern::Literal { sort, value }, Pattern::Binder(binder)) => {
            if !covers(binder, &Head::Family(sort.clone())) {
                return Err(Stop::Disjoint);
            }
            if matches!(sort, Sort::Builtin(BuiltinSort::Int))
                && let Ok(number) = value.parse::<BigInt>()
            {
                facts.insert(path_text(path), Fact::Equal(number));
            }
            Ok(literal.clone())
        }
        (
            Pattern::Constructor {
                id,
                instance,
                arguments,
            },
            Pattern::Constructor {
                id: other,
                instance: other_instance,
                arguments: other_arguments,
            },
        ) => {
            if id != other || instance != other_instance {
                return Err(Stop::Disjoint);
            }
            let mut unified = Vec::new();
            for (index, (first, second)) in arguments.iter().zip(other_arguments).enumerate() {
                path.push(index);
                let argument = unify(signature, first, second, path, facts);
                path.pop();
                unified.push(argument?);
            }
            Ok(Pattern::Constructor {
                id: id.clone(),
                instance: instance.clone(),
                arguments: unified,
            })
        }
        (
            Pattern::Literal { sort, value },
            Pattern::Literal {
                sort: other,
                value: other_value,
            },
        ) => {
            if sort == other && value == other_value {
                Ok(left.clone())
            } else {
                Err(Stop::Disjoint)
            }
        }
        (Pattern::Binder(binder), family @ Pattern::Family(sort))
        | (family @ Pattern::Family(sort), Pattern::Binder(binder)) => {
            if covers(binder, &Head::Family(sort.clone())) {
                Ok(family.clone())
            } else {
                Err(Stop::Disjoint)
            }
        }
        (Pattern::Family(first), Pattern::Family(second)) => {
            if first == second {
                Ok(left.clone())
            } else {
                Err(Stop::Disjoint)
            }
        }
        (Pattern::Family(family), literal @ Pattern::Literal { sort, value })
        | (literal @ Pattern::Literal { sort, value }, Pattern::Family(family)) => {
            if family != sort {
                return Err(Stop::Disjoint);
            }
            if matches!(sort, Sort::Builtin(BuiltinSort::Int))
                && let Ok(number) = value.parse::<BigInt>()
            {
                facts.insert(path_text(path), Fact::Equal(number));
            }
            Ok(literal.clone())
        }
        (Pattern::Constructor { .. }, Pattern::Literal { .. } | Pattern::Family(_))
        | (Pattern::Literal { .. } | Pattern::Family(_), Pattern::Constructor { .. }) => {
            Err(Stop::Disjoint)
        }
    }
}

/// The concrete argument of a unified pattern: a comparison key and a
/// rendering. A binder at an Int path with a value is that value; another
/// binder is any value, named by its path in the key and `_` in the text.
fn pattern_text(
    pattern: &Pattern,
    path: &mut Path,
    values: &BTreeMap<Path, i128>,
) -> (String, String) {
    match pattern {
        Pattern::Binder(_) | Pattern::Family(_) | Pattern::Opaque => match values.get(path) {
            Some(value) => (value.to_string(), value.to_string()),
            None => (path_text(path), "_".to_owned()),
        },
        Pattern::Literal { sort, value } => {
            let key = if matches!(sort, Sort::Builtin(BuiltinSort::Int | BuiltinSort::Bool)) {
                value.clone()
            } else {
                format!("{sort:?}:{value}")
            };
            (key, value.clone())
        }
        Pattern::Constructor {
            id,
            instance,
            arguments,
        } => {
            let mut keys = Vec::new();
            let mut texts = Vec::new();
            for (index, argument) in arguments.iter().enumerate() {
                path.push(index);
                let (key, text) = pattern_text(argument, path, values);
                path.pop();
                keys.push(key);
                texts.push(text);
            }
            let name = display_name(id);
            let text = if arguments.is_empty() {
                name
            } else {
                format!("{name}({})", texts.join(", "))
            };
            (format!("{id:?}{instance:?}({})", keys.join(", ")), text)
        }
    }
}

/// A result with the unified argument substituted for its binders and its
/// builtins on literals evaluated: a comparison key and a rendering, `None`
/// for a form the check does not compare.
fn substitute(
    evaluator: &Evaluator<'_>,
    term: &SemanticTerm,
    side: &Side<'_>,
    unified: &[Pattern],
    values: &BTreeMap<Path, i128>,
    environment: &Environment<'_>,
) -> Option<(String, String)> {
    if let Some(literal) = ground_literal(evaluator, term, environment) {
        return Some((literal.clone(), literal));
    }
    let list = |terms: &mut dyn Iterator<Item = &SemanticTerm>| {
        let mut keys = Vec::new();
        let mut texts = Vec::new();
        for term in terms {
            let (key, text) = substitute(evaluator, term, side, unified, values, environment)?;
            keys.push(key);
            texts.push(text);
        }
        Some((keys.join(", "), texts.join(", ")))
    };
    match term.kind() {
        SemanticTermKind::Variable { variable } => {
            let path = side.paths.get(variable)?;
            let pattern = pattern_at(unified, path)?;
            Some(pattern_text(pattern, &mut path.clone(), values))
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
            let (head_key, head_text) = match application {
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
                head_text
            } else {
                format!("{head_text}({texts})")
            };
            Some((format!("{head_key}({keys})"), text))
        }
        SemanticTermKind::KSequence { items, .. } => {
            let (keys, texts) = list(&mut items.iter())?;
            Some((format!("seq({keys})"), format!("k::k![{texts}]")))
        }
        SemanticTermKind::Map(operands) => {
            let operation = format!("{:?}", operands.operation());
            let (keys, texts) = list(&mut operands.operands())?;
            Some((
                format!("map:{operation}({keys})"),
                format!("map::{}({texts})", snake_case(&operation)),
            ))
        }
        SemanticTermKind::List(operands) => {
            let operation = format!("{:?}", operands.operation());
            let (keys, texts) = list(&mut operands.operands())?;
            Some((
                format!("list:{operation}({keys})"),
                format!("list::{}({texts})", snake_case(&operation)),
            ))
        }
        SemanticTermKind::Set(operands) => {
            let operation = format!("{:?}", operands.operation());
            let (keys, texts) = list(&mut operands.operands())?;
            Some((
                format!("set:{operation}({keys})"),
                format!("set::{}({texts})", snake_case(&operation)),
            ))
        }
        _ => None,
    }
}

/// The Int values a candidate fixes: each Int literal of the unified
/// argument, and each Int binder at the candidate's value of its path, else
/// 0 (the guards then confirm or reject the choice).
fn int_values(
    patterns: &[Pattern],
    candidate: &BTreeMap<String, BigInt>,
) -> Option<BTreeMap<Path, i128>> {
    fn walk(
        pattern: &Pattern,
        path: &mut Path,
        candidate: &BTreeMap<String, BigInt>,
        values: &mut BTreeMap<Path, i128>,
    ) -> Option<()> {
        match pattern {
            Pattern::Binder(Sort::Builtin(BuiltinSort::Int))
            | Pattern::Family(Sort::Builtin(BuiltinSort::Int)) => {
                let value = candidate
                    .get(&path_text(path))
                    .map_or(Some(0), |value| i128::try_from(value).ok())?;
                values.insert(path.clone(), value);
            }
            Pattern::Literal {
                sort: Sort::Builtin(BuiltinSort::Int),
                value,
            } => {
                values.insert(path.clone(), value.parse().ok()?);
            }
            Pattern::Constructor { arguments, .. } => {
                for (index, argument) in arguments.iter().enumerate() {
                    path.push(index);
                    walk(argument, path, candidate, values)?;
                    path.pop();
                }
            }
            _ => {}
        }
        Some(())
    }
    let mut values = BTreeMap::new();
    for (index, pattern) in patterns.iter().enumerate() {
        walk(pattern, &mut vec![index], candidate, &mut values)?;
    }
    Some(values)
}

/// The value of a unified pattern once its Int binders have values: `None`
/// while some part of it is a binder of another sort.
fn ground(pattern: &Pattern, path: &mut Path, values: &BTreeMap<Path, i128>) -> Option<Ground> {
    match pattern {
        Pattern::Binder(Sort::Builtin(BuiltinSort::Int))
        | Pattern::Family(Sort::Builtin(BuiltinSort::Int)) => {
            values.get(path).copied().map(Ground::Int)
        }
        Pattern::Literal { sort, value } => match sort {
            Sort::Builtin(BuiltinSort::Int) => value.parse().ok().map(Ground::Int),
            Sort::Builtin(BuiltinSort::Bool) => Some(Ground::Bool(value == "true")),
            _ => None,
        },
        Pattern::Constructor {
            id,
            instance,
            arguments,
        } => {
            let mut grounds = Vec::new();
            for (index, argument) in arguments.iter().enumerate() {
                path.push(index);
                let value = ground(argument, path, values);
                path.pop();
                grounds.push(value?);
            }
            Some(Ground::Term {
                id: id.clone(),
                instance: instance.clone(),
                arguments: grounds,
            })
        }
        Pattern::Binder(_) | Pattern::Family(_) | Pattern::Opaque => None,
    }
}

/// The values of a side's binders whose unified subpattern is ground.
fn environment<'s>(
    side: &'s Side<'_>,
    unified: &[Pattern],
    values: &BTreeMap<Path, i128>,
) -> Environment<'s> {
    side.paths
        .iter()
        .filter_map(|(binder, path)| {
            let value = ground(pattern_at(unified, path)?, &mut path.clone(), values)?;
            Some((binder, value))
        })
        .collect()
}

/// A side's alternatives with the virtual columns `layout` lays out after
/// the arguments: its `k::matches!` tests expanded ([`expand`]), each with
/// its residual guard; `None` when its guard cannot be read.
fn expanded(
    signature: &Signature,
    side: &Side<'_>,
    layout: &BTreeMap<String, (Path, Sort)>,
) -> Option<Vec<(Vec<Pattern>, Formula)>> {
    let read = side.read.as_ref()?;
    let mut patterns = side.patterns.clone();
    patterns.extend(
        layout
            .values()
            .map(|(_, sort)| Pattern::Binder(sort.clone())),
    );
    let paths = layout
        .iter()
        .map(|(key, (path, _))| (key.clone(), path.clone()))
        .collect();
    Some(
        expand(signature, &patterns, &read.formula, &read.tests, &paths)
            .unwrap_or_else(|| vec![(patterns, read.formula.clone())]),
    )
}

/// The overlap of one pair of alternatives: an argument both apply to with
/// different results, or `None` when there is none or the check cannot
/// tell. `valuations` counts the guard valuations the function's pairs have
/// considered.
fn pair(
    signature: &Signature,
    evaluator: &Evaluator<'_>,
    production: &SemanticProduction,
    first: &Side<'_>,
    second: &Side<'_>,
    valuations: &mut u64,
) -> Option<EquationOverlap> {
    if first.patterns.len() != second.patterns.len() {
        return None;
    }
    let arity = first.patterns.len();
    let mut unified = Vec::new();
    for (index, (left, right)) in first.patterns.iter().zip(&second.patterns).enumerate() {
        match unify(
            signature,
            left,
            right,
            &mut vec![index],
            &mut BTreeMap::new(),
        ) {
            Ok(pattern) => unified.push(pattern),
            Err(Stop::Disjoint | Stop::Unknown) => return None,
        }
    }
    // Results equal with every binder left symbolic agree wherever both
    // equations apply.
    let symbolic = Environment::new();
    if let (Some(left), Some(right)) = (
        substitute(
            evaluator,
            first.result,
            first,
            &unified,
            &BTreeMap::new(),
            &symbolic,
        ),
        substitute(
            evaluator,
            second.result,
            second,
            &unified,
            &BTreeMap::new(),
            &symbolic,
        ),
    ) && left.0 == right.0
    {
        return None;
    }
    // The virtual columns of both sides, in one frame.
    let mut layout = BTreeMap::<String, (Path, Sort)>::new();
    for side in [first, second] {
        for (key, column) in side
            .read
            .as_ref()
            .map(|read| &read.virtuals)
            .into_iter()
            .flatten()
        {
            layout
                .entry(key.clone())
                .or_insert((Vec::new(), column.sort.clone()));
        }
    }
    for (index, (path, _)) in layout.values_mut().enumerate() {
        *path = vec![arity + index];
    }
    let (Some(lefts), Some(rights)) = (
        expanded(signature, first, &layout),
        expanded(signature, second, &layout),
    ) else {
        return None;
    };
    let mut projections = Projections::new();
    for side in [first, second] {
        if let Some(read) = &side.read {
            projections.extend(read.projections.clone());
        }
    }
    for (left_patterns, left_guard) in &lefts {
        for (right_patterns, right_guard) in &rights {
            if *valuations > FUNCTION_VALUATION_BUDGET {
                return None;
            }
            let mut facts = BTreeMap::new();
            let mut unified = Vec::new();
            for (index, (left, right)) in left_patterns.iter().zip(right_patterns).enumerate() {
                match unify(signature, left, right, &mut vec![index], &mut facts) {
                    Ok(pattern) => unified.push(pattern),
                    Err(Stop::Disjoint | Stop::Unknown) => break,
                }
            }
            if unified.len() != left_patterns.len() {
                continue;
            }
            let overlap = candidate(
                evaluator,
                production,
                (first, second),
                &unified[..arity],
                [left_guard, right_guard],
                &facts,
                &projections,
                valuations,
            );
            if overlap.is_some() {
                return overlap;
            }
        }
    }
    None
}

/// The overlap of two unified alternatives, confirmed exactly: a valuation
/// under which both residual guards may hold, made concrete, on which both
/// original guards hold and the results differ. The abstraction treats a
/// function's application as free, so a valuation may have no argument
/// (`TwoSign(v)` is 1 where `v` is -5): the search moves on to the next
/// valuation, up to [`CANDIDATE_LIMIT`] distinct arguments.
#[expect(
    clippy::too_many_arguments,
    reason = "One candidate: the two sides, their unified argument, guards, facts, and the budget."
)]
fn candidate(
    evaluator: &Evaluator<'_>,
    production: &SemanticProduction,
    (first, second): (&Side<'_>, &Side<'_>),
    unified: &[Pattern],
    guards: [&Formula; 2],
    facts: &BTreeMap<String, Fact>,
    projections: &Projections,
    valuations: &mut u64,
) -> Option<EquationOverlap> {
    let negations = guards.map(|guard| guard.clone().not());
    let negations = negations.iter().collect::<Vec<_>>();
    let mut start = 0;
    let mut tried = BTreeSet::new();
    loop {
        if *valuations > FUNCTION_VALUATION_BUDGET || tried.len() >= CANDIDATE_LIMIT {
            return None;
        }
        let (verdict, next) = decide_counted(&negations, facts, projections, false, start);
        *valuations = valuations.saturating_add(next.saturating_sub(start));
        let Verdict::Refuted(candidate) = verdict else {
            return None;
        };
        start = next;
        let values = int_values(unified, &candidate.values)?;
        if !tried.insert(values.clone()) {
            continue;
        }
        if let Confirmed::Overlap(overlap) =
            confirm(evaluator, production, (first, second), unified, &values)?
        {
            return Some(*overlap);
        }
    }
}

/// What a concrete argument shows about a pair.
enum Confirmed {
    /// Both original guards evaluate to `true` and the results differ.
    Overlap(Box<EquationOverlap>),
    /// A guard is false there, or the results agree.
    Rejected,
}

/// [`Confirmed`] at a concrete argument; `None` when the evaluation cannot
/// tell, which ends the search for the pair (another argument would meet
/// the same term).
fn confirm(
    evaluator: &Evaluator<'_>,
    production: &SemanticProduction,
    (first, second): (&Side<'_>, &Side<'_>),
    unified: &[Pattern],
    values: &BTreeMap<Path, i128>,
) -> Option<Confirmed> {
    let (first_environment, second_environment) = (
        environment(first, unified, values),
        environment(second, unified, values),
    );
    let holds = |side: &Side<'_>, environment: &Environment<'_>| match side.guard {
        None => Some(true),
        Some(guard) => guard_holds(evaluator, guard, environment),
    };
    if !holds(first, &first_environment)? || !holds(second, &second_environment)? {
        return Some(Confirmed::Rejected);
    }
    let (left, right) = (
        substitute(
            evaluator,
            first.result,
            first,
            unified,
            values,
            &first_environment,
        )?,
        substitute(
            evaluator,
            second.result,
            second,
            unified,
            values,
            &second_environment,
        )?,
    );
    if left.0 == right.0 {
        return Some(Confirmed::Rejected);
    }
    let function = display_name(production.id());
    let arguments = unified
        .iter()
        .enumerate()
        .map(|(index, pattern)| pattern_text(pattern, &mut vec![index], values).1)
        .collect::<Vec<_>>();
    Some(Confirmed::Overlap(Box::new(EquationOverlap {
        application: format!("{function}({})", arguments.join(", ")),
        function,
        first: first.rule.id().clone(),
        second: second.rule.id().clone(),
        results: (left.1, right.1),
    })))
}

/// The first exact overlap among equations at one priority, sorted by
/// identity, pair by pair (see the module documentation).
pub(crate) fn symbolic_overlap(
    signature: &EquationSignature,
    evaluator: &Evaluator<'_>,
    production: &SemanticProduction,
    rules: &[&SemanticRule],
) -> Option<EquationOverlap> {
    let signature = &signature.0;
    let alternatives = rules
        .iter()
        .map(|rule| sides(signature, rule))
        .collect::<Vec<_>>();
    let mut valuations = 0_u64;
    for (index, first) in alternatives.iter().enumerate() {
        let Some(first) = first else { continue };
        for second in alternatives[index + 1..].iter().flatten() {
            for left in first {
                for right in second {
                    if valuations > FUNCTION_VALUATION_BUDGET {
                        return None;
                    }
                    let overlap = pair(
                        signature,
                        evaluator,
                        production,
                        left,
                        right,
                        &mut valuations,
                    );
                    if overlap.is_some() {
                        return overlap;
                    }
                }
            }
        }
    }
    None
}
