//! V3: the check enumerates every overlap. Semantic, over the oracle's own `->E`: for each
//! equation `rho1`, each valuation `theta` of its left-hand side's variables by normal forms,
//! and each application position `q` of the left-hand side (the root included), when
//! `l1|q theta` is an innermost redex (its arguments are normal forms) at which `rho2` applies
//! in the oracle's `->E` (and, at the root, `rho1` applies too, `rho2` another equation), the
//! check must have unified `(rho1, q, rho2)` (either order at the root) with a unifier that
//! generalizes `theta`, or have answered an unresolved shape. Positions are positions of `l1`,
//! fixed by construction, so no instance can hide a position.

use std::collections::{BTreeMap, HashMap};

use k_rust_kore::kore::parser::parse_definition;

use super::{
    Rng,
    checks::{candidates_of, sort_name, values, without_aliases},
    engine::{Id, Node, Universe},
    language::{Definition, Pat, equation_index, pattern_variables},
};
use crate::{
    confluence::{RecordedOverlap, recording_overlaps},
    definition::BackendDefinition,
    term::{Term, TermKind},
};

/// Valuations tried per equation.
const VALUATIONS: usize = 24;

#[derive(Debug, Default)]
pub(super) struct Completeness {
    pub(super) definitions: usize,
    /// Redexes found, each requiring a recorded overlap.
    pub(super) redexes: usize,
    /// Of those, covered by an unresolved shape.
    pub(super) unresolved: usize,
    pub(super) failures: Vec<String>,
}

impl Completeness {
    pub(super) fn add(&mut self, other: Self) {
        self.definitions += other.definitions;
        self.redexes += other.redexes;
        self.unresolved += other.unresolved;
        self.failures.extend(other.failures);
    }
}

/// The oracle pattern of a backend term: applications, injections, `Int` literals, variables
/// (with their sorts) and lists; `None` for anything else.
pub(super) fn pattern_of(term: &Term) -> Option<Pat> {
    match term.kind() {
        TermKind::Variable(variable) => Some(Pat::Var(
            variable.name.to_string(),
            sort_name(&variable.sort)?,
        )),
        TermKind::DomainValue { sort, value } => {
            if sort_name(sort)? != "Int" {
                return None;
            }
            let text = std::str::from_utf8(value.as_bytes()).ok()?;
            Some(Pat::Int(text.parse().ok()?))
        }
        TermKind::Injection {
            source,
            target,
            term,
        } => Some(Pat::Inj(
            sort_name(source)?,
            sort_name(target)?,
            Box::new(pattern_of(term)?),
        )),
        TermKind::Application {
            symbol, arguments, ..
        } => {
            let arguments = arguments
                .iter()
                .map(pattern_of)
                .collect::<Option<Vec<_>>>()?;
            match symbol.name.as_ref() {
                "listUnit" => Some(Pat::List(Vec::new(), None, Vec::new())),
                "listItem" => Some(Pat::List(arguments, None, Vec::new())),
                _ => Some(Pat::App(symbol.name.to_string(), arguments)),
            }
        }
        TermKind::List { heads, rest, .. } => {
            let prefix = heads.iter().map(pattern_of).collect::<Option<Vec<_>>>()?;
            match rest {
                None => Some(Pat::List(prefix, None, Vec::new())),
                Some((middle, tail)) => {
                    let TermKind::Variable(variable) = middle.kind() else {
                        return None;
                    };
                    let suffix = tail.iter().map(pattern_of).collect::<Option<Vec<_>>>()?;
                    Some(Pat::List(prefix, Some(variable.name.to_string()), suffix))
                }
            }
        }
        TermKind::And(..) | TermKind::Map { .. } | TermKind::Set { .. } => None,
    }
}

/// The application positions of `pattern` (the root first), as argument paths: argument indexes
/// through applications and lists, 0 into an injection, and the conjuncts of an alias
/// `\and(p, X)` as 0 and 1; with the subpattern there.
fn application_positions(pattern: &Pat) -> Vec<(Vec<usize>, Pat)> {
    let mut positions = Vec::new();
    let mut stack = vec![(Vec::new(), pattern.clone())];
    while let Some((path, pattern)) = stack.pop() {
        let children: Vec<Pat> = match &pattern {
            Pat::App(_, arguments) => {
                positions.push((path.clone(), pattern.clone()));
                arguments.clone()
            }
            Pat::Inj(_, _, inner) => vec![(**inner).clone()],
            Pat::As(inner, name, sort) => {
                vec![(**inner).clone(), Pat::Var(name.clone(), sort.clone())]
            }
            Pat::List(prefix, rest, suffix) => {
                let mut children = prefix.clone();
                if let Some(rest) = rest {
                    children.push(Pat::Var(rest.clone(), "List".into()));
                }
                children.extend(suffix.iter().cloned());
                children
            }
            Pat::Var(..) | Pat::Int(_) => Vec::new(),
        };
        for (index, child) in children.into_iter().enumerate().rev() {
            let mut child_path = path.clone();
            child_path.push(index);
            stack.push((child_path, child));
        }
    }
    positions
}

/// Adds to `valuation` the values of the alias variables of `pattern`: each is the instance of
/// the subpattern it names. `false` when an alias variable also occurs in the subpattern with
/// another value: the left-hand side has no instance there.
fn with_aliases(
    universe: &mut Universe<'_>,
    pattern: &Pat,
    valuation: &mut HashMap<String, Id>,
) -> bool {
    match pattern {
        Pat::As(inner, name, _) => {
            if !with_aliases(universe, inner, valuation) {
                return false;
            }
            let value = universe.instantiate(&without_aliases(inner), valuation);
            match valuation.insert(name.clone(), value) {
                Some(previous) => previous == value,
                None => true,
            }
        }
        Pat::App(_, arguments) => arguments
            .iter()
            .all(|argument| with_aliases(universe, argument, valuation)),
        Pat::Inj(_, _, inner) => with_aliases(universe, inner, valuation),
        Pat::List(..) | Pat::Var(..) | Pat::Int(_) => true,
    }
}

/// Whether some unifier generalizes `valuation` on the variables of `record.first`'s left-hand
/// side: one instantiation of the unifier's free variables gives each variable its value.
/// `None` when a binding is not in the oracle's language.
fn generalizes(
    universe: &mut Universe<'_>,
    record: &RecordedOverlap,
    unifiers: &[crate::substitution::Substitution],
    valuation: &HashMap<String, Id>,
) -> Option<bool> {
    let variables = record.first.lhs.attributes().variables.clone();
    let mut decidable = true;
    for unifier in unifiers {
        let mut shared = HashMap::new();
        let mut all = true;
        for variable in &variables {
            let Some(value) = valuation.get(variable.name.as_ref()) else {
                decidable = false;
                all = false;
                break;
            };
            let bound = unifier
                .get(variable)
                .cloned()
                .unwrap_or_else(|| Term::variable(variable.clone()));
            let Some(pattern) = pattern_of(&bound) else {
                decidable = false;
                all = false;
                break;
            };
            if !universe.matches(&pattern, *value, &mut shared) {
                all = false;
                break;
            }
        }
        if all {
            return Some(true);
        }
    }
    decidable.then_some(false)
}

/// V3 on one definition.
pub(super) fn check_completeness(
    label: &str,
    definition: &Definition,
    rng: &mut Rng,
) -> Completeness {
    let mut result = Completeness {
        definitions: 1,
        ..Completeness::default()
    };
    if !definition.symbols.iter().any(|symbol| symbol.is_head()) {
        // The check stops after the precondition rows: no pair is enumerated.
        return result;
    }
    let source = definition.kore();
    let Ok(syntax) = parse_definition(&source) else {
        result.failures.push(format!("{label}: does not parse"));
        return result;
    };
    let (backend, recorded) =
        recording_overlaps(|| BackendDefinition::internalize(&syntax, "MAIN"));
    if let Err(error) = backend {
        result
            .failures
            .push(format!("{label}: does not internalize: {error:?}"));
        return result;
    }
    let mut by_pair = BTreeMap::<(usize, Vec<usize>, usize), Vec<&RecordedOverlap>>::new();
    for record in &recorded {
        let (Some(first), Some(second)) = (
            equation_index(record.first.attributes.label.as_deref()),
            equation_index(record.second.attributes.label.as_deref()),
        ) else {
            continue;
        };
        by_pair
            .entry((first, record.position.clone(), second))
            .or_default()
            .push(record);
    }
    let describe = || super::checks::describe(definition);
    let mut universe = Universe::new(definition);
    let values = values(&mut universe, rng);
    for (first, equation) in definition.equations.iter().enumerate() {
        let mut variables = BTreeMap::new();
        pattern_variables(&without_aliases(&equation.lhs), &mut variables);
        let positions = application_positions(&equation.lhs);
        for _ in 0..VALUATIONS {
            let mut valuation = HashMap::new();
            let mut complete = true;
            for (name, sort) in &variables {
                let sort = universe.sort_id(sort);
                let candidates = candidates_of(&mut universe, &values, sort);
                if candidates.is_empty() {
                    complete = false;
                    break;
                }
                valuation.insert(name.clone(), *rng.pick(&candidates));
            }
            if !complete {
                break;
            }
            if !with_aliases(&mut universe, &equation.lhs, &mut valuation) {
                continue;
            }
            for (position, subpattern) in &positions {
                let redex = universe.instantiate(&without_aliases(subpattern), &valuation);
                let Node::App(_, arguments) = universe.node_of(redex).clone() else {
                    continue;
                };
                if !arguments
                    .iter()
                    .all(|argument| universe.is_normal_form(*argument))
                {
                    continue;
                }
                let (applying, ended) = universe.applicable(redex);
                if !ended {
                    continue;
                }
                let root = position.is_empty();
                if root && !applying.iter().any(|(index, _)| *index == first) {
                    continue;
                }
                for (second, second_valuation) in &applying {
                    if root && *second == first {
                        continue;
                    }
                    result.redexes += 1;
                    let mut candidates = Vec::new();
                    if let Some(records) = by_pair.get(&(first, position.clone(), *second)) {
                        candidates.extend(records.iter().map(|record| (*record, &valuation)));
                    }
                    if root && let Some(records) = by_pair.get(&(*second, Vec::new(), first)) {
                        candidates.extend(records.iter().map(|record| (*record, second_valuation)));
                    }
                    let shown = universe.show(redex);
                    if candidates.is_empty() {
                        result.failures.push(format!(
                            "{label}: eq{second} applies at {shown}, position {position:?} of eq{first}, and the pair was not unified\n  definition:\n{}",
                            describe()
                        ));
                        continue;
                    }
                    let mut covered = false;
                    let mut unresolved = false;
                    let mut undecidable = false;
                    for (record, theta) in candidates {
                        match &record.unifiers {
                            Err(_) => unresolved = true,
                            Ok(unifiers) => {
                                match generalizes(&mut universe, record, unifiers, theta) {
                                    Some(true) => covered = true,
                                    Some(false) => {}
                                    None => undecidable = true,
                                }
                            }
                        }
                    }
                    if unresolved && !covered {
                        result.unresolved += 1;
                    } else if !covered && !undecidable {
                        result.failures.push(format!(
                            "{label}: eq{second} applies at {shown}, position {position:?} of eq{first}, and no unifier of the pair generalizes the valuation\n  definition:\n{}",
                            describe()
                        ));
                    }
                }
            }
        }
    }
    result
}

/// V3 over the templates, the probes and `cases` random definitions.
pub(super) fn run_completeness(cases: u64, seed: u64) -> Completeness {
    let mut total = Completeness::default();
    for (name, definition, _) in super::generator::templates() {
        let mut rng = Rng(seed);
        total.add(check_completeness(&name, &definition, &mut rng));
    }
    for probe in super::probes::probes() {
        let mut rng = Rng(seed);
        total.add(check_completeness(&probe.name, &probe.definition, &mut rng));
    }
    for case in 0..cases * 4 {
        let mut rng = Rng(seed ^ 0x5151 ^ case.wrapping_mul(0x9e37_79b9_7f4a_7c15));
        let (definition, _) = super::generator::random_definition(&mut rng);
        total.add(check_completeness(
            &format!("completeness case {case} (seed {seed:#x})"),
            &definition,
            &mut rng,
        ));
        if total.failures.len() >= 20 {
            break;
        }
    }
    total
}

#[test]
fn every_overlap_of_random_equations_is_enumerated() {
    super::on_large_stack(|| {
        let cases = super::environment("KRUST_DEFINEDNESS_ORACLE_CASES", super::DEFAULT_CASES);
        let seed = super::environment("KRUST_DEFINEDNESS_ORACLE_SEED", super::DEFAULT_SEED);
        let total = run_completeness(cases, seed);
        eprintln!(
            "overlap enumeration (seed {seed:#x}): {} definitions, {} redexes, {} covered by an unresolved shape, {} failures",
            total.definitions,
            total.redexes,
            total.unresolved,
            total.failures.len()
        );
        assert!(total.redexes > 0, "no redex found");
        assert!(total.failures.is_empty(), "{}", total.failures.join("\n"));
    });
}
