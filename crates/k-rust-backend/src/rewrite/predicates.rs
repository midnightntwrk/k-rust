//! Predicate vocabulary shared by the rewriting, search, and proof layers (row B21, a
//! responsibility, not an algorithm): three-valued predicate truth, alpha equivalence of
//! quantified conditions, unique extension with an `FxHashMap` position index, substitution
//! into predicates, constructor-domain coverage (the finite no-junk check), and the
//! concreteness check of rule attributes. O(|predicates|) per call; no counter, no worklist
//! beyond the binder peel.

use std::{
    collections::{BTreeMap, BTreeSet},
    hash::{Hash, Hasher},
};

use k_rust_kore::names::BuiltinSort;
use rustc_hash::{FxHashMap, FxHasher};

use crate::{
    definition::{BackendDefinition, ConstructorHead, constructor_head},
    rule::{Concreteness, ConstraintKind, Predicate, RewriteRule},
    substitution::{Substitution, substitute},
    term::{
        Sort, Term, TermKind, Variable,
        names::{VariableProvenance, split_marker},
    },
};

use super::{Pattern, Truth, is_functional_pattern};

fn conjoin(mut predicates: Vec<Predicate>) -> Predicate {
    match predicates.len() {
        0 => Predicate::True,
        1 => predicates.pop().unwrap(),
        _ => Predicate::And(predicates),
    }
}

pub(crate) fn quantify_introduced_variables(
    pattern: &Pattern,
    predicates: Vec<Predicate>,
) -> Predicate {
    let mut condition = conjoin(predicates);
    let state_variables = pattern_free_variables(pattern);
    let introduced = condition
        .free_variables()
        .difference(&state_variables)
        .cloned()
        .collect::<Vec<_>>();
    for variable in introduced.into_iter().rev() {
        condition = Predicate::Exists(variable, Box::new(condition));
    }
    condition
}

pub(crate) fn conjunctively_contains_alpha_equivalent(
    predicates: &[Predicate],
    target: &Predicate,
) -> bool {
    predicates.iter().any(|predicate| {
        alpha_equivalent(predicate, target)
            || matches!(predicate, Predicate::And(inner) if conjunctively_contains_alpha_equivalent(inner, target))
    })
}

fn alpha_equivalent(left: &Predicate, right: &Predicate) -> bool {
    let mut left_index = 0;
    let mut right_index = 0;
    alpha_normalize(left, &mut left_index) == alpha_normalize(right, &mut right_index)
}

fn alpha_normalize(predicate: &Predicate, next: &mut usize) -> Predicate {
    match predicate {
        Predicate::Exists(variable, inner) | Predicate::Forall(variable, inner) => {
            // NUL cannot occur in parsed KORE identifiers, so these canonical names cannot capture
            // a free source variable.
            let normalized = variable.with_name(format!("\0bound{next}"));
            *next += 1;
            let substitution = [(variable.clone(), Term::variable(normalized.clone()))]
                .into_iter()
                .collect();
            let inner = substitute_predicate(inner, &substitution);
            let inner = Box::new(alpha_normalize(&inner, next));
            if matches!(predicate, Predicate::Exists(..)) {
                Predicate::Exists(normalized, inner)
            } else {
                Predicate::Forall(normalized, inner)
            }
        }
        Predicate::Not(inner) => Predicate::Not(Box::new(alpha_normalize(inner, next))),
        Predicate::And(predicates) => Predicate::And(
            predicates
                .iter()
                .map(|predicate| alpha_normalize(predicate, next))
                .collect(),
        ),
        Predicate::Or(predicates) => Predicate::Or(
            predicates
                .iter()
                .map(|predicate| alpha_normalize(predicate, next))
                .collect(),
        ),
        Predicate::Implies(left, right) => Predicate::Implies(
            Box::new(alpha_normalize(left, next)),
            Box::new(alpha_normalize(right, next)),
        ),
        Predicate::Iff(left, right) => Predicate::Iff(
            Box::new(alpha_normalize(left, next)),
            Box::new(alpha_normalize(right, next)),
        ),
        predicate => predicate.clone(),
    }
}

pub(super) fn extend_unique(
    predicates: &mut Vec<Predicate>,
    added: impl IntoIterator<Item = Predicate>,
) {
    let hash = |predicate: &Predicate| {
        let mut hasher = FxHasher::default();
        predicate.hash(&mut hasher);
        hasher.finish()
    };
    let mut positions = FxHashMap::<u64, Vec<usize>>::default();
    for (position, predicate) in predicates.iter().enumerate() {
        positions.entry(hash(predicate)).or_default().push(position);
    }
    for predicate in added {
        let predicate_hash = hash(&predicate);
        let duplicate = positions.get(&predicate_hash).is_some_and(|candidates| {
            candidates
                .iter()
                .any(|&index| predicates[index] == predicate)
        });
        if !duplicate {
            let position = predicates.len();
            predicates.push(predicate);
            positions.entry(predicate_hash).or_default().push(position);
        }
    }
}

/// Checks the equation-only `concrete` and `symbolic` application attributes.
/// Rewrite rules never call this: Booster and Kore consult these attributes only for equations.
pub(crate) fn check_concreteness(
    rule: &RewriteRule,
    substitution: &Substitution,
) -> Option<Variable> {
    let constrained = match &rule.attributes.concreteness {
        Concreteness::Unconstrained => return None,
        Concreteness::All(kind) => rule
            .lhs
            .attributes()
            .variables
            .iter()
            .cloned()
            .map(|variable| (variable, *kind))
            .collect::<Vec<_>>(),
        Concreteness::Some(constrained) => constrained
            .iter()
            .filter_map(|((name, sort), kind)| {
                rule.lhs
                    .attributes()
                    .variables
                    .iter()
                    .find(|variable| {
                        matches!(
                            split_marker(
                                &variable.name,
                                &[VariableProvenance::Rule, VariableProvenance::Equation],
                            ),
                            (Some(_), rest) if rest == name.as_ref()
                        ) && sort_name(&variable.sort) == Some(sort.as_ref())
                    })
                    .cloned()
                    .map(|variable| (variable, *kind))
            })
            .collect(),
    };
    constrained.into_iter().find_map(|(variable, kind)| {
        let Some(term) = substitution.get(&variable) else {
            return Some(variable);
        };
        let concrete = term.attributes().constructor_like;
        let satisfied = match kind {
            ConstraintKind::Concrete => concrete,
            ConstraintKind::Symbolic => !concrete,
        };
        (!satisfied).then_some(variable)
    })
}

fn sort_name(sort: &Sort) -> Option<&str> {
    match sort {
        Sort::Application { name, .. } => Some(name.as_ref()),
        Sort::Variable(_) => None,
    }
}

pub(super) fn pattern_variable_names(pattern: &Pattern) -> BTreeSet<crate::term::Name> {
    pattern_free_variables(pattern)
        .into_iter()
        .map(|variable| variable.name)
        .collect()
}

fn pattern_free_variables(pattern: &Pattern) -> BTreeSet<Variable> {
    pattern
        .term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain(
            pattern
                .constraints
                .iter()
                .flat_map(Predicate::free_variables),
        )
        .collect()
}

/// Apply a saturated substitution throughout a predicate collection.
pub fn substitute_predicates(
    predicates: &[Predicate],
    substitution: &Substitution,
) -> Vec<Predicate> {
    predicates
        .iter()
        .map(|predicate| substitute_predicate(predicate, substitution))
        .collect()
}

fn substitute_predicate(predicate: &Predicate, substitution: &Substitution) -> Predicate {
    match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Term(term) => Predicate::Term(substitute(term, substitution)),
        Predicate::Equals(left, right) => Predicate::Equals(
            substitute(left, substitution),
            substitute(right, substitution),
        ),
        Predicate::Ceil(term) => Predicate::Ceil(substitute(term, substitution)),
        Predicate::Floor(term) => Predicate::Floor(substitute(term, substitution)),
        Predicate::In(left, right) => Predicate::In(
            substitute(left, substitution),
            substitute(right, substitution),
        ),
        Predicate::Not(inner) => {
            Predicate::Not(Box::new(substitute_predicate(inner, substitution)))
        }
        Predicate::And(inner) => Predicate::And(substitute_predicates(inner, substitution)),
        Predicate::Or(inner) => Predicate::Or(substitute_predicates(inner, substitution)),
        Predicate::Implies(left, right) => Predicate::Implies(
            Box::new(substitute_predicate(left, substitution)),
            Box::new(substitute_predicate(right, substitution)),
        ),
        Predicate::Iff(left, right) => Predicate::Iff(
            Box::new(substitute_predicate(left, substitution)),
            Box::new(substitute_predicate(right, substitution)),
        ),
        Predicate::Exists(variable, inner) => Predicate::Exists(
            variable.clone(),
            Box::new(substitute_predicate(
                inner,
                &without_variable(substitution, variable),
            )),
        ),
        Predicate::Forall(variable, inner) => Predicate::Forall(
            variable.clone(),
            Box::new(substitute_predicate(
                inner,
                &without_variable(substitution, variable),
            )),
        ),
    }
}

fn without_variable(substitution: &Substitution, variable: &Variable) -> Substitution {
    let mut substitution = substitution.clone();
    substitution.remove(variable);
    substitution
}

pub(crate) fn predicates_truth(predicates: &[Predicate]) -> Truth {
    predicates.iter().fold(Truth::True, |result, predicate| {
        and_truth(result, predicate_truth(predicate))
    })
}

/// Detect a constructor exclusion that contradicts an internalized finite no-junk axiom.
pub(crate) fn violates_finite_constructor_domain(
    definition: &BackendDefinition,
    predicates: &[Predicate],
) -> bool {
    let mut exclusions = BTreeMap::<Term, BTreeSet<ConstructorHead>>::new();
    for predicate in predicates {
        collect_constructor_exclusions(definition, predicate, &mut exclusions);
    }
    exclusions.into_iter().any(|(subject, excluded)| {
        definition
            .finite_constructor_heads(&subject.sort())
            .is_some_and(|constructors| constructors.is_subset(&excluded))
    })
}

fn collect_constructor_exclusions(
    definition: &BackendDefinition,
    predicate: &Predicate,
    exclusions: &mut BTreeMap<Term, BTreeSet<ConstructorHead>>,
) {
    if let Predicate::And(predicates) = predicate {
        for predicate in predicates {
            collect_constructor_exclusions(definition, predicate, exclusions);
        }
        return;
    }
    let Predicate::Not(inner) = predicate else {
        return;
    };
    let mut inner = inner.as_ref();
    let mut binders = BTreeSet::new();
    // Invariant: `binders` holds every `Exists` above `inner`; on exit `inner` is not an `Exists`.
    while let Predicate::Exists(variable, body) = inner {
        binders.insert(variable.clone());
        inner = body;
    }
    let Predicate::Equals(left, right) = inner else {
        return;
    };
    let pair = [(left, right), (right, left)]
        .into_iter()
        .find_map(|(subject, constructor)| {
            let head = constructor_head(constructor)?;
            definition
                .finite_constructor_heads(&subject.sort())
                .is_some_and(|constructors| constructors.contains(&head))
                .then_some((subject, constructor, head))
        });
    let Some((subject, constructor, head)) = pair else {
        return;
    };
    if !is_functional_pattern(subject)
        || !subject.attributes().variables.is_disjoint(&binders)
        || !constructor_pattern_covers_head(constructor, &binders)
    {
        return;
    }
    exclusions.entry(subject.clone()).or_default().insert(head);
}

/// Whether the pattern denotes every value with its constructor head, rather than one
/// instantiated constructor value.
fn constructor_pattern_covers_head(constructor: &Term, binders: &BTreeSet<Variable>) -> bool {
    let arguments = match constructor.kind() {
        TermKind::Application { arguments, .. } => arguments.as_slice(),
        TermKind::Injection { term, .. } => std::slice::from_ref(term),
        _ => return false,
    };
    if arguments.len() != binders.len() {
        return false;
    }
    let argument_variables = arguments
        .iter()
        .map(|argument| match argument.kind() {
            TermKind::Variable(variable) => Some(variable.clone()),
            _ => None,
        })
        .collect::<Option<BTreeSet<_>>>();
    argument_variables
        .is_some_and(|variables| variables.len() == arguments.len() && variables == *binders)
}

fn predicate_truth(predicate: &Predicate) -> Truth {
    match predicate {
        Predicate::True => Truth::True,
        Predicate::False => Truth::False,
        Predicate::Term(term) => bool_term_truth(term),
        Predicate::Equals(left, right) if left == right => Truth::True,
        Predicate::Equals(left, right)
            if (left.attributes().constructor_like && right.attributes().constructor_like)
                || left.structurally_distinct_after_normalization(right) =>
        {
            Truth::False
        }
        Predicate::Not(inner) => match predicate_truth(inner) {
            Truth::True => Truth::False,
            Truth::False => Truth::True,
            Truth::Unknown => Truth::Unknown,
        },
        Predicate::And(inner) => predicates_truth(inner),
        Predicate::Or(inner) => inner.iter().fold(Truth::False, |result, predicate| {
            or_truth(result, predicate_truth(predicate))
        }),
        Predicate::Implies(left, right) => or_truth(
            match predicate_truth(left) {
                Truth::True => Truth::False,
                Truth::False => Truth::True,
                Truth::Unknown => Truth::Unknown,
            },
            predicate_truth(right),
        ),
        Predicate::Iff(left, right) => match (predicate_truth(left), predicate_truth(right)) {
            (Truth::True, Truth::True) | (Truth::False, Truth::False) => Truth::True,
            (Truth::True, Truth::False) | (Truth::False, Truth::True) => Truth::False,
            _ => Truth::Unknown,
        },
        Predicate::Ceil(term) if term.attributes().constructor_like => Truth::True,
        Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Exists(..)
        | Predicate::Forall(..) => Truth::Unknown,
    }
}

fn bool_term_truth(term: &Term) -> Truth {
    match term.kind() {
        TermKind::DomainValue { sort, value }
            if sort.is_builtin(BuiltinSort::Bool) && value == "true" =>
        {
            Truth::True
        }
        TermKind::DomainValue { sort, value }
            if sort.is_builtin(BuiltinSort::Bool) && value == "false" =>
        {
            Truth::False
        }
        _ => Truth::Unknown,
    }
}

fn and_truth(left: Truth, right: Truth) -> Truth {
    match (left, right) {
        (Truth::False, _) | (_, Truth::False) => Truth::False,
        (Truth::True, Truth::True) => Truth::True,
        _ => Truth::Unknown,
    }
}

fn or_truth(left: Truth, right: Truth) -> Truth {
    match (left, right) {
        (Truth::True, _) | (_, Truth::True) => Truth::True,
        (Truth::False, Truth::False) => Truth::False,
        _ => Truth::Unknown,
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn large_unique_extensions_preserve_first_occurrence_order() {
        let sort = Sort::simple("SortS");
        let mut predicates = (0..20)
            .map(|index| {
                Predicate::Equals(
                    Term::variable(Variable::new(format!("X{index}"), sort.clone())),
                    Term::domain_value(sort.clone(), index.to_string()),
                )
            })
            .collect::<Vec<_>>();
        let original = predicates.clone();

        extend_unique(
            &mut predicates,
            [original[19].clone(), Predicate::True, original[0].clone()],
        );

        assert_eq!(&predicates[..20], original);
        assert_eq!(predicates[20], Predicate::True);
    }

    #[test]
    fn final_leaves_with_distinct_console_states_do_not_merge() {
        let definition = definition("");
        let cursor_zero = ExecutionIoState::new(Vec::from(&b"input"[..]));
        let mut cursor_evaluation = cursor_zero.begin_evaluation();
        assert_eq!(cursor_evaluation.read(1), b"i");
        let cursor_one = cursor_evaluation.commit();
        let mut left_evaluation = ExecutionIoState::default().begin_evaluation();
        left_evaluation.append("IO.write", 1, Vec::from(&b"left"[..]));
        let left_io = left_evaluation.commit();
        let mut right_evaluation = ExecutionIoState::default().begin_evaluation();
        right_evaluation.append("IO.write", 1, Vec::from(&b"right"[..]));
        let right_io = right_evaluation.commit();
        let leaf = |io| ExecutionLeaf {
            pattern: subject(&definition, "same"),
            depth: 1,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            effects: Vec::new(),
            io,
            halt_reason: HaltReason::Stuck,
        };

        let cursor_leaves = merge_equal_final_leaves(vec![leaf(cursor_zero), leaf(cursor_one)]);
        assert_eq!(cursor_leaves.len(), 2);

        let transcript_leaves = merge_equal_final_leaves(vec![leaf(left_io), leaf(right_io)]);

        assert_eq!(transcript_leaves.len(), 2);
        assert_eq!(
            transcript_leaves[0].io.transcript()[0].bytes.as_ref(),
            b"left"
        );
        assert_eq!(
            transcript_leaves[1].io.transcript()[0].bytes.as_ref(),
            b"right"
        );
    }
}
