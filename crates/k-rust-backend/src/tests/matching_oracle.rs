//! A naive backtracking AC match enumerator, kept as a test oracle for the collection solvers.
//!
//! Given a Set or Map pattern and subject and an initial substitution, enumerate every complete
//! match (each pattern element or entry selects a distinct subject one; the frame, if any, takes
//! the rest), sorted and deduplicated, or `None` when any sub-match is indeterminate. The
//! production solver (`solve_collection_pairs_in_definition`) answers the same question with
//! narrowing, frame entries, and definedness side conditions; the tests in `tests::matching`
//! compare hand-built terms against this enumeration.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::{
    matching::{MatchMode, MatchResult, SortGraph, cancel_common_opaque_chunks, match_terms},
    substitution::{Substitution, compose, substitute},
    term::{MapDefinition, SetDefinition, Term, TermKind},
};

/// Enumerate complete matches for an internal Set pattern against a normalized Set subject.
///
/// Set element selection is genuinely nondeterministic: `SetItem(X) REST` has one solution for
/// each element of a concrete subject. The ordinary matcher deliberately reports that case as
/// indeterminate because its result type represents only one substitution.
pub(super) fn match_set_terms_all(
    mode: MatchMode,
    sorts: &SortGraph,
    pattern: &Term,
    subject: &Term,
    initial: &Substitution,
) -> Option<Vec<Substitution>> {
    let pattern = substitute(pattern, initial);
    let subject = substitute(subject, initial);
    let (
        TermKind::Set {
            definition: pattern_definition,
            elements: pattern_elements,
            rest: pattern_rest,
        },
        TermKind::Set {
            definition: subject_definition,
            elements: subject_elements,
            rest: subject_rest,
        },
    ) = (pattern.kind(), subject.kind())
    else {
        return None;
    };
    if pattern_definition != subject_definition {
        return None;
    }
    let (pattern_rest, subject_rest) = cancel_common_opaque_chunks(
        pattern_rest.clone(),
        subject_rest.clone(),
        &pattern_definition.symbols.concat,
    );
    if subject_rest.is_some() && pattern_rest.is_none() {
        return None;
    }

    let mut pattern_elements = pattern_elements.iter().cloned().collect::<BTreeSet<_>>();
    let mut subject_elements = subject_elements.iter().cloned().collect::<BTreeSet<_>>();
    let common = pattern_elements
        .intersection(&subject_elements)
        .cloned()
        .collect::<Vec<_>>();
    for element in common {
        pattern_elements.remove(&element);
        subject_elements.remove(&element);
    }
    if pattern_rest.is_none() && pattern_elements.len() != subject_elements.len() {
        return Some(Vec::new());
    }
    if pattern_elements.len() > subject_elements.len() {
        return subject_rest.is_none().then(Vec::new);
    }

    let problem = SetMatchProblem {
        mode,
        sorts,
        definition: pattern_definition.clone(),
        elements: pattern_elements.into_iter().collect(),
        rest: pattern_rest,
        subject_rest,
    };
    let mut solutions = Vec::new();
    let mut indeterminate = false;
    problem.search(
        0,
        subject_elements.into_iter().collect(),
        initial.clone(),
        &mut solutions,
        &mut indeterminate,
    );
    if indeterminate {
        None
    } else {
        solutions.sort();
        solutions.dedup();
        Some(solutions)
    }
}

/// Enumerate complete matches for an internal Map pattern against a normalized Map subject.
///
/// Like Set selection, a symbolic key may select any concrete subject entry. Each key choice keeps
/// its value paired with it and the opaque frame receives exactly the entries not selected.
pub(super) fn match_map_terms_all(
    mode: MatchMode,
    sorts: &SortGraph,
    pattern: &Term,
    subject: &Term,
    initial: &Substitution,
) -> Option<Vec<Substitution>> {
    let pattern = substitute(pattern, initial);
    let subject = substitute(subject, initial);
    let (
        TermKind::Map {
            definition: pattern_definition,
            entries: pattern_entries,
            rest: pattern_rest,
        },
        TermKind::Map {
            definition: subject_definition,
            entries: subject_entries,
            rest: subject_rest,
        },
    ) = (pattern.kind(), subject.kind())
    else {
        return None;
    };
    if pattern_definition != subject_definition {
        return None;
    }
    let (pattern_rest, subject_rest) = cancel_common_opaque_chunks(
        pattern_rest.clone(),
        subject_rest.clone(),
        &pattern_definition.symbols.concat,
    );
    if subject_rest.is_some() && pattern_rest.is_none() {
        return None;
    }

    let pattern_entry_count = pattern_entries.len();
    let subject_entry_count = subject_entries.len();
    let mut pattern_entries = pattern_entries.iter().cloned().collect::<BTreeMap<_, _>>();
    let mut subject_entries = subject_entries.iter().cloned().collect::<BTreeMap<_, _>>();
    if pattern_entries.len() != pattern_entry_count || subject_entries.len() != subject_entry_count
    {
        return None;
    }
    let common_keys = pattern_entries
        .keys()
        .filter(|key| subject_entries.contains_key(*key))
        .cloned()
        .collect::<Vec<_>>();
    let mut substitutions = vec![initial.clone()];
    for key in common_keys {
        let pattern_value = pattern_entries.remove(&key).unwrap();
        let subject_value = subject_entries.remove(&key).unwrap();
        let mut next = Vec::new();
        for substitution in substitutions {
            match match_terms(
                mode,
                sorts,
                &substitute(&pattern_value, &substitution),
                &subject_value,
            ) {
                MatchResult::Success(found) => next.push(compose(&found, &substitution)),
                MatchResult::Failed(_) => {}
                MatchResult::Indeterminate { .. } => return None,
            }
        }
        substitutions = next;
    }
    if pattern_rest.is_none() && pattern_entries.len() != subject_entries.len() {
        return Some(Vec::new());
    }
    if pattern_entries.len() > subject_entries.len() {
        return subject_rest.is_none().then(Vec::new);
    }

    let problem = MapMatchProblem {
        mode,
        sorts,
        definition: pattern_definition.clone(),
        entries: pattern_entries.into_iter().collect(),
        rest: pattern_rest,
        subject_rest,
    };
    let mut solutions = Vec::new();
    let mut indeterminate = false;
    for substitution in substitutions {
        problem.search(
            0,
            subject_entries
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
            substitution,
            &mut solutions,
            &mut indeterminate,
        );
    }
    if indeterminate {
        None
    } else {
        solutions.sort();
        solutions.dedup();
        Some(solutions)
    }
}

pub(super) struct MapMatchProblem<'a> {
    mode: MatchMode,
    sorts: &'a SortGraph,
    definition: Arc<MapDefinition>,
    entries: Vec<(Term, Term)>,
    rest: Option<Term>,
    subject_rest: Option<Term>,
}

impl MapMatchProblem<'_> {
    fn search(
        &self,
        index: usize,
        remaining: Vec<(Term, Term)>,
        substitution: Substitution,
        solutions: &mut Vec<Substitution>,
        indeterminate: &mut bool,
    ) {
        if index == self.entries.len() {
            let Some(rest) = &self.rest else {
                if remaining.is_empty() {
                    solutions.push(substitution);
                }
                return;
            };
            let rest = substitute(rest, &substitution);
            let remainder = Term::map(
                self.definition.clone(),
                remaining,
                self.subject_rest.clone(),
            );
            match match_terms(self.mode, self.sorts, &rest, &remainder) {
                MatchResult::Success(found) => solutions.push(compose(&found, &substitution)),
                MatchResult::Failed(_) => {}
                MatchResult::Indeterminate { .. } => *indeterminate = true,
            }
            return;
        }

        let (key, value) = &self.entries[index];
        let key = substitute(key, &substitution);
        for subject_index in 0..remaining.len() {
            let (subject_key, subject_value) = &remaining[subject_index];
            let key_substitution = match match_terms(self.mode, self.sorts, &key, subject_key) {
                MatchResult::Success(found) => found,
                MatchResult::Failed(_) => continue,
                MatchResult::Indeterminate { .. } => {
                    *indeterminate = true;
                    continue;
                }
            };
            let substitution = compose(&key_substitution, &substitution);
            let value = substitute(value, &substitution);
            match match_terms(self.mode, self.sorts, &value, subject_value) {
                MatchResult::Success(value_substitution) => {
                    let mut next_remaining = remaining.clone();
                    next_remaining.remove(subject_index);
                    self.search(
                        index + 1,
                        next_remaining,
                        compose(&value_substitution, &substitution),
                        solutions,
                        indeterminate,
                    );
                }
                MatchResult::Failed(_) => {}
                MatchResult::Indeterminate { .. } => *indeterminate = true,
            }
        }
    }
}

pub(super) struct SetMatchProblem<'a> {
    mode: MatchMode,
    sorts: &'a SortGraph,
    definition: Arc<SetDefinition>,
    elements: Vec<Term>,
    rest: Option<Term>,
    subject_rest: Option<Term>,
}

impl SetMatchProblem<'_> {
    fn search(
        &self,
        index: usize,
        remaining: Vec<Term>,
        substitution: Substitution,
        solutions: &mut Vec<Substitution>,
        indeterminate: &mut bool,
    ) {
        if index == self.elements.len() {
            let Some(rest) = &self.rest else {
                if remaining.is_empty() {
                    solutions.push(substitution);
                }
                return;
            };
            let rest = substitute(rest, &substitution);
            let remainder = Term::set(
                self.definition.clone(),
                remaining,
                self.subject_rest.clone(),
            );
            match match_terms(self.mode, self.sorts, &rest, &remainder) {
                MatchResult::Success(found) => solutions.push(compose(&found, &substitution)),
                MatchResult::Failed(_) => {}
                MatchResult::Indeterminate { .. } => *indeterminate = true,
            }
            return;
        }

        let element = substitute(&self.elements[index], &substitution);
        for subject_index in 0..remaining.len() {
            let subject = &remaining[subject_index];
            match match_terms(self.mode, self.sorts, &element, subject) {
                MatchResult::Success(found) => {
                    let mut next_remaining = remaining.clone();
                    next_remaining.remove(subject_index);
                    self.search(
                        index + 1,
                        next_remaining,
                        compose(&found, &substitution),
                        solutions,
                        indeterminate,
                    );
                }
                MatchResult::Failed(_) => {}
                MatchResult::Indeterminate { .. } => *indeterminate = true,
            }
        }
    }
}
