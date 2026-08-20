//! Sort-aware one-way matching for rewrite rules and equations.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
};

use crate::{
    definition::BackendDefinition,
    substitution::{Substitution, compose, substitute},
    term::{ListDefinition, MapDefinition, Name, Sort, SymbolType, Term, TermKind, Variable},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MatchMode {
    Rewrite,
    Evaluate,
    Implies,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MatchResult {
    Success(Substitution),
    Failed(FailReason),
    Indeterminate {
        substitution: Substitution,
        remainder: Vec<(Term, Term)>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FailReason {
    DifferentValues(Term, Term),
    DifferentSymbols(Term, Term),
    DifferentSorts(Term, Term),
    VariableRecursion(Variable, Term),
    VariableConflict(Variable, Term, Term),
    KeyNotFound(Term, Term),
    DuplicateKeys(Term, Term),
    SharedVariables(BTreeSet<Variable>),
    Subsorting(SortError),
    ArgumentLengthsDiffer(Term, Term),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SortError {
    FoundSortVariable(Name),
    FoundUnknownSort(Sort),
}

/// Reflexive-transitive subsort closure keyed by the supersort name.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SortGraph {
    subsorts: BTreeMap<Name, BTreeSet<Name>>,
}

impl SortGraph {
    pub fn insert(&mut self, supersort: impl Into<Name>, subsorts: impl IntoIterator<Item = Name>) {
        let supersort = supersort.into();
        let mut closure = subsorts.into_iter().collect::<BTreeSet<_>>();
        closure.insert(supersort.clone());
        self.subsorts.insert(supersort, closure);
    }

    pub fn check_subsort(&self, sub: &Sort, sup: &Sort) -> Result<bool, SortError> {
        if sub == sup {
            return Ok(true);
        }
        let Sort::Application {
            name: sub_name,
            arguments: sub_arguments,
        } = sub
        else {
            let Sort::Variable(name) = sub else {
                unreachable!()
            };
            return Err(SortError::FoundSortVariable(name.clone()));
        };
        let Sort::Application {
            name: sup_name,
            arguments: sup_arguments,
        } = sup
        else {
            let Sort::Variable(name) = sup else {
                unreachable!()
            };
            return Err(SortError::FoundSortVariable(name.clone()));
        };
        let Some(subsorts) = self.subsorts.get(sup_name) else {
            return Err(SortError::FoundUnknownSort(sup.clone()));
        };
        if !subsorts.contains(sub_name) {
            return Ok(false);
        }
        if sub_arguments.len() != sup_arguments.len() {
            return Ok(false);
        }
        for (sub_argument, sup_argument) in sub_arguments.iter().zip(sup_arguments) {
            if !self.check_subsort(sub_argument, sup_argument)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn overlap(&self, left: &Sort, right: &Sort) -> bool {
        let (
            Sort::Application {
                name: left,
                arguments: left_arguments,
            },
            Sort::Application {
                name: right,
                arguments: right_arguments,
            },
        ) = (left, right)
        else {
            return true;
        };
        if !left_arguments.is_empty() || !right_arguments.is_empty() {
            return true;
        }
        match (self.subsorts.get(left), self.subsorts.get(right)) {
            (Some(left), Some(right)) => !left.is_disjoint(right),
            _ => true,
        }
    }
}

pub fn match_terms(
    mode: MatchMode,
    sorts: &SortGraph,
    pattern: &Term,
    subject: &Term,
) -> MatchResult {
    match_terms_with_context(mode, sorts, None, pattern, subject)
}

pub fn match_terms_in_definition(
    mode: MatchMode,
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
) -> MatchResult {
    match_terms_with_context(
        mode,
        &definition.sort_graph,
        Some(definition),
        pattern,
        subject,
    )
}

pub(crate) fn match_term_pairs_in_definition(
    mode: MatchMode,
    definition: &BackendDefinition,
    pairs: impl IntoIterator<Item = (Term, Term)>,
) -> MatchResult {
    let pairs = pairs
        .into_iter()
        .filter(|(pattern, subject)| pattern != subject)
        .collect::<Vec<_>>();
    if pairs.is_empty() {
        return MatchResult::Success(Substitution::new());
    }
    let pattern_variables = pairs
        .iter()
        .flat_map(|(pattern, _)| pattern.attributes().variables.iter().cloned())
        .collect::<BTreeSet<_>>();
    let subject_variables = pairs
        .iter()
        .flat_map(|(_, subject)| subject.attributes().variables.iter().cloned())
        .collect::<BTreeSet<_>>();
    let shared_variables = pattern_variables
        .intersection(&subject_variables)
        .cloned()
        .collect::<BTreeSet<_>>();
    if mode != MatchMode::Implies && !shared_variables.is_empty() {
        return match mode {
            MatchMode::Rewrite => MatchResult::Indeterminate {
                substitution: Substitution::new(),
                remainder: shared_variables
                    .into_iter()
                    .map(|variable| {
                        let term = Term::variable(variable);
                        (term.clone(), term)
                    })
                    .collect(),
            },
            MatchMode::Evaluate => {
                MatchResult::Failed(FailReason::SharedVariables(shared_variables))
            }
            MatchMode::Implies => unreachable!(),
        };
    }

    let mut matcher = Matcher {
        mode,
        sorts: &definition.sort_graph,
        definition: Some(definition),
        substitution: Substitution::new(),
        queue: pairs.into(),
        map_queue: VecDeque::new(),
        indeterminate: Vec::new(),
    };
    if let Err(reason) = matcher.run() {
        return MatchResult::Failed(reason);
    }
    if matcher.indeterminate.is_empty() {
        MatchResult::Success(matcher.substitution)
    } else {
        matcher.indeterminate.reverse();
        MatchResult::Indeterminate {
            substitution: matcher.substitution,
            remainder: matcher.indeterminate,
        }
    }
}

fn match_terms_with_context(
    mode: MatchMode,
    sorts: &SortGraph,
    definition: Option<&BackendDefinition>,
    pattern: &Term,
    subject: &Term,
) -> MatchResult {
    if pattern == subject {
        return MatchResult::Success(Substitution::new());
    }
    let shared_variables = pattern
        .attributes()
        .variables
        .intersection(&subject.attributes().variables)
        .cloned()
        .collect::<BTreeSet<_>>();
    if mode != MatchMode::Implies && !shared_variables.is_empty() {
        return match mode {
            MatchMode::Rewrite => MatchResult::Indeterminate {
                substitution: Substitution::new(),
                remainder: shared_variables
                    .into_iter()
                    .map(|variable| {
                        let term = Term::variable(variable);
                        (term.clone(), term)
                    })
                    .collect(),
            },
            MatchMode::Evaluate => {
                MatchResult::Failed(FailReason::SharedVariables(shared_variables))
            }
            MatchMode::Implies => unreachable!(),
        };
    }

    let mut matcher = Matcher {
        mode,
        sorts,
        definition,
        substitution: Substitution::new(),
        queue: VecDeque::from([(pattern.clone(), subject.clone())]),
        map_queue: VecDeque::new(),
        indeterminate: Vec::new(),
    };
    if let Err(reason) = matcher.run() {
        return MatchResult::Failed(reason);
    }
    if matcher.indeterminate.is_empty() {
        MatchResult::Success(matcher.substitution)
    } else {
        matcher.indeterminate.reverse();
        MatchResult::Indeterminate {
            substitution: matcher.substitution,
            remainder: matcher.indeterminate,
        }
    }
}

/// Enumerate complete matches for an internal Set pattern against a normalized Set subject.
///
/// Set element selection is genuinely nondeterministic: `SetItem(X) REST` has one solution for
/// each element of a concrete subject. The ordinary matcher deliberately reports that case as
/// indeterminate because its result type represents only one substitution. Rewrite execution uses
/// this helper to preserve every solution as a separate successor.
#[cfg(test)]
fn match_set_terms_all(
    mode: MatchMode,
    sorts: &SortGraph,
    pattern: &Term,
    subject: &Term,
    initial: &Substitution,
) -> Option<Vec<Substitution>> {
    match_set_terms_all_with_context(mode, sorts, None, pattern, subject, initial)
}

pub(crate) fn match_set_terms_all_in_definition(
    mode: MatchMode,
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    initial: &Substitution,
) -> Option<Vec<Substitution>> {
    match_set_terms_all_with_context(
        mode,
        &definition.sort_graph,
        Some(definition),
        pattern,
        subject,
        initial,
    )
}

fn match_set_terms_all_with_context(
    mode: MatchMode,
    sorts: &SortGraph,
    backend: Option<&BackendDefinition>,
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
    if pattern_definition != subject_definition
        || (subject_rest.is_some() && pattern_rest.is_none())
    {
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
        backend,
        definition: pattern_definition.clone(),
        elements: pattern_elements.into_iter().collect(),
        rest: pattern_rest.clone(),
        subject_rest: subject_rest.clone(),
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
#[cfg(test)]
fn match_map_terms_all(
    mode: MatchMode,
    sorts: &SortGraph,
    pattern: &Term,
    subject: &Term,
    initial: &Substitution,
) -> Option<Vec<Substitution>> {
    match_map_terms_all_with_context(mode, sorts, None, pattern, subject, initial)
}

pub(crate) fn match_map_terms_all_in_definition(
    mode: MatchMode,
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    initial: &Substitution,
) -> Option<Vec<Substitution>> {
    match_map_terms_all_with_context(
        mode,
        &definition.sort_graph,
        Some(definition),
        pattern,
        subject,
        initial,
    )
}

/// Enumerate complete collection matches for every deferred pair from an ordinary match.
///
/// A deferred Set or Map pair may have multiple AC solutions. Returning all substitutions keeps
/// that branching policy outside the one-result [`MatchResult`] API and lets each consumer decide
/// whether the solutions are execution branches or equivalent choices for a functional equation.
pub(crate) fn match_collection_remainders_all_in_definition(
    mode: MatchMode,
    definition: &BackendDefinition,
    initial: Substitution,
    remainder: &[(Term, Term)],
) -> Option<Vec<Substitution>> {
    let mut solutions = vec![initial];
    for (pattern, subject) in remainder {
        let mut next = Vec::new();
        for substitution in solutions {
            let matches = match_set_terms_all_in_definition(
                mode,
                definition,
                pattern,
                subject,
                &substitution,
            )
            .or_else(|| {
                match_map_terms_all_in_definition(mode, definition, pattern, subject, &substitution)
            })?;
            next.extend(matches);
        }
        solutions = next;
    }
    solutions.sort();
    solutions.dedup();
    Some(solutions)
}

fn match_map_terms_all_with_context(
    mode: MatchMode,
    sorts: &SortGraph,
    backend: Option<&BackendDefinition>,
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
    if pattern_definition != subject_definition
        || (subject_rest.is_some() && pattern_rest.is_none())
    {
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
            match match_terms_with_context(
                mode,
                sorts,
                backend,
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
        backend,
        definition: pattern_definition.clone(),
        entries: pattern_entries.into_iter().collect(),
        rest: pattern_rest.clone(),
        subject_rest: subject_rest.clone(),
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

struct MapMatchProblem<'a> {
    mode: MatchMode,
    sorts: &'a SortGraph,
    backend: Option<&'a BackendDefinition>,
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
            match match_terms_with_context(self.mode, self.sorts, self.backend, &rest, &remainder) {
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
            let key_substitution = match match_terms_with_context(
                self.mode,
                self.sorts,
                self.backend,
                &key,
                subject_key,
            ) {
                MatchResult::Success(found) => found,
                MatchResult::Failed(_) => continue,
                MatchResult::Indeterminate { .. } => {
                    *indeterminate = true;
                    continue;
                }
            };
            let substitution = compose(&key_substitution, &substitution);
            let value = substitute(value, &substitution);
            match match_terms_with_context(
                self.mode,
                self.sorts,
                self.backend,
                &value,
                subject_value,
            ) {
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

struct SetMatchProblem<'a> {
    mode: MatchMode,
    sorts: &'a SortGraph,
    backend: Option<&'a BackendDefinition>,
    definition: Arc<crate::term::SetDefinition>,
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
            match match_terms_with_context(self.mode, self.sorts, self.backend, &rest, &remainder) {
                MatchResult::Success(found) => solutions.push(compose(&found, &substitution)),
                MatchResult::Failed(_) => {}
                MatchResult::Indeterminate { .. } => *indeterminate = true,
            }
            return;
        }

        let element = substitute(&self.elements[index], &substitution);
        for subject_index in 0..remaining.len() {
            let subject = &remaining[subject_index];
            match match_terms_with_context(self.mode, self.sorts, self.backend, &element, subject) {
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

struct Matcher<'a> {
    mode: MatchMode,
    sorts: &'a SortGraph,
    definition: Option<&'a BackendDefinition>,
    substitution: Substitution,
    queue: VecDeque<(Term, Term)>,
    map_queue: VecDeque<(Term, Term)>,
    indeterminate: Vec<(Term, Term)>,
}

impl Matcher<'_> {
    fn run(&mut self) -> Result<(), FailReason> {
        while let Some((pattern, subject)) = self
            .queue
            .pop_front()
            .or_else(|| self.map_queue.pop_front())
        {
            self.match_one(pattern, subject)?;
        }
        Ok(())
    }

    fn match_one(&mut self, pattern: Term, subject: Term) -> Result<(), FailReason> {
        if self.mode == MatchMode::Implies && pattern == subject {
            return Ok(());
        }
        if self.mode == MatchMode::Evaluate && matches!(subject.kind(), TermKind::And(..)) {
            return self.defer(pattern, subject);
        }
        if self.mode == MatchMode::Evaluate
            && matches!(pattern.kind(), TermKind::And(..))
            && matches!(subject.kind(), TermKind::Variable(_))
        {
            return self.defer(pattern, subject);
        }
        if let TermKind::And(left, right) = pattern.kind() {
            self.enqueue(left.clone(), subject.clone());
            self.enqueue(right.clone(), subject);
            return Ok(());
        }
        if let TermKind::And(left, right) = subject.kind() {
            self.enqueue(pattern.clone(), left.clone());
            self.enqueue(pattern, right.clone());
            return Ok(());
        }
        if let Some((pattern, subject)) = self.resolve_overloads(&pattern, &subject) {
            self.enqueue(pattern, subject);
            return Ok(());
        }
        if let TermKind::Variable(variable) = pattern.kind() {
            return self.match_variable(variable.clone(), pattern, subject);
        }
        if matches!(subject.kind(), TermKind::Variable(_)) {
            return self.defer(pattern, subject);
        }

        match (pattern.kind(), subject.kind()) {
            (
                TermKind::DomainValue {
                    sort: pattern_sort,
                    value: pattern_value,
                },
                TermKind::DomainValue {
                    sort: subject_sort,
                    value: subject_value,
                },
            ) => {
                if pattern_value != subject_value {
                    Err(FailReason::DifferentValues(pattern, subject))
                } else if pattern_sort != subject_sort {
                    Err(FailReason::DifferentSorts(pattern, subject))
                } else {
                    Ok(())
                }
            }
            (
                TermKind::Injection {
                    source: pattern_source,
                    target: pattern_target,
                    term: pattern_term,
                },
                TermKind::Injection {
                    source: subject_source,
                    target: subject_target,
                    term: subject_term,
                },
            ) => {
                if pattern_target != subject_target {
                    return Err(FailReason::DifferentSorts(pattern, subject));
                }
                if pattern_source == subject_source {
                    self.enqueue(pattern_term.clone(), subject_term.clone());
                    return Ok(());
                }
                self.match_differing_injections(pattern, subject)
            }
            (
                TermKind::Application {
                    symbol: pattern_symbol,
                    sort_arguments: pattern_sorts,
                    arguments: pattern_arguments,
                },
                TermKind::Application {
                    symbol: subject_symbol,
                    sort_arguments: subject_sorts,
                    arguments: subject_arguments,
                },
            ) if (is_constructor(&pattern) && is_constructor(&subject))
                || (pattern_symbol.attributes.injective
                    && pattern_symbol.name == subject_symbol.name)
                || (self.mode == MatchMode::Evaluate
                    && is_function(&pattern)
                    && is_function(&subject)) =>
            {
                if pattern_symbol.name != subject_symbol.name {
                    if self.mode == MatchMode::Rewrite
                        || (is_constructor(&pattern) && is_constructor(&subject))
                    {
                        return Err(FailReason::DifferentSymbols(pattern, subject));
                    }
                    return self.defer(pattern, subject);
                }
                if pattern_arguments.len() != subject_arguments.len() {
                    return Err(FailReason::ArgumentLengthsDiffer(pattern, subject));
                }
                if pattern_sorts != subject_sorts {
                    return Err(FailReason::DifferentSorts(pattern, subject));
                }
                if self.mode != MatchMode::Rewrite
                    && (pattern_symbol.attributes.associative
                        || pattern_symbol.attributes.idempotent)
                {
                    return self.defer(pattern, subject);
                }
                for (pattern, subject) in pattern_arguments.iter().zip(subject_arguments) {
                    self.enqueue(pattern.clone(), subject.clone());
                }
                Ok(())
            }
            (
                TermKind::List {
                    definition: left,
                    heads: left_heads,
                    rest: left_rest,
                },
                TermKind::List {
                    definition: right,
                    heads: right_heads,
                    rest: right_rest,
                },
            ) if left == right => self.match_lists(
                left.clone(),
                left_heads.clone(),
                left_rest.clone(),
                right_heads.clone(),
                right_rest.clone(),
            ),
            (
                TermKind::Set {
                    definition: left,
                    elements: left_elements,
                    rest: left_rest,
                },
                TermKind::Set {
                    definition: right,
                    elements: right_elements,
                    rest: right_rest,
                },
            ) if left == right => self.match_sets(
                left.clone(),
                left_elements.clone(),
                left_rest.clone(),
                right_elements.clone(),
                right_rest.clone(),
            ),
            (
                TermKind::Map {
                    definition: left,
                    entries: left_entries,
                    rest: left_rest,
                },
                TermKind::Map {
                    definition: right,
                    entries: right_entries,
                    rest: right_rest,
                },
            ) if left == right => {
                if !self.queue.is_empty() {
                    self.map_queue.push_back((pattern, subject));
                    Ok(())
                } else {
                    self.match_maps(
                        left.clone(),
                        left_entries.clone(),
                        left_rest.clone(),
                        right_entries.clone(),
                        right_rest.clone(),
                    )
                }
            }
            (left, right) if same_collection_category(left, right) => {
                if collection_definition_matches(left, right) {
                    self.defer(pattern, subject)
                } else {
                    Err(FailReason::DifferentSorts(pattern, subject))
                }
            }
            (TermKind::Injection { .. }, right)
                if self.mode == MatchMode::Evaluate && is_collection(right) =>
            {
                self.defer(pattern, subject)
            }
            (left, TermKind::Injection { .. })
                if self.mode == MatchMode::Evaluate && is_collection(left) =>
            {
                self.defer(pattern, subject)
            }
            (_, _) if self.can_narrow_overload(&pattern, &subject) => self.defer(pattern, subject),
            (left, right)
                if (is_overload_head(self.definition, left) && is_rigid(right))
                    || (is_rigid(left) && is_overload_head(self.definition, right)) =>
            {
                Err(FailReason::DifferentSymbols(pattern, subject))
            }
            (left, right) if is_rigid(left) && is_rigid(right) => {
                Err(FailReason::DifferentSymbols(pattern, subject))
            }
            _ => self.defer(pattern, subject),
        }
    }

    fn match_differing_injections(
        &mut self,
        pattern: Term,
        subject: Term,
    ) -> Result<(), FailReason> {
        let (
            TermKind::Injection {
                source: pattern_source,
                term: pattern_term,
                ..
            },
            TermKind::Injection {
                source: subject_source,
                term: subject_term,
                ..
            },
        ) = (pattern.kind(), subject.kind())
        else {
            unreachable!()
        };
        let pattern_is_subsort = self
            .sorts
            .check_subsort(pattern_source, subject_source)
            .map_err(FailReason::Subsorting)?;
        let subject_is_subsort = self
            .sorts
            .check_subsort(subject_source, pattern_source)
            .map_err(FailReason::Subsorting)?;
        if !pattern_is_subsort && !subject_is_subsort {
            return Err(FailReason::DifferentSorts(
                pattern_term.clone(),
                subject_term.clone(),
            ));
        }
        if pattern_is_subsort
            && (is_function(subject_term) || matches!(subject_term.kind(), TermKind::Variable(_)))
        {
            return self.defer(pattern_term.clone(), subject_term.clone());
        }
        if subject_is_subsort {
            if let TermKind::Variable(variable) = pattern_term.kind() {
                return self.bind(
                    variable.clone(),
                    Term::injection(
                        subject_source.clone(),
                        pattern_source.clone(),
                        subject_term.clone(),
                    ),
                );
            }
            if is_function(pattern_term) {
                return self.defer(pattern_term.clone(), subject_term.clone());
            }
        }
        Err(FailReason::DifferentSorts(pattern, subject))
    }

    fn resolve_overloads(&self, pattern: &Term, subject: &Term) -> Option<(Term, Term)> {
        let definition = self.definition?;
        let pattern_view = OverloadView::new(pattern)?;
        let subject_view = OverloadView::new(subject)?;
        if pattern_view.symbol.name == subject_view.symbol.name {
            return None;
        }
        let common_name = if definition
            .overloads
            .is_overloading(&pattern_view.symbol.name, &subject_view.symbol.name)
        {
            pattern_view.symbol.name.clone()
        } else if definition
            .overloads
            .is_overloading(&subject_view.symbol.name, &pattern_view.symbol.name)
        {
            subject_view.symbol.name.clone()
        } else {
            let common = definition
                .overloads
                .common_overloads(&pattern_view.symbol.name, &subject_view.symbol.name);
            let minimal = common
                .iter()
                .filter(|candidate| {
                    !common.iter().any(|other| {
                        candidate != &other && definition.overloads.is_overloading(candidate, other)
                    })
                })
                .cloned()
                .collect::<Vec<_>>();
            let [common] = minimal.as_slice() else {
                return None;
            };
            common.clone()
        };
        let common = definition.symbols.get(&common_name)?.clone();
        let sort_arguments = if pattern_view.symbol.name == common_name {
            pattern_view.sort_arguments.clone()
        } else if subject_view.symbol.name == common_name {
            subject_view.sort_arguments.clone()
        } else if common.sort_variables.is_empty() {
            Vec::new()
        } else {
            return None;
        };
        Some((
            pattern_view.lift(common.clone(), &sort_arguments, self.sorts)?,
            subject_view.lift(common, &sort_arguments, self.sorts)?,
        ))
    }

    fn can_narrow_overload(&self, pattern: &Term, subject: &Term) -> bool {
        let Some(definition) = self.definition else {
            return false;
        };
        let Some(pattern) = OverloadView::new(pattern) else {
            return false;
        };
        let TermKind::Injection { term, .. } = subject.kind() else {
            return false;
        };
        let TermKind::Variable(variable) = term.kind() else {
            return false;
        };
        definition
            .overloads
            .overloaded_by(&pattern.symbol.name)
            .into_iter()
            .filter_map(|name| definition.symbols.get(&name))
            .any(|symbol| {
                symbol.sort_variables.is_empty()
                    && self
                        .sorts
                        .check_subsort(&symbol.result_sort, &variable.sort)
                        .unwrap_or(false)
            })
    }

    fn match_lists(
        &mut self,
        definition: Arc<ListDefinition>,
        pattern_heads: Vec<Term>,
        pattern_rest: Option<(Term, Vec<Term>)>,
        subject_heads: Vec<Term>,
        subject_rest: Option<(Term, Vec<Term>)>,
    ) -> Result<(), FailReason> {
        let (mut problems, head_remainder) = pair_prefix(&pattern_heads, &subject_heads);
        let empty = || Term::list(definition.clone(), Vec::new(), None);
        let list = |heads, rest| Term::list(definition.clone(), heads, rest);

        let mut rest_problems = match (pattern_rest, subject_rest, head_remainder) {
            (None, None, None) => Vec::new(),
            (None, None, Some(PairRemainder::Left(heads))) => {
                return Err(FailReason::DifferentValues(list(heads, None), empty()));
            }
            (None, None, Some(PairRemainder::Right(heads))) => {
                return Err(FailReason::DifferentValues(empty(), list(heads, None)));
            }
            (None, Some(rest), remainder) => {
                let (left, right) = match remainder {
                    Some(PairRemainder::Left(heads)) => {
                        (list(heads, None), list(Vec::new(), Some(rest)))
                    }
                    Some(PairRemainder::Right(heads)) => (empty(), list(heads, Some(rest))),
                    None => (empty(), list(Vec::new(), Some(rest))),
                };
                return Err(FailReason::DifferentValues(left, right));
            }
            (Some((middle, tails)), None, None) if tails.is_empty() => {
                vec![(middle, empty())]
            }
            (Some(rest), None, None) => {
                return Err(FailReason::DifferentValues(
                    list(Vec::new(), Some(rest)),
                    empty(),
                ));
            }
            (Some(rest), None, Some(PairRemainder::Left(heads))) => {
                return Err(FailReason::DifferentValues(
                    list(heads, Some(rest)),
                    empty(),
                ));
            }
            (Some((middle, tails)), None, Some(PairRemainder::Right(heads))) => {
                let (tail_pairs, tail_remainder) = pair_suffix(&tails, &heads);
                match tail_remainder {
                    None => prepend((middle, empty()), tail_pairs),
                    Some(PairRemainder::Left(extra)) => {
                        return Err(FailReason::DifferentValues(
                            list(Vec::new(), Some((middle, extra))),
                            empty(),
                        ));
                    }
                    Some(PairRemainder::Right(extra)) => {
                        prepend((middle, list(extra, None)), tail_pairs)
                    }
                }
            }
            (Some((pattern_middle, pattern_tails)), Some(subject_rest), remainder) => {
                let (subject_middle, subject_tails) = subject_rest;
                match remainder {
                    Some(PairRemainder::Left(heads)) => {
                        self.defer(
                            list(heads, Some((pattern_middle, pattern_tails))),
                            list(Vec::new(), Some((subject_middle, subject_tails))),
                        )?;
                        Vec::new()
                    }
                    remainder => {
                        let subject_heads = match remainder {
                            Some(PairRemainder::Right(heads)) => heads,
                            _ => Vec::new(),
                        };
                        let (tail_pairs, tail_remainder) =
                            pair_suffix(&pattern_tails, &subject_tails);
                        match tail_remainder {
                            None => prepend(
                                (
                                    pattern_middle,
                                    list(subject_heads, Some((subject_middle, Vec::new()))),
                                ),
                                tail_pairs,
                            ),
                            Some(PairRemainder::Left(extra)) => {
                                self.defer(
                                    list(Vec::new(), Some((pattern_middle, extra))),
                                    list(subject_heads, Some((subject_middle, Vec::new()))),
                                )?;
                                Vec::new()
                            }
                            Some(PairRemainder::Right(extra)) => prepend(
                                (
                                    pattern_middle,
                                    list(subject_heads, Some((subject_middle, extra))),
                                ),
                                tail_pairs,
                            ),
                        }
                    }
                }
            }
        };
        problems.append(&mut rest_problems);
        self.queue.extend(problems);
        Ok(())
    }

    fn match_maps(
        &mut self,
        definition: Arc<MapDefinition>,
        pattern_entries: Vec<(Term, Term)>,
        pattern_rest: Option<Term>,
        subject_entries: Vec<(Term, Term)>,
        subject_rest: Option<Term>,
    ) -> Result<(), FailReason> {
        let pattern_entries = pattern_entries
            .into_iter()
            .map(|(key, value)| (substitute(&key, &self.substitution), value))
            .collect::<Vec<_>>();
        check_duplicate_keys(&definition, &pattern_entries, &pattern_rest)?;
        check_duplicate_keys(&definition, &subject_entries, &subject_rest)?;

        let mut pattern = pattern_entries.into_iter().collect::<BTreeMap<_, _>>();
        let mut subject = subject_entries.into_iter().collect::<BTreeMap<_, _>>();
        let common_keys = pattern
            .keys()
            .filter(|key| subject.contains_key(*key))
            .cloned()
            .collect::<Vec<_>>();
        let mut problems = Vec::new();
        for key in common_keys {
            problems.push((pattern.remove(&key).unwrap(), subject.remove(&key).unwrap()));
        }

        let pattern = MapRemainder::new(pattern.into_iter().collect(), pattern_rest);
        let subject = MapRemainder::new(subject.into_iter().collect(), subject_rest);
        let mut rest = self.match_map_remainders(&definition, pattern, subject)?;
        problems.append(&mut rest);
        self.queue.extend(problems);
        Ok(())
    }

    fn match_sets(
        &mut self,
        definition: Arc<crate::term::SetDefinition>,
        pattern_elements: Vec<Term>,
        pattern_rest: Option<Term>,
        subject_elements: Vec<Term>,
        subject_rest: Option<Term>,
    ) -> Result<(), FailReason> {
        let mut pattern_elements = pattern_elements
            .into_iter()
            .map(|element| substitute(&element, &self.substitution))
            .collect::<BTreeSet<_>>();
        let mut subject_elements = subject_elements.into_iter().collect::<BTreeSet<_>>();
        let common = pattern_elements
            .intersection(&subject_elements)
            .cloned()
            .collect::<Vec<_>>();
        for element in common {
            pattern_elements.remove(&element);
            subject_elements.remove(&element);
        }

        let pattern_symbolic = pattern_elements
            .iter()
            .filter(|element| !element.attributes().constructor_like)
            .cloned()
            .collect::<Vec<_>>();
        let pattern_concrete = pattern_elements
            .iter()
            .filter(|element| element.attributes().constructor_like)
            .cloned()
            .collect::<Vec<_>>();
        let subject_symbolic = subject_elements
            .iter()
            .filter(|element| !element.attributes().constructor_like)
            .cloned()
            .collect::<Vec<_>>();
        let set = |elements, rest| Term::set(definition.clone(), elements, rest);

        if let Some(element) = pattern_concrete.first() {
            if subject_symbolic.is_empty() && subject_rest.is_none() {
                return Err(FailReason::KeyNotFound(
                    element.clone(),
                    set(subject_elements.into_iter().collect(), None),
                ));
            }
            return self.defer(
                set(pattern_elements.into_iter().collect(), pattern_rest),
                set(subject_elements.into_iter().collect(), subject_rest),
            );
        }

        if pattern_symbolic.is_empty() {
            let subject_is_empty = subject_elements.is_empty() && subject_rest.is_none();
            let subject = set(subject_elements.into_iter().collect(), subject_rest);
            if let Some(rest) = pattern_rest {
                self.enqueue(rest, subject);
                return Ok(());
            }
            if subject_is_empty {
                return Ok(());
            }
            return Err(FailReason::DifferentSymbols(set(Vec::new(), None), subject));
        }

        if pattern_symbolic.len() == 1
            && subject_elements.len() == 1
            && (subject_rest.is_none() || pattern_rest.is_some())
        {
            self.enqueue(
                pattern_symbolic.into_iter().next().unwrap(),
                subject_elements.into_iter().next().unwrap(),
            );
            if let Some(rest) = pattern_rest {
                self.enqueue(rest, set(Vec::new(), subject_rest));
            }
            return Ok(());
        }

        if subject_elements.is_empty() && subject_rest.is_none() {
            return Err(FailReason::DifferentSymbols(
                set(pattern_elements.into_iter().collect(), pattern_rest),
                set(Vec::new(), None),
            ));
        }
        self.defer(
            set(pattern_elements.into_iter().collect(), pattern_rest),
            set(subject_elements.into_iter().collect(), subject_rest),
        )
    }

    fn match_map_remainders(
        &mut self,
        definition: &Arc<MapDefinition>,
        pattern: MapRemainder,
        subject: MapRemainder,
    ) -> Result<Vec<(Term, Term)>, FailReason> {
        if let Some((key, _)) = pattern.concrete.first() {
            if subject.symbolic.is_empty() {
                return Err(FailReason::KeyNotFound(
                    key.clone(),
                    subject.to_term(definition.clone()),
                ));
            }
            self.defer(
                pattern.to_term(definition.clone()),
                subject.to_term(definition.clone()),
            )?;
            return Ok(Vec::new());
        }
        if pattern.symbolic.is_empty() && pattern.rest.is_none() {
            if subject.is_empty() {
                return Ok(Vec::new());
            }
            return Err(FailReason::DifferentSymbols(
                pattern.to_term(definition.clone()),
                subject.to_term(definition.clone()),
            ));
        }
        if pattern.symbolic.len() == 1
            && subject.concrete.len() + subject.symbolic.len() == 1
            && (subject.rest.is_none() || pattern.rest.is_some())
        {
            let (pattern_key, pattern_value) = pattern.symbolic[0].clone();
            let (subject_key, subject_value) = subject
                .concrete
                .first()
                .or_else(|| subject.symbolic.first())
                .unwrap()
                .clone();
            let mut problems = vec![(pattern_key, subject_key), (pattern_value, subject_value)];
            if let Some(rest) = pattern.rest {
                problems.push((
                    rest,
                    Term::map(definition.clone(), Vec::new(), subject.rest),
                ));
            }
            return Ok(problems);
        }
        if !pattern.symbolic.is_empty() {
            if subject.is_empty()
                || (pattern.rest.is_none()
                    && subject.concrete.is_empty()
                    && subject.symbolic.is_empty()
                    && subject
                        .rest
                        .as_ref()
                        .is_some_and(|term| matches!(term.kind(), TermKind::Variable(_))))
            {
                return Err(FailReason::DifferentSymbols(
                    pattern.to_term(definition.clone()),
                    subject.to_term(definition.clone()),
                ));
            }
            self.defer(
                pattern.to_term(definition.clone()),
                subject.to_term(definition.clone()),
            )?;
            return Ok(Vec::new());
        }
        let rest = pattern.rest.expect("non-empty remainder map");
        Ok(vec![(rest, subject.to_term(definition.clone()))])
    }

    fn match_variable(
        &mut self,
        variable: Variable,
        pattern: Term,
        subject: Term,
    ) -> Result<(), FailReason> {
        if let TermKind::Variable(subject_variable) = subject.kind()
            && variable.name == subject_variable.name
            && variable.sort != subject_variable.sort
        {
            return Err(FailReason::VariableConflict(
                variable.clone(),
                Term::variable(variable),
                subject,
            ));
        }
        let subject_sort = subject.sort();
        match self.sorts.check_subsort(&subject_sort, &variable.sort) {
            Ok(true) => {
                let subject = if subject_sort == variable.sort {
                    subject
                } else {
                    Term::injection(subject_sort, variable.sort.clone(), subject)
                };
                self.bind(variable, subject)
            }
            Ok(false)
                if (is_function(&subject) || matches!(subject.kind(), TermKind::Variable(_)))
                    && self.sorts.overlap(&subject_sort, &variable.sort) =>
            {
                self.defer(pattern, subject)
            }
            Ok(false) => Err(FailReason::DifferentSorts(pattern, subject)),
            Err(error) => Err(FailReason::Subsorting(error)),
        }
    }

    fn bind(&mut self, variable: Variable, term: Term) -> Result<(), FailReason> {
        if let Some(old) = self.substitution.get(&variable).cloned() {
            if old == term {
                return Ok(());
            }
            if old.attributes().constructor_like && term.attributes().constructor_like {
                return Err(FailReason::VariableConflict(variable, old, term));
            }
            return self.defer(old, term);
        }

        let term = substitute(&term, &self.substitution);
        if term.attributes().variables.contains(&variable) {
            if self.mode == MatchMode::Implies && !occurs_below_only_constructors(&variable, &term)
            {
                return self.defer(Term::variable(variable), term);
            }
            return Err(FailReason::VariableRecursion(variable, term));
        }
        let singleton = Substitution::from([(variable.clone(), term.clone())]);
        for value in self.substitution.values_mut() {
            *value = substitute(value, &singleton);
        }
        self.substitution.insert(variable, term);
        Ok(())
    }

    fn enqueue(&mut self, pattern: Term, subject: Term) {
        self.queue.push_back((pattern, subject));
    }

    fn defer(&mut self, pattern: Term, subject: Term) -> Result<(), FailReason> {
        self.indeterminate.push((pattern, subject));
        Ok(())
    }
}

/// Return whether an occurrence of `variable` is reachable through only rigid constructors and
/// sort injections. Such an occurrence makes a finite constructor term cyclic and therefore
/// unsatisfiable. Occurrences below functions or internal collections may disappear during
/// simplification, so implication matching retains those as equality conditions instead.
fn occurs_below_only_constructors(variable: &Variable, term: &Term) -> bool {
    match term.kind() {
        TermKind::Variable(found) => found == variable,
        TermKind::Injection { term, .. } => occurs_below_only_constructors(variable, term),
        TermKind::Application {
            symbol, arguments, ..
        } if symbol.attributes.symbol_type == SymbolType::Constructor => arguments
            .iter()
            .any(|argument| occurs_below_only_constructors(variable, argument)),
        TermKind::And(..)
        | TermKind::Application { .. }
        | TermKind::DomainValue { .. }
        | TermKind::Map { .. }
        | TermKind::List { .. }
        | TermKind::Set { .. } => false,
    }
}

struct OverloadView {
    original_sort: Sort,
    symbol: Arc<crate::term::Symbol>,
    sort_arguments: Vec<Sort>,
    arguments: Vec<Term>,
}

impl OverloadView {
    fn new(term: &Term) -> Option<Self> {
        let original_sort = term.sort();
        let application = match term.kind() {
            TermKind::Application { .. } => term,
            TermKind::Injection { term, .. } => term,
            _ => return None,
        };
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = application.kind()
        else {
            return None;
        };
        Some(Self {
            original_sort,
            symbol: symbol.clone(),
            sort_arguments: sort_arguments.clone(),
            arguments: arguments.clone(),
        })
    }

    fn lift(
        &self,
        common: Arc<crate::term::Symbol>,
        sort_arguments: &[Sort],
        sorts: &SortGraph,
    ) -> Option<Term> {
        if self.arguments.len() != common.argument_sorts.len()
            || sort_arguments.len() != common.sort_variables.len()
        {
            return None;
        }
        let parameters = common
            .sort_variables
            .iter()
            .cloned()
            .zip(sort_arguments.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        let arguments = self
            .arguments
            .iter()
            .zip(&common.argument_sorts)
            .map(|(argument, expected)| {
                let expected = substitute_sort_parameters(expected, &parameters);
                inject_to_sort(argument.clone(), expected, sorts)
            })
            .collect::<Option<Vec<_>>>()?;
        let application = Term::application(common, sort_arguments.to_vec(), arguments);
        inject_to_sort(application, self.original_sort.clone(), sorts)
    }
}

fn inject_to_sort(term: Term, target: Sort, sorts: &SortGraph) -> Option<Term> {
    let source = term.sort();
    if source == target {
        return Some(term);
    }
    sorts
        .check_subsort(&source, &target)
        .ok()?
        .then(|| Term::injection(source, target, term))
}

fn substitute_sort_parameters(sort: &Sort, parameters: &BTreeMap<Name, Sort>) -> Sort {
    match sort {
        Sort::Variable(name) => parameters
            .get(name)
            .cloned()
            .unwrap_or_else(|| sort.clone()),
        Sort::Application { name, arguments } => Sort::Application {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_sort_parameters(argument, parameters))
                .collect(),
        },
    }
}

enum PairRemainder {
    Left(Vec<Term>),
    Right(Vec<Term>),
}

fn pair_prefix(left: &[Term], right: &[Term]) -> (Vec<(Term, Term)>, Option<PairRemainder>) {
    let common = left.len().min(right.len());
    let pairs = left[..common]
        .iter()
        .cloned()
        .zip(right[..common].iter().cloned())
        .collect();
    let remainder = if left.len() > common {
        Some(PairRemainder::Left(left[common..].to_vec()))
    } else if right.len() > common {
        Some(PairRemainder::Right(right[common..].to_vec()))
    } else {
        None
    };
    (pairs, remainder)
}

fn pair_suffix(left: &[Term], right: &[Term]) -> (Vec<(Term, Term)>, Option<PairRemainder>) {
    let common = left.len().min(right.len());
    let pairs = left[left.len() - common..]
        .iter()
        .cloned()
        .zip(right[right.len() - common..].iter().cloned())
        .collect();
    let remainder = if left.len() > common {
        Some(PairRemainder::Left(left[..left.len() - common].to_vec()))
    } else if right.len() > common {
        Some(PairRemainder::Right(right[..right.len() - common].to_vec()))
    } else {
        None
    };
    (pairs, remainder)
}

fn prepend(pair: (Term, Term), mut pairs: Vec<(Term, Term)>) -> Vec<(Term, Term)> {
    pairs.insert(0, pair);
    pairs
}

struct MapRemainder {
    concrete: Vec<(Term, Term)>,
    symbolic: Vec<(Term, Term)>,
    rest: Option<Term>,
}

impl MapRemainder {
    fn new(entries: Vec<(Term, Term)>, rest: Option<Term>) -> Self {
        let (concrete, symbolic) = entries
            .into_iter()
            .partition(|(key, _)| key.attributes().constructor_like);
        Self {
            concrete,
            symbolic,
            rest,
        }
    }

    fn is_empty(&self) -> bool {
        self.concrete.is_empty() && self.symbolic.is_empty() && self.rest.is_none()
    }

    fn to_term(&self, definition: Arc<MapDefinition>) -> Term {
        let entries = self
            .concrete
            .iter()
            .chain(&self.symbolic)
            .cloned()
            .collect();
        Term::map(definition, entries, self.rest.clone())
    }
}

fn check_duplicate_keys(
    definition: &Arc<MapDefinition>,
    entries: &[(Term, Term)],
    rest: &Option<Term>,
) -> Result<(), FailReason> {
    let mut counts = BTreeMap::new();
    for (key, _) in entries {
        *counts.entry(key.clone()).or_insert(0usize) += 1;
    }
    if let Some((key, _)) = counts.into_iter().find(|(_, count)| *count > 1) {
        return Err(FailReason::DuplicateKeys(
            key,
            Term::map(definition.clone(), entries.to_vec(), rest.clone()),
        ));
    }
    Ok(())
}

fn is_constructor(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::Application { symbol, .. }
            if symbol.attributes.symbol_type == SymbolType::Constructor
    )
}

fn is_function(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::Application { symbol, .. }
            if matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
    )
}

fn is_collection(kind: &TermKind) -> bool {
    matches!(
        kind,
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. }
    )
}

fn is_rigid(kind: &TermKind) -> bool {
    matches!(
        kind,
        TermKind::DomainValue { .. }
            | TermKind::Injection { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. }
    ) || matches!(
        kind,
        TermKind::Application { symbol, .. }
            if symbol.attributes.symbol_type == SymbolType::Constructor
    )
}

fn is_overload_head(definition: Option<&BackendDefinition>, kind: &TermKind) -> bool {
    let (Some(definition), TermKind::Application { symbol, .. }) = (definition, kind) else {
        return false;
    };
    definition.overloads.is_overloaded(&symbol.name)
}

fn same_collection_category(left: &TermKind, right: &TermKind) -> bool {
    matches!(
        (left, right),
        (TermKind::Map { .. }, TermKind::Map { .. })
            | (TermKind::List { .. }, TermKind::List { .. })
            | (TermKind::Set { .. }, TermKind::Set { .. })
    )
}

fn collection_definition_matches(left: &TermKind, right: &TermKind) -> bool {
    match (left, right) {
        (
            TermKind::Map {
                definition: left, ..
            },
            TermKind::Map {
                definition: right, ..
            },
        ) => left == right,
        (
            TermKind::List {
                definition: left, ..
            },
            TermKind::List {
                definition: right, ..
            },
        )
        | (
            TermKind::Set {
                definition: left, ..
            },
            TermKind::Set {
                definition: right, ..
            },
        ) => left == right,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use k_rust_kore::kore::parser::parse_definition;

    use crate::term::{
        CollectionSymbols, FunctionType, ListDefinition, MapDefinition, Symbol, SymbolAttributes,
    };

    use super::*;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Outcome {
        Success,
        Failed,
        Indeterminate,
    }

    fn outcome(result: MatchResult) -> Outcome {
        match result {
            MatchResult::Success(_) => Outcome::Success,
            MatchResult::Failed(_) => Outcome::Failed,
            MatchResult::Indeterminate { .. } => Outcome::Indeterminate,
        }
    }

    fn sort() -> Sort {
        Sort::simple("SomeSort")
    }

    fn subsort() -> Sort {
        Sort::simple("ASubsort")
    }

    fn variable(name: &str, sort: Sort) -> Variable {
        Variable::new(name, sort)
    }

    fn var(name: &str, sort: Sort) -> Term {
        Term::variable(variable(name, sort))
    }

    fn domain_value(sort: Sort, value: &str) -> Term {
        Term::domain_value(sort, value)
    }

    fn constructor() -> Arc<Symbol> {
        Arc::new(Symbol::constructor("con1", vec![sort()], sort()))
    }

    fn function() -> Arc<Symbol> {
        Arc::new(Symbol {
            name: "f1".into(),
            sort_variables: Vec::new(),
            argument_sorts: vec![sort()],
            result_sort: sort(),
            attributes: SymbolAttributes {
                symbol_type: SymbolType::Function(FunctionType::Total),
                injective: false,
                associative: false,
                idempotent: false,
                macro_or_alias: false,
                has_evaluators: true,
                smt: None,
                hook: None,
                collection: None,
            },
        })
    }

    fn injective_function() -> Arc<Symbol> {
        let mut symbol = (*function()).clone();
        symbol.name = "injective".into();
        symbol.attributes.injective = true;
        Arc::new(symbol)
    }

    fn application(symbol: Arc<Symbol>, argument: Term) -> Term {
        Term::application(symbol, Vec::new(), vec![argument])
    }

    fn collection_symbols(prefix: &str) -> CollectionSymbols {
        CollectionSymbols {
            unit: format!("{prefix}Unit").into(),
            element: format!("{prefix}Element").into(),
            concat: format!("{prefix}Concat").into(),
        }
    }

    fn map_definition() -> Arc<MapDefinition> {
        Arc::new(MapDefinition {
            symbols: collection_symbols("map"),
            key_sort: "MapKey".into(),
            value_sort: "MapValue".into(),
            map_sort: "MapSort".into(),
        })
    }

    fn list_definition() -> Arc<ListDefinition> {
        Arc::new(ListDefinition {
            symbols: collection_symbols("list"),
            element_sort: "SomeSort".into(),
            list_sort: "ListSort".into(),
        })
    }

    fn set_definition() -> Arc<crate::term::SetDefinition> {
        Arc::new(crate::term::SetDefinition {
            symbols: collection_symbols("set"),
            element_sort: "SetElement".into(),
            list_sort: "SetSort".into(),
        })
    }

    fn kinds() -> Vec<(&'static str, Term, Term)> {
        let subject_constructor = application(constructor(), domain_value(sort(), "constructor"));
        let map_definition = map_definition();
        let list_definition = list_definition();
        let set_definition = set_definition();
        vec![
            (
                "And",
                Term::and(var("P1", sort()), var("P2", sort())),
                Term::and(subject_constructor.clone(), subject_constructor.clone()),
            ),
            (
                "DomainValue",
                domain_value(sort(), "domain"),
                domain_value(sort(), "domain"),
            ),
            (
                "Injection",
                Term::injection(subsort(), sort(), var("PI", subsort())),
                Term::injection(subsort(), sort(), domain_value(subsort(), "injected")),
            ),
            (
                "Map",
                Term::map(map_definition.clone(), Vec::new(), None),
                Term::map(map_definition, Vec::new(), None),
            ),
            (
                "List",
                Term::list(list_definition.clone(), Vec::new(), None),
                Term::list(list_definition, Vec::new(), None),
            ),
            (
                "Set",
                Term::set(set_definition.clone(), Vec::new(), None),
                Term::set(set_definition, Vec::new(), None),
            ),
            (
                "Constructor",
                application(constructor(), var("PC", sort())),
                subject_constructor,
            ),
            (
                "Function",
                application(function(), var("PF", sort())),
                application(function(), domain_value(sort(), "function")),
            ),
            ("Variable", var("PX", sort()), var("SY", sort())),
        ]
    }

    fn sort_graph() -> SortGraph {
        let mut graph = SortGraph::default();
        graph.insert("SomeSort", [Name::from("ASubsort")]);
        graph.insert("ASubsort", []);
        for name in ["MapKey", "MapValue", "MapSort", "ListSort", "SetSort"] {
            graph.insert(name, []);
        }
        graph
    }

    fn overload_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortSub{} [hasDomainValues{}()]
                sort SortLeft{} []
                sort SortRight{} []
                sort SortTop{} []
                symbol lower{}(SortSub{}) : SortSub{} [constructor{}()]
                symbol upper{}(SortTop{}) : SortTop{} [constructor{}()]
                symbol left{}(SortLeft{}) : SortLeft{} [constructor{}()]
                symbol right{}(SortRight{}) : SortRight{} [constructor{}()]
                symbol common{}(SortTop{}) : SortTop{} [constructor{}()]
                axiom{R} \equals{SortTop{}, R}(
                    upper{}(X:SortTop{}),
                    inj{SortSub{}, SortTop{}}(lower{}(Y:SortSub{}))
                ) [symbol-overload{}(upper{}(), lower{}())]
                axiom{R} \equals{SortTop{}, R}(
                    common{}(X:SortTop{}),
                    inj{SortLeft{}, SortTop{}}(left{}(Y:SortLeft{}))
                ) [symbol-overload{}(common{}(), left{}())]
                axiom{R} \equals{SortTop{}, R}(
                    common{}(X:SortTop{}),
                    inj{SortRight{}, SortTop{}}(right{}(Y:SortRight{}))
                ) [symbol-overload{}(common{}(), right{}())]
            endmodule []"#,
        )
        .expect("overload definition should parse");
        let mut definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("overload definition should internalize");
        definition.sort_graph.insert(
            "SortTop",
            [
                Name::from("SortSub"),
                Name::from("SortLeft"),
                Name::from("SortRight"),
            ],
        );
        definition
            .sort_graph
            .insert("SortLeft", [Name::from("SortSub")]);
        definition
            .sort_graph
            .insert("SortRight", [Name::from("SortSub")]);
        definition
    }

    fn expected(mode: MatchMode) -> [[Outcome; 9]; 9] {
        use Outcome::{Failed as F, Indeterminate as I, Success as S};
        match mode {
            MatchMode::Rewrite => [
                [S, S, S, F, F, F, S, S, S],
                [F, S, F, F, F, F, F, I, I],
                [F, F, S, F, F, F, F, I, I],
                [F, F, F, S, F, F, F, I, I],
                [F, F, F, F, S, F, F, I, I],
                [F, F, F, F, F, S, F, I, I],
                [S, F, F, F, F, F, S, I, I],
                [I, I, I, I, I, I, I, I, I],
                [S, S, S, F, F, F, S, S, S],
            ],
            MatchMode::Evaluate => [
                [I, S, S, F, F, F, S, S, I],
                [I, S, F, F, F, F, F, I, I],
                [I, F, S, I, I, I, F, I, I],
                [I, F, I, S, F, F, F, I, I],
                [I, F, I, F, S, F, F, I, I],
                [I, F, I, F, F, S, F, I, I],
                [I, F, F, F, F, F, S, I, I],
                [I, I, I, I, I, I, I, S, I],
                [I, S, S, F, F, F, S, S, S],
            ],
            MatchMode::Implies => [
                [S, S, S, F, F, F, S, S, S],
                [F, S, F, F, F, F, F, I, I],
                [F, F, S, F, F, F, F, I, I],
                [F, F, F, S, F, F, F, I, I],
                [F, F, F, F, S, F, F, I, I],
                [F, F, F, F, F, S, F, I, I],
                [S, F, F, F, F, F, S, I, I],
                [I, I, I, I, I, I, I, I, I],
                [S, S, S, F, F, F, S, S, S],
            ],
        }
    }

    #[test]
    fn matches_the_reference_dispatch_grid() {
        let kinds = kinds();
        let sorts = sort_graph();
        for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
            for ((pattern_name, pattern, _), expected_row) in kinds.iter().zip(expected(mode)) {
                for ((subject_name, _, subject), expected) in kinds.iter().zip(expected_row) {
                    assert_eq!(
                        outcome(match_terms(mode, &sorts, pattern, subject)),
                        expected,
                        "{mode:?}: {pattern_name} vs {subject_name}"
                    );
                }
            }
        }
    }

    #[test]
    fn returns_the_reference_oriented_substitution() {
        let pattern = application(constructor(), var("X", sort()));
        let subject = application(constructor(), domain_value(sort(), "value"));
        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([(
                variable("X", sort()),
                domain_value(sort(), "value"),
            )]))
        );
    }

    #[test]
    fn identical_shared_variables_match_without_a_binding() {
        let term = Term::variable(variable("X", sort()));

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &term, &term),
            MatchResult::Success(Substitution::new())
        );
    }

    #[test]
    fn decomposes_matching_injective_functions_during_rewriting() {
        let symbol = injective_function();
        let variable = variable("X", sort());
        let value = domain_value(sort(), "value");
        let pattern = application(symbol.clone(), Term::variable(variable.clone()));
        let subject = application(symbol, value.clone());

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([(variable, value)]))
        );
    }

    #[test]
    fn lifts_a_direct_overload_across_a_sort_injection() {
        let definition = overload_definition();
        let variable = Variable::new("X", Sort::simple("SortTop"));
        let pattern = Term::application(
            definition.symbols["upper"].clone(),
            Vec::new(),
            vec![Term::variable(variable.clone())],
        );
        let value = Term::domain_value(Sort::simple("SortSub"), "value");
        let subject = Term::injection(
            Sort::simple("SortSub"),
            Sort::simple("SortTop"),
            Term::application(
                definition.symbols["lower"].clone(),
                Vec::new(),
                vec![value.clone()],
            ),
        );

        assert_eq!(
            match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject),
            MatchResult::Success(Substitution::from([(
                variable,
                Term::injection(Sort::simple("SortSub"), Sort::simple("SortTop"), value,),
            )]))
        );
    }

    #[test]
    fn rejects_a_rigid_domain_value_outside_an_overload_family() {
        let definition = overload_definition();
        let pattern = Term::application(
            definition.symbols["upper"].clone(),
            Vec::new(),
            vec![Term::variable(Variable::new("X", Sort::simple("SortTop")))],
        );
        let subject = Term::injection(
            Sort::simple("SortSub"),
            Sort::simple("SortTop"),
            Term::domain_value(Sort::simple("SortSub"), "value"),
        );

        assert!(matches!(
            match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject),
            MatchResult::Failed(FailReason::DifferentSymbols(..))
        ));
    }

    #[test]
    fn lifts_a_direct_overload_in_the_pattern_orientation() {
        let definition = overload_definition();
        let variable = Variable::new("X", Sort::simple("SortSub"));
        let pattern = Term::injection(
            Sort::simple("SortSub"),
            Sort::simple("SortTop"),
            Term::application(
                definition.symbols["lower"].clone(),
                Vec::new(),
                vec![Term::variable(variable.clone())],
            ),
        );
        let value = Term::domain_value(Sort::simple("SortSub"), "value");
        let subject = Term::application(
            definition.symbols["upper"].clone(),
            Vec::new(),
            vec![Term::injection(
                Sort::simple("SortSub"),
                Sort::simple("SortTop"),
                value.clone(),
            )],
        );

        assert_eq!(
            match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject),
            MatchResult::Success(Substitution::from([(variable, value)]))
        );
    }

    #[test]
    fn lifts_incomparable_symbols_to_their_unique_common_overload() {
        let definition = overload_definition();
        let variable = Variable::new("X", Sort::simple("SortSub"));
        let pattern = Term::injection(
            Sort::simple("SortLeft"),
            Sort::simple("SortTop"),
            Term::application(
                definition.symbols["left"].clone(),
                Vec::new(),
                vec![Term::injection(
                    Sort::simple("SortSub"),
                    Sort::simple("SortLeft"),
                    Term::variable(variable.clone()),
                )],
            ),
        );
        let value = Term::domain_value(Sort::simple("SortSub"), "value");
        let subject = Term::injection(
            Sort::simple("SortRight"),
            Sort::simple("SortTop"),
            Term::application(
                definition.symbols["right"].clone(),
                Vec::new(),
                vec![Term::injection(
                    Sort::simple("SortSub"),
                    Sort::simple("SortRight"),
                    value.clone(),
                )],
            ),
        );

        assert_eq!(
            match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject),
            MatchResult::Success(Substitution::from([(variable, value)]))
        );
    }

    #[test]
    fn matches_concrete_list_heads() {
        let definition = list_definition();
        let first = domain_value(sort(), "first");
        let second = domain_value(sort(), "second");
        let pattern = Term::list(
            definition.clone(),
            vec![first.clone(), var("X", sort())],
            None,
        );
        let subject = Term::list(definition, vec![first, second.clone()], None);

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([(variable("X", sort()), second,)]))
        );
    }

    #[test]
    fn extracts_a_list_remainder() {
        let definition = list_definition();
        let first = domain_value(sort(), "first");
        let second = domain_value(sort(), "second");
        let remainder = variable("REST", Sort::simple("ListSort"));
        let pattern = Term::list(
            definition.clone(),
            Vec::new(),
            Some((Term::variable(remainder.clone()), Vec::new())),
        );
        let expected = Term::list(
            definition.clone(),
            vec![first.clone(), second.clone()],
            None,
        );
        let subject = Term::list(definition, vec![first, second], None);

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([(remainder, expected)]))
        );
    }

    #[test]
    fn matches_map_values_at_concrete_keys() {
        let definition = map_definition();
        let key = domain_value(Sort::simple("MapKey"), "key");
        let value = domain_value(Sort::simple("MapValue"), "value");
        let value_variable = variable("VALUE", Sort::simple("MapValue"));
        let pattern = Term::map(
            definition.clone(),
            vec![(key.clone(), Term::variable(value_variable.clone()))],
            None,
        );
        let subject = Term::map(definition, vec![(key, value.clone())], None);

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([(value_variable, value)]))
        );
    }

    #[test]
    fn matches_the_only_symbolic_map_entry() {
        let definition = map_definition();
        let key_variable = variable("KEY", Sort::simple("MapKey"));
        let value_variable = variable("VALUE", Sort::simple("MapValue"));
        let key = domain_value(Sort::simple("MapKey"), "key");
        let value = domain_value(Sort::simple("MapValue"), "value");
        let pattern = Term::map(
            definition.clone(),
            vec![(
                Term::variable(key_variable.clone()),
                Term::variable(value_variable.clone()),
            )],
            None,
        );
        let subject = Term::map(definition, vec![(key.clone(), value.clone())], None);

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([
                (key_variable, key),
                (value_variable, value),
            ]))
        );
    }

    #[test]
    fn empties_a_map_frame_after_an_unambiguous_selection() {
        let definition = map_definition();
        let key_variable = variable("KEY", Sort::simple("MapKey"));
        let value_variable = variable("VALUE", Sort::simple("MapValue"));
        let rest_variable = variable("REST", Sort::simple("MapSort"));
        let key = domain_value(Sort::simple("MapKey"), "key");
        let value = domain_value(Sort::simple("MapValue"), "value");
        let empty = Term::map(definition.clone(), Vec::new(), None);
        let pattern = Term::map(
            definition.clone(),
            vec![(
                Term::variable(key_variable.clone()),
                Term::variable(value_variable.clone()),
            )],
            Some(Term::variable(rest_variable.clone())),
        );
        let subject = Term::map(definition, vec![(key.clone(), value.clone())], None);

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([
                (key_variable, key),
                (rest_variable, empty),
                (value_variable, value),
            ]))
        );
    }

    #[test]
    fn matches_symbolic_map_entries_and_preserves_the_subject_frame() {
        let definition = map_definition();
        let key_variable = variable("KEY", Sort::simple("MapKey"));
        let value_variable = variable("VALUE", Sort::simple("MapValue"));
        let rest_variable = variable("REST", Sort::simple("MapSort"));
        let subject_key = variable("SUBJECT_KEY", Sort::simple("MapKey"));
        let subject_value = variable("SUBJECT_VALUE", Sort::simple("MapValue"));
        let subject_rest = variable("SUBJECT_REST", Sort::simple("MapSort"));
        let pattern = Term::map(
            definition.clone(),
            vec![(
                Term::variable(key_variable.clone()),
                Term::variable(value_variable.clone()),
            )],
            Some(Term::variable(rest_variable.clone())),
        );
        let subject = Term::map(
            definition.clone(),
            vec![(
                Term::variable(subject_key.clone()),
                Term::variable(subject_value.clone()),
            )],
            Some(Term::variable(subject_rest.clone())),
        );

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([
                (key_variable, Term::variable(subject_key)),
                (
                    rest_variable,
                    Term::map(definition, Vec::new(), Some(Term::variable(subject_rest)),),
                ),
                (value_variable, Term::variable(subject_value)),
            ]))
        );
    }

    #[test]
    fn enumerates_every_symbolic_map_key_selection() {
        let definition = map_definition();
        let key_variable = variable("KEY", Sort::simple("MapKey"));
        let value_variable = variable("VALUE", Sort::simple("MapValue"));
        let rest_variable = variable("REST", Sort::simple("MapSort"));
        let first_key = domain_value(Sort::simple("MapKey"), "first");
        let first_value = domain_value(Sort::simple("MapValue"), "first-value");
        let second_key = domain_value(Sort::simple("MapKey"), "second");
        let second_value = domain_value(Sort::simple("MapValue"), "second-value");
        let pattern = Term::map(
            definition.clone(),
            vec![(
                Term::variable(key_variable.clone()),
                Term::variable(value_variable.clone()),
            )],
            Some(Term::variable(rest_variable.clone())),
        );
        let subject = Term::map(
            definition.clone(),
            vec![
                (first_key.clone(), first_value.clone()),
                (second_key.clone(), second_value.clone()),
            ],
            None,
        );

        assert_eq!(
            match_map_terms_all(
                MatchMode::Rewrite,
                &sort_graph(),
                &pattern,
                &subject,
                &Substitution::new(),
            ),
            Some(vec![
                Substitution::from([
                    (key_variable.clone(), first_key.clone()),
                    (
                        rest_variable.clone(),
                        Term::map(
                            definition.clone(),
                            vec![(second_key.clone(), second_value.clone())],
                            None,
                        ),
                    ),
                    (value_variable.clone(), first_value.clone()),
                ]),
                Substitution::from([
                    (key_variable, second_key),
                    (
                        rest_variable,
                        Term::map(definition, vec![(first_key, first_value)], None),
                    ),
                    (value_variable, second_value),
                ]),
            ])
        );
    }

    #[test]
    fn carries_an_open_map_subject_frame_through_every_selection() {
        let definition = map_definition();
        let key_variable = variable("KEY", Sort::simple("MapKey"));
        let value_variable = variable("VALUE", Sort::simple("MapValue"));
        let rest_variable = variable("REST", Sort::simple("MapSort"));
        let subject_rest = variable("SUBJECT_REST", Sort::simple("MapSort"));
        let first_key = domain_value(Sort::simple("MapKey"), "first");
        let first_value = domain_value(Sort::simple("MapValue"), "first-value");
        let second_key = domain_value(Sort::simple("MapKey"), "second");
        let second_value = domain_value(Sort::simple("MapValue"), "second-value");
        let pattern = Term::map(
            definition.clone(),
            vec![(
                Term::variable(key_variable.clone()),
                Term::variable(value_variable.clone()),
            )],
            Some(Term::variable(rest_variable.clone())),
        );
        let subject = Term::map(
            definition.clone(),
            vec![
                (first_key.clone(), first_value.clone()),
                (second_key.clone(), second_value.clone()),
            ],
            Some(Term::variable(subject_rest.clone())),
        );

        assert_eq!(
            match_map_terms_all(
                MatchMode::Rewrite,
                &sort_graph(),
                &pattern,
                &subject,
                &Substitution::new(),
            ),
            Some(vec![
                Substitution::from([
                    (key_variable.clone(), first_key.clone()),
                    (
                        rest_variable.clone(),
                        Term::map(
                            definition.clone(),
                            vec![(second_key.clone(), second_value.clone())],
                            Some(Term::variable(subject_rest.clone())),
                        ),
                    ),
                    (value_variable.clone(), first_value.clone()),
                ]),
                Substitution::from([
                    (key_variable, second_key),
                    (
                        rest_variable,
                        Term::map(
                            definition,
                            vec![(first_key, first_value)],
                            Some(Term::variable(subject_rest)),
                        ),
                    ),
                    (value_variable, second_value),
                ]),
            ])
        );
    }

    #[test]
    fn enumerates_map_entry_permutations_without_splitting_values_from_keys() {
        let definition = map_definition();
        let first_key_variable = variable("KEY1", Sort::simple("MapKey"));
        let first_value_variable = variable("VALUE1", Sort::simple("MapValue"));
        let second_key_variable = variable("KEY2", Sort::simple("MapKey"));
        let second_value_variable = variable("VALUE2", Sort::simple("MapValue"));
        let first_key = domain_value(Sort::simple("MapKey"), "first");
        let first_value = domain_value(Sort::simple("MapValue"), "first-value");
        let second_key = domain_value(Sort::simple("MapKey"), "second");
        let second_value = domain_value(Sort::simple("MapValue"), "second-value");
        let pattern = Term::map(
            definition.clone(),
            vec![
                (
                    Term::variable(first_key_variable.clone()),
                    Term::variable(first_value_variable.clone()),
                ),
                (
                    Term::variable(second_key_variable.clone()),
                    Term::variable(second_value_variable.clone()),
                ),
            ],
            None,
        );
        let subject = Term::map(
            definition,
            vec![
                (first_key.clone(), first_value.clone()),
                (second_key.clone(), second_value.clone()),
            ],
            None,
        );

        assert_eq!(
            match_map_terms_all(
                MatchMode::Rewrite,
                &sort_graph(),
                &pattern,
                &subject,
                &Substitution::new(),
            ),
            Some(vec![
                Substitution::from([
                    (first_key_variable.clone(), first_key.clone()),
                    (first_value_variable.clone(), first_value.clone()),
                    (second_key_variable.clone(), second_key.clone()),
                    (second_value_variable.clone(), second_value.clone()),
                ]),
                Substitution::from([
                    (first_key_variable, second_key),
                    (first_value_variable, second_value),
                    (second_key_variable, first_key),
                    (second_value_variable, first_value),
                ]),
            ])
        );
    }

    #[test]
    fn extracts_a_map_remainder_after_common_keys() {
        let definition = map_definition();
        let common_key = domain_value(Sort::simple("MapKey"), "common");
        let extra_key = domain_value(Sort::simple("MapKey"), "extra");
        let common_value = domain_value(Sort::simple("MapValue"), "common-value");
        let extra_value = domain_value(Sort::simple("MapValue"), "extra-value");
        let remainder = variable("REST", Sort::simple("MapSort"));
        let pattern = Term::map(
            definition.clone(),
            vec![(common_key.clone(), common_value.clone())],
            Some(Term::variable(remainder.clone())),
        );
        let expected = Term::map(
            definition.clone(),
            vec![(extra_key.clone(), extra_value.clone())],
            None,
        );
        let subject = Term::map(
            definition,
            vec![(common_key, common_value), (extra_key, extra_value)],
            None,
        );

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([(remainder, expected)]))
        );
    }

    #[test]
    fn matches_identical_concrete_sets_independent_of_input_order() {
        let definition = set_definition();
        let first = domain_value(Sort::simple("SetElement"), "first");
        let second = domain_value(Sort::simple("SetElement"), "second");
        let pattern = Term::set(
            definition.clone(),
            vec![first.clone(), second.clone()],
            None,
        );
        let subject = Term::set(definition, vec![second, first], None);

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::new())
        );
    }

    #[test]
    fn extracts_a_set_remainder_after_common_elements() {
        let definition = set_definition();
        let common = domain_value(Sort::simple("SetElement"), "common");
        let extra = domain_value(Sort::simple("SetElement"), "extra");
        let remainder = variable("REST", Sort::simple("SetSort"));
        let pattern = Term::set(
            definition.clone(),
            vec![common.clone()],
            Some(Term::variable(remainder.clone())),
        );
        let expected = Term::set(definition.clone(), vec![extra.clone()], None);
        let subject = Term::set(definition, vec![common, extra], None);

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([(remainder, expected)]))
        );
    }

    #[test]
    fn matches_an_unambiguous_symbolic_set_element() {
        let definition = set_definition();
        let element_variable = variable("ELEMENT", Sort::simple("SetElement"));
        let element = domain_value(Sort::simple("SetElement"), "element");
        let pattern = Term::set(
            definition.clone(),
            vec![Term::variable(element_variable.clone())],
            None,
        );
        let subject = Term::set(definition, vec![element.clone()], None);

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([(element_variable, element)]))
        );
    }

    #[test]
    fn empties_a_set_frame_after_an_unambiguous_selection() {
        let definition = set_definition();
        let element_variable = variable("ELEMENT", Sort::simple("SetElement"));
        let rest_variable = variable("REST", Sort::simple("SetSort"));
        let element = domain_value(Sort::simple("SetElement"), "element");
        let empty = Term::set(definition.clone(), Vec::new(), None);
        let pattern = Term::set(
            definition.clone(),
            vec![Term::variable(element_variable.clone())],
            Some(Term::variable(rest_variable.clone())),
        );
        let subject = Term::set(definition, vec![element.clone()], None);

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([
                (element_variable, element),
                (rest_variable, empty),
            ]))
        );
    }

    #[test]
    fn matches_symbolic_set_elements_and_preserves_the_subject_frame() {
        let definition = set_definition();
        let element_variable = variable("ELEMENT", Sort::simple("SetElement"));
        let rest_variable = variable("REST", Sort::simple("SetSort"));
        let subject_element = variable("SUBJECT_ELEMENT", Sort::simple("SetElement"));
        let subject_rest = variable("SUBJECT_REST", Sort::simple("SetSort"));
        let pattern = Term::set(
            definition.clone(),
            vec![Term::variable(element_variable.clone())],
            Some(Term::variable(rest_variable.clone())),
        );
        let subject = Term::set(
            definition.clone(),
            vec![Term::variable(subject_element.clone())],
            Some(Term::variable(subject_rest.clone())),
        );

        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([
                (element_variable, Term::variable(subject_element)),
                (
                    rest_variable,
                    Term::set(definition, Vec::new(), Some(Term::variable(subject_rest)),),
                ),
            ]))
        );
    }

    #[test]
    fn defers_ambiguous_symbolic_set_selection() {
        let definition = set_definition();
        let pattern = Term::set(
            definition.clone(),
            vec![var("ELEMENT", Sort::simple("SetElement"))],
            Some(var("REST", Sort::simple("SetSort"))),
        );
        let subject = Term::set(
            definition,
            vec![
                domain_value(Sort::simple("SetElement"), "first"),
                domain_value(Sort::simple("SetElement"), "second"),
            ],
            None,
        );

        assert!(matches!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Indeterminate { remainder, .. } if remainder == vec![(pattern, subject)]
        ));
    }

    #[test]
    fn enumerates_every_symbolic_set_selection() {
        let definition = set_definition();
        let element_variable = variable("ELEMENT", Sort::simple("SetElement"));
        let rest_variable = variable("REST", Sort::simple("SetSort"));
        let first = domain_value(Sort::simple("SetElement"), "first");
        let second = domain_value(Sort::simple("SetElement"), "second");
        let pattern = Term::set(
            definition.clone(),
            vec![Term::variable(element_variable.clone())],
            Some(Term::variable(rest_variable.clone())),
        );
        let subject = Term::set(
            definition.clone(),
            vec![first.clone(), second.clone()],
            None,
        );

        assert_eq!(
            match_set_terms_all(
                MatchMode::Rewrite,
                &sort_graph(),
                &pattern,
                &subject,
                &Substitution::new(),
            ),
            Some(vec![
                Substitution::from([
                    (element_variable.clone(), first.clone()),
                    (
                        rest_variable.clone(),
                        Term::set(definition.clone(), vec![second.clone()], None),
                    ),
                ]),
                Substitution::from([
                    (element_variable, second),
                    (rest_variable, Term::set(definition, vec![first], None)),
                ]),
            ])
        );
    }

    #[test]
    fn carries_an_open_set_subject_frame_through_every_selection() {
        let definition = set_definition();
        let element_variable = variable("ELEMENT", Sort::simple("SetElement"));
        let rest_variable = variable("REST", Sort::simple("SetSort"));
        let subject_rest = variable("SUBJECT_REST", Sort::simple("SetSort"));
        let first = domain_value(Sort::simple("SetElement"), "first");
        let second = domain_value(Sort::simple("SetElement"), "second");
        let pattern = Term::set(
            definition.clone(),
            vec![Term::variable(element_variable.clone())],
            Some(Term::variable(rest_variable.clone())),
        );
        let subject = Term::set(
            definition.clone(),
            vec![first.clone(), second.clone()],
            Some(Term::variable(subject_rest.clone())),
        );

        assert_eq!(
            match_set_terms_all(
                MatchMode::Rewrite,
                &sort_graph(),
                &pattern,
                &subject,
                &Substitution::new(),
            ),
            Some(vec![
                Substitution::from([
                    (element_variable.clone(), first.clone()),
                    (
                        rest_variable.clone(),
                        Term::set(
                            definition.clone(),
                            vec![second.clone()],
                            Some(Term::variable(subject_rest.clone())),
                        ),
                    ),
                ]),
                Substitution::from([
                    (element_variable, second),
                    (
                        rest_variable,
                        Term::set(definition, vec![first], Some(Term::variable(subject_rest)),),
                    ),
                ]),
            ])
        );
    }

    #[test]
    fn enumerates_set_element_permutations_without_reuse() {
        let definition = set_definition();
        let first_variable = variable("FIRST", Sort::simple("SetElement"));
        let second_variable = variable("SECOND", Sort::simple("SetElement"));
        let first = domain_value(Sort::simple("SetElement"), "first");
        let second = domain_value(Sort::simple("SetElement"), "second");
        let pattern = Term::set(
            definition.clone(),
            vec![
                Term::variable(first_variable.clone()),
                Term::variable(second_variable.clone()),
            ],
            None,
        );
        let subject = Term::set(definition, vec![first.clone(), second.clone()], None);

        assert_eq!(
            match_set_terms_all(
                MatchMode::Rewrite,
                &sort_graph(),
                &pattern,
                &subject,
                &Substitution::new(),
            ),
            Some(vec![
                Substitution::from([
                    (first_variable.clone(), first.clone()),
                    (second_variable.clone(), second.clone()),
                ]),
                Substitution::from([(first_variable, second), (second_variable, first),]),
            ])
        );
    }

    #[test]
    fn rejects_a_nonempty_pattern_against_the_empty_set() {
        let definition = set_definition();
        let pattern = Term::set(
            definition.clone(),
            vec![var("ELEMENT", Sort::simple("SetElement"))],
            Some(var("REST", Sort::simple("SetSort"))),
        );
        let subject = Term::set(definition, Vec::new(), None);

        assert!(matches!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Failed(FailReason::DifferentSymbols(_, _))
        ));
    }

    #[test]
    fn reports_duplicate_map_keys() {
        let definition = map_definition();
        let key = domain_value(Sort::simple("MapKey"), "duplicate");
        let pattern = Term::map(
            definition.clone(),
            vec![
                (key.clone(), domain_value(Sort::simple("MapValue"), "one")),
                (key.clone(), domain_value(Sort::simple("MapValue"), "two")),
            ],
            None,
        );
        let subject = Term::map(definition, Vec::new(), None);

        assert!(matches!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Failed(FailReason::DuplicateKeys(found, _)) if found == key
        ));
    }
}
