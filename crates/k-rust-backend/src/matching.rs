//! Sort-aware one-way matching for rewrite rules and equations.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
};

use crate::{
    substitution::{Substitution, substitute},
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

struct Matcher<'a> {
    mode: MatchMode,
    sorts: &'a SortGraph,
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
            ) if left == right
                && left_elements.is_empty()
                && right_elements.is_empty()
                && left_rest.is_none()
                && right_rest.is_none() =>
            {
                Ok(())
            }
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
            && pattern.rest.is_none()
            && subject.rest.is_none()
            && subject.concrete.len() + subject.symbolic.len() == 1
        {
            let (pattern_key, pattern_value) = pattern.symbolic[0].clone();
            let (subject_key, subject_value) = subject
                .concrete
                .first()
                .or_else(|| subject.symbolic.first())
                .unwrap()
                .clone();
            return Ok(vec![
                (pattern_key, subject_key),
                (pattern_value, subject_value),
            ]);
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

    fn kinds() -> Vec<(&'static str, Term, Term)> {
        let subject_constructor = application(constructor(), domain_value(sort(), "constructor"));
        let map_definition = map_definition();
        let list_definition = list_definition();
        let set_definition = Arc::new(ListDefinition {
            symbols: collection_symbols("set"),
            element_sort: "SetElement".into(),
            list_sort: "SetSort".into(),
        });
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
