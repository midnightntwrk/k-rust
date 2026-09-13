//! Sort-aware one-way matching for rewrite rules and equations.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
};

use k_rust_kore::measure::{self, Counter};

use crate::{
    builtin::{BuiltinResult, evaluate_hook},
    definition::BackendDefinition,
    rule::Predicate,
    substitution::{Substitution, compose, substitute},
    term::{ListDefinition, MapDefinition, Name, Sort, SymbolType, Term, TermKind, Variable},
    unification::{UnificationResult, unify_term_pairs},
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

    pub(crate) fn subsorts_of(&self, sort: &Sort) -> Option<&BTreeSet<Name>> {
        let Sort::Application { name, arguments } = sort else {
            return None;
        };
        arguments
            .is_empty()
            .then(|| self.subsorts.get(name))
            .flatten()
    }

    fn overlap(&self, left: &Sort, right: &Sort) -> bool {
        self.known_overlap(left, right).unwrap_or(true)
    }

    fn known_overlap(&self, left: &Sort, right: &Sort) -> Option<bool> {
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
            return None;
        };
        if !left_arguments.is_empty() || !right_arguments.is_empty() {
            return None;
        }
        match (self.subsorts.get(left), self.subsorts.get(right)) {
            (Some(left), Some(right)) => Some(!left.is_disjoint(right)),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum InjectionEquality {
    Direct(Term, Term),
    Split(Term, Term),
    Distinct,
    Unknown,
}

pub(crate) fn match_injection_equality(
    sorts: Option<&SortGraph>,
    left: &Term,
    right: &Term,
) -> Option<InjectionEquality> {
    let (
        TermKind::Injection {
            source: left_source,
            target: left_target,
            term: left,
        },
        TermKind::Injection {
            source: right_source,
            target: right_target,
            term: right,
        },
    ) = (left.kind(), right.kind())
    else {
        return None;
    };
    if left_target != right_target {
        return Some(InjectionEquality::Distinct);
    }
    if left_source == right_source {
        return Some(InjectionEquality::Direct(left.clone(), right.clone()));
    }
    if let Some(sorts) = sorts {
        if sorts.check_subsort(right_source, left_source).ok() == Some(true) {
            return Some(InjectionEquality::Split(
                left.clone(),
                Term::injection(right_source.clone(), left_source.clone(), right.clone()),
            ));
        }
        if sorts.check_subsort(left_source, right_source).ok() == Some(true) {
            return Some(InjectionEquality::Split(
                Term::injection(left_source.clone(), right_source.clone(), left.clone()),
                right.clone(),
            ));
        }
    }
    if has_constructor_like_top(left) || has_constructor_like_top(right) {
        return Some(InjectionEquality::Distinct);
    }
    if let Some(sorts) = sorts
        && let (Some(left), Some(right)) = (
            sorts.subsorts_of(left_source),
            sorts.subsorts_of(right_source),
        )
        && left.is_disjoint(right)
    {
        return Some(InjectionEquality::Distinct);
    }
    Some(InjectionEquality::Unknown)
}

fn has_constructor_like_top(term: &Term) -> bool {
    term.attributes().constructor_like
        || matches!(
            term.kind(),
            TermKind::Application { symbol, .. }
                if symbol.attributes.symbol_type == SymbolType::Constructor
        )
        || matches!(
            term.kind(),
            TermKind::Injection { .. }
                | TermKind::Map { .. }
                | TermKind::List { .. }
                | TermKind::Set { .. }
        )
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
            // Matching binds pattern variables only; a variable on both sides needs
            // unification. The pairs themselves are the remainder, so that the caller can
            // unify them or solve them as collections.
            MatchMode::Rewrite => MatchResult::Indeterminate {
                substitution: Substitution::new(),
                remainder: pairs,
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
    measure::bump(Counter::MatchingProblems);
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
            // As in `match_term_pairs_in_definition`: the pair is the remainder, not a
            // placeholder over the shared variables, which would drop the pair.
            MatchMode::Rewrite => MatchResult::Indeterminate {
                substitution: Substitution::new(),
                remainder: vec![(pattern.clone(), subject.clone())],
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

/// One solution for a set of deferred collection pairs.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct CollectionSolution {
    /// Rule-variable bindings plus any subject variables narrowed by the solution.
    pub substitution: Substitution,
    /// Irreducible equalities discovered while pairing collection elements.
    pub constraints: Vec<Predicate>,
    /// Fresh collection remainders introduced while narrowing a subject frame.
    pub fresh: BTreeSet<Variable>,
}

/// Rewrite-side support for narrowing subject collection frames.
pub(crate) struct Narrowing<'a> {
    /// Mint a variable of the requested collection sort which is fresh in the current pattern.
    pub fresh_frame: &'a mut dyn FnMut(&Sort) -> Variable,
}

enum PairSolution {
    Solved(CollectionSolution),
    NoSolution,
    Indeterminate,
}

/// Solve deferred collection pairs in their original, pattern-oriented order.
///
/// `None` means at least one pair needs collection or term theory outside the supported fragment;
/// an empty vector means the equation is decidably bottom. Supplying [`Narrowing`] additionally
/// permits a variable frame on the subject side to absorb pattern entries.
pub(crate) fn solve_collection_pairs_in_definition(
    mode: MatchMode,
    definition: &BackendDefinition,
    initial: Substitution,
    pairs: &[(Term, Term)],
    mut narrowing: Option<&mut Narrowing<'_>>,
) -> Option<Vec<CollectionSolution>> {
    let mut solutions = vec![CollectionSolution {
        substitution: initial,
        constraints: Vec::new(),
        fresh: BTreeSet::new(),
    }];
    for (pattern, subject) in pairs {
        let mut next = Vec::new();
        for solution in solutions {
            next.extend(solve_collection_pair(
                mode,
                definition,
                pattern,
                subject,
                solution,
                &mut narrowing,
            )?);
        }
        solutions = next;
    }
    for solution in &mut solutions {
        solution.constraints.sort();
        solution.constraints.dedup();
    }
    solutions.sort();
    solutions.dedup();
    Some(solutions)
}

fn solve_collection_pair(
    mode: MatchMode,
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    solution: CollectionSolution,
    narrowing: &mut Option<&mut Narrowing<'_>>,
) -> Option<Vec<CollectionSolution>> {
    let pattern = substitute(pattern, &solution.substitution);
    let subject = substitute(subject, &solution.substitution);
    match (pattern.kind(), subject.kind()) {
        (TermKind::Map { .. }, TermKind::Map { .. }) => {
            solve_map_pair(mode, definition, &pattern, &subject, solution, narrowing)
        }
        (TermKind::Set { .. }, TermKind::Set { .. }) => {
            solve_set_pair(mode, definition, &pattern, &subject, solution, narrowing)
        }
        (TermKind::Application { .. }, TermKind::Set { .. }) if set_parts(&pattern).is_some() => {
            solve_set_pair(mode, definition, &pattern, &subject, solution, narrowing)
        }
        (TermKind::List { .. }, TermKind::List { .. }) => solve_list_pair(
            mode,
            definition,
            &pattern,
            &subject,
            solution,
            narrowing.is_some(),
        ),
        (
            TermKind::Map { .. } | TermKind::Set { .. } | TermKind::List { .. },
            TermKind::Variable(_),
        ) if narrowing.is_some() => {
            match solve_term_pair(mode, definition, solution, &pattern, &subject, true) {
                PairSolution::Solved(solution) => Some(vec![solution]),
                PairSolution::NoSolution => Some(Vec::new()),
                PairSolution::Indeterminate => None,
            }
        }
        _ => None,
    }
}

fn solve_term_pair(
    mode: MatchMode,
    definition: &BackendDefinition,
    solution: CollectionSolution,
    pattern: &Term,
    subject: &Term,
    allow_narrowing: bool,
) -> PairSolution {
    let pattern = substitute(pattern, &solution.substitution);
    let subject = substitute(subject, &solution.substitution);
    match match_terms_with_context(
        mode,
        &definition.sort_graph,
        Some(definition),
        &pattern,
        &subject,
    ) {
        MatchResult::Success(found) => PairSolution::Solved(CollectionSolution {
            substitution: compose(&found, &solution.substitution),
            ..solution
        }),
        MatchResult::Failed(_) => PairSolution::NoSolution,
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } if allow_narrowing => {
            let substitution = compose(&substitution, &solution.substitution);
            match unify_term_pairs(definition, substitution, remainder) {
                UnificationResult::Unified(unified) => {
                    let mut constraints = solution.constraints;
                    constraints.extend(unified.constraints);
                    PairSolution::Solved(CollectionSolution {
                        substitution: unified.substitution,
                        constraints,
                        fresh: solution.fresh,
                    })
                }
                UnificationResult::Bottom(_) => PairSolution::NoSolution,
                UnificationResult::Unsupported { .. } => PairSolution::Indeterminate,
            }
        }
        MatchResult::Indeterminate { .. } => PairSolution::Indeterminate,
    }
}

fn solve_list_pair(
    mode: MatchMode,
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    mut solution: CollectionSolution,
    allow_narrowing: bool,
) -> Option<Vec<CollectionSolution>> {
    match match_terms_with_context(
        mode,
        &definition.sort_graph,
        Some(definition),
        pattern,
        subject,
    ) {
        MatchResult::Success(found) => {
            solution.substitution = compose(&found, &solution.substitution);
            return Some(vec![solution]);
        }
        MatchResult::Failed(_) => return Some(Vec::new()),
        MatchResult::Indeterminate { .. } if !allow_narrowing => return None,
        MatchResult::Indeterminate {
            substitution,
            remainder: _,
        } => {
            solution.substitution = compose(&substitution, &solution.substitution);
        }
    }

    let pattern = substitute(pattern, &solution.substitution);
    let subject = substitute(subject, &solution.substitution);
    let (
        TermKind::List {
            definition: pattern_definition,
            heads: pattern_heads,
            rest: pattern_rest,
        },
        TermKind::List {
            definition: subject_definition,
            heads: subject_heads,
            rest: subject_rest,
        },
    ) = (pattern.kind(), subject.kind())
    else {
        return None;
    };
    if pattern_definition != subject_definition {
        return Some(Vec::new());
    }

    match (pattern_rest, subject_rest) {
        (None, Some((subject_middle, subject_tails))) => solve_single_list_frame(
            mode,
            definition,
            pattern_definition,
            solution,
            pattern_heads,
            subject_heads,
            subject_middle,
            subject_tails,
            true,
        ),
        (Some((pattern_middle, pattern_tails)), None) => solve_single_list_frame(
            mode,
            definition,
            pattern_definition,
            solution,
            subject_heads,
            pattern_heads,
            pattern_middle,
            pattern_tails,
            false,
        ),
        (Some((pattern_middle, pattern_tails)), Some((subject_middle, subject_tails))) => {
            solve_two_list_frames(
                mode,
                definition,
                pattern_definition,
                solution,
                pattern_heads,
                pattern_middle,
                pattern_tails,
                subject_heads,
                subject_middle,
                subject_tails,
            )
        }
        (None, None) => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn solve_single_list_frame(
    mode: MatchMode,
    backend: &BackendDefinition,
    definition: &Arc<ListDefinition>,
    solution: CollectionSolution,
    closed: &[Term],
    framed_heads: &[Term],
    frame: &Term,
    framed_tails: &[Term],
    frame_on_subject: bool,
) -> Option<Vec<CollectionSolution>> {
    if !matches!(frame.kind(), TermKind::Variable(_)) {
        return None;
    }
    let Some(frame_end) = closed.len().checked_sub(framed_tails.len()) else {
        return Some(Vec::new());
    };
    if framed_heads.len() > frame_end {
        return Some(Vec::new());
    }

    let mut pairs = Vec::with_capacity(framed_heads.len() + framed_tails.len() + 1);
    if frame_on_subject {
        pairs.extend(
            closed[..framed_heads.len()]
                .iter()
                .cloned()
                .zip(framed_heads.iter().cloned()),
        );
        pairs.extend(
            closed[frame_end..]
                .iter()
                .cloned()
                .zip(framed_tails.iter().cloned()),
        );
        pairs.push((
            Term::list(
                definition.clone(),
                closed[framed_heads.len()..frame_end].to_vec(),
                None,
            ),
            frame.clone(),
        ));
    } else {
        pairs.extend(
            framed_heads
                .iter()
                .cloned()
                .zip(closed[..framed_heads.len()].iter().cloned()),
        );
        pairs.extend(
            framed_tails
                .iter()
                .cloned()
                .zip(closed[frame_end..].iter().cloned()),
        );
        pairs.push((
            frame.clone(),
            Term::list(
                definition.clone(),
                closed[framed_heads.len()..frame_end].to_vec(),
                None,
            ),
        ));
    }
    solve_ordered_term_pairs(mode, backend, solution, pairs)
}

#[allow(clippy::too_many_arguments)]
fn solve_two_list_frames(
    mode: MatchMode,
    backend: &BackendDefinition,
    definition: &Arc<ListDefinition>,
    solution: CollectionSolution,
    pattern_heads: &[Term],
    pattern_middle: &Term,
    pattern_tails: &[Term],
    subject_heads: &[Term],
    subject_middle: &Term,
    subject_tails: &[Term],
) -> Option<Vec<CollectionSolution>> {
    if !matches!(pattern_middle.kind(), TermKind::Variable(_))
        || !matches!(subject_middle.kind(), TermKind::Variable(_))
    {
        return None;
    }
    let (mut pairs, head_remainder) = pair_prefix(pattern_heads, subject_heads);
    let (tail_pairs, tail_remainder) = pair_suffix(pattern_tails, subject_tails);
    pairs.extend(tail_pairs);
    let (pattern_extra_heads, subject_extra_heads) = match head_remainder {
        Some(PairRemainder::Left(terms)) => (terms, Vec::new()),
        Some(PairRemainder::Right(terms)) => (Vec::new(), terms),
        None => (Vec::new(), Vec::new()),
    };
    let (pattern_extra_tails, subject_extra_tails) = match tail_remainder {
        Some(PairRemainder::Left(terms)) => (terms, Vec::new()),
        Some(PairRemainder::Right(terms)) => (Vec::new(), terms),
        None => (Vec::new(), Vec::new()),
    };
    let pattern_has_extra = !pattern_extra_heads.is_empty() || !pattern_extra_tails.is_empty();
    let subject_has_extra = !subject_extra_heads.is_empty() || !subject_extra_tails.is_empty();
    if pattern_has_extra && subject_has_extra {
        return None;
    }
    let middle_pair = if pattern_has_extra {
        (
            Term::list(
                definition.clone(),
                pattern_extra_heads,
                Some((pattern_middle.clone(), pattern_extra_tails)),
            ),
            subject_middle.clone(),
        )
    } else if subject_has_extra {
        (
            pattern_middle.clone(),
            Term::list(
                definition.clone(),
                subject_extra_heads,
                Some((subject_middle.clone(), subject_extra_tails)),
            ),
        )
    } else {
        (pattern_middle.clone(), subject_middle.clone())
    };
    pairs.push(middle_pair);
    solve_ordered_term_pairs(mode, backend, solution, pairs)
}

fn solve_ordered_term_pairs(
    mode: MatchMode,
    definition: &BackendDefinition,
    mut solution: CollectionSolution,
    pairs: Vec<(Term, Term)>,
) -> Option<Vec<CollectionSolution>> {
    for (pattern, subject) in pairs {
        solution = match solve_term_pair(mode, definition, solution, &pattern, &subject, true) {
            PairSolution::Solved(solution) => solution,
            PairSolution::NoSolution => return Some(Vec::new()),
            PairSolution::Indeterminate => return None,
        };
    }
    Some(vec![solution])
}

fn solve_map_pair(
    mode: MatchMode,
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    solution: CollectionSolution,
    narrowing: &mut Option<&mut Narrowing<'_>>,
) -> Option<Vec<CollectionSolution>> {
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
        unreachable!()
    };
    if pattern_definition != subject_definition {
        return Some(Vec::new());
    }
    let pattern_entry_count = pattern_entries.len();
    let subject_entry_count = subject_entries.len();
    let mut pattern_entries = pattern_entries.iter().cloned().collect::<BTreeMap<_, _>>();
    let mut subject_entries = subject_entries.iter().cloned().collect::<BTreeMap<_, _>>();
    if pattern_entries.len() != pattern_entry_count || subject_entries.len() != subject_entry_count
    {
        return None;
    }
    let (pattern_rest, subject_rest) = cancel_common_opaque_chunks(
        pattern_rest.clone(),
        subject_rest.clone(),
        &pattern_definition.symbols.concat,
    );

    let common_keys = pattern_entries
        .keys()
        .filter(|key| subject_entries.contains_key(*key))
        .cloned()
        .collect::<Vec<_>>();
    let mut solutions = vec![solution];
    for key in common_keys {
        let pattern_value = pattern_entries.remove(&key).unwrap();
        let subject_value = subject_entries.remove(&key).unwrap();
        let mut next = Vec::new();
        for solution in solutions {
            match solve_term_pair(
                mode,
                definition,
                solution,
                &pattern_value,
                &subject_value,
                narrowing.is_some(),
            ) {
                PairSolution::Solved(solution) => next.push(solution),
                PairSolution::NoSolution => {}
                PairSolution::Indeterminate => return None,
            }
        }
        solutions = next;
    }

    measure::bump(Counter::MatchingCollectionProblems);
    let problem = MapCollectionProblem {
        mode,
        backend: definition,
        definition: pattern_definition.clone(),
        entries: pattern_entries.into_iter().collect(),
        rest: pattern_rest,
        subject_rest,
    };
    let remaining = subject_entries.into_iter().collect::<Vec<_>>();
    let mut found = Vec::new();
    let mut indeterminate = false;
    for solution in solutions {
        problem.search(
            0,
            remaining.clone(),
            Vec::new(),
            solution,
            narrowing,
            &mut found,
            &mut indeterminate,
        );
    }
    (!indeterminate).then_some(found)
}

struct MapCollectionProblem<'a> {
    mode: MatchMode,
    backend: &'a BackendDefinition,
    definition: Arc<MapDefinition>,
    entries: Vec<(Term, Term)>,
    rest: Option<Term>,
    subject_rest: Option<Term>,
}

impl MapCollectionProblem<'_> {
    #[allow(clippy::too_many_arguments)]
    fn search(
        &self,
        index: usize,
        remaining: Vec<(Term, Term)>,
        frame_entries: Vec<(Term, Term)>,
        solution: CollectionSolution,
        narrowing: &mut Option<&mut Narrowing<'_>>,
        solutions: &mut Vec<CollectionSolution>,
        indeterminate: &mut bool,
    ) {
        if index == self.entries.len() {
            self.finish(
                remaining,
                frame_entries,
                solution,
                narrowing,
                solutions,
                indeterminate,
            );
            return;
        }

        let (key, value) = &self.entries[index];
        for subject_index in 0..remaining.len() {
            let (subject_key, subject_value) = &remaining[subject_index];
            let solution = match solve_term_pair(
                self.mode,
                self.backend,
                solution.clone(),
                key,
                subject_key,
                narrowing.is_some(),
            ) {
                PairSolution::Solved(solution) => solution,
                PairSolution::NoSolution => continue,
                PairSolution::Indeterminate => {
                    *indeterminate = true;
                    continue;
                }
            };
            let solution = match solve_term_pair(
                self.mode,
                self.backend,
                solution,
                value,
                subject_value,
                narrowing.is_some(),
            ) {
                PairSolution::Solved(solution) => solution,
                PairSolution::NoSolution => continue,
                PairSolution::Indeterminate => {
                    *indeterminate = true;
                    continue;
                }
            };
            let mut next_remaining = remaining.clone();
            next_remaining.remove(subject_index);
            self.search(
                index + 1,
                next_remaining,
                frame_entries.clone(),
                solution,
                narrowing,
                solutions,
                indeterminate,
            );
        }

        if narrowing.is_some()
            && matches!(
                self.subject_rest.as_ref().map(Term::kind),
                Some(TermKind::Variable(_))
            )
        {
            let mut frame_entries = frame_entries;
            frame_entries.push((key.clone(), value.clone()));
            self.search(
                index + 1,
                remaining,
                frame_entries,
                solution,
                narrowing,
                solutions,
                indeterminate,
            );
        } else if self.subject_rest.is_some() {
            *indeterminate = true;
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn finish(
        &self,
        remaining: Vec<(Term, Term)>,
        frame_entries: Vec<(Term, Term)>,
        solution: CollectionSolution,
        narrowing: &mut Option<&mut Narrowing<'_>>,
        solutions: &mut Vec<CollectionSolution>,
        indeterminate: &mut bool,
    ) {
        if frame_entries.is_empty() {
            if let Some(rest) = &self.rest {
                let subject = Term::map(
                    self.definition.clone(),
                    remaining,
                    self.subject_rest.clone(),
                );
                match solve_term_pair(
                    self.mode,
                    self.backend,
                    solution,
                    rest,
                    &subject,
                    narrowing.is_some(),
                ) {
                    PairSolution::Solved(solution) => solutions.push(solution),
                    PairSolution::NoSolution => {}
                    PairSolution::Indeterminate => *indeterminate = true,
                }
                return;
            }
            match &self.subject_rest {
                None if remaining.is_empty() => solutions.push(solution),
                Some(subject_rest) if narrowing.is_some() => {
                    if let TermKind::Variable(variable) = subject_rest.kind() {
                        if !remaining.is_empty() {
                            return;
                        }
                        let empty = Term::map(self.definition.clone(), Vec::new(), None);
                        match solve_term_pair(
                            self.mode,
                            self.backend,
                            solution,
                            subject_rest,
                            &empty,
                            true,
                        ) {
                            PairSolution::Solved(solution) => solutions.push(solution),
                            PairSolution::NoSolution => {}
                            PairSolution::Indeterminate => *indeterminate = true,
                        }
                        debug_assert_eq!(variable.sort, empty.sort());
                    } else {
                        *indeterminate = true;
                    }
                }
                Some(_) => *indeterminate = true,
                None => {}
            }
            return;
        }

        let Some(subject_rest) = &self.subject_rest else {
            return;
        };
        let TermKind::Variable(frame) = subject_rest.kind() else {
            *indeterminate = true;
            return;
        };
        if self.rest.is_none() {
            if remaining.is_empty() {
                let value = Term::map(
                    self.definition.clone(),
                    frame_entries
                        .into_iter()
                        .map(|(key, value)| {
                            (
                                substitute(&key, &solution.substitution),
                                substitute(&value, &solution.substitution),
                            )
                        })
                        .collect(),
                    None,
                );
                match solve_term_pair(
                    self.mode,
                    self.backend,
                    solution,
                    subject_rest,
                    &value,
                    true,
                ) {
                    PairSolution::Solved(solution) => solutions.push(solution),
                    PairSolution::NoSolution => {}
                    PairSolution::Indeterminate => *indeterminate = true,
                }
            }
            return;
        }
        let Some(narrowing) = narrowing.as_deref_mut() else {
            *indeterminate = true;
            return;
        };
        let fresh = (narrowing.fresh_frame)(&frame.sort);
        let fresh_term = Term::variable(fresh.clone());
        let assigned = Term::map(
            self.definition.clone(),
            frame_entries
                .into_iter()
                .map(|(key, value)| {
                    (
                        substitute(&key, &solution.substitution),
                        substitute(&value, &solution.substitution),
                    )
                })
                .collect(),
            Some(fresh_term.clone()),
        );
        let solution = match solve_term_pair(
            self.mode,
            self.backend,
            solution,
            subject_rest,
            &assigned,
            true,
        ) {
            PairSolution::Solved(mut solution) => {
                solution.fresh.insert(fresh);
                solution
            }
            PairSolution::NoSolution => return,
            PairSolution::Indeterminate => {
                *indeterminate = true;
                return;
            }
        };
        let remainder = Term::map(self.definition.clone(), remaining, Some(fresh_term));
        match solve_term_pair(
            self.mode,
            self.backend,
            solution,
            self.rest.as_ref().expect("pattern frame checked above"),
            &remainder,
            true,
        ) {
            PairSolution::Solved(solution) => solutions.push(solution),
            PairSolution::NoSolution => {}
            PairSolution::Indeterminate => *indeterminate = true,
        }
    }
}

/// A collection term: an internal collection, or an opaque concatenation of collection
/// symbols, which `Term::set` and its siblings leave as the bare application when it carries no
/// element.
pub(crate) fn is_collection_term(term: &Term) -> bool {
    match term.kind() {
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. } => true,
        TermKind::Application { symbol, .. } => {
            symbol
                .attributes
                .collection
                .as_ref()
                .is_some_and(|collection| match collection {
                    crate::term::CollectionMetadata::Map(definition) => {
                        definition.symbols.concat == symbol.name
                    }
                    crate::term::CollectionMetadata::List(definition) => {
                        definition.symbols.concat == symbol.name
                    }
                    crate::term::CollectionMetadata::Set(definition) => {
                        definition.symbols.concat == symbol.name
                    }
                })
        }
        _ => false,
    }
}

/// The parts of a Set term: an internal set, or an opaque concatenation viewed as a set with no
/// element and that concatenation as its rest.
fn set_parts(term: &Term) -> Option<(Arc<crate::term::SetDefinition>, Vec<Term>, Option<Term>)> {
    match term.kind() {
        TermKind::Set {
            definition,
            elements,
            rest,
        } => Some((definition.clone(), elements.clone(), rest.clone())),
        TermKind::Application { symbol, .. } => match &symbol.attributes.collection {
            Some(crate::term::CollectionMetadata::Set(definition))
                if definition.symbols.concat == symbol.name =>
            {
                Some((definition.clone(), Vec::new(), Some(term.clone())))
            }
            _ => None,
        },
        _ => None,
    }
}

fn solve_set_pair(
    mode: MatchMode,
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    solution: CollectionSolution,
    narrowing: &mut Option<&mut Narrowing<'_>>,
) -> Option<Vec<CollectionSolution>> {
    let (
        Some((pattern_definition, pattern_elements, pattern_rest)),
        Some((subject_definition, subject_elements, subject_rest)),
    ) = (set_parts(pattern), set_parts(subject))
    else {
        unreachable!()
    };
    if pattern_definition != subject_definition {
        return Some(Vec::new());
    }
    let (pattern_rest, subject_rest) = cancel_common_opaque_chunks(
        pattern_rest,
        subject_rest,
        &pattern_definition.symbols.concat,
    );
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
    measure::bump(Counter::MatchingCollectionProblems);
    let problem = SetCollectionProblem {
        mode,
        backend: definition,
        definition: pattern_definition.clone(),
        elements: pattern_elements.into_iter().collect(),
        rest: pattern_rest,
        subject_rest,
    };
    let mut found = Vec::new();
    let mut indeterminate = false;
    problem.search(
        0,
        subject_elements.into_iter().collect(),
        Vec::new(),
        solution,
        narrowing,
        &mut found,
        &mut indeterminate,
    );
    (!indeterminate).then_some(found)
}

struct SetCollectionProblem<'a> {
    mode: MatchMode,
    backend: &'a BackendDefinition,
    definition: Arc<crate::term::SetDefinition>,
    elements: Vec<Term>,
    rest: Option<Term>,
    subject_rest: Option<Term>,
}

impl SetCollectionProblem<'_> {
    #[allow(clippy::too_many_arguments)]
    fn search(
        &self,
        index: usize,
        remaining: Vec<Term>,
        frame_elements: Vec<Term>,
        solution: CollectionSolution,
        narrowing: &mut Option<&mut Narrowing<'_>>,
        solutions: &mut Vec<CollectionSolution>,
        indeterminate: &mut bool,
    ) {
        if index == self.elements.len() {
            self.finish(
                remaining,
                frame_elements,
                solution,
                narrowing,
                solutions,
                indeterminate,
            );
            return;
        }

        let element = &self.elements[index];
        for subject_index in 0..remaining.len() {
            match solve_term_pair(
                self.mode,
                self.backend,
                solution.clone(),
                element,
                &remaining[subject_index],
                narrowing.is_some(),
            ) {
                PairSolution::Solved(solution) => {
                    let mut next_remaining = remaining.clone();
                    next_remaining.remove(subject_index);
                    self.search(
                        index + 1,
                        next_remaining,
                        frame_elements.clone(),
                        solution,
                        narrowing,
                        solutions,
                        indeterminate,
                    );
                }
                PairSolution::NoSolution => {}
                PairSolution::Indeterminate => *indeterminate = true,
            }
        }

        if narrowing.is_some()
            && matches!(
                self.subject_rest.as_ref().map(Term::kind),
                Some(TermKind::Variable(_))
            )
        {
            let mut frame_elements = frame_elements;
            frame_elements.push(element.clone());
            self.search(
                index + 1,
                remaining,
                frame_elements,
                solution,
                narrowing,
                solutions,
                indeterminate,
            );
        } else if self.subject_rest.is_some() {
            *indeterminate = true;
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn finish(
        &self,
        remaining: Vec<Term>,
        frame_elements: Vec<Term>,
        solution: CollectionSolution,
        narrowing: &mut Option<&mut Narrowing<'_>>,
        solutions: &mut Vec<CollectionSolution>,
        indeterminate: &mut bool,
    ) {
        if frame_elements.is_empty() {
            if let Some(rest) = &self.rest {
                let subject = Term::set(
                    self.definition.clone(),
                    remaining,
                    self.subject_rest.clone(),
                );
                match solve_term_pair(
                    self.mode,
                    self.backend,
                    solution,
                    rest,
                    &subject,
                    narrowing.is_some(),
                ) {
                    PairSolution::Solved(solution) => solutions.push(solution),
                    PairSolution::NoSolution => {}
                    PairSolution::Indeterminate => *indeterminate = true,
                }
                return;
            }
            match &self.subject_rest {
                None if remaining.is_empty() => solutions.push(solution),
                Some(subject_rest) if narrowing.is_some() => {
                    if matches!(subject_rest.kind(), TermKind::Variable(_)) {
                        if !remaining.is_empty() {
                            return;
                        }
                        let empty = Term::set(self.definition.clone(), Vec::new(), None);
                        match solve_term_pair(
                            self.mode,
                            self.backend,
                            solution,
                            subject_rest,
                            &empty,
                            true,
                        ) {
                            PairSolution::Solved(solution) => solutions.push(solution),
                            PairSolution::NoSolution => {}
                            PairSolution::Indeterminate => *indeterminate = true,
                        }
                    } else {
                        *indeterminate = true;
                    }
                }
                Some(_) => *indeterminate = true,
                None => {}
            }
            return;
        }

        let Some(subject_rest) = &self.subject_rest else {
            return;
        };
        let TermKind::Variable(frame) = subject_rest.kind() else {
            *indeterminate = true;
            return;
        };
        if self.rest.is_none() {
            if remaining.is_empty() {
                let value = Term::set(
                    self.definition.clone(),
                    frame_elements
                        .into_iter()
                        .map(|element| substitute(&element, &solution.substitution))
                        .collect(),
                    None,
                );
                match solve_term_pair(
                    self.mode,
                    self.backend,
                    solution,
                    subject_rest,
                    &value,
                    true,
                ) {
                    PairSolution::Solved(solution) => solutions.push(solution),
                    PairSolution::NoSolution => {}
                    PairSolution::Indeterminate => *indeterminate = true,
                }
            }
            return;
        }
        let Some(narrowing) = narrowing.as_deref_mut() else {
            *indeterminate = true;
            return;
        };
        let fresh = (narrowing.fresh_frame)(&frame.sort);
        let fresh_term = Term::variable(fresh.clone());
        let assigned = Term::set(
            self.definition.clone(),
            frame_elements
                .into_iter()
                .map(|element| substitute(&element, &solution.substitution))
                .collect(),
            Some(fresh_term.clone()),
        );
        let solution = match solve_term_pair(
            self.mode,
            self.backend,
            solution,
            subject_rest,
            &assigned,
            true,
        ) {
            PairSolution::Solved(mut solution) => {
                solution.fresh.insert(fresh);
                solution
            }
            PairSolution::NoSolution => return,
            PairSolution::Indeterminate => {
                *indeterminate = true;
                return;
            }
        };
        let remainder = Term::set(self.definition.clone(), remaining, Some(fresh_term));
        match solve_term_pair(
            self.mode,
            self.backend,
            solution,
            self.rest.as_ref().expect("pattern frame checked above"),
            &remainder,
            true,
        ) {
            PairSolution::Solved(solution) => solutions.push(solution),
            PairSolution::NoSolution => {}
            PairSolution::Indeterminate => *indeterminate = true,
        }
    }
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
    solve_collection_pairs_in_definition(mode, definition, initial, remainder, None).map(
        |solutions| {
            solutions
                .into_iter()
                .map(|solution| solution.substitution)
                .collect()
        },
    )
}

#[derive(Clone)]
struct OpaqueConcatHead {
    symbol: Arc<crate::term::Symbol>,
    sort_arguments: Vec<Sort>,
}

/// Cancel opaque chunks which occur on both sides of an AC equation.
///
/// The reference normalizer treats opaque children as a multiset, but retains the greater
/// multiplicity of a common child in the unified term because duplicate opaque collections may
/// later normalize to bottom. Rewriting only needs the residual equation, so removing every
/// occurrence from both differences is equivalent while leaving duplicate-definedness handling to
/// collection simplification.
pub(crate) fn cancel_common_opaque_chunks(
    left: Option<Term>,
    right: Option<Term>,
    concat: &Name,
) -> (Option<Term>, Option<Term>) {
    let (mut left, left_head) = flatten_opaque_chunks(left, concat);
    let (mut right, right_head) = flatten_opaque_chunks(right, concat);
    let common = left
        .iter()
        .filter(|term| right.contains(*term))
        .cloned()
        .collect::<BTreeSet<_>>();
    left.retain(|term| !common.contains(term));
    right.retain(|term| !common.contains(term));
    left.sort();
    right.sort();
    (
        rebuild_opaque_chunks(left, left_head),
        rebuild_opaque_chunks(right, right_head),
    )
}

fn flatten_opaque_chunks(
    rest: Option<Term>,
    concat: &Name,
) -> (Vec<Term>, Option<OpaqueConcatHead>) {
    fn visit(
        term: Term,
        concat: &Name,
        chunks: &mut Vec<Term>,
        head: &mut Option<OpaqueConcatHead>,
    ) {
        if let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = term.kind()
            && &symbol.name == concat
            && let [left, right] = arguments.as_slice()
        {
            head.get_or_insert_with(|| OpaqueConcatHead {
                symbol: symbol.clone(),
                sort_arguments: sort_arguments.clone(),
            });
            visit(left.clone(), concat, chunks, head);
            visit(right.clone(), concat, chunks, head);
        } else {
            chunks.push(term);
        }
    }

    let mut chunks = Vec::new();
    let mut head = None;
    if let Some(rest) = rest {
        visit(rest, concat, &mut chunks, &mut head);
    }
    (chunks, head)
}

fn rebuild_opaque_chunks(chunks: Vec<Term>, head: Option<OpaqueConcatHead>) -> Option<Term> {
    let mut chunks = chunks.into_iter();
    let first = chunks.next()?;
    Some(chunks.fold(first, |left, right| {
        let head = head
            .as_ref()
            .expect("multiple opaque chunks came from a concatenation");
        Term::application(
            head.symbol.clone(),
            head.sort_arguments.clone(),
            vec![left, right],
        )
    }))
}

fn is_opaque_concat(term: &Term, concat: &Name) -> bool {
    matches!(term.kind(), TermKind::Application { symbol, .. } if &symbol.name == concat)
}

/// Expand implication remainders where a closed destination map is unified with an open current
/// map. Each returned branch is one AC entry permutation expressed as ordinary term equalities;
/// the implication layer can simplify and existentially quantify those equations uniformly with
/// its other obligations.
pub(crate) fn expand_closed_map_implication_remainders(
    initial: &Substitution,
    remainder: &[(Term, Term)],
) -> Option<Vec<Vec<(Term, Term)>>> {
    let mut expanded = false;
    let mut branches = vec![Vec::new()];
    for (pattern, subject) in remainder {
        let pattern = substitute(pattern, initial);
        let subject = substitute(subject, initial);
        let expansion = match (pattern.kind(), subject.kind()) {
            (
                TermKind::Map {
                    definition: pattern_definition,
                    entries: pattern_entries,
                    rest: None,
                },
                TermKind::Map {
                    definition: subject_definition,
                    entries: subject_entries,
                    rest: Some(subject_rest),
                },
            ) if pattern_definition == subject_definition
                && subject_entries.len() <= pattern_entries.len() =>
            {
                let mut solutions = Vec::new();
                ClosedMapImplicationProblem {
                    pattern_definition,
                    pattern_entries,
                    subject_entries,
                    subject_rest,
                }
                .enumerate(0, Vec::new(), &mut solutions);
                Some(solutions)
            }
            _ => None,
        };
        let Some(expansion) = expansion else {
            for branch in &mut branches {
                branch.push((pattern.clone(), subject.clone()));
            }
            continue;
        };
        expanded = true;
        let mut next = Vec::new();
        for branch in branches {
            for equations in &expansion {
                let mut combined = branch.clone();
                combined.extend(equations.iter().cloned());
                next.push(combined);
            }
        }
        branches = next;
    }
    if !expanded {
        return None;
    }
    branches.sort();
    branches.dedup();
    Some(branches)
}

struct ClosedMapImplicationProblem<'a> {
    pattern_definition: &'a Arc<MapDefinition>,
    pattern_entries: &'a [(Term, Term)],
    subject_entries: &'a [(Term, Term)],
    subject_rest: &'a Term,
}

impl ClosedMapImplicationProblem<'_> {
    fn enumerate(
        &self,
        subject_index: usize,
        selected: Vec<(usize, Vec<(Term, Term)>)>,
        solutions: &mut Vec<Vec<(Term, Term)>>,
    ) {
        if subject_index == self.subject_entries.len() {
            let selected_indices = selected
                .iter()
                .map(|(index, _)| *index)
                .collect::<BTreeSet<_>>();
            let remaining = self
                .pattern_entries
                .iter()
                .enumerate()
                .filter(|(index, _)| !selected_indices.contains(index))
                .map(|(_, entry)| entry.clone())
                .collect();
            let mut equations = selected
                .into_iter()
                .flat_map(|(_, equations)| equations)
                .collect::<Vec<_>>();
            equations.push((
                self.subject_rest.clone(),
                Term::map(self.pattern_definition.clone(), remaining, None),
            ));
            solutions.push(equations);
            return;
        }

        let (subject_key, subject_value) = &self.subject_entries[subject_index];
        let used = selected
            .iter()
            .map(|(index, _)| *index)
            .collect::<BTreeSet<_>>();
        for (pattern_index, (pattern_key, pattern_value)) in self.pattern_entries.iter().enumerate()
        {
            if used.contains(&pattern_index) {
                continue;
            }
            let mut next = selected.clone();
            next.push((
                pattern_index,
                vec![
                    (subject_key.clone(), pattern_key.clone()),
                    (subject_value.clone(), pattern_value.clone()),
                ],
            ));
            self.enumerate(subject_index + 1, next, solutions);
        }
    }
}

/// Every result of `LIST.update(L, I, V)` is a fixed point of updating at `I` with `V`.
/// Reuse the hook to refute a concrete result with a conflicting element or an out-of-range index.
/// This necessary condition is independent of `L`; satisfying it does not solve for the base list.
fn list_update_cannot_match(pattern: &Term, subject: &Term) -> bool {
    let TermKind::Application {
        symbol, arguments, ..
    } = pattern.kind()
    else {
        return false;
    };
    if symbol.attributes.hook.as_deref() != Some("LIST.update")
        || !matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
        || !subject.attributes().constructor_like
        || !matches!(subject.kind(), TermKind::List { rest: None, .. })
    {
        return false;
    }
    let [_, index, value] = arguments.as_slice() else {
        return false;
    };
    match evaluate_hook(
        "LIST.update",
        &[subject.clone(), index.clone(), value.clone()],
    ) {
        Ok(BuiltinResult::Bottom) => true,
        Ok(BuiltinResult::Value(updated)) => {
            updated.attributes().constructor_like && updated != *subject
        }
        _ => false,
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
        measure::bump(Counter::MatchingPairs);
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
            _ if list_update_cannot_match(&pattern, &subject) => {
                Err(FailReason::DifferentValues(pattern, subject))
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
            if self.sorts.known_overlap(pattern_source, subject_source) == Some(true)
                && !has_constructor_like_top(pattern_term)
                && !has_constructor_like_top(subject_term)
            {
                return self.defer(pattern, subject);
            }
            return Err(FailReason::DifferentSorts(
                pattern_term.clone(),
                subject_term.clone(),
            ));
        }
        if pattern_is_subsort
            && (is_function(subject_term) || matches!(subject_term.kind(), TermKind::Variable(_)))
        {
            let pattern_term = Term::injection(
                pattern_source.clone(),
                subject_source.clone(),
                pattern_term.clone(),
            );
            debug_assert_eq!(pattern_term.sort(), subject_term.sort());
            return self.defer(pattern_term, subject_term.clone());
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
                let subject_term = Term::injection(
                    subject_source.clone(),
                    pattern_source.clone(),
                    subject_term.clone(),
                );
                debug_assert_eq!(pattern_term.sort(), subject_term.sort());
                return self.defer(pattern_term.clone(), subject_term);
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
                let narrowable = self.mode == MatchMode::Rewrite
                    && !matches!(remainder, Some(PairRemainder::Right(_)));
                if narrowable {
                    let pattern_heads = match remainder {
                        Some(PairRemainder::Left(heads)) => heads,
                        None => Vec::new(),
                        Some(PairRemainder::Right(_)) => unreachable!("excluded above"),
                    };
                    self.defer(list(pattern_heads, None), list(Vec::new(), Some(rest)))?;
                    Vec::new()
                } else {
                    let (left, right) = match remainder {
                        Some(PairRemainder::Left(heads)) => {
                            (list(heads, None), list(Vec::new(), Some(rest)))
                        }
                        Some(PairRemainder::Right(heads)) => (empty(), list(heads, Some(rest))),
                        None => (empty(), list(Vec::new(), Some(rest))),
                    };
                    return Err(FailReason::DifferentValues(left, right));
                }
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

        if pattern_rest
            .as_ref()
            .is_some_and(|rest| is_opaque_concat(rest, &definition.symbols.concat))
            || subject_rest
                .as_ref()
                .is_some_and(|rest| is_opaque_concat(rest, &definition.symbols.concat))
        {
            return self.defer(
                Term::map(definition.clone(), pattern_entries, pattern_rest),
                Term::map(definition, subject_entries, subject_rest),
            );
        }

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
        if pattern_rest
            .as_ref()
            .is_some_and(|rest| is_opaque_concat(rest, &definition.symbols.concat))
            || subject_rest
                .as_ref()
                .is_some_and(|rest| is_opaque_concat(rest, &definition.symbols.concat))
        {
            return self.defer(
                Term::set(definition.clone(), pattern_elements, pattern_rest),
                Term::set(definition, subject_elements, subject_rest),
            );
        }
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
            let subject_has_rest = subject_rest.is_some();
            let subject = set(subject_elements.into_iter().collect(), subject_rest);
            if let Some(rest) = pattern_rest {
                self.enqueue(rest, subject);
                return Ok(());
            }
            if subject_is_empty {
                return Ok(());
            }
            if self.mode == MatchMode::Rewrite && subject_has_rest {
                return self.defer(set(Vec::new(), None), subject);
            }
            return Err(FailReason::DifferentSymbols(set(Vec::new(), None), subject));
        }

        if pattern_symbolic.len() == 1 && subject_elements.len() == 1 && subject_rest.is_none() {
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
            if self.mode == MatchMode::Rewrite && subject.rest.is_some() {
                self.defer(
                    pattern.to_term(definition.clone()),
                    subject.to_term(definition.clone()),
                )?;
                return Ok(Vec::new());
            }
            return Err(FailReason::DifferentSymbols(
                pattern.to_term(definition.clone()),
                subject.to_term(definition.clone()),
            ));
        }
        if pattern.symbolic.len() == 1
            && subject.concrete.len() + subject.symbolic.len() == 1
            && subject.rest.is_none()
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
                    && self.mode != MatchMode::Rewrite
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
pub(crate) fn occurs_below_only_constructors(variable: &Variable, term: &Term) -> bool {
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
