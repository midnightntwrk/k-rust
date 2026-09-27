//! ```toml algorithm
//! id = "backend.matching.syntactic"
//! name = "sort-aware one-way first-order matching by pair decomposition"
//! sites = ["match_terms_with_context", "match_terms", "match_terms_in_definition", "match_term_pairs_in_definition", "Matcher::run", "Matcher::match_one"]
//! variable = "p = pairs popped, bounded by |pattern| plus subject-side And duplications and one map_queue postponement per map pair; a = pair arity; s = bindings in the substitution; t = size of a bound term"
//! counters = ["MatchingProblems", "MatchingPairs"]
//! span = "per problem"
//! consumes = [{ type = "k_rust_backend::matching::collections::CollectionSolution", role = "collection solution" }]
//! produces = [{ type = "k_rust_backend::matching::MatchResult", role = "match result" }]
//!
//! [[cost]]
//! mode = "one matching problem"
//! bound = "O(p x (a + s x t))"
//! ```
//!
//! ```toml algorithm
//! id = "backend.matching.relation_query"
//! name = "subsort and overload membership queries"
//! sites = ["SortGraph::check_subsort"]
//! variable = "S = sorts or overloaded symbols; g = sort-argument nodes of the two compared sorts; C = overload closure pairs"
//! counters = []
//! no_counter = "relation queries have no dedicated counter"
//! span = "none"
//!
//! [[cost]]
//! mode = "SortGraph::check_subsort"
//! bound = "O(g x log |S|)"
//!
//! [[cost]]
//! mode = "OverloadGraph::is_overloading, OverloadGraph::overloaded_by"
//! bound = "O(log |S|) plus the size of the returned set"
//!
//! [[cost]]
//! mode = "OverloadGraph::common_overloads"
//! bound = "O(|C|)"
//! ```
//!
//! Sort-aware one-way first-order matching by pair decomposition (a Martelli-Montanari work
//! queue without unification: pattern variables bind, subject variables defer), O(p) pair pops per
//! problem for p bounded by |pattern| plus subject-side `And` duplications and one `map_queue`
//! postponement per map pair, each pop O(arity) plus an eager composition of the substitution per
//! binding; `Counter::MatchingProblems`, `Counter::MatchingPairs`. Subsort and overload membership
//! queries over the closures `definition.rs` builds, O(log |S|) per sort head plus one lookup per
//! nested sort argument, and a linear scan of the overload closure for `common_overloads`.
//! AC and A collection matching is `collections`, re-exported here so every entry
//! point of `crate::matching` keeps its path.

mod collections;

pub(crate) use collections::{
    CollectionSolution, Narrowing, expand_closed_map_implication_remainders, is_collection_term,
    match_collection_remainders_all_in_definition, solve_collection_pairs_in_definition,
};
// Named only by `src/tests/matching_oracle.rs`.
#[cfg(test)]
pub(crate) use collections::cancel_common_opaque_chunks;
use collections::{
    MapRemainder, PairRemainder, is_opaque_concat, list_update_cannot_match, pair_prefix,
    pair_suffix, prepend,
};

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
};

use rustc_hash::FxHashMap;

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    definition::BackendDefinition,
    instance_normal::is_anywhere_application,
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

    /// Whether two sorts without sort arguments have a common subsort, when both are known.
    pub(crate) fn known_overlap(&self, left: &Sort, right: &Sort) -> Option<bool> {
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

/// Match `pattern` against `subject` without a definition. With no equations to consult, an
/// `anywhere` application of the subject is never taken as a normal form (see
/// [`match_terms_in_definition`]).
pub fn match_terms(
    mode: MatchMode,
    sorts: &SortGraph,
    pattern: &Term,
    subject: &Term,
) -> MatchResult {
    match_terms_with_context(
        mode,
        sorts,
        None,
        pattern,
        subject,
        mode == MatchMode::Evaluate,
    )
}

/// Match `pattern` against `subject`: `Failed` means that no instance of `subject` is an
/// instance of `pattern`, `Success` that `subject` is the given instance of `pattern`.
///
/// In `Evaluate` mode `pattern` is the left-hand side of an equation and `subject` the term the
/// equation is tried on. The equation rewrites the application `subject` itself, so its root is
/// compared by its head and arguments as it stands; only the subterms below it are compared as
/// the values they denote.
///
/// An application of an `anywhere` production that is not a declared function denotes the
/// value of its normal form under the equations, and distinct normal forms are distinct values.
/// Such a subject application (other than the `Evaluate` root) is compared by its head and
/// arguments, and refuted against a different head, only when it is instance-normal
/// ([`BackendDefinition::instance_normal`]): an equation may rewrite some instance of any other
/// one to a term with other arguments or another head (`wrap(s(z)) = wrap(z)` for `wrap(s(X))`
/// at `X = z`). Such a pair is left in the remainder. The pattern side keeps its reading: the
/// left-hand side of a rule or equation is matched as written.
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
        mode == MatchMode::Evaluate,
    )
}

pub(crate) fn match_term_pairs_in_definition(
    mode: MatchMode,
    definition: &BackendDefinition,
    pairs: impl IntoIterator<Item = (Term, Term)>,
) -> MatchResult {
    let _span = measure::algorithm_span(Algorithm::BackendMatchingSyntactic);
    measure::bump(Counter::MatchingProblems);
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

    let mut matcher = Matcher::new(mode, &definition.sort_graph, Some(definition), pairs.into());
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

/// `equation_root`: `subject` is the term an equation with left-hand side `pattern` is tried on,
/// so its own head is taken as it stands (see [`match_terms_in_definition`]).
fn match_terms_with_context(
    mode: MatchMode,
    sorts: &SortGraph,
    definition: Option<&BackendDefinition>,
    pattern: &Term,
    subject: &Term,
    equation_root: bool,
) -> MatchResult {
    let _span = measure::algorithm_span(Algorithm::BackendMatchingSyntactic);
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
    // Rule application renames a rule's variables apart from the subject before matching
    // (`rule::rename_apart`), so this guard only meets callers whose two sides share one scope,
    // where a variable on both sides is one variable and needs unification.
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

    let mut matcher = Matcher::new(
        mode,
        sorts,
        definition,
        VecDeque::from([(pattern.clone(), subject.clone())]),
    );
    if equation_root {
        matcher.given_heads.push(subject.clone());
    }
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
    definition: Option<&'a BackendDefinition>,
    substitution: Substitution,
    queue: VecDeque<(Term, Term)>,
    map_queue: VecDeque<(Term, Term)>,
    indeterminate: Vec<(Term, Term)>,
    /// Subject applications (these handles, not equal terms) whose head is taken as it stands:
    /// the root an equation is tried on, and a subject that overload resolution lifted from an
    /// application whose head is fixed.
    given_heads: Vec<Term>,
    /// Instance normality of the subject terms asked about or implied so far: every argument of
    /// an instance-normal constructor or `anywhere` application, and the operand of an
    /// instance-normal injection, is instance-normal, so one scan covers the whole subterm.
    instance_normal: FxHashMap<Term, bool>,
}

impl<'a> Matcher<'a> {
    fn new(
        mode: MatchMode,
        sorts: &'a SortGraph,
        definition: Option<&'a BackendDefinition>,
        queue: VecDeque<(Term, Term)>,
    ) -> Self {
        Self {
            mode,
            sorts,
            definition,
            substitution: Substitution::new(),
            queue,
            map_queue: VecDeque::new(),
            indeterminate: Vec::new(),
            given_heads: Vec::new(),
            instance_normal: FxHashMap::default(),
        }
    }

    /// Whether the head of the subject term `subject` is the head of every value it denotes.
    /// That holds for every term but an `anywhere` application that is not a declared function;
    /// such an application qualifies when its head is given ([`Self::given_heads`]) or when it is
    /// instance-normal, so that no equation can rewrite any of its instances.
    fn subject_head_is_fixed(&mut self, subject: &Term) -> bool {
        if !is_anywhere_application(subject)
            || self.given_heads.iter().any(|given| given.ptr_eq(subject))
        {
            return true;
        }
        if let Some(known) = self.instance_normal.get(subject) {
            return *known;
        }
        let normal = self
            .definition
            .is_some_and(|definition| definition.instance_normal(subject));
        self.instance_normal.insert(subject.clone(), normal);
        normal
    }

    /// Record the immediate subterms of an instance-normal `subject` that the matcher is about
    /// to compare as instance-normal too.
    fn inherit_instance_normality(&mut self, subject: &Term) {
        if self.instance_normal.get(subject) != Some(&true) {
            return;
        }
        match subject.kind() {
            TermKind::Application {
                symbol, arguments, ..
            } if symbol.attributes.symbol_type == SymbolType::Constructor
                || is_anywhere_application(subject) =>
            {
                for argument in arguments {
                    self.instance_normal.insert(argument.clone(), true);
                }
            }
            TermKind::Injection { term, .. } => {
                self.instance_normal.insert(term.clone(), true);
            }
            _ => {}
        }
    }

    fn run(&mut self) -> Result<(), FailReason> {
        // Map pairs wait until `queue` is empty so that map keys are bound before map problems are
        // solved; a pop enqueues only proper subterms or re-enqueues a deferred pair at most once,
        // so the loop terminates; `indeterminate` collects pairs neither solved nor refuted.
        // Invariant: `substitution` matches every popped pair; queued pairs are still unchecked.
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
        // Every arm below either compares the subject's head and arguments or refutes the pair
        // by the subject's head. For an `anywhere` subject application whose head is not fixed,
        // an equation may give some instance other arguments or another head, so neither is
        // sound; the pair is left to the caller, unless it is syntactically solved.
        if !self.subject_head_is_fixed(&subject) {
            if pattern == subject {
                return Ok(());
            }
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
                    self.inherit_instance_normality(&subject);
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
                || (self.mode == MatchMode::Rewrite
                    && is_rewrite_rigid(pattern.kind())
                    && is_rewrite_rigid(subject.kind()))
                // An equal `anywhere` head is compared by arguments in every mode without asking
                // for `injective`: the subject's head is fixed (checked above), so its arguments
                // are those of the normal form it denotes, and the pattern is read as written.
                || ((pattern_symbol.attributes.injective || is_anywhere_application(&pattern))
                    && pattern_symbol.name == subject_symbol.name)
                || (self.mode == MatchMode::Evaluate
                    && is_function(&pattern)
                    && is_function(&subject)) =>
            {
                if pattern_symbol.name != subject_symbol.name {
                    // An equation pattern headed by an overloaded production cannot denote a
                    // different production once the subject is concrete and its head fixed
                    // (checked before this match).
                    if self.mode == MatchMode::Rewrite
                        || (is_constructor(&pattern) && is_constructor(&subject))
                        || (self.mode == MatchMode::Evaluate
                            && is_overload_head(self.definition, pattern.kind())
                            && subject.concrete_after_normalization())
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
                self.inherit_instance_normality(&subject);
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
            (left, right)
                if (self.mode == MatchMode::Rewrite
                    && is_rewrite_rigid(left)
                    && is_rewrite_rigid(right))
                    || (is_rigid(left) && is_rigid(right))
                    // The subject is not rigid, so it is an `anywhere` application, whose head
                    // is fixed (checked before this match), or a declared function, which is
                    // never concrete after normalization.
                    || (self.mode == MatchMode::Evaluate
                        && is_rigid(left)
                        && subject.concrete_after_normalization()) =>
            {
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
            if self.mode == MatchMode::Evaluate
                && self.sorts.known_overlap(pattern_source, subject_source) == Some(true)
            {
                match self.lower_normalized_overload_to_sort(subject_term, pattern_source) {
                    OverloadLowering::Lowered(lowered) => {
                        self.enqueue(pattern_term.clone(), lowered);
                        return Ok(());
                    }
                    OverloadLowering::Impossible => {
                        return Err(FailReason::DifferentSorts(
                            pattern_term.clone(),
                            subject_term.clone(),
                        ));
                    }
                    OverloadLowering::Indeterminate => {}
                }
            }
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
            if self.mode == MatchMode::Rewrite
                && is_rewrite_rigid(subject_term.kind())
                && self.subject_head_is_fixed(subject_term)
            {
                self.enqueue(pattern_term, subject_term.clone());
                return Ok(());
            }
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
                if self.mode == MatchMode::Rewrite && is_rewrite_rigid(pattern_term.kind()) {
                    self.enqueue(pattern_term.clone(), subject_term);
                    return Ok(());
                }
                return self.defer(pattern_term.clone(), subject_term);
            }
        }
        Err(FailReason::DifferentSorts(pattern, subject))
    }

    /// Lower a normalized overloaded application to a requested overlapping sort.
    ///
    /// This is the inverse of [`OverloadView::lift`]. It is deliberately restricted to terms
    /// which are concrete after normalization: variables and ordinary functions keep the result
    /// indeterminate instead of being guessed into a lesser overload.
    fn lower_normalized_overload_to_sort(
        &mut self,
        term: &Term,
        target: &Sort,
    ) -> OverloadLowering {
        let source = term.sort();
        if &source == target {
            return OverloadLowering::Lowered(term.clone());
        }
        match self.sorts.check_subsort(&source, target) {
            Ok(true) => {
                return OverloadLowering::Lowered(Term::injection(
                    source,
                    target.clone(),
                    term.clone(),
                ));
            }
            Err(_) => return OverloadLowering::Indeterminate,
            Ok(false) => {}
        }
        if let TermKind::Injection {
            source: inner_source,
            term: inner,
            ..
        } = term.kind()
        {
            if inner_source == target {
                return OverloadLowering::Lowered(inner.clone());
            }
            return self.lower_normalized_overload_to_sort(inner, target);
        }

        let Some(definition) = self.definition else {
            return OverloadLowering::Indeterminate;
        };
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = term.kind()
        else {
            // A domain value or a collection: no equation changes the sort of its value, so a
            // concrete one is not an injection from `target`.
            return if term.concrete_after_normalization() {
                OverloadLowering::Impossible
            } else {
                OverloadLowering::Indeterminate
            };
        };

        let candidates = definition.overloads.overloaded_by(&symbol.name);
        let mut lowered = Vec::new();
        let mut indeterminate = Vec::new();
        for candidate_name in candidates {
            let Some(candidate) = definition.symbols.get(&candidate_name) else {
                indeterminate.push(candidate_name);
                continue;
            };
            let Some(result_sort) = instantiated_symbol_sort(candidate, sort_arguments) else {
                indeterminate.push(candidate.name.clone());
                continue;
            };
            match self.sorts.check_subsort(&result_sort, target) {
                Ok(false) if &result_sort != target => continue,
                Err(_) => {
                    indeterminate.push(candidate.name.clone());
                    continue;
                }
                Ok(_) => {}
            }
            if candidate.argument_sorts.len() != arguments.len() {
                indeterminate.push(candidate.name.clone());
                continue;
            }
            let Some(parameters) = symbol_parameters(candidate, sort_arguments) else {
                indeterminate.push(candidate.name.clone());
                continue;
            };
            let mut candidate_arguments = Vec::with_capacity(arguments.len());
            let mut candidate_impossible = false;
            let mut candidate_indeterminate = false;
            for (argument, expected) in arguments.iter().zip(&candidate.argument_sorts) {
                let expected = substitute_sort_parameters(expected, &parameters);
                match self.lower_normalized_overload_to_sort(argument, &expected) {
                    OverloadLowering::Lowered(argument) => candidate_arguments.push(argument),
                    OverloadLowering::Impossible => {
                        candidate_impossible = true;
                        break;
                    }
                    OverloadLowering::Indeterminate => {
                        candidate_indeterminate = true;
                        candidate_impossible = true;
                        break;
                    }
                }
            }
            if candidate_indeterminate {
                indeterminate.push(candidate.name.clone());
            }
            if candidate_impossible {
                continue;
            }
            let application = Term::application(
                candidate.clone(),
                sort_arguments.clone(),
                candidate_arguments,
            );
            let candidate_sort = application.sort();
            let application = if &candidate_sort == target {
                application
            } else {
                Term::injection(candidate_sort, target.clone(), application)
            };
            lowered.push((candidate.name.clone(), application));
        }
        let minimal = lowered
            .iter()
            .filter(|(candidate, _)| {
                !lowered.iter().any(|(lesser, _)| {
                    candidate != lesser && definition.overloads.is_overloading(candidate, lesser)
                })
            })
            .collect::<Vec<_>>();
        if let Some((_, first)) = minimal.first()
            && minimal.iter().all(|(_, term)| term == first)
            && indeterminate.iter().all(|candidate| {
                minimal
                    .iter()
                    .any(|(name, _)| definition.overloads.is_overloading(candidate, name))
            })
        {
            return OverloadLowering::Lowered(first.clone());
        }
        // No production of the overload family represents `term` in `target`, which refutes
        // only when `term` denotes a value with its own head: an equation may rewrite an
        // `anywhere` application that is not instance-normal to one that lowers.
        if minimal.is_empty()
            && indeterminate.is_empty()
            && term.concrete_after_normalization()
            && self.subject_head_is_fixed(term)
        {
            OverloadLowering::Impossible
        } else {
            OverloadLowering::Indeterminate
        }
    }

    /// Lift a pair of distinct heads of one overload family to their least common production.
    /// Lifting the subject to `common(inj(arguments))` asserts that the pair is equivalent to
    /// comparing arguments under `common`. That holds when the subject's own head is fixed: then
    /// the lifted term denotes the subject's value through the overload equation, and a value
    /// with head `common` is an instance of the lifted pattern exactly when the arguments match.
    /// A subject whose head is not fixed is not lifted, and its lifted form, which an overload
    /// equation rewrites by construction, is given its head ([`Self::given_heads`]).
    fn resolve_overloads(&mut self, pattern: &Term, subject: &Term) -> Option<(Term, Term)> {
        let definition = self.definition?;
        let pattern_name = &overload_head(pattern)?.name;
        let subject_name = &overload_head(subject)?.name;
        // A symbol outside every overload relation neither overloads the other head nor shares
        // an overload with it, so no common production exists: most pairs of distinct heads
        // end here, before a view of either side is built.
        if pattern_name == subject_name
            || !definition.overloads.is_overloaded(pattern_name)
            || !definition.overloads.is_overloaded(subject_name)
        {
            return None;
        }
        let pattern_view = OverloadView::new(pattern)?;
        let subject_view = OverloadView::new(subject)?;
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
        let subject_application = overload_application(subject)?;
        if !self.subject_head_is_fixed(subject_application) {
            return None;
        }
        let pattern = pattern_view.lift(common.clone(), &sort_arguments, self.sorts)?;
        let subject = subject_view.lift(common, &sort_arguments, self.sorts)?;
        if let Some(lifted) = overload_application(&subject) {
            self.given_heads.push(lifted.clone());
        }
        Some((pattern, subject))
    }

    fn can_narrow_overload(&self, pattern: &Term, subject: &Term) -> bool {
        let Some(definition) = self.definition else {
            return false;
        };
        let Some(pattern) = overload_head(pattern) else {
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
            .overloaded_by(&pattern.name)
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
        if let Some(old) = self.substitution.get(&variable) {
            if *old == term {
                return Ok(());
            }
            let old = old.clone();
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
        // Only a value that mentions `variable` changes under the singleton substitution;
        // every other value is kept as it is instead of being rebuilt into an equal handle.
        let mut singleton = None;
        for value in self.substitution.values_mut() {
            if value.attributes().variables.contains(&variable) {
                let singleton = singleton
                    .get_or_insert_with(|| Substitution::from([(variable.clone(), term.clone())]));
                *value = substitute(value, singleton);
            }
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

enum OverloadLowering {
    Lowered(Term),
    Impossible,
    Indeterminate,
}

fn symbol_parameters(
    symbol: &crate::term::Symbol,
    sort_arguments: &[Sort],
) -> Option<BTreeMap<Name, Sort>> {
    (symbol.sort_variables.len() == sort_arguments.len()).then(|| {
        symbol
            .sort_variables
            .iter()
            .cloned()
            .zip(sort_arguments.iter().cloned())
            .collect()
    })
}

fn instantiated_symbol_sort(symbol: &crate::term::Symbol, sort_arguments: &[Sort]) -> Option<Sort> {
    let parameters = symbol_parameters(symbol, sort_arguments)?;
    Some(substitute_sort_parameters(&symbol.result_sort, &parameters))
}

/// The symbol of the application `term` is, directly or under one injection: the head an
/// [`OverloadView`] of `term` has.
fn overload_head(term: &Term) -> Option<&Arc<crate::term::Symbol>> {
    match overload_application(term)?.kind() {
        TermKind::Application { symbol, .. } => Some(symbol),
        _ => None,
    }
}

/// The application `term` is, directly or under one injection.
fn overload_application(term: &Term) -> Option<&Term> {
    let application = match term.kind() {
        TermKind::Injection { term, .. } => term,
        _ => term,
    };
    matches!(application.kind(), TermKind::Application { .. }).then_some(application)
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

fn check_duplicate_keys(
    definition: &Arc<MapDefinition>,
    entries: &[(Term, Term)],
    rest: &Option<Term>,
) -> Result<(), FailReason> {
    // The least key that occurs twice. In entries sorted by key, as `Term::map` stores them,
    // equal keys are adjacent, so one pass over neighbours finds it without copying a key;
    // entries in another order (a pattern's, after its keys were substituted) are counted.
    let duplicate = if entries.is_sorted_by(|left, right| left.0 <= right.0) {
        entries
            .windows(2)
            .find(|pair| pair[0].0 == pair[1].0)
            .map(|pair| pair[0].0.clone())
    } else {
        let mut counts = BTreeMap::new();
        for (key, _) in entries {
            *counts.entry(key).or_insert(0usize) += 1;
        }
        counts
            .into_iter()
            .find(|(_, count)| *count > 1)
            .map(|(key, _)| key.clone())
    };
    if let Some(key) = duplicate {
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
                || symbol.attributes.macro_or_alias
    )
}

/// Whether rewrite matching compares a term by its head: a rigid term or an `anywhere`
/// application that is not a declared function. On the subject side the `anywhere` case also
/// needs a fixed head ([`rewrite_rigid_subject`]).
fn is_rewrite_rigid(kind: &TermKind) -> bool {
    is_rigid(kind)
        || matches!(
            kind,
            TermKind::Application { symbol, .. }
                if symbol.attributes.anywhere && !symbol.attributes.declared_function
        )
}

/// Whether the rewrite matcher compares the subject term `term` by its head, so that a rule
/// whose pattern has another rigid head fails on it: `term` is rewrite-rigid and, when it is an
/// `anywhere` application, instance-normal. The rule index keys a subject by its head exactly
/// when this holds, since a key may drop only rules the matcher refutes.
pub(crate) fn rewrite_rigid_subject(definition: &BackendDefinition, term: &Term) -> bool {
    is_rewrite_rigid(term.kind())
        && (!is_anywhere_application(term) || definition.instance_normal(term))
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
