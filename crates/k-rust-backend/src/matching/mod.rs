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
//! variable = "S = nodes of the subsort order or overloaded symbols; c = nodes of the two compared sort terms; C = overload closure pairs"
//! counters = []
//! no_counter = "relation queries have no dedicated counter"
//! span = "none"
//!
//! [[cost]]
//! mode = "SortGraph::check_subsort"
//! bound = "O(c x log |S|)"
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
//! queries over the closures `definition.rs` builds, O(log |S|) sort comparisons per query, each
//! linear in the compared sorts, and a linear scan of the overload closure for `common_overloads`.
//! AC and A collection matching is `collections`, re-exported here so every entry
//! point of `crate::matching` keeps its path.

mod collections;
#[cfg(test)]
pub(crate) use collections::SPLIT_COPIES;

pub(crate) use collections::{
    CollectionMatches, CollectionSolution, Narrowing, expand_closed_map_implication_remainders,
    is_collection_term, match_collection_remainders_all_in_definition,
    solve_collection_pairs_in_definition,
};
// Named only by `src/tests/matching_oracle.rs`.
#[cfg(test)]
pub(crate) use collections::cancel_common_opaque_chunks;
use collections::{
    CommonKeys, MapRemainder, PairRemainder, binds_each_key_once, find_common_keys,
    is_opaque_concat, list_update_cannot_match, pair_prefix, pair_suffix, prepend,
};

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
};

use rustc_hash::FxHashMap;

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    definition::BackendDefinition,
    instance_normal::InstanceNormal,
    substitution::{Substitution, substitute},
    term::{
        HeadRole, ListDefinition, MapDefinition, Name, Sort, SymbolType, Term, TermKind, Variable,
        head::{
            Fixed, FixedRoot, Head, HeadClash, NormalEvidence, NormalForms, Open, PatternReading,
            RecordedPatterns, ReleasedRoots, RigidCycle, RootComparison, classify_pattern,
            classify_value, compare_roots, rigid_occurrence,
        },
    },
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

impl MatchResult {
    /// The refutation this result states: `Some` exactly for [`MatchResult::Failed`], where no
    /// instance of the subject is an instance of the pattern. A match that succeeded, or one
    /// left open, refutes nothing:
    ///
    /// ```
    /// use k_rust_backend::{matching::MatchResult, substitution::Substitution};
    /// assert!(MatchResult::Success(Substitution::new()).refutation().is_none());
    /// ```
    #[must_use]
    pub fn refutation(&self) -> Option<MatchFailed> {
        match self {
            Self::Failed(_) => Some(MatchFailed(())),
            Self::Success(_) | Self::Indeterminate { .. } => None,
        }
    }
}

/// A token that the left-hand side of a pattern failed to match a subject: no instance of the
/// subject is an instance of the pattern.
///
/// It is minted only from a failed match, by [`MatchResult::refutation`] or by the collection
/// matcher when the deferred collection pairs of a match have no solution. A caller outside
/// this module can name the type but not build a value:
///
/// ```compile_fail
/// use k_rust_backend::matching::{MatchFailed, MatchResult};
/// fn refute(r: &MatchResult) {
///     let _: Option<MatchFailed> = Some(MatchFailed(()));
/// }
/// ```
///
/// ```
/// use k_rust_backend::matching::{MatchFailed, MatchResult};
/// fn refute(r: &MatchResult) {
///     let _: Option<MatchFailed> = r.refutation();
/// }
/// ```
#[derive(Debug)]
pub struct MatchFailed(());

/// Why no instance of a subject is an instance of a pattern.
///
/// A clash of roots carries a [`HeadClash`], and a variable that would be bound to a term built
/// around itself a [`RigidCycle`]. The backend builds both only from roots that are the roots of
/// every value their terms denote, so neither refutation can be stated about two bare terms:
///
/// ```compile_fail
/// use k_rust_backend::{matching::FailReason, term::Term};
/// fn refute(t: Term) -> FailReason {
///     FailReason::DifferentSymbols(t.clone(), t)
/// }
/// ```
///
/// ```
/// use k_rust_backend::{matching::FailReason, term::Term};
/// fn refute(t: Term) -> FailReason {
///     FailReason::DifferentValues(t.clone(), t)
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FailReason {
    DifferentValues(Term, Term),
    /// Two roots that no one value has.
    DifferentSymbols(HeadClash),
    /// Two collections whose elements or entries cannot be paired: their contents differ, not
    /// their roots.
    DifferentContents(Term, Term),
    DifferentSorts(Term, Term),
    /// A variable that would be bound to a term built around it by free constructors and
    /// injections.
    VariableRecursion(RigidCycle),
    VariableConflict(Variable, Term, Term),
    /// A constructor-like map key or set element of the pattern that the subject, whose keys or
    /// elements are all constructor-like and which has no rest, does not contain.
    KeyNotFound(Term),
    /// A map key or a set element that occurs twice, and the collection: `\bottom`.
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

/// A sort in which no sort variable occurs: a sort of the theory and a node of its order.
/// The derived order is the inner sort's, which `Borrow<Sort>` lookups rely on.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct ClosedSort(Sort);

impl ClosedSort {
    pub(crate) fn new(sort: Sort) -> Result<Self, Sort> {
        if first_sort_variable(&sort).is_some() {
            Err(sort)
        } else {
            Ok(Self(sort))
        }
    }

    pub(crate) fn simple(name: impl Into<Name>) -> Self {
        Self(Sort::simple(name))
    }

    pub(crate) fn sort(&self) -> &Sort {
        &self.0
    }

    pub(crate) fn head(&self) -> &Name {
        let Sort::Application { name, .. } = &self.0 else {
            unreachable!("a closed sort has an application root")
        };
        name
    }
}

impl std::borrow::Borrow<Sort> for ClosedSort {
    fn borrow(&self) -> &Sort {
        self.sort()
    }
}

fn first_sort_variable(sort: &Sort) -> Option<&Name> {
    match sort {
        Sort::Variable(name) => Some(name),
        Sort::Application { arguments, .. } => arguments.iter().find_map(first_sort_variable),
    }
}

/// The reflexive-transitive closure of declared pairs over whole closed sorts.
/// Closed-sort membership is answered only from that closure: a declared instance is below
/// its supersort regardless of arity, other instances gain no edge, and constructors gain no
/// covariance from their arguments. The head relation is only the closure's projection: it
/// over-approximates whether some instance of one head may be below another.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SortGraph {
    /// Every node and the nodes below it, itself included: the closure of the subsort axioms.
    below: BTreeMap<ClosedSort, BTreeSet<ClosedSort>>,
    /// The declared sort constructors; a closed sort of one that is no node is below only itself.
    constructors: BTreeSet<Name>,
    /// Head projection of `below` (I2), reflexive on every constructor.
    heads_below: BTreeMap<Name, BTreeSet<Name>>,
}

impl SortGraph {
    /// Derives `heads_below` from the closure: for each node, the heads of its set plus its own
    /// head; each declared constructor maps at least to itself.
    pub(crate) fn from_closure(
        constructors: impl IntoIterator<Item = Name>,
        below: BTreeMap<ClosedSort, BTreeSet<ClosedSort>>,
    ) -> Self {
        let constructors = constructors.into_iter().collect::<BTreeSet<_>>();
        let mut heads_below = constructors
            .iter()
            .map(|name| (name.clone(), BTreeSet::from([name.clone()])))
            .collect::<BTreeMap<_, _>>();
        for (sup, subs) in &below {
            let heads = heads_below.entry(sup.head().clone()).or_default();
            heads.insert(sup.head().clone());
            heads.extend(subs.iter().map(|sub| sub.head().clone()));
        }
        Self {
            below,
            constructors,
            heads_below,
        }
    }

    pub fn insert(&mut self, supersort: impl Into<Name>, subsorts: impl IntoIterator<Item = Name>) {
        let supersort = supersort.into();
        let mut heads = subsorts.into_iter().collect::<BTreeSet<_>>();
        heads.insert(supersort.clone());
        let below = heads.iter().cloned().map(ClosedSort::simple).collect();
        self.below
            .insert(ClosedSort::simple(supersort.clone()), below);
        self.heads_below.insert(supersort.clone(), heads);
        self.constructors.insert(supersort);
    }

    pub fn check_subsort(&self, sub: &Sort, sup: &Sort) -> Result<bool, SortError> {
        // Reflexivity holds even before resolving a sort; distinct root variables are open.
        if sub == sup {
            return Ok(true);
        }
        let Sort::Application { name: sub_head, .. } = sub else {
            let Sort::Variable(name) = sub else {
                unreachable!()
            };
            return Err(SortError::FoundSortVariable(name.clone()));
        };
        let Sort::Application { name: sup_head, .. } = sup else {
            let Sort::Variable(name) = sup else {
                unreachable!()
            };
            return Err(SortError::FoundSortVariable(name.clone()));
        };
        // A node's down-set states every declared path to that whole sort, without covariance.
        // A closed sub absent from that complete set has no path to sup, so the answer is false.
        if let Some(set) = self.below.get(sup) {
            if set.contains(sub) {
                return Ok(true);
            }
            if first_sort_variable(sub).is_none() {
                return Ok(false);
            }
        }
        // A closed instance absent from the axioms is below only itself; its head must be known.
        // The declared-sort check keeps an undeclared head an error.
        if !self.constructors.contains(sup_head) && !self.heads_below.contains_key(sup_head) {
            return Err(SortError::FoundUnknownSort(sup.clone()));
        }
        let variable = first_sort_variable(sub).or_else(|| first_sort_variable(sup));
        let Some(variable) = variable else {
            return Ok(false);
        };
        // Open sorts stand for all instances. Only absence in the head projection refutes all.
        if sub_head != sup_head
            && !self
                .heads_below
                .get(sup_head)
                .is_some_and(|heads| heads.contains(sub_head))
        {
            return Ok(false);
        }
        Err(SortError::FoundSortVariable(variable.clone()))
    }

    fn overlap(&self, left: &Sort, right: &Sort) -> bool {
        self.known_overlap(left, right).unwrap_or(true)
    }

    /// Whether two closed sorts with known heads have a common subsort in the exact order.
    /// A closed sort absent from the axioms has the singleton down-set containing itself.
    pub(crate) fn known_overlap(&self, left: &Sort, right: &Sort) -> Option<bool> {
        let (
            Sort::Application {
                name: left_head, ..
            },
            Sort::Application {
                name: right_head, ..
            },
        ) = (left, right)
        else {
            return None;
        };
        if first_sort_variable(left).is_some()
            || first_sort_variable(right).is_some()
            || (!self.constructors.contains(left_head) && !self.heads_below.contains_key(left_head))
            || (!self.constructors.contains(right_head)
                && !self.heads_below.contains_key(right_head))
        {
            return None;
        }
        Some(match (self.below.get(left), self.below.get(right)) {
            (Some(a), Some(b)) => !a.is_disjoint(b),
            (Some(a), None) => a.contains(right),
            (None, Some(b)) => b.contains(left),
            (None, None) => left == right,
        })
    }

    pub(crate) fn closures(&self) -> impl Iterator<Item = (&ClosedSort, &BTreeSet<ClosedSort>)> {
        self.below.iter()
    }

    /// The maximal sorts below both `left` and `right` in the exact order: every common subsort
    /// is below one of them, and none of them is strictly below another. `None` when either
    /// sort has a sort variable or an unknown head, so that the order does not decide the
    /// question; an empty list when the two sorts have no common subsort. A closed sort absent
    /// from the axioms has the singleton down-set containing itself.
    pub(crate) fn maximal_common_subsorts(&self, left: &Sort, right: &Sort) -> Option<Vec<Sort>> {
        self.known_overlap(left, right)?;
        let down = |sort: &Sort| -> BTreeSet<Sort> {
            match self.below.get(sort) {
                Some(below) => below.iter().map(|sort| sort.sort().clone()).collect(),
                None => BTreeSet::from([sort.clone()]),
            }
        };
        let (left_down, right_down) = (down(left), down(right));
        let common = left_down
            .intersection(&right_down)
            .cloned()
            .collect::<Vec<_>>();
        Some(
            common
                .iter()
                .filter(|candidate| {
                    !common.iter().any(|other| {
                        other != *candidate && self.check_subsort(candidate, other) == Ok(true)
                    })
                })
                .cloned()
                .collect(),
        )
    }

    /// An over-approximation over heads; must never answer a question about one closed sort.
    pub(crate) fn heads_possibly_below(&self, head: &str) -> Option<&BTreeSet<Name>> {
        self.heads_below.get(head)
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
        && sorts.known_overlap(left_source, right_source) == Some(false)
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
                if symbol.attributes.head_role() == HeadRole::FreeConstructor
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
/// (`BackendDefinition::instance_normal`): an equation may rewrite some instance of any other
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
        definition.sort_graph(),
        Some(definition),
        pattern,
        subject,
        mode == MatchMode::Evaluate,
    )
}

/// [`match_terms_in_definition`] in `Evaluate` mode for an equation's left-hand side `pattern`,
/// whose map frames in `unread_frames` nothing else in the equation reads
/// (`rule::unread_map_frames`). Such a frame is left unbound where the subject map is
/// `ceil_free` and the pattern's keys are all found in it, instead of being bound to a copy of
/// the subject's other entries ([`Matcher::match_maps`]).
pub(crate) fn match_equation_in_definition(
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    unread_frames: &BTreeSet<Variable>,
) -> MatchResult {
    match_terms_with_context_and_frames(
        MatchMode::Evaluate,
        definition.sort_graph(),
        Some(definition),
        pattern,
        subject,
        true,
        unread_frames,
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

    let matcher = Matcher::new(
        mode,
        definition.sort_graph(),
        Some(definition),
        pairs.iter().cloned().collect(),
    );
    matcher.finish(|| pairs)
}

/// Match an equation's left-hand side `pattern` against `subject` in `Evaluate` mode, as the
/// critical-pair join of the load-time check does (`confluence::join`): the root of `subject` is
/// the term the equation is tried on, and an equation-head application below it is read as a
/// value only with the evidence `settled` gives, never with the simplifier's certificate or the
/// instance-normal scan, which are the claims the check decides.
pub(crate) fn match_with_settled_evidence(
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    settled: &SettledEvidence<'_>,
) -> MatchResult {
    let _span = measure::algorithm_span(Algorithm::BackendMatchingSyntactic);
    measure::bump(Counter::MatchingProblems);
    if pattern == subject {
        return MatchResult::Success(Substitution::new());
    }
    if !pattern
        .attributes()
        .variables
        .is_disjoint(&subject.attributes().variables)
    {
        let shared = pattern
            .attributes()
            .variables
            .intersection(&subject.attributes().variables)
            .cloned()
            .collect();
        return MatchResult::Failed(FailReason::SharedVariables(shared));
    }
    let mut matcher = Matcher::new(
        MatchMode::Evaluate,
        definition.sort_graph(),
        Some(definition),
        VecDeque::from([(pattern.clone(), subject.clone())]),
    );
    matcher.normal_forms.settled = Some(settled);
    matcher.normal_forms.given.equation_root(subject.clone());
    matcher.finish(|| vec![(pattern.clone(), subject.clone())])
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
    match_terms_with_context_and_frames(
        mode,
        sorts,
        definition,
        pattern,
        subject,
        equation_root,
        &NO_FRAMES,
    )
}

fn match_terms_with_context_and_frames(
    mode: MatchMode,
    sorts: &SortGraph,
    definition: Option<&BackendDefinition>,
    pattern: &Term,
    subject: &Term,
    equation_root: bool,
    unread_frames: &BTreeSet<Variable>,
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
    matcher.unread_frames = unread_frames;
    if equation_root {
        matcher.normal_forms.given.equation_root(subject.clone());
    }
    matcher.finish(|| vec![(pattern.clone(), subject.clone())])
}

static NO_FRAMES: BTreeSet<Variable> = BTreeSet::new();

struct Matcher<'a> {
    mode: MatchMode,
    sorts: &'a SortGraph,
    definition: Option<&'a BackendDefinition>,
    substitution: Substitution,
    queue: VecDeque<(Term, Term)>,
    map_queue: VecDeque<(Term, Term)>,
    indeterminate: Vec<(Term, Term)>,
    /// Algebraic function decomposition gives a sufficient instance only. Its bindings must
    /// not justify refutation elsewhere in this problem or escape an unresolved match.
    tentative_arguments: bool,
    /// The oracle that classifies subject terms as the values they denote.
    normal_forms: SubjectNormalForms<'a>,
    /// Map frames of the pattern whose binding nothing reads ([`match_equation_in_definition`]).
    unread_frames: &'a BTreeSet<Variable>,
}

/// Subject applications (these handles, not equal terms) whose root is taken as it stands: the
/// root an equation is tried on, which the equation rewrites as written, and a subject that
/// overload resolution lifted from an application whose root is fixed, which an overload
/// equation rewrites by construction ([`Matcher::resolve_overloads`]). The two insertion
/// methods are the only ones.
#[derive(Default)]
struct GivenHeads(Vec<Term>);

impl GivenHeads {
    /// The term an equation is tried on.
    fn equation_root(&mut self, subject: Term) {
        self.0.push(subject);
    }

    /// The lifted form of a subject application whose root is fixed.
    fn overload_lift(&mut self, lifted: Term) {
        self.0.push(lifted);
    }

    fn contains(&self, term: &Term) -> bool {
        self.0.iter().any(|given| given.ptr_eq(term))
    }
}

/// The evidence the critical-pair join gives the matcher for an equation-head application.
type SettledEvidence<'a> = dyn Fn(&Term) -> Option<NormalEvidence> + 'a;

/// The matcher's evidence that an equation-head subject application is a normal form on every
/// instance, so that its root is the root of every value it denotes: its root is given
/// ([`GivenHeads`]), the simplifier certified it ([`NormalEvidence::certified`]), or it is
/// instance-normal ([`BackendDefinition::instance_normal`]), which is asked once per term.
struct SubjectNormalForms<'a> {
    definition: Option<&'a BackendDefinition>,
    given: GivenHeads,
    /// For the critical-pair join (`confluence::join`): the only evidence besides the given
    /// heads, in place of the certificate and the instance-normal scan, which the join must not
    /// read (`match_with_settled_evidence`).
    settled: Option<&'a SettledEvidence<'a>>,
    /// Instance normality of the subject terms asked about or implied so far: every argument of
    /// an instance-normal constructor or equation-head application, and the operand of an
    /// instance-normal injection, is instance-normal, so one scan covers the whole subterm.
    instance_normal: FxHashMap<Term, Option<InstanceNormal>>,
}

impl NormalForms for SubjectNormalForms<'_> {
    fn evidence(&mut self, application: &Term) -> Option<NormalEvidence> {
        if self.given.contains(application) {
            return Some(NormalEvidence::given());
        }
        if let Some(settled) = self.settled {
            return settled(application);
        }
        // Certified by the simplifier: no equation applies to it on any path, so no scan.
        if let Some(certified) = NormalEvidence::certified(application) {
            return Some(certified);
        }
        let token = match self.instance_normal.get(application) {
            Some(known) => *known,
            None => {
                let token = self
                    .definition
                    .and_then(|definition| definition.instance_normal(application));
                self.instance_normal.insert(application.clone(), token);
                token
            }
        };
        token.map(NormalEvidence::instance_normal)
    }
}

impl SubjectNormalForms<'_> {
    /// Record the immediate subterms of an instance-normal `subject` that the matcher is about
    /// to compare as instance-normal too: a subterm of a normal form is a normal form, on every
    /// instance.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn inherit(&mut self, subject: &Term) {
        let Some(Some(token)) = self.instance_normal.get(subject).copied() else {
            return;
        };
        let subterm = Some(token.argument());
        match subject.kind() {
            TermKind::Application {
                symbol, arguments, ..
            } => match symbol.attributes.head_role() {
                HeadRole::FreeConstructor | HeadRole::EquationHead => {
                    for argument in arguments {
                        self.instance_normal.insert(argument.clone(), subterm);
                    }
                }
                HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual => {}
            },
            TermKind::Injection { term, .. } => {
                self.instance_normal.insert(term.clone(), subterm);
            }
            TermKind::Variable(_)
            | TermKind::And(..)
            | TermKind::DomainValue { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. } => {}
        }
    }
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
            tentative_arguments: false,
            normal_forms: SubjectNormalForms {
                definition,
                given: GivenHeads::default(),
                settled: None,
                instance_normal: FxHashMap::default(),
            },
            unread_frames: &NO_FRAMES,
        }
    }

    fn finish(mut self, original: impl FnOnce() -> Vec<(Term, Term)>) -> MatchResult {
        let result = self.run();
        if self.tentative_arguments && (result.is_err() || !self.indeterminate.is_empty()) {
            return MatchResult::Indeterminate {
                substitution: Substitution::new(),
                remainder: original(),
            };
        }
        if let Err(reason) = result {
            return MatchResult::Failed(reason);
        }
        if self.indeterminate.is_empty() {
            MatchResult::Success(self.substitution)
        } else {
            self.indeterminate.reverse();
            MatchResult::Indeterminate {
                substitution: self.substitution,
                remainder: self.indeterminate,
            }
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
        // Every arm below either compares the subject's root and arguments or refutes the pair
        // by the subject's root, so the subject is classified here as the value it denotes, and
        // not earlier: its oracle may run the instance-normal scan, which the pairs decided above
        // never need. For an equation-head subject application whose root is not fixed, an
        // equation may give some instance other arguments or another root. An uninterpreted
        // symbol likewise does not individuate its arguments or separate itself from other
        // roots. Each pair is left to the caller unless it is syntactically solved.
        let subject_head = classify_value(&subject, &mut self.normal_forms);
        if let Head::Open(Open::EquationHead | Open::Uninterpreted) = subject_head {
            if pattern == subject {
                return Ok(());
            }
            return self.defer(pattern, subject);
        }
        let policy = matcher_root_policy(
            self.mode,
            pattern_head(self.mode, self.definition, &pattern),
            subject_head,
            &MatchedPair {
                definition: self.definition,
                pattern: &pattern,
                subject: &subject,
            },
        );

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
                    ..
                },
            ) => {
                if pattern_target != subject_target {
                    return Err(FailReason::DifferentSorts(pattern, subject));
                }
                if pattern_source == subject_source {
                    self.match_subterms(
                        std::slice::from_ref(pattern_term),
                        ComparedSubject::of(subject_head, &subject),
                    );
                    return Ok(());
                }
                self.match_differing_injections(pattern, subject)
            }
            (
                TermKind::Application {
                    sort_arguments: pattern_sorts,
                    arguments: pattern_arguments,
                    ..
                },
                TermKind::Application {
                    sort_arguments: subject_sorts,
                    arguments: subject_arguments,
                    ..
                },
            ) if matches!(policy, RootPolicy::Decompose) => {
                // A complete as-written instance suffices to apply an equation, preserving
                // simplifications over algebraic functions. Failure of this candidate, even
                // at a later binding conflict, says nothing about other algebraic instances.
                if self.mode == MatchMode::Evaluate
                    && matches!(
                        subject_head,
                        Head::Open(Open::Function {
                            refutable_arguments: false,
                            ..
                        })
                    )
                {
                    self.tentative_arguments = true;
                }
                if pattern_arguments.len() != subject_arguments.len() {
                    return Err(FailReason::ArgumentLengthsDiffer(pattern, subject));
                }
                if pattern_sorts != subject_sorts {
                    return Err(FailReason::DifferentSorts(pattern, subject));
                }
                self.match_subterms(
                    pattern_arguments,
                    ComparedSubject::of(subject_head, &subject),
                );
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
                left_heads.to_vec(),
                left_rest
                    .clone()
                    .map(|(middle, tails)| (middle, tails.to_vec())),
                right_heads.to_vec(),
                right_rest
                    .clone()
                    .map(|(middle, tails)| (middle, tails.to_vec())),
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
                left_elements.to_vec(),
                left_rest.clone(),
                right_elements.to_vec(),
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
                        left_entries,
                        left_rest.clone(),
                        &subject,
                        right_entries,
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
            _ => match policy {
                RootPolicy::Refute(clash) => Err(FailReason::DifferentSymbols(
                    clash.between(pattern, subject),
                )),
                RootPolicy::Decompose | RootPolicy::Undecided => {
                    if list_update_cannot_match(&pattern, &subject) {
                        Err(FailReason::DifferentValues(pattern, subject))
                    } else {
                        self.defer(pattern, subject)
                    }
                }
            },
        }
    }

    /// Pair the immediate subterms of a pattern with those of a subject with the same root,
    /// the one place the matcher replaces a pair by pairs of subterms: the arguments of two
    /// applications of one symbol that the root policy decomposes, or the operands of two
    /// injections with the same sorts. `subject` says why the subject's subterms are the ones
    /// to compare. An instance-normal subject passes its normality on to its subterms.
    fn match_subterms(&mut self, pattern_subterms: &[Term], subject: ComparedSubject<'_>) {
        let subject = subject.term();
        self.normal_forms.inherit(subject);
        let subject_subterms = match subject.kind() {
            TermKind::Application { arguments, .. } => arguments.as_slice(),
            TermKind::Injection { term, .. } => std::slice::from_ref(term),
            _ => unreachable!("only applications and injections are compared by their subterms"),
        };
        for (pattern, subject) in pattern_subterms.iter().zip(subject_subterms) {
            self.enqueue(pattern.clone(), subject.clone());
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
            // A rewrite rule's pattern is compared as written with an operand whose root is
            // fixed, or residual as in `matcher_root_policy`.
            if self.mode == MatchMode::Rewrite
                && matches!(
                    classify_value(subject_term, &mut self.normal_forms),
                    Head::Fixed(_) | Head::Residual
                )
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
                if self.mode == MatchMode::Rewrite
                    && matches!(
                        classify_pattern(PatternReading::AsWritten, pattern_term),
                        Head::Fixed(_) | Head::Residual
                    )
                {
                    self.enqueue(pattern_term.clone(), subject_term);
                    return Ok(());
                }
                return self.defer(pattern_term.clone(), subject_term);
            }
            // A conjunction (an `as` pattern `\and(P, A)`) matches the lifted subject when each
            // conjunct does, which `match_one` decomposes: `inj{S,T}(s)` is `inj{P,T}(inj{S,P}(s))`.
            if matches!(pattern_term.kind(), TermKind::And(..)) {
                self.enqueue(
                    pattern_term.clone(),
                    Term::injection(
                        subject_source.clone(),
                        pattern_source.clone(),
                        subject_term.clone(),
                    ),
                );
                return Ok(());
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
            return self.no_lowering(term);
        };

        // A lower production would replace this root with one whose arguments can
        // be compared. An uninterpreted application supplies no such decomposition.
        if symbol.attributes.head_role() == HeadRole::Uninterpreted {
            return OverloadLowering::Indeterminate;
        }

        let candidates = definition.overloads().overloaded_by(&symbol.name);
        let mut lowered = Vec::new();
        let mut indeterminate = Vec::new();
        for candidate_name in candidates {
            let Some(candidate) = definition.symbols().get(&candidate_name) else {
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
                    candidate != lesser && definition.overloads().is_overloading(candidate, lesser)
                })
            })
            .collect::<Vec<_>>();
        if let Some((_, first)) = minimal.first()
            && minimal.iter().all(|(_, term)| term == first)
            && indeterminate.iter().all(|candidate| {
                minimal
                    .iter()
                    .any(|(name, _)| definition.overloads().is_overloading(candidate, name))
            })
        {
            return OverloadLowering::Lowered(first.clone());
        }
        if minimal.is_empty() && indeterminate.is_empty() {
            self.no_lowering(term)
        } else {
            OverloadLowering::Indeterminate
        }
    }

    /// No production of the overload family represents `term` in the requested sort. That
    /// refutes only when `term` is concrete and its root is the root of every value it denotes:
    /// an equation may rewrite an equation-head application that is not a normal form on every
    /// instance to one that lowers, and a macro or alias application denotes its expansion.
    fn no_lowering(&mut self, term: &Term) -> OverloadLowering {
        if !term.concrete_after_normalization() {
            return OverloadLowering::Indeterminate;
        }
        match classify_value(term, &mut self.normal_forms) {
            Head::Fixed(_) => OverloadLowering::Impossible,
            Head::Open(_) | Head::Residual => OverloadLowering::Indeterminate,
        }
    }

    /// Lift a pair of distinct heads of one overload family to their least common production.
    /// Lifting the subject to `common(inj(arguments))` asserts that the pair is equivalent to
    /// comparing arguments under `common`. That holds when the subject's own head is fixed: then
    /// the lifted term denotes the subject's value through the overload equation, and a value
    /// with head `common` is an instance of the lifted pattern exactly when the arguments match.
    /// A subject whose head is not fixed is not lifted, and its lifted form, which an overload
    /// equation rewrites by construction, is given its head ([`GivenHeads::overload_lift`]).
    fn resolve_overloads(&mut self, pattern: &Term, subject: &Term) -> Option<(Term, Term)> {
        let definition = self.definition?;
        let pattern_symbol = overload_head(pattern)?;
        let subject_symbol = overload_head(subject)?;
        let pattern_name = &pattern_symbol.name;
        let subject_name = &subject_symbol.name;
        // A symbol outside every overload relation neither overloads the other head nor shares
        // an overload with it, so no common production exists: most pairs of distinct heads
        // end here, before a view of either side is built.
        if pattern_name == subject_name
            || !definition.overloads().is_overloaded(pattern_name)
            || !definition.overloads().is_overloaded(subject_name)
        {
            return None;
        }
        // Lifting to a common free head must not give an uninterpreted application
        // argument bindings that its own role forbids.
        if pattern_symbol.attributes.head_role() == HeadRole::Uninterpreted
            || subject_symbol.attributes.head_role() == HeadRole::Uninterpreted
        {
            return None;
        }
        let pattern_view = OverloadView::new(pattern)?;
        let subject_view = OverloadView::new(subject)?;
        let common_name = if definition
            .overloads()
            .is_overloading(&pattern_view.symbol.name, &subject_view.symbol.name)
        {
            pattern_view.symbol.name.clone()
        } else if definition
            .overloads()
            .is_overloading(&subject_view.symbol.name, &pattern_view.symbol.name)
        {
            subject_view.symbol.name.clone()
        } else {
            let common = definition
                .overloads()
                .common_overloads(&pattern_view.symbol.name, &subject_view.symbol.name);
            let minimal = common
                .iter()
                .filter(|candidate| {
                    !common.iter().any(|other| {
                        candidate != &other
                            && definition.overloads().is_overloading(candidate, other)
                    })
                })
                .cloned()
                .collect::<Vec<_>>();
            let [common] = minimal.as_slice() else {
                return None;
            };
            common.clone()
        };
        let common = definition.symbols().get(&common_name)?.clone();
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
        if let Head::Open(Open::EquationHead | Open::Uninterpreted) =
            classify_value(subject_application, &mut self.normal_forms)
        {
            return None;
        }
        let pattern = pattern_view.lift(common.clone(), &sort_arguments, self.sorts)?;
        let subject = subject_view.lift(common, &sort_arguments, self.sorts)?;
        if let Some(lifted) = overload_application(&subject) {
            self.normal_forms.given.overload_lift(lifted.clone());
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
            .overloads()
            .overloaded_by(&pattern.name)
            .into_iter()
            .filter_map(|name| definition.symbols().get(&name))
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

    /// Match the map `pattern_entries` with `pattern_rest` against `subject`, whose entries and
    /// rest are `subject_entries` and `subject_rest`.
    ///
    /// The pattern's keys are taken under the substitution so far, which may reorder them or
    /// make two of them equal; the subject's entries are as `Term::map` stores them, so its keys
    /// are found by search (`split_common_keys`), and only the entries outside the common keys
    /// are copied.
    fn match_maps(
        &mut self,
        definition: Arc<MapDefinition>,
        pattern_entries: &[(Term, Term)],
        pattern_rest: Option<Term>,
        subject: &Term,
        subject_entries: &[(Term, Term)],
        subject_rest: Option<Term>,
    ) -> Result<(), FailReason> {
        let mut pattern_entries = pattern_entries
            .iter()
            .map(|(key, value)| (substitute(key, &self.substitution), value.clone()))
            .collect::<Vec<_>>();
        check_duplicate_keys(&definition, &pattern_entries, &pattern_rest)?;
        if !binds_each_key_once(subject) {
            check_duplicate_keys(&definition, subject_entries, &subject_rest)?;
        }

        if pattern_rest
            .as_ref()
            .is_some_and(|rest| is_opaque_concat(rest, &definition.symbols.concat))
            || subject_rest
                .as_ref()
                .is_some_and(|rest| is_opaque_concat(rest, &definition.symbols.concat))
        {
            return self.defer(
                Term::map(definition.clone(), pattern_entries, pattern_rest),
                Term::map(definition, subject_entries.to_vec(), subject_rest),
            );
        }

        // The pattern's keys are pairwise different now, so ordering its entries by key alone
        // gives them the stored order of a map's entries.
        pattern_entries.sort_by(|left, right| left.0.cmp(&right.0));
        let found = find_common_keys(&pattern_entries, subject_entries);
        // The subject binds every key the pattern names, so the pattern's rest would be bound to
        // the subject's other entries, a map of the rest's sort. When nothing in the equation
        // reads that binding (`rule::unread_map_frames`), the instance is the same without it:
        // its one other use, the binding's definedness obligation (`ceil_term` of the bound
        // term, `condition::EquationInstance::new`), is empty, since a sub-map of a `ceil_free`
        // map is `ceil_free` (its entries are a subset, its keys still strictly increase, its
        // rest is the same). So the rest is not built.
        if found.pattern_only.is_empty()
            && subject.attributes().ceil_free()
            && pattern_rest.as_ref().is_some_and(|rest| {
                matches!(rest.kind(), TermKind::Variable(variable)
                    if self.unread_frames.contains(variable))
            })
        {
            self.queue.extend(found.values);
            return Ok(());
        }
        // A constructor-like pattern key that no subject entry binds syntactically, while the
        // subject has no rest (which could bind it) and every other key of the subject is
        // constructor-like too, is bound by no subject entry at all:
        // distinct constructor-like terms denote distinct values. The match fails on that key,
        // decided from key attributes alone, before the subject's other entries are copied: the
        // failure names the key and nothing else, since no reader of a failed match needs the
        // subject's remainder. A constructor-like map has constructor-like keys.
        if let Some((key, _)) = found
            .pattern_only
            .iter()
            .find(|(key, _)| key.attributes().constructor_like)
            && subject_rest.is_none()
            && (subject.attributes().constructor_like
                || found
                    .others(subject_entries)
                    .all(|(key, _)| key.attributes().constructor_like))
        {
            return Err(FailReason::KeyNotFound(key.clone()));
        }
        let CommonKeys {
            mut values,
            pattern_only,
            subject_only,
        } = found.split(subject_entries);

        let pattern = MapRemainder::new(pattern_only, pattern_rest);
        let subject = MapRemainder::new(subject_only, subject_rest);
        let mut rest = self.match_map_remainders(&definition, pattern, subject)?;
        values.append(&mut rest);
        self.queue.extend(values);
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
        let pattern_elements = pattern_elements
            .into_iter()
            .map(|element| substitute(&element, &self.substitution))
            .collect::<Vec<_>>();
        check_duplicate_elements(&definition, &pattern_elements, &pattern_rest)?;
        check_duplicate_elements(&definition, &subject_elements, &subject_rest)?;
        let mut pattern_elements = pattern_elements.into_iter().collect::<BTreeSet<_>>();
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
                return Err(FailReason::KeyNotFound(element.clone()));
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
            return Err(FailReason::DifferentContents(
                set(Vec::new(), None),
                subject,
            ));
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
            return Err(FailReason::DifferentContents(
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
        if !pattern.concrete.is_empty() {
            // `match_maps` refutes a pattern key that a subject without a rest and with
            // constructor-like keys only lacks.
            debug_assert!(!subject.symbolic.is_empty() || subject.rest.is_some());
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
            return Err(FailReason::DifferentContents(
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
                return Err(FailReason::DifferentContents(
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
            // `variable = term` has no solution when `variable` occurs in `term` below free
            // constructors and injections only. Below any other root the occurrence may vanish
            // when that root is evaluated, and `variable` itself is no cycle, so the pair is left
            // to the caller. The two sides share variables in `Implies` mode, and in the other
            // modes once a pattern variable bound to a subject variable is substituted into a
            // map key or set element.
            return match rigid_occurrence(&variable, &term) {
                Some(cycle) => Err(FailReason::VariableRecursion(cycle)),
                None => self.defer(Term::variable(variable), term),
            };
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

/// How a mode reads a pattern's root: a rewrite rule's left-hand side is matched as written,
/// and an equation's left-hand side or an implication pattern denotes, at an equation-head
/// subterm, the value of its normal form.
fn pattern_reading(mode: MatchMode) -> PatternReading {
    match mode {
        MatchMode::Rewrite => PatternReading::AsWritten,
        MatchMode::Evaluate | MatchMode::Implies => PatternReading::UpToEquations,
    }
}

/// The classification of a pattern's root that [`matcher_root_policy`] reads. `Evaluate` reads an
/// equation's left-hand side as the values it denotes: an equation-head application that denotes
/// one ground term, whose instance-normal token the load recorded, is that normal form, fixed by
/// the evidence an equal subject would carry ([`RecordedPatterns`]); every other root is read up
/// to equations. The other modes read the pattern as [`pattern_reading`] says.
fn pattern_head<'t>(
    mode: MatchMode,
    definition: Option<&BackendDefinition>,
    pattern: &'t Term,
) -> Head<'t> {
    match (mode, definition) {
        (MatchMode::Evaluate, Some(definition)) => {
            classify_value(pattern, &mut RecordedPatterns(definition))
        }
        _ => classify_pattern(pattern_reading(mode), pattern),
    }
}

/// What [`matcher_root_policy`] reads about a pattern and a subject besides the classification
/// of their roots. Each fact is computed when the policy asks for it, so that a pair pays only
/// for the facts its arm reads (an overload fact is a set lookup).
trait PairFacts {
    /// Both roots are applications of symbols with one name.
    fn same_name(&self) -> bool;
    /// The pattern's root is an application of a function-typed symbol (`SymbolType::Function`),
    /// which covers equation heads and function-typed macros as well as functions.
    fn pattern_function_typed(&self) -> bool;
    /// The subject's root is an application of a function-typed symbol.
    fn subject_function_typed(&self) -> bool;
    /// The pattern's root is an application of a production of an overload family.
    fn pattern_overloaded(&self) -> bool;
    /// The subject's root is an application of a production of an overload family.
    fn subject_overloaded(&self) -> bool;
    /// The subject is concrete after normalization: ground, with roots a normal form can have.
    /// A shape, not evidence.
    fn subject_concrete(&self) -> bool;
}

/// The facts of a pair the matcher met.
struct MatchedPair<'p> {
    definition: Option<&'p BackendDefinition>,
    pattern: &'p Term,
    subject: &'p Term,
}

impl PairFacts for MatchedPair<'_> {
    fn same_name(&self) -> bool {
        matches!(
            (self.pattern.kind(), self.subject.kind()),
            (
                TermKind::Application { symbol: pattern, .. },
                TermKind::Application { symbol: subject, .. },
            ) if pattern.name == subject.name
        )
    }

    fn pattern_function_typed(&self) -> bool {
        is_function(self.pattern)
    }

    fn subject_function_typed(&self) -> bool {
        is_function(self.subject)
    }

    fn pattern_overloaded(&self) -> bool {
        is_overload_head(self.definition, self.pattern.kind())
    }

    fn subject_overloaded(&self) -> bool {
        is_overload_head(self.definition, self.subject.kind())
    }

    fn subject_concrete(&self) -> bool {
        self.subject.concrete_after_normalization()
    }
}

/// What the roots of a pattern and a subject decide ([`matcher_root_policy`]).
#[derive(Clone, Copy, Debug)]
enum RootPolicy {
    /// Two applications of one symbol, compared by their sort arguments, their arity, the
    /// symbol's algebraic axioms, and then argument by argument.
    Decompose,
    /// No value of the subject has the pattern's root; the clash is built as `Clash` says.
    Refute(Clash),
    /// The roots decide nothing.
    Undecided,
}

/// How the [`HeadClash`] of a refutation is built.
#[derive(Clone, Copy, Debug)]
enum Clash {
    /// Two fixed roots that `compare_roots` found distinct.
    Roots(ReleasedRoots),
    /// An overloaded root that is not fixed under its reading, refuted because the productions of
    /// an overload family have no equations besides their overload equations (open question Q2
    /// of the classifier's design).
    OverloadFamily,
    /// A macro or alias root, refuted as if fixed because the executable boundary rejects
    /// such terms first (open question Q3).
    ResidualRoot,
}

impl Clash {
    /// The clash between the owned pattern and subject the policy classified.
    fn between(self, pattern: Term, subject: Term) -> HeadClash {
        match self {
            Clash::Roots(witness) => HeadClash::new(witness, pattern, subject),
            Clash::OverloadFamily => HeadClash::overload_family(pattern, subject),
            Clash::ResidualRoot => HeadClash::residual_root(pattern, subject),
        }
    }
}

/// A subject whose immediate subterms the matcher pairs with those of a pattern with the same
/// root ([`Matcher::match_subterms`]), and why they are the subterms to compare.
#[derive(Clone, Copy, Debug)]
enum ComparedSubject<'t> {
    /// Its root is fixed, so its subterms are those of every value it denotes.
    Fixed(Fixed<'t>),
    /// Its root is not fixed, and an arm of [`matcher_root_policy`] compares it as written: an
    /// application of a function declared injective (open question Q5), of a function-typed
    /// symbol in `Evaluate` mode, whose root is the one an equation is tried on, or of a macro
    /// or alias in `Rewrite` mode (Q3).
    AsWritten(&'t Term),
}

impl<'t> ComparedSubject<'t> {
    fn of(head: Head<'t>, subject: &'t Term) -> Self {
        match head {
            Head::Fixed(fixed) => Self::Fixed(fixed),
            Head::Open(_) | Head::Residual => Self::AsWritten(subject),
        }
    }

    fn term(self) -> &'t Term {
        match self {
            Self::Fixed(fixed) => fixed.term(),
            Self::AsWritten(term) => term,
        }
    }
}

/// The matcher's root policy: what the root of `pattern`, classified under the reading of
/// `mode` ([`pattern_reading`]), and the root of `subject`, classified as the value it denotes
/// and not an equation head without evidence (the gate of `Matcher::match_one`), decide.
/// Pure: the classifications and `facts` are its only inputs.
///
/// The three modes read the roots differently (`matcher_root_policy` of the classifier's
/// design). `Rewrite` matches a rule's left-hand side as written, so every fixed or residual
/// root is compared by its symbol. `Evaluate` matches an equation's left-hand side against the
/// term the equation is tried on, and refutes an equation-head subject with evidence by its
/// root only when the subject is concrete (open question Q7). `Evaluate` also reads an
/// equation-head pattern with evidence ([`pattern_head`]) as the one normal form it denotes, and
/// refutes it by its root in the two cases that mirror that one: against a rigid subject, and
/// against a concrete equation-head subject with evidence of another symbol; so whether two
/// ground normal forms are one value does not depend on which side wrote which. `Implies` never
/// refutes an equation-head subject by its root (Q7), and reads no evidence for a pattern. In
/// every mode an equation-head pattern, read up to equations outside `Rewrite`, and a function
/// declared injective are compared by arguments with an application of their own symbol (Q1,
/// Q5), and an overloaded root is refuted against a rigid one (Q2).
#[must_use]
#[deny(clippy::wildcard_enum_match_arm)]
fn matcher_root_policy(
    mode: MatchMode,
    pattern: Head<'_>,
    subject: Head<'_>,
    facts: &impl PairFacts,
) -> RootPolicy {
    let applications = is_application(pattern) && is_application(subject);
    if applications && compares_applications(mode, pattern, subject, facts) {
        return if facts.same_name() {
            RootPolicy::Decompose
        } else if refutes_another_symbol(mode, pattern, subject, facts) {
            refutation(pattern, subject)
        } else {
            RootPolicy::Undecided
        };
    }
    // Two applications of one macro or alias symbol that are not compared by arguments: the
    // symbol is not free, so its applications may denote one value with different arguments,
    // and one symbol is no clash of roots.
    if applications && is_residual(pattern) && facts.same_name() {
        return RootPolicy::Undecided;
    }
    if refutes_roots(mode, pattern, subject, facts) {
        refutation(pattern, subject)
    } else {
        RootPolicy::Undecided
    }
}

/// Whether two applications are compared by symbol and then by arguments.
#[deny(clippy::wildcard_enum_match_arm)]
fn compares_applications(
    mode: MatchMode,
    pattern: Head<'_>,
    subject: Head<'_>,
    facts: &impl PairFacts,
) -> bool {
    if matches!(pattern, Head::Open(Open::Uninterpreted))
        || matches!(subject, Head::Open(Open::Uninterpreted))
    {
        return false;
    }
    // Two free-constructor applications are equal exactly when their symbols and arguments are.
    (is_free_constructor(pattern) && is_free_constructor(subject))
        // An equation-head pattern against an application of its own symbol, whose root is fixed
        // (the gate), so that its arguments are those of the normal form it denotes; the pattern
        // is read as written, although its instances need not be normal forms (Q1). A function
        // declared injective, an axiom the backend does not check against the function's
        // equations (Q5); the role keeps `injective` only for a function without `anywhere`.
        || ((is_injective_function(pattern) || is_equation_head(pattern)) && facts.same_name())
        || match mode {
            // A rule's left-hand side is matched as written: its fixed or residual root against
            // the subject's.
            MatchMode::Rewrite => is_fixed_or_residual(pattern) && is_fixed_or_residual(subject),
            // An equation's left-hand side against the term it is tried on: two applications of
            // function-typed symbols are compared as written.
            MatchMode::Evaluate => {
                facts.pattern_function_typed() && facts.subject_function_typed()
            }
            MatchMode::Implies => false,
        }
}

/// Whether two applications of different symbols that `compares_applications` compares are
/// refuted.
#[deny(clippy::wildcard_enum_match_arm)]
fn refutes_another_symbol(
    mode: MatchMode,
    pattern: Head<'_>,
    subject: Head<'_>,
    facts: &impl PairFacts,
) -> bool {
    (is_free_constructor(pattern) && is_free_constructor(subject))
        || match mode {
            MatchMode::Rewrite => true,
            // Q2: an equation's left-hand side headed by an overloaded production against a
            // concrete subject whose root is fixed. An equation-head pattern with evidence (one
            // ground normal form, whose token the load recorded) against a concrete subject whose
            // root is fixed, here an equation-head application with evidence of another symbol:
            // each side's evidence states that it is a normal form, the freeness claim states
            // that distinct normal forms are distinct values, and two applications of different
            // symbols are distinct terms, so the subject is not the pattern's one value. The
            // refutation therefore rests on the two sides' own claims and adds none. Leaving the
            // pair undecided would also be symmetric (the exchanged pair reaches this arm too),
            // but a certified normal form would then not be read as its own value on the pattern
            // side, which is what reading a ground normal form as a value means.
            MatchMode::Evaluate => {
                (facts.pattern_overloaded() || is_equation_head_value(pattern))
                    && facts.subject_concrete()
            }
            MatchMode::Implies => false,
        }
}

/// Whether the roots of a pair that no arm compares by arguments are refuted.
#[deny(clippy::wildcard_enum_match_arm)]
fn refutes_roots(
    mode: MatchMode,
    pattern: Head<'_>,
    subject: Head<'_>,
    facts: &impl PairFacts,
) -> bool {
    // Q2: an overloaded root against a rigid one, in either orientation.
    (facts.pattern_overloaded() && is_rigid_root(subject))
        || (is_rigid_root(pattern) && facts.subject_overloaded())
        || (is_rigid_root(pattern) && is_rigid_root(subject))
        || match mode {
            MatchMode::Rewrite => is_fixed_or_residual(pattern) && is_fixed_or_residual(subject),
            // Q7: an equation-head subject with evidence is refuted by its root only when it is
            // concrete. A function application, the other root that is neither rigid nor a
            // gated equation head, is never concrete after normalization. The mirror: an
            // equation-head pattern with evidence (one ground normal form) is refuted by a rigid
            // subject root.
            MatchMode::Evaluate => {
                (is_rigid_root(pattern) && facts.subject_concrete())
                    || (is_equation_head_value(pattern) && is_rigid_root(subject))
            }
            // Q7: never an equation-head subject.
            MatchMode::Implies => false,
        }
}

/// The refutation of a pair whose roots the policy separates. Two fixed roots clash through
/// `compare_roots`; otherwise the refutation rests on an open question, and the clash is built
/// by its named mint: a residual root against a fixed or residual one (Q3), and an overloaded
/// root that is not fixed under its reading (Q2), the only refutation the policy makes with an
/// open side.
#[deny(clippy::wildcard_enum_match_arm)]
fn refutation(pattern: Head<'_>, subject: Head<'_>) -> RootPolicy {
    RootPolicy::Refute(match pattern {
        Head::Fixed(pattern) => match subject {
            Head::Fixed(subject) => match compare_roots(pattern, subject) {
                RootComparison::Distinct(witness) => Clash::Roots(witness.release()),
                // Two roots `compare_roots` does not separate are compared by an arm of their own
                // kind in `Matcher::match_one`, before any refutation.
                RootComparison::SameApplication(_)
                | RootComparison::ArityMismatch
                | RootComparison::DomainValues
                | RootComparison::Injections
                | RootComparison::Collections(_) => return RootPolicy::Undecided,
            },
            Head::Residual => Clash::ResidualRoot,
            Head::Open(_) => Clash::OverloadFamily,
        },
        Head::Residual => match subject {
            Head::Fixed(_) | Head::Residual => Clash::ResidualRoot,
            Head::Open(_) => Clash::OverloadFamily,
        },
        Head::Open(_) => Clash::OverloadFamily,
    })
}

/// An application root: a free constructor, an equation head, a function, an uninterpreted
/// symbol, a macro or an alias.
#[deny(clippy::wildcard_enum_match_arm)]
fn is_application(head: Head<'_>) -> bool {
    match head {
        Head::Fixed(fixed) => match fixed.root() {
            FixedRoot::FreeConstructor | FixedRoot::EquationHead(_) => true,
            FixedRoot::DomainValue | FixedRoot::Injection | FixedRoot::Collection(_) => false,
        },
        Head::Open(open) => match open {
            Open::Function { .. } | Open::Uninterpreted | Open::EquationHead => true,
            Open::Variable | Open::And => false,
        },
        Head::Residual => true,
    }
}

/// A fixed root other than an equation head's, or a residual root: the roots the matcher
/// refutes by in every mode.
#[deny(clippy::wildcard_enum_match_arm)]
fn is_rigid_root(head: Head<'_>) -> bool {
    match head {
        Head::Fixed(fixed) => match fixed.root() {
            FixedRoot::DomainValue
            | FixedRoot::Injection
            | FixedRoot::Collection(_)
            | FixedRoot::FreeConstructor => true,
            FixedRoot::EquationHead(_) => false,
        },
        Head::Residual => true,
        Head::Open(_) => false,
    }
}

/// A fixed or residual root: every root a rule's left-hand side read as written compares by its
/// symbol.
#[deny(clippy::wildcard_enum_match_arm)]
fn is_fixed_or_residual(head: Head<'_>) -> bool {
    match head {
        Head::Fixed(_) | Head::Residual => true,
        Head::Open(_) => false,
    }
}

#[deny(clippy::wildcard_enum_match_arm)]
fn is_free_constructor(head: Head<'_>) -> bool {
    match head {
        Head::Fixed(fixed) => match fixed.root() {
            FixedRoot::FreeConstructor => true,
            FixedRoot::DomainValue
            | FixedRoot::Injection
            | FixedRoot::Collection(_)
            | FixedRoot::EquationHead(_) => false,
        },
        Head::Open(_) | Head::Residual => false,
    }
}

/// An equation-head application fixed by evidence about its value: in `Evaluate` mode, a pattern
/// that denotes one ground term with a recorded token ([`pattern_head`]); never a pattern read as
/// written.
#[deny(clippy::wildcard_enum_match_arm)]
fn is_equation_head_value(head: Head<'_>) -> bool {
    match head {
        Head::Fixed(fixed) => match fixed.root() {
            FixedRoot::EquationHead(evidence) => evidence.of_a_value(),
            FixedRoot::DomainValue
            | FixedRoot::Injection
            | FixedRoot::Collection(_)
            | FixedRoot::FreeConstructor => false,
        },
        Head::Open(_) | Head::Residual => false,
    }
}

/// An application of an equation head, fixed as written or open up to equations.
#[deny(clippy::wildcard_enum_match_arm)]
fn is_equation_head(head: Head<'_>) -> bool {
    match head {
        Head::Fixed(fixed) => match fixed.root() {
            FixedRoot::EquationHead(_) => true,
            FixedRoot::DomainValue
            | FixedRoot::Injection
            | FixedRoot::Collection(_)
            | FixedRoot::FreeConstructor => false,
        },
        Head::Open(open) => match open {
            Open::EquationHead => true,
            Open::Variable | Open::And | Open::Function { .. } | Open::Uninterpreted => false,
        },
        Head::Residual => false,
    }
}

#[deny(clippy::wildcard_enum_match_arm)]
fn is_injective_function(head: Head<'_>) -> bool {
    match head {
        Head::Open(open) => match open {
            Open::Function { injective, .. } => injective,
            Open::Variable | Open::And | Open::EquationHead | Open::Uninterpreted => false,
        },
        Head::Fixed(_) | Head::Residual => false,
    }
}

#[deny(clippy::wildcard_enum_match_arm)]
fn is_residual(head: Head<'_>) -> bool {
    match head {
        Head::Residual => true,
        Head::Fixed(_) | Head::Open(_) => false,
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

/// `term`, an application or an injection of one, lifted to the overload `common` with
/// `sort_arguments`, as overload resolution lifts it ([`Matcher::resolve_overloads`]): each
/// argument injected into `common`'s argument sort, and the application injected back into
/// `term`'s sort. `None` when a sort does not fit. The overload equation of `common` over the
/// application's symbol rewrites the lifted term to `term`, so the two are equal modulo the
/// overload axioms. For the critical-pair unifier (`confluence::unify`), which reads the
/// overload axioms as the matcher does.
pub(crate) fn lift_to_overload(
    term: &Term,
    common: Arc<crate::term::Symbol>,
    sort_arguments: &[Sort],
    sorts: &SortGraph,
) -> Option<Term> {
    OverloadView::new(term)?.lift(common, sort_arguments, sorts)
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

/// A set that holds an element twice is `\bottom` (set concatenation is nilpotent, `Term::set`),
/// so it matches nothing and nothing matches it. The pattern's elements are checked after the
/// substitution so far, which can make two of them equal. The failure reuses
/// `FailReason::DuplicateKeys`: a set's elements are its keys.
fn check_duplicate_elements(
    definition: &Arc<crate::term::SetDefinition>,
    elements: &[Term],
    rest: &Option<Term>,
) -> Result<(), FailReason> {
    let mut seen = BTreeSet::new();
    let mut duplicates = elements
        .iter()
        .filter(|element| !seen.insert(*element))
        .collect::<Vec<_>>();
    duplicates.sort();
    if let Some(element) = duplicates.first() {
        return Err(FailReason::DuplicateKeys(
            (*element).clone(),
            Term::set(definition.clone(), elements.to_vec(), rest.clone()),
        ));
    }
    Ok(())
}

/// Whether `term` is an application of a function-typed symbol (`SymbolType::Function`). This is
/// a declaration read, not a role: it covers equation heads and function-typed macros and
/// aliases as well as functions, which is what the matcher's `Evaluate` comparison of two
/// function-typed applications and its subsort arms test.
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

fn is_overload_head(definition: Option<&BackendDefinition>, kind: &TermKind) -> bool {
    let (Some(definition), TermKind::Application { symbol, .. }) = (definition, kind) else {
        return false;
    };
    definition.overloads().is_overloaded(&symbol.name)
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
    //! The root policy against the guards it replaced.

    use std::{
        cell::RefCell,
        collections::{BTreeMap, BTreeSet},
    };

    use k_rust_kore::names::WellKnownSymbol;
    use proptest::{
        prelude::*,
        test_runner::{Config, TestRng, TestRunner},
    };

    use super::*;
    use crate::{term::Symbol, tests::lean_bridge::generators};

    /// How a transcription of `Matcher::match_one` reads a symbol's role.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Flags {
        /// The declared flags, as `eea634ce` read them before the roles existed.
        Declared,
        /// The roles, as the integration base read them (`c11e4adb`).
        Roles,
    }

    /// What an arm of `Matcher::match_one` decides about the roots of a pair.
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    enum Arm {
        /// The subject is an equation-head application without evidence, or an uninterpreted
        /// application (the gate).
        Gate,
        /// An arm of its own kind: two domain values, two injections, two collections of one
        /// category, or in `Evaluate` an injection against a collection.
        Kind,
        /// Two applications of one symbol compared by their arguments.
        Decompose,
        /// Refuted by the roots.
        Refute,
        /// Left undecided by the roots.
        Undecided,
    }

    fn symbol(term: &Term) -> Option<&Symbol> {
        match term.kind() {
            TermKind::Application { symbol, .. } => Some(symbol),
            _ => None,
        }
    }

    /// `is_constructor` of the transcribed commit.
    fn head_is_constructor(flags: Flags, term: &Term) -> bool {
        symbol(term).is_some_and(|symbol| match flags {
            Flags::Declared => symbol.attributes.symbol_type == SymbolType::Constructor,
            Flags::Roles => symbol.attributes.head_role() == HeadRole::FreeConstructor,
        })
    }

    /// `is_function` of both commits.
    fn head_is_function(term: &Term) -> bool {
        matches!(
            term.kind(),
            TermKind::Application { symbol, .. }
                if matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
        )
    }

    /// `is_anywhere_application` of the transcribed commit.
    fn head_is_anywhere_application(flags: Flags, term: &Term) -> bool {
        symbol(term).is_some_and(|symbol| match flags {
            Flags::Declared => {
                let declared = symbol.attributes.declaration();
                declared.anywhere && !declared.declared_function
            }
            Flags::Roles => symbol.attributes.head_role() == HeadRole::EquationHead,
        })
    }

    /// The `injective` read of the decomposition guard of the transcribed commit.
    fn head_is_injective(flags: Flags, symbol: &Symbol) -> bool {
        match flags {
            Flags::Declared => symbol.attributes.declaration().injective,
            Flags::Roles => matches!(
                symbol.attributes.head_role(),
                HeadRole::Function {
                    injective: true,
                    ..
                }
            ),
        }
    }

    /// `is_rigid` of the transcribed commit.
    fn head_is_rigid(flags: Flags, term: &Term) -> bool {
        matches!(
            term.kind(),
            TermKind::DomainValue { .. }
                | TermKind::Injection { .. }
                | TermKind::Map { .. }
                | TermKind::List { .. }
                | TermKind::Set { .. }
        ) || symbol(term).is_some_and(|symbol| match flags {
            Flags::Declared => {
                symbol.attributes.symbol_type == SymbolType::Constructor
                    || symbol.attributes.macro_or_alias
            }
            Flags::Roles => matches!(
                symbol.attributes.head_role(),
                HeadRole::FreeConstructor | HeadRole::Residual
            ),
        })
    }

    /// `is_rewrite_rigid` of the transcribed commit.
    fn head_is_rewrite_rigid(flags: Flags, term: &Term) -> bool {
        head_is_rigid(flags, term) || head_is_anywhere_application(flags, term)
    }

    /// `is_overload_head`, over the overloaded names of the generated case.
    fn head_is_overload_head(overloaded: &BTreeSet<Name>, term: &Term) -> bool {
        symbol(term).is_some_and(|symbol| overloaded.contains(&symbol.name))
    }

    /// The arms of `Matcher::match_one` from the subject gate to the end
    /// (`git show eea634ce:crates/k-rust-backend/src/matching/mod.rs`, lines 598-803), with
    /// every guard as written there, over the predicates above. `fixed` is the answer of
    /// `subject_head_is_fixed` for an equation-head subject; `can_narrow_overload` is false,
    /// since no overload family of the generated cases has a lesser production. With
    /// [`Flags::Roles`] it transcribes the integration base, where the roles replaced the
    /// declared flags and a pair of applications of one macro or alias symbol that the
    /// decomposition guard does not take is deferred.
    fn transcribed_arm(
        flags: Flags,
        mode: MatchMode,
        pattern: &Term,
        subject: &Term,
        fixed: bool,
        overloaded: &BTreeSet<Name>,
    ) -> Arm {
        let is_constructor = |term| head_is_constructor(flags, term);
        let is_function = head_is_function;
        let is_rigid = |term| head_is_rigid(flags, term);
        let is_rewrite_rigid = |term| head_is_rewrite_rigid(flags, term);
        let is_anywhere_application = |term| head_is_anywhere_application(flags, term);
        let is_overload_head = |term| head_is_overload_head(overloaded, term);
        let subject_head_is_fixed = !is_anywhere_application(subject) || fixed;
        if !subject_head_is_fixed {
            return Arm::Gate;
        }
        match (pattern.kind(), subject.kind()) {
            (TermKind::DomainValue { .. }, TermKind::DomainValue { .. })
            | (TermKind::Injection { .. }, TermKind::Injection { .. }) => Arm::Kind,
            (
                TermKind::Application {
                    symbol: pattern_symbol,
                    ..
                },
                TermKind::Application {
                    symbol: subject_symbol,
                    ..
                },
            ) if (is_constructor(pattern) && is_constructor(subject))
                || (mode == MatchMode::Rewrite
                    && is_rewrite_rigid(pattern)
                    && is_rewrite_rigid(subject))
                || ((head_is_injective(flags, pattern_symbol)
                    || is_anywhere_application(pattern))
                    && pattern_symbol.name == subject_symbol.name)
                || (mode == MatchMode::Evaluate
                    && is_function(pattern)
                    && is_function(subject)) =>
            {
                if pattern_symbol.name != subject_symbol.name {
                    if mode == MatchMode::Rewrite
                        || (is_constructor(pattern) && is_constructor(subject))
                        || (mode == MatchMode::Evaluate
                            && is_overload_head(pattern)
                            && subject.concrete_after_normalization())
                    {
                        return Arm::Refute;
                    }
                    return Arm::Undecided;
                }
                Arm::Decompose
            }
            (left, right) if same_collection_category(left, right) => Arm::Kind,
            (TermKind::Injection { .. }, right)
                if mode == MatchMode::Evaluate && is_collection(right) =>
            {
                Arm::Kind
            }
            (left, TermKind::Injection { .. })
                if mode == MatchMode::Evaluate && is_collection(left) =>
            {
                Arm::Kind
            }
            (
                TermKind::Application {
                    symbol: pattern_symbol,
                    ..
                },
                TermKind::Application {
                    symbol: subject_symbol,
                    ..
                },
            ) if flags == Flags::Roles
                && pattern_symbol.name == subject_symbol.name
                && pattern_symbol.attributes.head_role() == HeadRole::Residual =>
            {
                Arm::Undecided
            }
            _ if (is_overload_head(pattern) && is_rigid(subject))
                || (is_rigid(pattern) && is_overload_head(subject)) =>
            {
                Arm::Refute
            }
            _ if (mode == MatchMode::Rewrite
                && is_rewrite_rigid(pattern)
                && is_rewrite_rigid(subject))
                || (is_rigid(pattern) && is_rigid(subject))
                || (mode == MatchMode::Evaluate
                    && is_rigid(pattern)
                    && subject.concrete_after_normalization()) =>
            {
                Arm::Refute
            }
            // `list_update_cannot_match`, then the deferral: neither reads a root's rigidity.
            _ => Arm::Undecided,
        }
    }

    /// Evidence for every equation-head subject, or for none.
    struct Evidence(bool);

    impl NormalForms for Evidence {
        fn evidence(&mut self, _application: &Term) -> Option<NormalEvidence> {
            self.0.then(NormalEvidence::given)
        }
    }

    /// The facts of a generated pair, whose overloaded productions are given by name.
    struct GeneratedPair<'p> {
        pattern: &'p Term,
        subject: &'p Term,
        overloaded: &'p BTreeSet<Name>,
    }

    impl PairFacts for GeneratedPair<'_> {
        fn same_name(&self) -> bool {
            symbol(self.pattern)
                .zip(symbol(self.subject))
                .is_some_and(|(pattern, subject)| pattern.name == subject.name)
        }

        fn pattern_function_typed(&self) -> bool {
            is_function(self.pattern)
        }

        fn subject_function_typed(&self) -> bool {
            is_function(self.subject)
        }

        fn pattern_overloaded(&self) -> bool {
            head_is_overload_head(self.overloaded, self.pattern)
        }

        fn subject_overloaded(&self) -> bool {
            head_is_overload_head(self.overloaded, self.subject)
        }

        fn subject_concrete(&self) -> bool {
            self.subject.concrete_after_normalization()
        }
    }

    /// The arm the policy selects, in the arm order of `Matcher::match_one`, after checking
    /// that its clash is built from what the refutation rests on.
    fn policy_arm(
        mode: MatchMode,
        pattern: &Term,
        subject: &Term,
        fixed: bool,
        overloaded: &BTreeSet<Name>,
    ) -> Arm {
        let subject_head = classify_value(subject, &mut Evidence(fixed));
        if let Head::Open(Open::EquationHead | Open::Uninterpreted) = subject_head {
            return Arm::Gate;
        }
        let pattern_head = classify_pattern(pattern_reading(mode), pattern);
        let facts = GeneratedPair {
            pattern,
            subject,
            overloaded,
        };
        let policy = matcher_root_policy(mode, pattern_head, subject_head, &facts);
        match (pattern.kind(), subject.kind()) {
            (TermKind::DomainValue { .. }, TermKind::DomainValue { .. })
            | (TermKind::Injection { .. }, TermKind::Injection { .. }) => Arm::Kind,
            (TermKind::Application { .. }, TermKind::Application { .. })
                if matches!(policy, RootPolicy::Decompose) =>
            {
                Arm::Decompose
            }
            (left, right) if same_collection_category(left, right) => Arm::Kind,
            (TermKind::Injection { .. }, right)
                if mode == MatchMode::Evaluate && is_collection(right) =>
            {
                Arm::Kind
            }
            (left, TermKind::Injection { .. })
                if mode == MatchMode::Evaluate && is_collection(left) =>
            {
                Arm::Kind
            }
            _ => match policy {
                RootPolicy::Refute(clash) => {
                    match clash {
                        Clash::Roots(_) => assert!(
                            matches!(
                                (pattern_head, subject_head),
                                (Head::Fixed(_), Head::Fixed(_))
                            ),
                            "two fixed roots"
                        ),
                        Clash::ResidualRoot => assert!(
                            matches!(pattern_head, Head::Residual)
                                || matches!(subject_head, Head::Residual)
                        ),
                        Clash::OverloadFamily => {
                            assert!(facts.pattern_overloaded() || facts.subject_overloaded())
                        }
                    }
                    let built = clash.between(pattern.clone(), subject.clone());
                    assert_eq!(built.into_terms(), (pattern.clone(), subject.clone()));
                    Arm::Refute
                }
                RootPolicy::Decompose | RootPolicy::Undecided => Arm::Undecided,
            },
        }
    }

    /// Whether the root of `term` is an application of a symbol whose role CBC-02-T2 changed
    /// (B1: `constructor` and `anywhere`; B2: a macro or alias; B3: `anywhere`, `function` and
    /// `injective`), or FU-20-T1 changed (B4: uninterpreted), so that the declared flags and the
    /// role disagree.
    fn changed_role(term: &Term) -> bool {
        symbol(term).is_some_and(|symbol| {
            let declared = symbol.attributes.declaration();
            symbol.attributes.head_role() == HeadRole::Uninterpreted
                || declared.macro_or_alias
                || (declared.anywhere
                    && !declared.declared_function
                    && declared.symbol_type == SymbolType::Constructor)
                || (declared.anywhere
                    && declared.declared_function
                    && declared.injective
                    && matches!(declared.symbol_type, SymbolType::Function(_)))
        })
    }

    /// One symbol per name, as in a definition: a subject application whose symbol has the
    /// pattern root's name is rebuilt with the pattern's symbol, and `share` rebuilds any
    /// subject application with it, so that pairs of one symbol are frequent.
    fn consistent(pattern: &Term, subject: Term, share: bool) -> Term {
        match (pattern.kind(), subject.kind()) {
            (
                TermKind::Application {
                    symbol: pattern_symbol,
                    ..
                },
                TermKind::Application {
                    symbol: subject_symbol,
                    sort_arguments,
                    arguments,
                },
            ) if share || pattern_symbol.name == subject_symbol.name => Term::application(
                pattern_symbol.clone(),
                sort_arguments.clone(),
                arguments.clone(),
            ),
            _ => subject,
        }
    }

    /// Acceptance of CBC-02-T4: over the terms of the Lean bridge generators, in every mode,
    /// with and without evidence for an equation-head subject and with every set of overloaded
    /// names, `matcher_root_policy` selects the arm the guards of `eea634ce` selected, except
    /// for a root symbol whose role CBC-02-T2 changed (B1-B3), and the arm the integration
    /// base selected except for uninterpreted roots (B4), whose applications never decompose
    /// and whose subjects always reach the gate.
    #[test]
    fn the_root_policy_selects_the_arms_of_the_guards_it_replaced() {
        let names = [WellKnownSymbol::KCell.as_str(), "LblA", "LblB", "kseq"];
        let strategy = (
            prop_oneof![
                Just(MatchMode::Rewrite),
                Just(MatchMode::Evaluate),
                Just(MatchMode::Implies)
            ],
            generators::term(),
            generators::term(),
            any::<bool>(),
            any::<bool>(),
            prop::sample::subsequence(names.to_vec(), 0..=names.len()),
        );
        let counts = RefCell::new(BTreeMap::<(String, Arm), usize>::new());
        let mut runner = TestRunner::new(Config {
            cases: 8192,
            ..Config::default()
        });
        runner
            .run(
                &strategy,
                |(mode, pattern, subject, share, fixed, overloaded)| {
                    let subject = consistent(&pattern, subject, share);
                    // Pairs decided before the gate: a variable or a conjunction on either
                    // side, and in `Implies` two equal sides.
                    let before_gate = |term: &Term| {
                        matches!(term.kind(), TermKind::Variable(_) | TermKind::And(..))
                    };
                    if before_gate(&pattern)
                        || before_gate(&subject)
                        || (mode == MatchMode::Implies && pattern == subject)
                    {
                        return Ok(());
                    }
                    let overloaded = overloaded.into_iter().map(Name::from).collect();
                    let arm = policy_arm(mode, &pattern, &subject, fixed, &overloaded);
                    let uninterpreted = |term: &Term| {
                        symbol(term).is_some_and(|symbol| {
                            symbol.attributes.head_role() == HeadRole::Uninterpreted
                        })
                    };
                    let reading = if uninterpreted(&pattern) || uninterpreted(&subject) {
                        prop_assert_ne!(arm, Arm::Decompose);
                        if arm == Arm::Refute {
                            let pattern_head = classify_pattern(pattern_reading(mode), &pattern);
                            let subject_head = classify_value(&subject, &mut Evidence(fixed));
                            prop_assert!(
                                (head_is_overload_head(&overloaded, &pattern)
                                    && is_rigid_root(subject_head))
                                    || (is_rigid_root(pattern_head)
                                        && head_is_overload_head(&overloaded, &subject)),
                                "an uninterpreted pair is refuted only by the overload arm (Q2)"
                            );
                        }
                        if uninterpreted(&subject) {
                            prop_assert_eq!(arm, Arm::Gate);
                        }
                        "uninterpreted"
                    } else {
                        let base = transcribed_arm(
                            Flags::Roles,
                            mode,
                            &pattern,
                            &subject,
                            fixed,
                            &overloaded,
                        );
                        prop_assert_eq!(arm, base, "integration base, {:?}", mode);
                        if changed_role(&pattern) || changed_role(&subject) {
                            "changed role"
                        } else {
                            let head = transcribed_arm(
                                Flags::Declared,
                                mode,
                                &pattern,
                                &subject,
                                fixed,
                                &overloaded,
                            );
                            prop_assert_eq!(arm, head, "eea634ce, {:?}", mode);
                            "declared"
                        }
                    };
                    *counts
                        .borrow_mut()
                        .entry((format!("{mode:?} {reading}"), arm))
                        .or_default() += 1;
                    Ok(())
                },
            )
            .unwrap();
        let counts = counts.into_inner();
        for mode in ["Rewrite", "Evaluate", "Implies"] {
            for arm in [
                Arm::Gate,
                Arm::Kind,
                Arm::Decompose,
                Arm::Refute,
                Arm::Undecided,
            ] {
                assert!(
                    counts.contains_key(&(format!("{mode} declared"), arm)),
                    "no {mode} case compared with eea634ce reached {arm:?}: {counts:?}"
                );
            }
        }
    }

    /// The root class of a term in [`the_evaluate_policy_refutes_two_normal_forms_in_either_orientation`]:
    /// a free constructor, a domain value, an injection or an equation-head application, each
    /// ground and concrete after normalization; `None` for any other term.
    fn normal_form_class(term: &Term) -> Option<&'static str> {
        if !term.attributes().variables.is_empty() || !term.concrete_after_normalization() {
            return None;
        }
        match term.kind() {
            TermKind::DomainValue { .. } => Some("domain value"),
            TermKind::Injection { .. } => Some("injection"),
            TermKind::Application { symbol, .. } => match symbol.attributes.head_role() {
                HeadRole::FreeConstructor => Some("free constructor"),
                HeadRole::EquationHead => Some("equation head"),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether two ground normal forms the backend certifies are one value or two does not
    /// depend on which side of a match writes which (K12). A recorded pattern is an equation-head
    /// application read with the evidence an equal subject carries, so in `Evaluate`, with every
    /// equation-head application read with evidence on either side, the policy refutes a pair of
    /// such terms exactly when it refutes the pair exchanged. The other modes read no pattern
    /// evidence and are not symmetric by design (`Rewrite` reads the left-hand side as written,
    /// `Implies` never refutes an equation-head subject by its root).
    #[test]
    fn the_evaluate_policy_refutes_two_normal_forms_in_either_orientation() {
        let counts = RefCell::new(BTreeMap::<(&str, &str, bool), usize>::new());
        // A fixed seed: the reach assertions below read the sample, which a random seed would
        // make vary from run to run.
        let config = Config {
            cases: 8192,
            ..Config::default()
        };
        let rng = TestRng::deterministic_rng(config.rng_algorithm);
        let mut runner = TestRunner::new_with_rng(config, rng);
        runner
            .run(
                &(generators::term(), generators::term(), any::<bool>()),
                |(left, right, share)| {
                    let right = consistent(&left, right, share);
                    let (Some(left_class), Some(right_class)) =
                        (normal_form_class(&left), normal_form_class(&right))
                    else {
                        return Ok(());
                    };
                    let overloaded = BTreeSet::new();
                    let refutes = |pattern: &Term, subject: &Term| {
                        let facts = GeneratedPair {
                            pattern,
                            subject,
                            overloaded: &overloaded,
                        };
                        matches!(
                            matcher_root_policy(
                                MatchMode::Evaluate,
                                classify_value(pattern, &mut Evidence(true)),
                                classify_value(subject, &mut Evidence(true)),
                                &facts,
                            ),
                            RootPolicy::Refute(_)
                        )
                    };
                    let forward = refutes(&left, &right);
                    prop_assert_eq!(
                        forward,
                        refutes(&right, &left),
                        "pattern {:?}, subject {:?}",
                        left,
                        right
                    );
                    let (first, second) = if left_class <= right_class {
                        (left_class, right_class)
                    } else {
                        (right_class, left_class)
                    };
                    *counts
                        .borrow_mut()
                        .entry((first, second, forward))
                        .or_default() += 1;
                    Ok(())
                },
            )
            .unwrap();
        let counts = counts.into_inner();
        // The arms the recorded patterns added are reached: an equation head against each rigid
        // class, and against an equation head (of another symbol, refuted; of its own symbol,
        // compared by arguments).
        for class in ["domain value", "free constructor", "injection"] {
            let pair = if class < "equation head" {
                (class, "equation head", true)
            } else {
                ("equation head", class, true)
            };
            assert!(
                counts.contains_key(&pair),
                "{pair:?} not reached: {counts:?}"
            );
        }
        for refuted in [true, false] {
            let pair = ("equation head", "equation head", refuted);
            assert!(
                counts.contains_key(&pair),
                "{pair:?} not reached: {counts:?}"
            );
        }
    }
}
