//! Mutation sites, selection policies and candidate folding.
//!
//! Sites are term positions of one [`Baseline`], identified by their
//! [`TermRef`]; there are no site, candidate or mutant digests. Operators build
//! a [`Patch`] from a selected origin, and [`Selection::fold`] checks that
//! every edit targets a sentence of that origin. Equal patches fold into one
//! candidate that keeps every origin, and a patch that does not apply is a
//! rejected disposition, never a mutant.
//!
//! The stages are distinct types with private fields: a [`Discovery`], the
//! [`Selection`] that [`select`] makes of it, and the [`CandidateGeneration`]
//! that [`Selection::fold`] makes of that, which is the only one a campaign
//! runs. A generation can be scored only when its discovery was exhaustive,
//! which only declarative derivation gives: [`derive_sites`] and its unions
//! and joins. Exhaustive means every match of the declared selector
//! expression, whose rule labels and label-and-path references must resolve.
//! A [`Discovery::supplied`] or [`Discovery::filter`]ed one never is. Each stage
//! borrows the baseline it was derived from, and a campaign compares that
//! borrow with its own baseline by address. Address identity needs no digest:
//! the borrow keeps the baseline alive, so no other live baseline can share
//! its address. An equal clone is a different baseline to this check, which
//! refuses it conservatively.

use crate::sort::Typing;
use crate::{
    Baseline, Edit, InsertPosition, Patch, PatchFailure, SentenceRef, TermRef, apply, child,
    field_term,
};
use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::{Label, Sort, Term};
use std::collections::BTreeSet;
use std::fmt;

/// Selection failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateFailureKind {
    DuplicateSite,
    InvalidJoin,
    CardinalityMismatch,
    CandidateCap,
    IncompleteGeneration,
    InvalidBinding,
    /// An operator built an edit outside the sentences of its origin.
    UnauthorizedEdit,
    /// A supplied site, or a selector's rule label or label-and-path, is not a
    /// term position of the baseline.
    UnknownSite,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateFailure {
    kind: CandidateFailureKind,
    detail: String,
}

impl CandidateFailure {
    fn new(kind: CandidateFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    #[must_use]
    pub const fn kind(&self) -> CandidateFailureKind {
        self.kind
    }
}

impl fmt::Display for CandidateFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for CandidateFailure {}

/// One matched term position. Its identity is `at`; `role` names the
/// selector clause that matched it in a joined tuple.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Site {
    pub role: String,
    pub at: TermRef,
}

/// Named terms bound by a discovery tuple, ordered by name at construction.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Bindings(Vec<(String, Term)>);

impl Bindings {
    /// Sorts `bindings` by name.
    ///
    /// # Errors
    ///
    /// Rejects a repeated name, or a name that is not an upper-case initial
    /// followed by ASCII alphanumerics or underscores.
    pub fn new(mut bindings: Vec<(String, Term)>) -> Result<Self, CandidateFailure> {
        bindings.sort_by(|left, right| left.0.cmp(&right.0));
        check_binding_names(bindings.iter().map(|(name, _)| name.as_str()))?;
        Ok(Self(bindings))
    }

    #[must_use]
    pub fn as_slice(&self) -> &[(String, Term)] {
        &self.0
    }

    /// The term bound to `name`.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Term> {
        self.0
            .binary_search_by(|(bound, _)| bound.as_str().cmp(name))
            .ok()
            .map(|index| &self.0[index].1)
    }
}

/// One discovered match: a site tuple and its bindings.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiscoveryTuple {
    pub sites: Vec<Site>,
    pub bindings: Bindings,
}

/// The discovered tuples of one operator over one baseline, and whether they
/// are all of them.
///
/// Only declarative derivations give an exhaustive discovery: [`derive_sites`]
/// when it decided every position, and [`Discovery::union`] and
/// [`Discovery::join`] when every input is exhaustive and (for a join) every
/// unification was decided. Each considers every match of its selector
/// clauses, their disjunction or their join. Narrowing by code
/// ([`Discovery::filter`]) and hand-supplied tuples ([`Discovery::supplied`])
/// are never exhaustive, because nothing shows that every match of a declared
/// selector was considered, so a selection over them is never scored.
#[derive(Clone)]
pub struct Discovery<'b> {
    baseline: &'b Baseline,
    tuples: Vec<DiscoveryTuple>,
    exhaustive: bool,
    joined: bool,
    tuple_symmetric: bool,
}

impl<'b> Discovery<'b> {
    /// An exhaustive discovery with no tuples, the identity of [`Self::union`]
    /// for discoveries with this shape.
    #[must_use]
    pub const fn empty(baseline: &'b Baseline, joined: bool, tuple_symmetric: bool) -> Self {
        Self {
            baseline,
            tuples: Vec::new(),
            exhaustive: true,
            joined,
            tuple_symmetric,
        }
    }

    /// Tuples supplied by hand over `baseline`, for shapes no derivation
    /// produces. The discovery is not exhaustive.
    ///
    /// # Errors
    ///
    /// Returns `UnknownSite` when a site is not a term position of `baseline`.
    pub fn supplied(
        baseline: &'b Baseline,
        tuples: Vec<DiscoveryTuple>,
        joined: bool,
        tuple_symmetric: bool,
    ) -> Result<Self, CandidateFailure> {
        if let Some(site) = tuples
            .iter()
            .flat_map(|tuple| &tuple.sites)
            .find(|site| baseline.term(&site.at).is_none())
        {
            return Err(CandidateFailure::new(
                CandidateFailureKind::UnknownSite,
                format!("{:?} is not a term position of the baseline", site.at),
            ));
        }
        Ok(Self {
            baseline,
            tuples,
            exhaustive: false,
            joined,
            tuple_symmetric,
        })
    }

    /// Keeps the tuples `keep` accepts. The result is not exhaustive: `keep`
    /// is opaque code, not a declared selector, so nothing shows which
    /// matches it was meant to keep, and a selection over it is never
    /// scored. Narrow with [`SiteSelector`] clauses to keep exhaustiveness.
    #[must_use]
    pub fn filter(mut self, mut keep: impl FnMut(&DiscoveryTuple) -> bool) -> Self {
        self.tuples.retain(|tuple| keep(tuple));
        self.exhaustive = false;
        self
    }

    /// The tuples of `self` and then those of `other` that `self` does not
    /// already have: every match of either selector, once. Identical tuples
    /// appear once; a site both inputs match under different roles or
    /// bindings stays twice, and [`select`] refuses the repeat
    /// (`DuplicateSite`). It is exhaustive when both inputs are.
    ///
    /// # Errors
    ///
    /// Returns `InvalidJoin` for discoveries of different baselines, or that
    /// differ in whether they are joined or tuple-symmetric.
    pub fn union(&self, other: &Self) -> Result<Self, CandidateFailure> {
        if !std::ptr::eq(self.baseline, other.baseline) {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidJoin,
                "discoveries of different baselines do not unite",
            ));
        }
        if (self.joined, self.tuple_symmetric) != (other.joined, other.tuple_symmetric) {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidJoin,
                "discoveries of different shapes do not unite",
            ));
        }
        let mut tuples = self.tuples.clone();
        for tuple in &other.tuples {
            if !self.tuples.contains(tuple) {
                tuples.push(tuple.clone());
            }
        }
        Ok(Self {
            baseline: self.baseline,
            tuples,
            exhaustive: self.exhaustive && other.exhaustive,
            joined: self.joined,
            tuple_symmetric: self.tuple_symmetric,
        })
    }

    /// Joins every tuple of `self` with every tuple of `other`, in that
    /// order. A joined tuple lists both tuples' sites, and their bindings
    /// with each name once.
    ///
    /// A name bound on both sides is one pattern variable, and the pair is a
    /// tuple only when every such name unifies: its two terms are equal once
    /// each semantic cast over a variable is read as that variable's sort,
    /// and every variable in them has a sort. The joined tuple keeps `self`'s
    /// term for the name. A pair whose terms still differ with casts and
    /// variable sorts ignored does not match. A pair whose terms differ only
    /// in casts and variable sorts, or hold a variable whose sort comes from
    /// outside the bound term, is undecided: the baseline's typing would
    /// decide it, which this join does not consult, so the pair is left out
    /// and the join is not exhaustive.
    ///
    /// Otherwise the join is exhaustive when both inputs are, since every
    /// pair is considered. A pair that repeats a site is kept, and
    /// [`select`] rejects it.
    ///
    /// # Errors
    ///
    /// Returns `InvalidJoin` for discoveries of different baselines.
    pub fn join(&self, other: &Self, tuple_symmetric: bool) -> Result<Self, CandidateFailure> {
        if !std::ptr::eq(self.baseline, other.baseline) {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidJoin,
                "discoveries of different baselines do not join",
            ));
        }
        let mut exhaustive = self.exhaustive && other.exhaustive;
        let mut tuples = Vec::new();
        for left in &self.tuples {
            for right in &other.tuples {
                let unified = right
                    .bindings
                    .0
                    .iter()
                    .filter_map(|(name, term)| Some(unify(left.bindings.get(name)?, term)))
                    .fold(Unification::Match, Unification::and);
                match unified {
                    Unification::Match => {}
                    Unification::Mismatch => continue,
                    Unification::Undecided => {
                        exhaustive = false;
                        continue;
                    }
                }
                let mut bindings = left.bindings.0.clone();
                bindings.extend(
                    right
                        .bindings
                        .0
                        .iter()
                        .filter(|(name, _)| left.bindings.get(name).is_none())
                        .cloned(),
                );
                tuples.push(DiscoveryTuple {
                    sites: left.sites.iter().chain(&right.sites).cloned().collect(),
                    bindings: Bindings::new(bindings)?,
                });
            }
        }
        Ok(Self {
            baseline: self.baseline,
            tuples,
            exhaustive,
            joined: true,
            tuple_symmetric,
        })
    }

    /// The baseline the sites are positions of.
    #[must_use]
    pub const fn baseline(&self) -> &'b Baseline {
        self.baseline
    }

    #[must_use]
    pub fn tuples(&self) -> &[DiscoveryTuple] {
        &self.tuples
    }

    /// Every match was considered.
    #[must_use]
    pub const fn exhaustive(&self) -> bool {
        self.exhaustive
    }

    /// Tuples join several selector roles.
    #[must_use]
    pub const fn joined(&self) -> bool {
        self.joined
    }

    /// Tuples that are permutations of one another are one instance.
    #[must_use]
    pub const fn tuple_symmetric(&self) -> bool {
        self.tuple_symmetric
    }
}

impl fmt::Debug for Discovery<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Discovery")
            .field("tuples", &self.tuples)
            .field("exhaustive", &self.exhaustive)
            .field("joined", &self.joined)
            .field("tuple_symmetric", &self.tuple_symmetric)
            .finish_non_exhaustive()
    }
}

/// Whether two terms bound to one name are one term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Unification {
    /// Equal, with every variable's sort given inside the terms.
    Match,
    /// Different even with casts and variable sorts ignored.
    Mismatch,
    /// Equal with casts and variable sorts ignored, and not decided otherwise.
    Undecided,
}

impl Unification {
    /// Both hold: any mismatch decides, and otherwise any undecided part is.
    const fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::Mismatch, _) | (_, Self::Mismatch) => Self::Mismatch,
            (Self::Undecided, _) | (_, Self::Undecided) => Self::Undecided,
            (Self::Match, Self::Match) => Self::Match,
        }
    }
}

/// A variable and its sort: its own annotation, or the sort of the semantic
/// cast directly over a variable without one, which is how the loader writes
/// `A:Nat`.
fn sorted_variable(term: &Term) -> Option<(&str, Option<Sort>)> {
    match term.unannotated() {
        Term::Variable { name, sort } => Some((name, sort.clone())),
        Term::Apply { label, arguments } => {
            let cast = label.semantic_cast_sort()?;
            match arguments.as_slice() {
                [argument] => match argument.unannotated() {
                    Term::Variable { name, sort: None } => Some((name, Some(cast))),
                    Term::Variable {
                        name,
                        sort: Some(sort),
                    } if *sort == cast => Some((name, Some(cast))),
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

/// The label and argument of a semantic cast.
fn cast_argument(term: &Term) -> Option<(&Label, &Term)> {
    match term.unannotated() {
        Term::Apply { label, arguments } if label.semantic_cast_sort().is_some() => {
            match arguments.as_slice() {
                [argument] => Some((label, argument)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Compares two bound terms modulo how a variable's sort is written (an
/// annotation or a cast over it) and semantic casts, without consulting the
/// baseline's typing. A match needs every variable's sort written inside
/// the terms and equal; two terms that still differ once casts and variable
/// sorts are ignored are a mismatch; anything else is undecided.
fn unify(left: &Term, right: &Term) -> Unification {
    let (left, right) = (left.unannotated(), right.unannotated());
    if let (Some((left_name, left_sort)), Some((right_name, right_sort))) =
        (sorted_variable(left), sorted_variable(right))
    {
        return if left_name != right_name {
            Unification::Mismatch
        } else if left_sort.is_some() && left_sort == right_sort {
            Unification::Match
        } else {
            Unification::Undecided
        };
    }
    match (cast_argument(left), cast_argument(right)) {
        (Some((left_cast, left_argument)), Some((right_cast, right_argument)))
            if left_cast == right_cast =>
        {
            return unify(left_argument, right_argument);
        }
        // A cast over a term is that term only when the term has the cast's
        // sort, which only the baseline's typing decides.
        (Some((_, argument)), _) => {
            return unify(argument, right).and(Unification::Undecided);
        }
        (_, Some((_, argument))) => {
            return unify(left, argument).and(Unification::Undecided);
        }
        (None, None) => {}
    }
    let all = |left: &[Term], right: &[Term]| {
        if left.len() == right.len() {
            left.iter()
                .zip(right)
                .map(|(left, right)| unify(left, right))
                .fold(Unification::Match, Unification::and)
        } else {
            Unification::Mismatch
        }
    };
    match (left, right) {
        (Term::Variable { .. }, _) | (_, Term::Variable { .. }) => Unification::Mismatch,
        (
            Term::Rewrite {
                left: left_left,
                right: left_right,
            },
            Term::Rewrite {
                left: right_left,
                right: right_right,
            },
        ) => unify(left_left, right_left).and(unify(left_right, right_right)),
        (
            Term::As {
                pattern: left_pattern,
                alias: left_alias,
            },
            Term::As {
                pattern: right_pattern,
                alias: right_alias,
            },
        ) => unify(left_pattern, right_pattern).and(unify(left_alias, right_alias)),
        (Term::Sequence(left), Term::Sequence(right)) => all(left, right),
        (
            Term::Apply {
                label: left_label,
                arguments: left_arguments,
            },
            Term::Apply {
                label: right_label,
                arguments: right_arguments,
            },
        ) if left_label == right_label => all(left_arguments, right_arguments),
        _ if left == right => Unification::Match,
        _ => Unification::Mismatch,
    }
}

/// One conjunctive clause of a site selector. A selector without a clause of
/// some kind does not constrain that property: without a `RuleLabel` clause,
/// labelled and unlabelled rules both match.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SiteSelector {
    /// The rule carries this module-qualified label.
    RuleLabel(String),
    /// The position is exactly this term path; `[0]`, `[1]` and `[2]` are
    /// the body, requires and ensures fields.
    Path(Vec<u32>),
    /// The term at the position has exactly this sort (not a subsort).
    Sort(Sort),
    /// The position holds an application of this label.
    Head { label: String },
    /// Binds the term at the position to this name, which must be an
    /// upper-case K variable name. It constrains nothing by itself; a join
    /// unifies the names both sides bind ([`Discovery::join`]).
    Bind(String),
}

/// Derives every term position of the baseline's written rules that
/// satisfies all `selector` clauses, as unary tuples in [`TermRef`] order,
/// each binding the matched term to every `Bind` name.
///
/// Every written rule and every position in it is considered. Only rules are
/// considered, and only written ones: generated sentences are excluded.
/// A position that satisfies every other clause but whose sort cannot be
/// decided locally (see the sort module) is neither a site nor a non-site,
/// so a selector with a `Sort` clause that meets one yields a discovery that
/// is not exhaustive, and is never scored.
///
/// # Errors
///
/// Returns `InvalidBinding` when the `Bind` names are not unique K variable
/// names, whether or not any position matches.
/// Returns `UnknownSite` when a `RuleLabel` names no written rule or a `Path`
/// is not a position of a rule named by a `RuleLabel`.
pub fn derive_sites<'b>(
    baseline: &'b Baseline,
    role: &str,
    selector: &[SiteSelector],
) -> Result<Discovery<'b>, CandidateFailure> {
    let mut names = selector
        .iter()
        .filter_map(|clause| match clause {
            SiteSelector::Bind(name) => Some(name.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    names.sort_unstable();
    check_binding_names(names.iter().copied())?;
    let written_rules = baseline
        .authored_sentences()
        .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
        .collect::<Vec<_>>();
    for clause in selector {
        let SiteSelector::RuleLabel(label) = clause else {
            continue;
        };
        let matching = written_rules
            .iter()
            .filter(|(_, sentence)| {
                sentence.attributes().string(AttributeKey::Label) == Some(label.as_str())
            })
            .collect::<Vec<_>>();
        if matching.is_empty() {
            return Err(CandidateFailure::new(
                CandidateFailureKind::UnknownSite,
                format!("no written rule is labelled {label}"),
            ));
        }
        for (rule_ref, _) in matching {
            for path in selector.iter().filter_map(|clause| match clause {
                SiteSelector::Path(path) => Some(path),
                _ => None,
            }) {
                if baseline
                    .term(&TermRef::new(rule_ref.clone(), path.as_slice()))
                    .is_none()
                {
                    return Err(CandidateFailure::new(
                        CandidateFailureKind::UnknownSite,
                        format!("{label} has no position {path:?}"),
                    ));
                }
            }
        }
    }
    let bind = |term: &Term| {
        Bindings(
            names
                .iter()
                .map(|name| ((*name).to_owned(), term.clone()))
                .collect(),
        )
    };
    let sorts = selector
        .iter()
        .filter_map(|clause| match clause {
            SiteSelector::Sort(sort) => Some(sort),
            _ => None,
        })
        .collect::<Vec<_>>();
    let resolved = &baseline.loaded().resolved;
    let views = resolved.views();
    let mut exhaustive = true;
    let mut sites = Vec::new();
    for (sentence_ref, sentence) in baseline.authored_sentences() {
        if !matches!(sentence, Sentence::Rule { .. })
            || !selector.iter().all(|clause| match clause {
                SiteSelector::RuleLabel(label) => {
                    sentence.attributes().string(AttributeKey::Label) == Some(label.as_str())
                }
                _ => true,
            })
        {
            continue;
        }
        let typing =
            (!sorts.is_empty()).then(|| Typing::new(resolved, &views, &sentence_ref.module));
        for field in 0..3 {
            let Some(root) = field_term(sentence, field) else {
                continue;
            };
            let mut stack = vec![(vec![field], root)];
            while let Some((path, term)) = stack.pop() {
                let matched = selector.iter().all(|clause| match clause {
                    SiteSelector::RuleLabel(_) | SiteSelector::Sort(_) | SiteSelector::Bind(_) => {
                        true
                    }
                    SiteSelector::Path(wanted) => path == *wanted,
                    SiteSelector::Head { label } => matches!(
                        term.unannotated(),
                        Term::Apply { label: head, .. } if head.name == *label
                    ),
                });
                let sorted = match &typing {
                    Some(typing) if matched => {
                        let actual = typing
                            .as_ref()
                            .ok()
                            .and_then(|typing| typing.site_sort(sentence, &path).ok());
                        exhaustive &= actual.is_some();
                        actual.is_some_and(|actual| sorts.iter().all(|wanted| actual == **wanted))
                    }
                    _ => true,
                };
                if matched && sorted {
                    sites.push((TermRef::new(sentence_ref.clone(), path.clone()), bind(term)));
                }
                let children = (0..)
                    .map_while(|step| Some((step, child(term, step)?)))
                    .collect::<Vec<_>>();
                for (step, term) in children.into_iter().rev() {
                    let mut path = path.clone();
                    path.push(step);
                    stack.push((path, term));
                }
            }
        }
    }
    sites.sort_by(|left, right| left.0.cmp(&right.0));
    Ok(Discovery {
        baseline,
        tuples: sites
            .into_iter()
            .map(|(at, bindings)| DiscoveryTuple {
                sites: vec![Site {
                    role: role.to_owned(),
                    at,
                }],
                bindings,
            })
            .collect(),
        exhaustive,
        joined: false,
        tuple_symmetric: false,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SelectionPolicy {
    Exact {
        expected_tuple_count: usize,
        expected_tuple_arity: usize,
    },
    Each,
    TupleEach,
    AllMatches,
}

/// One policy-derived origin before identical-patch folding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatchOrigin {
    pub site_tuple: Vec<TermRef>,
    pub discovery_tuples: Vec<DiscoveryTuple>,
}

/// One deduplicated candidate that applies to the baseline. Origins keep
/// their selection order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Candidate {
    pub operator: String,
    pub patch: Patch,
    pub origins: Vec<PatchOrigin>,
}

/// Whether a producer considered its whole declared finite input.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Completeness {
    /// The declared finite input was completely considered.
    CompleteFinite,
    /// The producer declares that some relevant input was not considered.
    Incomplete,
}

/// What became of one selected origin.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CandidateDisposition {
    /// The origin's patch is `candidates[index]`.
    Mutant(usize),
    /// The origin's patch does not apply to the baseline.
    Rejected(PatchFailure),
}

/// The origins [`select`] chose from one discovery, before any patch exists.
///
/// A selection has no candidates and is never scored; [`Selection::fold`]
/// turns it into a [`CandidateGeneration`].
#[derive(Clone)]
pub struct Selection<'b> {
    baseline: &'b Baseline,
    selected_origins: Vec<PatchOrigin>,
    completeness: Completeness,
    failure: Option<CandidateFailureKind>,
}

impl<'b> Selection<'b> {
    /// The baseline of the discovery the origins were selected from.
    #[must_use]
    pub const fn baseline(&self) -> &'b Baseline {
        self.baseline
    }

    /// The origins in canonical order, after the candidate cap.
    #[must_use]
    pub fn selected_origins(&self) -> &[PatchOrigin] {
        &self.selected_origins
    }

    #[must_use]
    pub const fn completeness(&self) -> Completeness {
        self.completeness
    }

    /// Why the selection is not a complete one: a cardinality or join
    /// mismatch (with no origins), or an incomplete generation.
    #[must_use]
    pub const fn failure(&self) -> Option<CandidateFailureKind> {
        self.failure
    }
}

impl fmt::Debug for Selection<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Selection")
            .field("selected_origins", &self.selected_origins)
            .field("completeness", &self.completeness)
            .field("failure", &self.failure)
            .finish_non_exhaustive()
    }
}

/// The candidates of one folded selection, the only input a campaign runs.
///
/// It is built only by [`Selection::fold`], so it always went through
/// [`select`] and the fold's edit and apply checks against the baseline it
/// records.
#[derive(Clone)]
pub struct CandidateGeneration<'b> {
    baseline: &'b Baseline,
    candidates: Vec<Candidate>,
    selected_origins: Vec<PatchOrigin>,
    dispositions: Vec<CandidateDisposition>,
    completeness: Completeness,
    failure: Option<CandidateFailureKind>,
}

impl<'b> CandidateGeneration<'b> {
    /// The baseline every candidate applies to.
    #[must_use]
    pub const fn baseline(&self) -> &'b Baseline {
        self.baseline
    }

    /// Whether this generation was derived from `baseline` itself (by
    /// address; see the module documentation).
    #[must_use]
    pub fn derived_from(&self, baseline: &Baseline) -> bool {
        std::ptr::eq(self.baseline, baseline)
    }

    /// The distinct applicable patches, in the order of their first origin.
    #[must_use]
    pub fn candidates(&self) -> &[Candidate] {
        &self.candidates
    }

    #[must_use]
    pub fn selected_origins(&self) -> &[PatchOrigin] {
        &self.selected_origins
    }

    /// What became of each selected origin, parallel to `selected_origins`.
    /// Every origin rejected is an empty generation with nonempty
    /// dispositions; nothing selected is one with none.
    #[must_use]
    pub fn dispositions(&self) -> &[CandidateDisposition] {
        &self.dispositions
    }

    #[must_use]
    pub const fn completeness(&self) -> Completeness {
        self.completeness
    }

    #[must_use]
    pub const fn failure(&self) -> Option<CandidateFailureKind> {
        self.failure
    }

    /// Whether a score over this generation's mutants is a claim about every
    /// mutant its operator selects: selection considered the whole declared
    /// input (`CompleteFinite`, no failure) and at least one candidate exists.
    ///
    /// An empty generation, whether nothing was selected or every origin was
    /// rejected, is not scored: a score over no mutants would claim nothing
    /// about the operator, and cannot tell a selector that matches nothing
    /// from a mistaken one.
    #[must_use]
    pub fn scored(&self) -> bool {
        self.completeness == Completeness::CompleteFinite
            && self.failure.is_none()
            && !self.candidates.is_empty()
    }
}

impl fmt::Debug for CandidateGeneration<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("CandidateGeneration")
            .field("candidates", &self.candidates)
            .field("selected_origins", &self.selected_origins)
            .field("dispositions", &self.dispositions)
            .field("completeness", &self.completeness)
            .field("failure", &self.failure)
            .finish_non_exhaustive()
    }
}

/// Folds exact/each/tuple-each/all-matches over discovered tuples.
///
/// Tuples are taken in canonical order, the order of their site
/// [`TermRef`]s, whatever order discovery supplied them in.
///
/// # Errors
///
/// Rejects a zero cap, an empty or repeated tuple, a tuple that repeats a
/// site or has an empty role, a non-unary tuple of an unjoined discovery, and
/// symmetric handling of an unjoined discovery. None of these publish a
/// generation.
pub fn select<'b>(
    discovery: &Discovery<'b>,
    policy: SelectionPolicy,
    candidate_cap: usize,
) -> Result<Selection<'b>, CandidateFailure> {
    if candidate_cap == 0 {
        return Err(CandidateFailure::new(
            CandidateFailureKind::CandidateCap,
            "candidate cap must be positive",
        ));
    }
    let canonical = canonical_tuples(discovery)?;
    let mut tuples = canonical.clone();
    if discovery.tuple_symmetric {
        let mut groups: Vec<Vec<DiscoveryTuple>> = Vec::new();
        for tuple in tuples {
            let key = symmetric_key(&tuple);
            if let Some(group) = groups
                .iter_mut()
                .find(|group| symmetric_key(&group[0]) == key)
            {
                group.push(tuple);
            } else {
                groups.push(vec![tuple]);
            }
        }
        tuples = groups.iter().map(|group| group[0].clone()).collect();
    }

    let mut origins = match policy {
        SelectionPolicy::Exact {
            expected_tuple_count,
            expected_tuple_arity,
        } => {
            if !discovery.exhaustive {
                return Ok(incomplete(discovery.baseline));
            }
            if tuples
                .iter()
                .any(|tuple| tuple.sites.len() != expected_tuple_arity)
            {
                return Ok(failed(
                    discovery.baseline,
                    CandidateFailureKind::InvalidJoin,
                ));
            }
            if tuples.len() != expected_tuple_count {
                return Ok(failed(
                    discovery.baseline,
                    CandidateFailureKind::CardinalityMismatch,
                ));
            }
            tuples.iter().map(ordinary_origin).collect()
        }
        SelectionPolicy::Each => {
            if discovery.joined || tuples.iter().any(|tuple| tuple.sites.len() != 1) {
                return Ok(failed(
                    discovery.baseline,
                    CandidateFailureKind::InvalidJoin,
                ));
            }
            tuples.iter().map(ordinary_origin).collect()
        }
        SelectionPolicy::TupleEach => {
            if !discovery.joined {
                return Ok(failed(
                    discovery.baseline,
                    CandidateFailureKind::InvalidJoin,
                ));
            }
            if discovery.tuple_symmetric {
                tuples
                    .iter()
                    .map(|representative| {
                        let key = symmetric_key(representative);
                        PatchOrigin {
                            site_tuple: site_refs(representative),
                            // `canonical` is already in canonical order.
                            discovery_tuples: canonical
                                .iter()
                                .filter(|tuple| symmetric_key(tuple) == key)
                                .cloned()
                                .collect(),
                        }
                    })
                    .collect()
            } else {
                tuples.iter().map(ordinary_origin).collect()
            }
        }
        SelectionPolicy::AllMatches => {
            if discovery.joined || tuples.iter().any(|tuple| tuple.sites.len() != 1) {
                return Ok(failed(
                    discovery.baseline,
                    CandidateFailureKind::InvalidJoin,
                ));
            }
            if tuples.is_empty() {
                Vec::new()
            } else {
                vec![PatchOrigin {
                    site_tuple: tuples.iter().flat_map(site_refs).collect(),
                    discovery_tuples: tuples,
                }]
            }
        }
    };
    let omitted = origins.len() > candidate_cap;
    origins.truncate(candidate_cap);
    let complete = discovery.exhaustive && !omitted;
    Ok(Selection {
        baseline: discovery.baseline,
        selected_origins: origins,
        completeness: if complete {
            Completeness::CompleteFinite
        } else {
            Completeness::Incomplete
        },
        failure: (!complete).then_some(CandidateFailureKind::IncompleteGeneration),
    })
}

impl<'b> Selection<'b> {
    /// Builds one patch per retained origin with `patch_for`, folds equal
    /// patches into one candidate that keeps every origin, and applies each
    /// distinct patch once to the baseline the selection was derived from.
    ///
    /// Every edit must target a sentence that holds a site of its origin: a
    /// term, sentence or attribute edit names that sentence, an insertion
    /// before or after names it, and a module-start or module-end insertion
    /// names the module of one of those sentences. The check is per sentence,
    /// like the former receipt's target lineage: operators legitimately edit
    /// around a site (the right-hand side of a body site, an attribute of the
    /// site's rule), so no term-level relation between site and edit is
    /// imposed. Because of it, two origins fold into one candidate only when
    /// they share a sentence.
    ///
    /// A patch that does not apply (for example a no-change patch) is a
    /// rejected disposition and never a candidate. The generation keeps the
    /// selection's origins, completeness and failure, and one disposition per
    /// origin.
    ///
    /// # Errors
    ///
    /// Returns `UnauthorizedEdit` when some origin's patch edits outside that
    /// origin's sentences. No generation is published then, not even the
    /// candidates of the other origins.
    pub fn fold(
        self,
        operator: &str,
        mut patch_for: impl FnMut(&PatchOrigin) -> Patch,
    ) -> Result<CandidateGeneration<'b>, CandidateFailure> {
        let mut candidates: Vec<Candidate> = Vec::new();
        let mut rejected: Vec<(Patch, PatchFailure)> = Vec::new();
        let mut dispositions = Vec::with_capacity(self.selected_origins.len());
        for origin in &self.selected_origins {
            let patch = patch_for(origin);
            if let Some(edit) = patch
                .edits()
                .iter()
                .find(|edit| !edit_is_authorized(edit, origin))
            {
                return Err(CandidateFailure::new(
                    CandidateFailureKind::UnauthorizedEdit,
                    format!(
                        "{operator}: edit {edit:?} targets no sentence of origin {:?}",
                        origin.site_tuple
                    ),
                ));
            }
            if let Some(index) = candidates
                .iter()
                .position(|candidate| candidate.patch == patch)
            {
                candidates[index].origins.push(origin.clone());
                dispositions.push(CandidateDisposition::Mutant(index));
            } else if let Some((_, failure)) = rejected.iter().find(|(other, _)| *other == patch) {
                dispositions.push(CandidateDisposition::Rejected(failure.clone()));
            } else {
                match apply(self.baseline, &patch) {
                    Ok(_) => {
                        dispositions.push(CandidateDisposition::Mutant(candidates.len()));
                        candidates.push(Candidate {
                            operator: operator.to_owned(),
                            patch,
                            origins: vec![origin.clone()],
                        });
                    }
                    Err(failure) => {
                        dispositions.push(CandidateDisposition::Rejected(failure.clone()));
                        rejected.push((patch, failure));
                    }
                }
            }
        }
        Ok(CandidateGeneration {
            baseline: self.baseline,
            candidates,
            selected_origins: self.selected_origins,
            dispositions,
            completeness: self.completeness,
            failure: self.failure,
        })
    }
}

/// Whether `edit` targets a sentence that holds a site of `origin`.
fn edit_is_authorized(edit: &Edit, origin: &PatchOrigin) -> bool {
    let holds_site =
        |sentence: &SentenceRef| origin.site_tuple.iter().any(|at| at.sentence == *sentence);
    match edit {
        Edit::ReplaceTerm { at, .. } => holds_site(&at.sentence),
        Edit::ReplaceSentence { at, .. }
        | Edit::DeleteSentence { at }
        | Edit::AddAttribute { at, .. }
        | Edit::RemoveAttribute { at, .. }
        | Edit::ReplaceAttribute { at, .. }
        | Edit::InsertSentence {
            position: InsertPosition::Before(at) | InsertPosition::After(at),
            ..
        } => holds_site(at),
        Edit::InsertSentence {
            position: InsertPosition::ModuleStart(module) | InsertPosition::ModuleEnd(module),
            ..
        } => origin
            .site_tuple
            .iter()
            .any(|at| at.sentence.module == *module),
    }
}

/// Checks the tuples and returns them in canonical order.
fn canonical_tuples(discovery: &Discovery) -> Result<Vec<DiscoveryTuple>, CandidateFailure> {
    if discovery.tuple_symmetric && !discovery.joined {
        return Err(CandidateFailure::new(
            CandidateFailureKind::InvalidJoin,
            "symmetric tuple handling requires a joined discovery",
        ));
    }
    let mut keys = BTreeSet::new();
    for tuple in &discovery.tuples {
        if tuple.sites.is_empty() {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidJoin,
                "discovery tuples must be nonempty",
            ));
        }
        if !discovery.joined && tuple.sites.len() != 1 {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidJoin,
                "an unjoined discovery may supply only unary tuples",
            ));
        }
        let key = site_refs(tuple);
        if tuple.sites.iter().any(|site| site.role.is_empty())
            || key.iter().collect::<BTreeSet<_>>().len() != key.len()
        {
            return Err(CandidateFailure::new(
                CandidateFailureKind::DuplicateSite,
                "tuple repeats a site or has an empty selector role",
            ));
        }
        if !keys.insert(key) {
            return Err(CandidateFailure::new(
                CandidateFailureKind::DuplicateSite,
                "discovery tuple is repeated",
            ));
        }
    }
    let mut tuples = discovery.tuples.clone();
    tuples.sort_by_key(site_refs);
    Ok(tuples)
}

fn site_refs(tuple: &DiscoveryTuple) -> Vec<TermRef> {
    tuple.sites.iter().map(|site| site.at.clone()).collect()
}

fn symmetric_key(tuple: &DiscoveryTuple) -> Vec<TermRef> {
    let mut key = site_refs(tuple);
    key.sort();
    key
}

/// Rejects a repeated name among sorted `names`, or a name that is not an
/// upper-case initial followed by ASCII alphanumerics or underscores.
fn check_binding_names<'a>(
    names: impl IntoIterator<Item = &'a str>,
) -> Result<(), CandidateFailure> {
    let mut previous = None;
    for name in names {
        if !valid_binding_name(name) || previous == Some(name) {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidBinding,
                "binding names must be unique K variable names",
            ));
        }
        previous = Some(name);
    }
    Ok(())
}

fn valid_binding_name(value: &str) -> bool {
    let mut bytes = value.bytes();
    matches!(bytes.next(), Some(b'A'..=b'Z'))
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

fn ordinary_origin(tuple: &DiscoveryTuple) -> PatchOrigin {
    PatchOrigin {
        site_tuple: site_refs(tuple),
        discovery_tuples: vec![tuple.clone()],
    }
}

const fn failed(baseline: &Baseline, kind: CandidateFailureKind) -> Selection<'_> {
    Selection {
        baseline,
        selected_origins: Vec::new(),
        completeness: Completeness::CompleteFinite,
        failure: Some(kind),
    }
}

const fn incomplete(baseline: &Baseline) -> Selection<'_> {
    Selection {
        baseline,
        selected_origins: Vec::new(),
        completeness: Completeness::Incomplete,
        failure: Some(CandidateFailureKind::IncompleteGeneration),
    }
}
