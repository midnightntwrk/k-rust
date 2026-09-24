//! Mutation sites, selection policies and candidate folding.
//!
//! Sites are term positions of one [`Baseline`], identified by their
//! [`TermRef`]; there are no site, candidate or mutant digests. Operators build
//! a [`Patch`] from a selected origin, so every edit is authorized by the sites
//! it was built from. Equal patches fold into one candidate that keeps every
//! origin, and a patch that does not apply is a rejected disposition, never a
//! mutant.

use crate::{Baseline, Patch, PatchFailure, TermRef, apply, child, field_term};
use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::Term;
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
        if bindings.iter().any(|(name, _)| !valid_binding_name(name))
            || bindings.windows(2).any(|pair| pair[0].0 == pair[1].0)
        {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidBinding,
                "binding names must be unique K variable names",
            ));
        }
        Ok(Self(bindings))
    }

    #[must_use]
    pub fn as_slice(&self) -> &[(String, Term)] {
        &self.0
    }
}

/// One discovered match: a site tuple and its bindings.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiscoveryTuple {
    pub sites: Vec<Site>,
    pub bindings: Bindings,
}

/// The discovered tuples of one operator and whether they are all of them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Discovery {
    pub tuples: Vec<DiscoveryTuple>,
    /// Every match was considered.
    pub exhaustive: bool,
    /// Tuples join several selector roles.
    pub joined: bool,
    /// Tuples that are permutations of one another are one instance.
    pub tuple_symmetric: bool,
}

/// One conjunctive clause of a site selector.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SiteSelector {
    /// The rule carries this module-qualified label.
    RuleLabel(String),
    /// The position is a whole sentence field: 0 body, 1 requires, 2 ensures.
    Root(u32),
    /// The position holds an application of this label.
    Head { label: String },
}

/// Derives every term position of the baseline's written rules that
/// satisfies all `selector` clauses, as unary tuples in [`TermRef`] order.
///
/// The result is exhaustive: every written rule and every position in it is
/// considered.
#[must_use]
pub fn derive_sites(baseline: &Baseline, role: &str, selector: &[SiteSelector]) -> Discovery {
    let mut sites = Vec::new();
    for (sentence_ref, sentence) in baseline.authored_sentences() {
        if !matches!(sentence, Sentence::Rule { .. })
            || !selector.iter().all(|clause| match clause {
                SiteSelector::RuleLabel(label) => {
                    sentence.attributes().string(AttributeKey::Label) == Some(label.as_str())
                }
                SiteSelector::Root(_) | SiteSelector::Head { .. } => true,
            })
        {
            continue;
        }
        for field in 0..3 {
            let Some(root) = field_term(sentence, field) else {
                continue;
            };
            let mut stack = vec![(vec![field], root)];
            while let Some((path, term)) = stack.pop() {
                let matched = selector.iter().all(|clause| match clause {
                    SiteSelector::RuleLabel(_) => true,
                    SiteSelector::Root(root) => path.as_slice() == [*root],
                    SiteSelector::Head { label } => matches!(
                        term.unannotated(),
                        Term::Apply { label: head, .. } if head.name == *label
                    ),
                });
                if matched {
                    sites.push(TermRef::new(sentence_ref.clone(), path.clone()));
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
    sites.sort();
    Discovery {
        tuples: sites
            .into_iter()
            .map(|at| DiscoveryTuple {
                sites: vec![Site {
                    role: role.to_owned(),
                    at,
                }],
                bindings: Bindings::default(),
            })
            .collect(),
        exhaustive: true,
        joined: false,
        tuple_symmetric: false,
    }
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
    /// Completeness is unknown. Generation never produces it; kink-campaign
    /// oracle sides still use it.
    Unknown,
}

/// What became of one selected origin.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CandidateDisposition {
    /// The origin's patch is `candidates[index]`.
    Mutant(usize),
    /// The origin's patch does not apply to the baseline.
    Rejected(PatchFailure),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateGeneration {
    pub candidates: Vec<Candidate>,
    pub selected_origins: Vec<PatchOrigin>,
    pub completeness: Completeness,
    pub failure: Option<CandidateFailureKind>,
    pub scored: bool,
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
pub fn select(
    discovery: &Discovery,
    policy: SelectionPolicy,
    candidate_cap: usize,
) -> Result<CandidateGeneration, CandidateFailure> {
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
                return Ok(incomplete());
            }
            if tuples
                .iter()
                .any(|tuple| tuple.sites.len() != expected_tuple_arity)
            {
                return Ok(failed(CandidateFailureKind::InvalidJoin));
            }
            if tuples.len() != expected_tuple_count {
                return Ok(failed(CandidateFailureKind::CardinalityMismatch));
            }
            tuples.iter().map(ordinary_origin).collect()
        }
        SelectionPolicy::Each => {
            if discovery.joined || tuples.iter().any(|tuple| tuple.sites.len() != 1) {
                return Ok(failed(CandidateFailureKind::InvalidJoin));
            }
            tuples.iter().map(ordinary_origin).collect()
        }
        SelectionPolicy::TupleEach => {
            if !discovery.joined {
                return Ok(failed(CandidateFailureKind::InvalidJoin));
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
                return Ok(failed(CandidateFailureKind::InvalidJoin));
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
    Ok(CandidateGeneration {
        candidates: Vec::new(),
        selected_origins: origins,
        completeness: if complete {
            Completeness::CompleteFinite
        } else {
            Completeness::Incomplete
        },
        failure: (!complete).then_some(CandidateFailureKind::IncompleteGeneration),
        scored: complete,
    })
}

impl CandidateGeneration {
    /// Builds one patch per retained origin with `patch_for`, folds equal
    /// patches into one candidate that keeps every origin, and applies each
    /// distinct patch to `baseline` once.
    ///
    /// A patch that does not apply (for example a no-change patch) is a
    /// rejected disposition and never a candidate. The dispositions are
    /// parallel to `selected_origins`.
    #[must_use]
    pub fn fold(
        mut self,
        baseline: &Baseline,
        operator: &str,
        mut patch_for: impl FnMut(&PatchOrigin) -> Patch,
    ) -> (Self, Vec<CandidateDisposition>) {
        let mut rejected: Vec<(Patch, PatchFailure)> = Vec::new();
        let mut dispositions = Vec::with_capacity(self.selected_origins.len());
        for origin in &self.selected_origins {
            let patch = patch_for(origin);
            if let Some(index) = self
                .candidates
                .iter()
                .position(|candidate| candidate.patch == patch)
            {
                self.candidates[index].origins.push(origin.clone());
                dispositions.push(CandidateDisposition::Mutant(index));
            } else if let Some((_, failure)) = rejected.iter().find(|(other, _)| *other == patch) {
                dispositions.push(CandidateDisposition::Rejected(failure.clone()));
            } else {
                match apply(baseline, &patch) {
                    Ok(_) => {
                        dispositions.push(CandidateDisposition::Mutant(self.candidates.len()));
                        self.candidates.push(Candidate {
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
        (self, dispositions)
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

fn failed(kind: CandidateFailureKind) -> CandidateGeneration {
    CandidateGeneration {
        candidates: Vec::new(),
        selected_origins: Vec::new(),
        completeness: Completeness::CompleteFinite,
        failure: Some(kind),
        scored: false,
    }
}

fn incomplete() -> CandidateGeneration {
    CandidateGeneration {
        candidates: Vec::new(),
        selected_origins: Vec::new(),
        completeness: Completeness::Incomplete,
        failure: Some(CandidateFailureKind::IncompleteGeneration),
        scored: false,
    }
}
