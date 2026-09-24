use kink_portable::{Digest, DigestDomain, SemanticJson, digest as checked_digest};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Stable selection/receipt failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateFailureKind {
    InvalidRegistry,
    DuplicateSite,
    InvalidJoin,
    CardinalityMismatch,
    CandidateCap,
    IncompleteGeneration,
    InvalidBinding,
    InvalidReceipt,
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

/// One K-supplied semantic match. `order` is the checked definition-order key.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Site {
    pub site_id: Digest,
    pub selector_role: String,
    pub target_lineage: Digest,
    pub term_path: SemanticJson,
    pub bindings: Vec<super::Binding>,
}

/// One complete canonical binding record for one discovery tuple.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiscoveryTuple {
    pub sites: Vec<Site>,
    pub bindings: Vec<super::Binding>,
}

/// The K-authored join shape; the host only checks supplied tuples.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiscoveryRegistry {
    pub tuples: Vec<DiscoveryTuple>,
    pub evidence: DiscoveryEvidence,
    pub joined: bool,
    pub tuple_symmetric: bool,
}

/// Claimed registry completion tied to one role-typed registry artifact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DiscoveryEvidence {
    CompleteFinite {
        registry: super::ArtifactRef,
    },
    Incomplete {
        registry: super::ArtifactRef,
        failure: CandidateFailureKind,
    },
}

/// Independently resolved K-owned registry order and semantic roots.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiscoveryAuthority {
    pub registry_id: Digest,
    pub operator_id: String,
    pub operator_version: u64,
    pub operator_digest: Digest,
    pub baseline_definition_digest: Digest,
    pub canonical_sites: Vec<Site>,
    pub canonical_tuples: Vec<DiscoveryTuple>,
    pub discovery_complete: bool,
    pub joined_roles: Option<Vec<String>>,
    pub tuple_symmetric: bool,
}

/// A registry that has passed identity, membership, order, and completion validation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidatedDiscoveryRegistry {
    tuples: Vec<DiscoveryTuple>,
    exhaustive: bool,
    joined: bool,
    tuple_symmetric: bool,
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
    pub site_tuple: Vec<Digest>,
    pub discovery_tuples: Vec<DiscoveryTuple>,
}

/// One deterministic supplied patch plus its complete origin receipt set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SuppliedPatch {
    pub patch_id: Digest,
    pub origin: PatchOrigin,
    pub edit_receipts: Vec<EditOriginReceipt>,
}

/// One deduplicated candidate. Origins retain policy-derived order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Candidate {
    pub patch_id: Digest,
    pub candidate_id: Digest,
    pub origins: Vec<SuppliedPatch>,
}

/// Whether a producer considered its whole declared finite input.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Completeness {
    /// The declared finite input was completely considered.
    CompleteFinite,
    /// The producer declares that some relevant input was not considered.
    Incomplete,
    /// Completeness is unknown.
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateGeneration {
    pub candidates: Vec<Candidate>,
    pub selected_origins: Vec<PatchOrigin>,
    pub completeness: Completeness,
    pub failure: Option<CandidateFailureKind>,
    pub scored: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatchTemplateRole {
    pub name: String,
    pub operation: String,
    pub source_roles: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EditReceiptSource {
    pub discovery_tuple_index: usize,
    pub site_id: Digest,
    pub selector_role: String,
    pub tuple_bindings: Vec<super::Binding>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EditOriginReceipt {
    pub edit_id: Digest,
    pub operation: String,
    pub target_lineage: Digest,
    pub operator_id: String,
    pub operator_version: u64,
    pub operator_digest: Digest,
    pub patch_template_digest: Digest,
    pub template_role: String,
    pub sources: Vec<EditReceiptSource>,
}

/// Exact operator/template roots against which edit receipts are checked.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReceiptAuthority {
    pub operator_id: String,
    pub operator_version: u64,
    pub operator_digest: Digest,
    pub patch_template_digest: Digest,
}

impl DiscoveryRegistry {
    /// Validates supplied discovery against independently resolved K-owned authority.
    pub fn validate(
        &self,
        authority: &DiscoveryAuthority,
    ) -> Result<ValidatedDiscoveryRegistry, CandidateFailure> {
        validate_authority(authority)?;
        if self.joined != authority.joined_roles.is_some()
            || self.tuple_symmetric != authority.tuple_symmetric
        {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidRegistry,
                "registry join shape differs from its resolved authority",
            ));
        }
        let (registry, exhaustive) = match &self.evidence {
            DiscoveryEvidence::CompleteFinite { registry } => (registry, true),
            DiscoveryEvidence::Incomplete { registry, failure } => {
                if *failure != CandidateFailureKind::IncompleteGeneration {
                    return Err(CandidateFailure::new(
                        CandidateFailureKind::InvalidRegistry,
                        "incomplete discovery has the wrong closed failure",
                    ));
                }
                (registry, false)
            }
        };
        if registry.role != "mutation-site-registry"
            || registry.digest != authority.registry_id
            || exhaustive != authority.discovery_complete
        {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidRegistry,
                "registry identity or completeness differs from resolved authority",
            ));
        }

        let site_definitions = authority
            .canonical_sites
            .iter()
            .map(|site| (site.site_id.clone(), site))
            .collect::<BTreeMap<_, _>>();
        let mut supplied_by_key = BTreeMap::<Vec<Digest>, &DiscoveryTuple>::new();
        for tuple in &self.tuples {
            if tuple.sites.is_empty() {
                return Err(CandidateFailure::new(
                    CandidateFailureKind::InvalidJoin,
                    "discovery tuples must be nonempty",
                ));
            }
            validate_bindings(&tuple.bindings)?;
            let mut local = BTreeSet::new();
            for site in &tuple.sites {
                if site.selector_role.is_empty() || !local.insert(site.site_id.clone()) {
                    return Err(CandidateFailure::new(
                        CandidateFailureKind::DuplicateSite,
                        "tuple repeats a site or has an empty selector role",
                    ));
                }
                if site_definitions.get(&site.site_id).copied() != Some(site) {
                    return Err(CandidateFailure::new(
                        CandidateFailureKind::InvalidRegistry,
                        "tuple site is dangling or differs from resolved canonical membership",
                    ));
                }
            }
            let identity_key = tuple
                .sites
                .iter()
                .map(|site| site.site_id.clone())
                .collect::<Vec<_>>();
            if supplied_by_key.insert(identity_key, tuple).is_some() {
                return Err(CandidateFailure::new(
                    CandidateFailureKind::DuplicateSite,
                    "discovery tuple is repeated",
                ));
            }
        }
        if !self.joined && self.tuples.iter().any(|tuple| tuple.sites.len() != 1) {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidJoin,
                "a null join may supply only unary tuples",
            ));
        }
        if supplied_by_key.len() != authority.canonical_tuples.len() {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidRegistry,
                "supplied tuple membership is not the complete resolved registry sequence",
            ));
        }
        let mut canonical = Vec::with_capacity(authority.canonical_tuples.len());
        for expected in &authority.canonical_tuples {
            let key = expected
                .sites
                .iter()
                .map(|site| site.site_id.clone())
                .collect::<Vec<_>>();
            let Some(supplied) = supplied_by_key.remove(&key) else {
                return Err(CandidateFailure::new(
                    CandidateFailureKind::InvalidRegistry,
                    "supplied tuples omit or substitute a canonical tuple",
                ));
            };
            if supplied != expected {
                return Err(CandidateFailure::new(
                    CandidateFailureKind::InvalidRegistry,
                    "tuple bindings or site metadata differ from resolved authority",
                ));
            }
            canonical.push(expected.clone());
        }
        Ok(ValidatedDiscoveryRegistry {
            tuples: canonical,
            exhaustive,
            joined: self.joined,
            tuple_symmetric: self.tuple_symmetric,
        })
    }
}

fn validate_authority(authority: &DiscoveryAuthority) -> Result<(), CandidateFailure> {
    if authority.operator_id.is_empty() || authority.operator_version == 0 {
        return Err(CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            "resolved operator identity is empty or has version zero",
        ));
    }
    let mut sites = BTreeMap::new();
    for site in &authority.canonical_sites {
        if site.selector_role.is_empty() {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidRegistry,
                "canonical site selector role must be nonempty",
            ));
        }
        validate_bindings(&site.bindings)?;
        validate_term_path(&site.term_path)?;
        let derived = derive_site_id(
            &authority.operator_id,
            authority.operator_version,
            &authority.baseline_definition_digest,
            &site.target_lineage,
            &site.selector_role,
            site.term_path.clone(),
            &site.bindings,
        )?;
        if site.site_id != derived || sites.insert(site.site_id.clone(), site).is_some() {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidRegistry,
                "canonical site identity drifted or is duplicated",
            ));
        }
    }
    if let Some(roles) = &authority.joined_roles {
        let unique = roles.iter().collect::<BTreeSet<_>>();
        if roles.len() < 2
            || unique.len() != roles.len()
            || roles.iter().any(|role| role.is_empty())
        {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidJoin,
                "joined authority roles must be unique, nonempty, and have arity at least two",
            ));
        }
    }
    let mut tuples = BTreeSet::new();
    for tuple in &authority.canonical_tuples {
        if tuple.sites.is_empty() {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidJoin,
                "canonical discovery tuple must be nonempty",
            ));
        }
        validate_bindings(&tuple.bindings)?;
        let mut local = BTreeSet::new();
        for site in &tuple.sites {
            if !local.insert(site.site_id.clone())
                || sites.get(&site.site_id).copied() != Some(site)
            {
                return Err(CandidateFailure::new(
                    CandidateFailureKind::InvalidRegistry,
                    "canonical tuple has a repeated, dangling, or drifted site",
                ));
            }
        }
        let key = tuple
            .sites
            .iter()
            .map(|site| site.site_id.clone())
            .collect::<Vec<_>>();
        if !tuples.insert(key) {
            return Err(CandidateFailure::new(
                CandidateFailureKind::DuplicateSite,
                "canonical discovery tuple is repeated",
            ));
        }
        match &authority.joined_roles {
            None if tuple.sites.len() == 1 => {}
            None => {
                return Err(CandidateFailure::new(
                    CandidateFailureKind::InvalidJoin,
                    "null join authority contains a non-unary tuple",
                ));
            }
            Some(roles) => {
                let actual = tuple
                    .sites
                    .iter()
                    .map(|site| site.selector_role.as_str())
                    .collect::<Vec<_>>();
                let exact = actual == roles.iter().map(String::as_str).collect::<Vec<_>>();
                let symmetric = authority.tuple_symmetric && {
                    let mut actual = actual;
                    actual.sort_unstable();
                    let mut expected = roles.iter().map(String::as_str).collect::<Vec<_>>();
                    expected.sort_unstable();
                    actual == expected
                };
                if !exact && !symmetric {
                    return Err(CandidateFailure::new(
                        CandidateFailureKind::InvalidJoin,
                        "joined tuple does not follow its declared role interface",
                    ));
                }
            }
        }
    }
    if authority.joined_roles.is_none()
        && authority.canonical_tuples
            != authority
                .canonical_sites
                .iter()
                .cloned()
                .map(|site| DiscoveryTuple {
                    bindings: site.bindings.clone(),
                    sites: vec![site],
                })
                .collect::<Vec<_>>()
    {
        return Err(CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            "null join authority must contain one singleton tuple per canonical site",
        ));
    }
    if authority.joined_roles.is_some() {
        let ranks = authority
            .canonical_sites
            .iter()
            .enumerate()
            .map(|(rank, site)| (site.site_id.clone(), rank))
            .collect::<BTreeMap<_, _>>();
        let keys = authority
            .canonical_tuples
            .iter()
            .map(|tuple| {
                tuple
                    .sites
                    .iter()
                    .map(|site| ranks[&site.site_id])
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        if keys.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidRegistry,
                "joined tuples are not in canonical site-membership order",
            ));
        }
    }
    if authority.tuple_symmetric && authority.joined_roles.is_none() {
        return Err(CandidateFailure::new(
            CandidateFailureKind::InvalidJoin,
            "symmetric tuple handling requires a joined registry",
        ));
    }
    Ok(())
}

/// Folds exact/each/tuple-each/all-matches over supplied K tuples.
pub fn select(
    registry: &DiscoveryRegistry,
    authority: &DiscoveryAuthority,
    policy: SelectionPolicy,
    candidate_cap: usize,
) -> Result<CandidateGeneration, CandidateFailure> {
    if candidate_cap == 0 {
        return Err(CandidateFailure::new(
            CandidateFailureKind::CandidateCap,
            "candidate cap must be positive",
        ));
    }
    let validated = registry.validate(authority)?;
    let mut tuples = validated.tuples.clone();
    if validated.tuple_symmetric {
        let mut groups: Vec<Vec<DiscoveryTuple>> = Vec::new();
        for tuple in tuples {
            let mut symmetric_key = tuple
                .sites
                .iter()
                .map(|site| site.site_id.clone())
                .collect::<Vec<_>>();
            symmetric_key.sort();
            if let Some(group) = groups.iter_mut().find(|group| {
                let mut key = group[0]
                    .sites
                    .iter()
                    .map(|site| site.site_id.clone())
                    .collect::<Vec<_>>();
                key.sort();
                key == symmetric_key
            }) {
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
            if !validated.exhaustive {
                return Ok(incomplete(Vec::new()));
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
            if validated.joined || tuples.iter().any(|tuple| tuple.sites.len() != 1) {
                return Ok(failed(CandidateFailureKind::InvalidJoin));
            }
            tuples.iter().map(ordinary_origin).collect()
        }
        SelectionPolicy::TupleEach => {
            if !validated.joined {
                return Ok(failed(CandidateFailureKind::InvalidJoin));
            }
            if validated.tuple_symmetric {
                let all = validated.tuples.clone();
                tuples
                    .iter()
                    .map(|representative| {
                        let mut key = representative
                            .sites
                            .iter()
                            .map(|site| site.site_id.clone())
                            .collect::<Vec<_>>();
                        key.sort();
                        let mut retained = all
                            .iter()
                            .filter(|tuple| {
                                let mut other = tuple
                                    .sites
                                    .iter()
                                    .map(|site| site.site_id.clone())
                                    .collect::<Vec<_>>();
                                other.sort();
                                other == key
                            })
                            .cloned()
                            .collect::<Vec<_>>();
                        retained.sort_by_key(|tuple| {
                            validated
                                .tuples
                                .iter()
                                .position(|candidate| candidate == tuple)
                                .expect("validated tuple is retained")
                        });
                        PatchOrigin {
                            site_tuple: representative
                                .sites
                                .iter()
                                .map(|site| site.site_id.clone())
                                .collect(),
                            discovery_tuples: retained,
                        }
                    })
                    .collect()
            } else {
                tuples.iter().map(ordinary_origin).collect()
            }
        }
        SelectionPolicy::AllMatches => {
            if validated.joined || tuples.iter().any(|tuple| tuple.sites.len() != 1) {
                return Ok(failed(CandidateFailureKind::InvalidJoin));
            }
            if tuples.is_empty() {
                Vec::new()
            } else {
                vec![PatchOrigin {
                    site_tuple: tuples
                        .iter()
                        .map(|tuple| tuple.sites[0].site_id.clone())
                        .collect(),
                    discovery_tuples: tuples,
                }]
            }
        }
    };
    let omitted = origins.len() > candidate_cap;
    origins.truncate(candidate_cap);
    let complete = validated.exhaustive && !omitted;
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
    /// Associates one deterministic patch with each retained origin and folds equal patches.
    pub fn fold_patches(
        mut self,
        operator_id: &str,
        operator_version: u64,
        baseline_definition_digest: &Digest,
        patches: Vec<SuppliedPatch>,
    ) -> Result<Self, CandidateFailure> {
        if patches.len() != self.selected_origins.len()
            || patches
                .iter()
                .zip(&self.selected_origins)
                .any(|(patch, origin)| patch.origin != *origin)
        {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidRegistry,
                "supplied patches do not correspond one-for-one with retained origins",
            ));
        }
        let mut by_patch: BTreeMap<Digest, Vec<SuppliedPatch>> = BTreeMap::new();
        let mut order = Vec::new();
        for patch in patches {
            if !by_patch.contains_key(&patch.patch_id) {
                order.push(patch.patch_id.clone());
            }
            by_patch
                .entry(patch.patch_id.clone())
                .or_default()
                .push(patch);
        }
        self.candidates = order
            .into_iter()
            .map(|patch_id| {
                let candidate_id = derive_candidate_id(
                    operator_id,
                    operator_version,
                    baseline_definition_digest,
                    &patch_id,
                )?;
                Ok(Candidate {
                    origins: by_patch.remove(&patch_id).expect("ordered patch exists"),
                    patch_id,
                    candidate_id,
                })
            })
            .collect::<Result<Vec<_>, CandidateFailure>>()?;
        Ok(self)
    }
}

/// Validates exact edit-to-origin receipts without interpreting template semantics.
pub fn validate_edit_receipts(
    patch: &SuppliedPatch,
    authority: &ReceiptAuthority,
    roles: &[PatchTemplateRole],
    operator_selector_roles: &[String],
    edit_order: &[Digest],
) -> Result<(), CandidateFailure> {
    if patch.edit_receipts.len() != edit_order.len()
        || patch
            .edit_receipts
            .iter()
            .zip(edit_order)
            .any(|(receipt, edit)| &receipt.edit_id != edit)
    {
        return Err(invalid_receipt(
            "receipt list must exactly follow patch edit order",
        ));
    }
    let role_map = roles
        .iter()
        .map(|role| (role.name.as_str(), role))
        .collect::<BTreeMap<_, _>>();
    if role_map.len() != roles.len()
        || roles.iter().any(|role| {
            role.name.is_empty()
                || role.operation.is_empty()
                || role.source_roles.is_empty()
                || role.source_roles.iter().any(String::is_empty)
                || role.source_roles.iter().collect::<BTreeSet<_>>().len()
                    != role.source_roles.len()
        })
    {
        return Err(invalid_receipt(
            "template roles and source interfaces must be unique and nonempty",
        ));
    }
    let covered_roles = roles
        .iter()
        .flat_map(|role| role.source_roles.iter())
        .collect::<Vec<_>>();
    if covered_roles != operator_selector_roles.iter().collect::<Vec<_>>() {
        return Err(invalid_receipt(
            "template source roles must exactly cover operator selectors in clause order",
        ));
    }
    if patch.origin.site_tuple.is_empty()
        || patch
            .origin
            .site_tuple
            .iter()
            .collect::<BTreeSet<_>>()
            .len()
            != patch.origin.site_tuple.len()
        || patch.origin.discovery_tuples.is_empty()
    {
        return Err(invalid_receipt(
            "patch origin must have unique sites and at least one discovery tuple",
        ));
    }
    for receipt in &patch.edit_receipts {
        if receipt.operator_id != authority.operator_id
            || receipt.operator_version != authority.operator_version
            || receipt.operator_digest != authority.operator_digest
            || receipt.patch_template_digest != authority.patch_template_digest
        {
            return Err(invalid_receipt(
                "receipt binds another operator or patch template",
            ));
        }
        let Some(role) = role_map.get(receipt.template_role.as_str()) else {
            return Err(invalid_receipt("receipt names an unknown template role"));
        };
        if receipt.operation != role.operation || receipt.sources.len() != role.source_roles.len() {
            return Err(invalid_receipt(
                "receipt operation or source arity differs from its role",
            ));
        }
        let mut authorized = false;
        let mut previous_source_position = None;
        let mut seen_sources = BTreeSet::new();
        for (source, expected_role) in receipt.sources.iter().zip(&role.source_roles) {
            let Some(tuple) = patch
                .origin
                .discovery_tuples
                .get(source.discovery_tuple_index)
            else {
                return Err(invalid_receipt(
                    "receipt source tuple index is out of range",
                ));
            };
            let Some(site) = tuple
                .sites
                .iter()
                .find(|site| site.site_id == source.site_id)
            else {
                return Err(invalid_receipt(
                    "receipt source site is absent from its tuple",
                ));
            };
            let site_position = tuple
                .sites
                .iter()
                .position(|candidate| candidate.site_id == source.site_id)
                .expect("source site was resolved");
            let source_position = (source.discovery_tuple_index, site_position);
            if previous_source_position.is_some_and(|previous| previous >= source_position)
                || !seen_sources.insert((source.discovery_tuple_index, source.site_id.clone()))
            {
                return Err(invalid_receipt(
                    "receipt sources must be unique in discovery tuple and site order",
                ));
            }
            previous_source_position = Some(source_position);
            if &source.selector_role != expected_role
                || source.selector_role != site.selector_role
                || source.tuple_bindings != tuple.bindings
                || !patch.origin.site_tuple.contains(&source.site_id)
            {
                return Err(invalid_receipt(
                    "receipt source role or complete bindings drifted",
                ));
            }
            authorized |= site.target_lineage == receipt.target_lineage;
        }
        if !authorized {
            return Err(invalid_receipt(
                "receipt sources do not authorize the edit target lineage",
            ));
        }
    }
    Ok(())
}

fn validate_bindings(bindings: &[super::Binding]) -> Result<(), CandidateFailure> {
    let names = bindings
        .iter()
        .map(|item| item.name.as_str())
        .collect::<Vec<_>>();
    if names.windows(2).any(|pair| pair[0] >= pair[1])
        || names.iter().any(|name| !valid_binding_name(name))
    {
        return Err(CandidateFailure::new(
            CandidateFailureKind::InvalidBinding,
            "discovery bindings must have unique names ordered by name",
        ));
    }
    for binding in bindings {
        validate_binding_term(&binding.term)?;
    }
    Ok(())
}

fn validate_binding_term(term: &kink_portable::Term) -> Result<(), CandidateFailure> {
    use kink_portable::TermNode;

    if term.sort.is_empty() {
        return Err(CandidateFailure::new(
            CandidateFailureKind::InvalidBinding,
            "binding term sort must be nonempty",
        ));
    }
    match &term.node {
        TermNode::Token { .. } => {}
        TermNode::Variable { name } if !name.is_empty() => {}
        TermNode::Variable { .. } => {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidBinding,
                "binding variable name must be nonempty",
            ));
        }
        TermNode::Application { label, args, .. } => {
            if label.is_empty() {
                return Err(CandidateFailure::new(
                    CandidateFailureKind::InvalidBinding,
                    "binding application label must be nonempty",
                ));
            }
            for argument in args {
                validate_binding_term(argument)?;
            }
        }
        TermNode::Rewrite { left, right } => {
            validate_binding_term(left)?;
            validate_binding_term(right)?;
            if left.sort != right.sort || left.sort != term.sort {
                return Err(CandidateFailure::new(
                    CandidateFailureKind::InvalidBinding,
                    "binding rewrite sorts disagree",
                ));
            }
        }
        TermNode::Sequence { items } => {
            for item in items {
                validate_binding_term(item)?;
            }
        }
        TermNode::Injection {
            from_sort,
            to_sort,
            term: child,
        } => {
            validate_binding_term(child)?;
            if child.sort != *from_sort || term.sort != *to_sort {
                return Err(CandidateFailure::new(
                    CandidateFailureKind::InvalidBinding,
                    "binding injection sorts disagree",
                ));
            }
        }
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
        site_tuple: tuple
            .sites
            .iter()
            .map(|site| site.site_id.clone())
            .collect(),
        discovery_tuples: vec![tuple.clone()],
    }
}

/// Derives the v1 candidate identity from the exact operator/baseline/patch roots.
pub fn derive_candidate_id(
    operator_id: &str,
    operator_version: u64,
    baseline: &Digest,
    patch_id: &Digest,
) -> Result<Digest, CandidateFailure> {
    if operator_id.is_empty() || operator_version == 0 {
        return Err(CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            "candidate operator identity must be nonempty with a positive version",
        ));
    }
    let version = i64::try_from(operator_version).map_err(|_| {
        CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            "candidate operator version exceeds i64",
        )
    })?;
    let value = object([
        ("operatorId", string(operator_id)),
        ("operatorVersion", SemanticJson::Integer(version)),
        ("baselineDefinitionDigest", string(baseline.as_str())),
        ("patchId", string(patch_id.as_str())),
    ]);
    checked_digest(
        &DigestDomain::new("k-in-k/candidate/v1").expect("static domain"),
        &value,
    )
    .map_err(|error| {
        CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            format!("candidate identity contains invalid semantic JSON: {error}"),
        )
    })
}

/// Derives a K-supplied discovery site identity without discovering a site.
pub fn derive_site_id(
    operator_id: &str,
    operator_version: u64,
    baseline_definition_digest: &Digest,
    target_lineage: &Digest,
    selector_role: &str,
    term_path: SemanticJson,
    bindings: &[super::Binding],
) -> Result<Digest, CandidateFailure> {
    if operator_id.is_empty() || operator_version == 0 || selector_role.is_empty() {
        return Err(CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            "site identity roots must be nonempty with a positive operator version",
        ));
    }
    let operator_version = i64::try_from(operator_version).map_err(|_| {
        CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            "site operator version exceeds i64",
        )
    })?;
    validate_term_path(&term_path)?;
    let mut normalized = bindings.to_vec();
    normalized.sort_by(|left, right| left.name.cmp(&right.name));
    validate_bindings(&normalized)?;
    let value = object([
        ("operatorId", string(operator_id)),
        ("operatorVersion", SemanticJson::Integer(operator_version)),
        (
            "baselineDefinitionDigest",
            string(baseline_definition_digest.as_str()),
        ),
        ("targetLineage", string(target_lineage.as_str())),
        ("selectorRole", string(selector_role)),
        ("termPath", term_path),
        (
            "bindings",
            SemanticJson::Array(
                normalized
                    .iter()
                    .map(|binding| {
                        object([
                            ("name", string(&binding.name)),
                            ("term", binding.term.to_json()),
                        ])
                    })
                    .collect(),
            ),
        ),
    ]);
    checked_digest(
        &DigestDomain::new("k-in-k/site/v1").expect("static domain"),
        &value,
    )
    .map_err(|error| {
        CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            format!("site identity contains invalid semantic JSON: {error}"),
        )
    })
}

/// Derives the v1 mutant identity; this remains distinct from candidate identity.
#[must_use]
pub fn derive_mutant_id(baseline_definition_digest: &Digest, patch_id: &Digest) -> Digest {
    digest(
        &DigestDomain::new("k-in-k/mutant/v1").expect("static domain"),
        &object([
            (
                "baselineDefinitionDigest",
                string(baseline_definition_digest.as_str()),
            ),
            ("patchId", string(patch_id.as_str())),
        ]),
    )
}

/// Derives the v1 instance identity including every discovery binding and edit receipt.
pub fn derive_instance_id(
    operator_id: &str,
    operator_version: u64,
    baseline_definition_digest: &Digest,
    policy: SelectionPolicy,
    patch: &SuppliedPatch,
) -> Result<Digest, CandidateFailure> {
    if operator_id.is_empty() || operator_version == 0 {
        return Err(CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            "instance operator identity must be nonempty with a positive version",
        ));
    }
    let operator_version = i64::try_from(operator_version).map_err(|_| {
        CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            "instance operator version exceeds i64",
        )
    })?;
    let discovery_tuples = patch
        .origin
        .discovery_tuples
        .iter()
        .map(|tuple| {
            object([
                (
                    "siteTuple",
                    SemanticJson::Array(
                        tuple
                            .sites
                            .iter()
                            .map(|site| string(site.site_id.as_str()))
                            .collect(),
                    ),
                ),
                ("bindings", bindings_json(&tuple.bindings)),
            ])
        })
        .collect();
    let receipts = patch
        .edit_receipts
        .iter()
        .map(|receipt| {
            let operator_version = i64::try_from(receipt.operator_version).map_err(|_| {
                CandidateFailure::new(
                    CandidateFailureKind::InvalidReceipt,
                    "receipt operator version exceeds i64",
                )
            })?;
            let sources = receipt
                .sources
                .iter()
                .map(|source| {
                    let tuple_index =
                        i64::try_from(source.discovery_tuple_index).map_err(|_| {
                            CandidateFailure::new(
                                CandidateFailureKind::InvalidReceipt,
                                "receipt discovery tuple index exceeds i64",
                            )
                        })?;
                    Ok(object([
                        ("discoveryTupleIndex", SemanticJson::Integer(tuple_index)),
                        ("siteId", string(source.site_id.as_str())),
                        ("selectorRole", string(&source.selector_role)),
                        ("tupleBindings", bindings_json(&source.tuple_bindings)),
                    ]))
                })
                .collect::<Result<Vec<_>, CandidateFailure>>()?;
            Ok(object([
                ("editId", string(receipt.edit_id.as_str())),
                (
                    "operator",
                    object([
                        ("id", string(&receipt.operator_id)),
                        ("version", SemanticJson::Integer(operator_version)),
                        ("digest", string(receipt.operator_digest.as_str())),
                    ]),
                ),
                (
                    "patchTemplateDigest",
                    string(receipt.patch_template_digest.as_str()),
                ),
                ("templateRole", string(&receipt.template_role)),
                ("sources", SemanticJson::Array(sources)),
            ]))
        })
        .collect::<Result<Vec<_>, CandidateFailure>>()?;
    let value = object([
        ("operatorId", string(operator_id)),
        ("operatorVersion", SemanticJson::Integer(operator_version)),
        (
            "baselineDefinitionDigest",
            string(baseline_definition_digest.as_str()),
        ),
        ("policy", string(policy.as_str())),
        (
            "siteTuple",
            SemanticJson::Array(
                patch
                    .origin
                    .site_tuple
                    .iter()
                    .map(|site| string(site.as_str()))
                    .collect(),
            ),
        ),
        ("discoveryTuples", SemanticJson::Array(discovery_tuples)),
        ("patchId", string(patch.patch_id.as_str())),
        ("editReceipts", SemanticJson::Array(receipts)),
    ]);
    checked_digest(
        &DigestDomain::new("k-in-k/instance/v1").expect("static domain"),
        &value,
    )
    .map_err(|error| {
        CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            format!("instance identity contains invalid semantic JSON: {error}"),
        )
    })
}

impl SelectionPolicy {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Exact { .. } => "exact",
            Self::Each => "each",
            Self::TupleEach => "tuple-each",
            Self::AllMatches => "all-matches",
        }
    }
}

/// Canonical digest for a name-sorted supplied binding list.
pub fn canonical_binding_digest(bindings: &[super::Binding]) -> Result<Digest, CandidateFailure> {
    let mut normalized = bindings.to_vec();
    normalized.sort_by(|left, right| left.name.cmp(&right.name));
    validate_bindings(&normalized)?;
    checked_digest(
        &DigestDomain::new("k-in-k/bindings/v1").expect("static domain"),
        &SemanticJson::Array(
            normalized
                .iter()
                .map(|binding| {
                    object([
                        ("name", string(&binding.name)),
                        ("term", binding.term.to_json()),
                    ])
                })
                .collect(),
        ),
    )
    .map_err(|error| {
        CandidateFailure::new(
            CandidateFailureKind::InvalidBinding,
            format!("binding digest contains invalid semantic JSON: {error}"),
        )
    })
}

fn bindings_json(bindings: &[super::Binding]) -> SemanticJson {
    SemanticJson::Array(
        bindings
            .iter()
            .map(|binding| {
                object([
                    ("name", string(&binding.name)),
                    ("term", binding.term.to_json()),
                ])
            })
            .collect(),
    )
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

fn incomplete(origins: Vec<PatchOrigin>) -> CandidateGeneration {
    CandidateGeneration {
        candidates: Vec::new(),
        selected_origins: origins,
        completeness: Completeness::Incomplete,
        failure: Some(CandidateFailureKind::IncompleteGeneration),
        scored: false,
    }
}

fn invalid_receipt(detail: impl Into<String>) -> CandidateFailure {
    CandidateFailure::new(CandidateFailureKind::InvalidReceipt, detail)
}

fn validate_term_path(value: &SemanticJson) -> Result<(), CandidateFailure> {
    let Some(steps) = value.as_array() else {
        return Err(CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            "site term path must be an array",
        ));
    };
    if steps.is_empty() {
        return Err(CandidateFailure::new(
            CandidateFailureKind::InvalidRegistry,
            "site term path must be nonempty",
        ));
    }
    for step in steps {
        let Some(fields) = step.as_object() else {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidRegistry,
                "site path step must be an object",
            ));
        };
        let valid = match fields.get("kind").and_then(SemanticJson::as_str) {
            Some("field") if fields.len() == 2 => matches!(
                fields.get("name").and_then(SemanticJson::as_str),
                Some("sentence" | "body" | "lhs" | "rhs" | "requires" | "ensures" | "attributes")
            ),
            Some("argument" | "sequence-item") if fields.len() == 2 => fields
                .get("index")
                .and_then(SemanticJson::as_i64)
                .is_some_and(|index| index >= 0),
            Some("injection-term") if fields.len() == 1 => true,
            Some("attribute") if fields.len() == 2 => fields
                .get("name")
                .and_then(SemanticJson::as_str)
                .is_some_and(|name| !name.is_empty()),
            _ => false,
        };
        if !valid {
            return Err(CandidateFailure::new(
                CandidateFailureKind::InvalidRegistry,
                "site term path contains an open or malformed step",
            ));
        }
    }
    Ok(())
}

fn string(value: &str) -> SemanticJson {
    SemanticJson::String(value.to_owned())
}

fn object<const N: usize>(items: [(&str, SemanticJson); N]) -> SemanticJson {
    SemanticJson::Object(
        items
            .into_iter()
            .map(|(key, value)| (key.to_owned(), value))
            .collect(),
    )
}

fn digest(domain: &DigestDomain, value: &SemanticJson) -> Digest {
    checked_digest(domain, value).expect("validated candidate inputs form semantic JSON")
}

#[cfg(test)]
mod tests {
    use super::*;
    use kink_portable::{Term, TermNode};

    fn digest_value(character: char) -> Digest {
        Digest::parse(&character.to_string().repeat(64)).expect("test digest")
    }

    fn term(sort: &str, text: &str) -> Term {
        Term {
            sort: sort.to_owned(),
            node: TermNode::Token {
                text: text.to_owned(),
            },
        }
    }

    fn term_path() -> SemanticJson {
        SemanticJson::Array(vec![object([
            ("kind", string("field")),
            ("name", string("body")),
        ])])
    }

    fn site(character: char, role: &str, _order: u64) -> Site {
        let target_lineage = digest_value(if character == 'a' { 'd' } else { 'e' });
        let term_path = term_path();
        let bindings = Vec::new();
        Site {
            site_id: derive_site_id(
                "op",
                1,
                &digest_value('a'),
                &target_lineage,
                role,
                term_path.clone(),
                &bindings,
            )
            .expect("test site identity"),
            selector_role: role.to_owned(),
            target_lineage,
            term_path,
            bindings,
        }
    }

    fn tuple(sites: Vec<Site>) -> DiscoveryTuple {
        DiscoveryTuple {
            sites,
            bindings: Vec::new(),
        }
    }

    fn authority(
        tuples: &[DiscoveryTuple],
        joined_roles: Option<Vec<String>>,
    ) -> DiscoveryAuthority {
        let mut canonical_sites = Vec::new();
        for tuple in tuples {
            for site in &tuple.sites {
                if !canonical_sites.contains(site) {
                    canonical_sites.push(site.clone());
                }
            }
        }
        DiscoveryAuthority {
            registry_id: digest_value('f'),
            operator_id: "op".to_owned(),
            operator_version: 1,
            operator_digest: digest_value('c'),
            baseline_definition_digest: digest_value('a'),
            canonical_sites,
            canonical_tuples: tuples.to_vec(),
            discovery_complete: true,
            joined_roles,
            tuple_symmetric: false,
        }
    }

    #[test]
    fn public_identity_helpers_reject_unrepresentable_inputs() {
        let baseline = digest_value('a');
        assert_eq!(
            derive_site_id(
                "op",
                u64::MAX,
                &baseline,
                &digest_value('d'),
                "write",
                term_path(),
                &[],
            )
            .expect_err("oversized site operator version")
            .kind(),
            CandidateFailureKind::InvalidRegistry
        );
        let patch = SuppliedPatch {
            patch_id: digest_value('9'),
            origin: PatchOrigin {
                site_tuple: Vec::new(),
                discovery_tuples: Vec::new(),
            },
            edit_receipts: Vec::new(),
        };
        assert_eq!(
            derive_instance_id("op", u64::MAX, &baseline, SelectionPolicy::Each, &patch)
                .expect_err("oversized instance operator version")
                .kind(),
            CandidateFailureKind::InvalidRegistry
        );
        assert_eq!(
            derive_instance_id("e\u{301}", 1, &baseline, SelectionPolicy::Each, &patch)
                .expect_err("non-NFC instance operator")
                .kind(),
            CandidateFailureKind::InvalidRegistry
        );
    }

    #[test]
    fn cap_is_applied_before_patch_deduplication() {
        let tuples = vec![
            tuple(vec![site('a', "write", 1)]),
            tuple(vec![site('b', "load", 2)]),
        ];
        let authority = authority(&tuples, None);
        let registry = DiscoveryRegistry {
            tuples,
            evidence: DiscoveryEvidence::CompleteFinite {
                registry: crate::ArtifactRef {
                    role: "mutation-site-registry".to_owned(),
                    digest: authority.registry_id.clone(),
                },
            },
            joined: false,
            tuple_symmetric: false,
        };
        let selected = select(&registry, &authority, SelectionPolicy::Each, 1).expect("selection");
        assert_eq!(selected.selected_origins.len(), 1);
        assert_eq!(
            selected.failure,
            Some(CandidateFailureKind::IncompleteGeneration)
        );
        assert!(!selected.scored);
    }

    #[test]
    fn binding_digest_normalizes_name_order() {
        let left = vec![
            super::super::Binding {
                name: "V".to_owned(),
                term: term("Int", "7"),
            },
            super::super::Binding {
                name: "A".to_owned(),
                term: term("Address", "1"),
            },
        ];
        let mut right = left.clone();
        right.reverse();
        assert_eq!(
            canonical_binding_digest(&left),
            canonical_binding_digest(&right)
        );
    }

    #[test]
    fn receipt_requires_exact_source_bindings_and_authorization() {
        let binding = super::super::Binding {
            name: "A".to_owned(),
            term: term("Address", "1"),
        };
        let discovery = DiscoveryTuple {
            sites: vec![site('a', "write", 1)],
            bindings: vec![binding.clone()],
        };
        let origin = ordinary_origin(&discovery);
        let edit_id = digest_value('b');
        let operator_digest = digest_value('c');
        let template_digest = digest_value('f');
        let authority = ReceiptAuthority {
            operator_id: "op".to_owned(),
            operator_version: 1,
            operator_digest: operator_digest.clone(),
            patch_template_digest: template_digest.clone(),
        };
        let source_site_id = discovery.sites[0].site_id.clone();
        let mut patch = SuppliedPatch {
            patch_id: digest_value('9'),
            origin,
            edit_receipts: vec![EditOriginReceipt {
                edit_id: edit_id.clone(),
                operation: "replace-term".to_owned(),
                target_lineage: digest_value('d'),
                operator_id: "op".to_owned(),
                operator_version: 1,
                operator_digest: operator_digest.clone(),
                patch_template_digest: template_digest.clone(),
                template_role: "replacement".to_owned(),
                sources: vec![EditReceiptSource {
                    discovery_tuple_index: 0,
                    site_id: source_site_id,
                    selector_role: "write".to_owned(),
                    tuple_bindings: vec![binding],
                }],
            }],
        };
        let roles = [PatchTemplateRole {
            name: "replacement".to_owned(),
            operation: "replace-term".to_owned(),
            source_roles: vec!["write".to_owned()],
        }];
        assert!(
            validate_edit_receipts(
                &patch,
                &authority,
                &roles,
                &["write".to_owned()],
                &[edit_id]
            )
            .is_ok()
        );
        patch.edit_receipts[0].sources[0].tuple_bindings.clear();
        assert_eq!(
            validate_edit_receipts(
                &patch,
                &authority,
                &roles,
                &["write".to_owned()],
                &[digest_value('b')]
            )
            .expect_err("missing bindings")
            .kind(),
            CandidateFailureKind::InvalidReceipt
        );
        patch.edit_receipts[0].sources[0].tuple_bindings =
            patch.origin.discovery_tuples[0].bindings.clone();
        patch.edit_receipts[0].target_lineage = digest_value('e');
        assert_eq!(
            validate_edit_receipts(
                &patch,
                &authority,
                &roles,
                &["write".to_owned()],
                &[digest_value('b')]
            )
            .expect_err("cross-origin target")
            .kind(),
            CandidateFailureKind::InvalidReceipt
        );
    }
}
