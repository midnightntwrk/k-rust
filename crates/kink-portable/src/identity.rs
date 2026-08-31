use crate::definition::{GeneratedIdentity, Location, SentenceKind};
use crate::json::{Digest, DigestDomain, SemanticJson, digest};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Closed portable identity failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IdentityErrorKind {
    /// The JSON shape is not the closed v1 shape.
    MalformedValue,
    /// The value names a native or portable form outside the supported v1 surface.
    UnsupportedForm,
    /// An unordered set contains a duplicate or is not in canonical order.
    NonCanonicalSet,
    /// A supplied identity differs from the derived identity.
    DigestMismatch,
    /// Local sort, signature, variable, or provenance invariants fail.
    IllFormed,
}

/// Typed identity/portable-value failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IdentityError {
    kind: IdentityErrorKind,
    detail: String,
}

impl IdentityError {
    /// Constructs a typed failure.
    #[must_use]
    pub fn new(kind: IdentityErrorKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Returns the decision-bearing classification.
    #[must_use]
    pub const fn kind(&self) -> IdentityErrorKind {
        self.kind
    }
}

impl fmt::Display for IdentityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for IdentityError {}

/// Baseline-family identity input.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BaselineFamily {
    /// Human family name.
    pub family_name: String,
    /// Entry modules, interpreted as a set for identity.
    pub entry_modules: Vec<String>,
    /// Semantic compatibility profile.
    pub compatibility_profile: String,
}

impl BaselineFamily {
    /// Parses the exact closed identity payload.
    pub fn from_json(value: &SemanticJson) -> Result<Self, IdentityError> {
        let fields = exact_object(
            value,
            &["familyName", "entryModules", "compatibilityProfile"],
            "baseline family",
        )?;
        let family_name = nonempty_string(fields.get("familyName"), "familyName")?;
        let compatibility_profile =
            nonempty_string(fields.get("compatibilityProfile"), "compatibilityProfile")?;
        let entries = fields
            .get("entryModules")
            .and_then(SemanticJson::as_array)
            .ok_or_else(|| malformed("entryModules must be an array"))?;
        let mut entry_modules = Vec::with_capacity(entries.len());
        let mut unique = BTreeSet::new();
        for entry in entries {
            let entry = nonempty_string(Some(entry), "entryModules item")?;
            if !unique.insert(entry.clone()) {
                return Err(IdentityError::new(
                    IdentityErrorKind::NonCanonicalSet,
                    "baseline family repeats an entry module",
                ));
            }
            entry_modules.push(entry);
        }
        if entry_modules.is_empty() {
            return Err(malformed("entryModules must not be empty"));
        }
        Ok(Self {
            family_name,
            entry_modules,
            compatibility_profile,
        })
    }

    /// Returns the normalized digest payload, sorting only `entryModules`.
    #[must_use]
    pub fn identity_payload(&self) -> SemanticJson {
        let mut entries = self.entry_modules.clone();
        entries.sort();
        object([
            ("familyName", SemanticJson::String(self.family_name.clone())),
            (
                "entryModules",
                SemanticJson::Array(entries.into_iter().map(SemanticJson::String).collect()),
            ),
            (
                "compatibilityProfile",
                SemanticJson::String(self.compatibility_profile.clone()),
            ),
        ])
    }
}

/// Definition-summary module used by the definition role projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionIdentityModule {
    /// Logical module name.
    pub name: String,
    /// Semantic module ordinal.
    pub ordinal: u64,
    /// Ordered import names.
    pub imports: Vec<String>,
    /// Ordered sentence content fingerprints.
    pub sentence_content_fingerprints: Vec<Digest>,
}

/// Exact definition role identity projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionIdentitySummary {
    /// Baseline-family identity.
    pub baseline_family_id: Digest,
    /// Ordered modules.
    pub modules: Vec<DefinitionIdentityModule>,
}

impl DefinitionIdentitySummary {
    /// Returns the frozen definition digest payload.
    #[must_use]
    pub fn identity_payload(&self) -> SemanticJson {
        let modules = self
            .modules
            .iter()
            .map(|module| {
                object([
                    ("name", SemanticJson::String(module.name.clone())),
                    (
                        "ordinal",
                        SemanticJson::Integer(
                            i64::try_from(module.ordinal).expect("v1 ordinal fits i64"),
                        ),
                    ),
                    (
                        "imports",
                        SemanticJson::Array(
                            module
                                .imports
                                .iter()
                                .cloned()
                                .map(SemanticJson::String)
                                .collect(),
                        ),
                    ),
                    (
                        "sentenceContentFingerprints",
                        SemanticJson::Array(
                            module
                                .sentence_content_fingerprints
                                .iter()
                                .map(|value| SemanticJson::String(value.to_string()))
                                .collect(),
                        ),
                    ),
                ])
            })
            .collect();
        object([
            ("schemaVersion", SemanticJson::Integer(1)),
            (
                "representation",
                SemanticJson::String("portable-mutation-semantic-slice-v1".to_owned()),
            ),
            (
                "baselineFamilyId",
                SemanticJson::String(self.baseline_family_id.to_string()),
            ),
            ("modules", SemanticJson::Array(modules)),
        ])
    }
}

/// A compact identity-vector anchor. `checkout_root` is intentionally absent.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LegacySentenceAnchor {
    /// Input sentence anchored in logical source coordinates.
    Input {
        /// Baseline family.
        baseline_family_id: Digest,
        /// Logical module.
        module: String,
        /// Logical source URI.
        source: String,
        /// Source range.
        location: [i64; 4],
        /// Sentence kind.
        kind: String,
        /// Occurrence among otherwise identical anchors.
        source_occurrence_ordinal: i64,
    },
    /// Generated sentence anchor.
    Generated {
        /// Generating transformation.
        transformation_id: Digest,
        /// Sorted unique parents.
        parents: Vec<Digest>,
        /// Destination anchor identity.
        anchor_identity: Digest,
        /// Generated role.
        role: String,
        /// Deterministic ordinal.
        ordinal: i64,
    },
}

/// Derives the baseline-family ID.
pub fn baseline_family_id(family: &BaselineFamily) -> Result<Digest, IdentityError> {
    let mut unique = BTreeSet::new();
    if family.entry_modules.iter().any(|item| !unique.insert(item)) {
        return Err(IdentityError::new(
            IdentityErrorKind::NonCanonicalSet,
            "baseline family repeats an entry module",
        ));
    }
    identity_digest(
        &domain("k-in-k/baseline-family/v1"),
        &family.identity_payload(),
    )
}

/// Derives one source sentence lineage ID.
#[allow(clippy::too_many_arguments)]
pub fn input_lineage_id(
    baseline_family_id: &Digest,
    module: &str,
    source: &str,
    location: &Location,
    kind: SentenceKind,
    source_occurrence_ordinal: u64,
) -> Result<Digest, IdentityError> {
    let payload = object([
        (
            "baselineFamilyId",
            SemanticJson::String(baseline_family_id.to_string()),
        ),
        ("module", SemanticJson::String(module.to_owned())),
        ("source", SemanticJson::String(source.to_owned())),
        ("location", location.to_json()),
        ("kind", SemanticJson::String(kind.as_str().to_owned())),
        (
            "sourceOccurrenceOrdinal",
            SemanticJson::Integer(
                i64::try_from(source_occurrence_ordinal).expect("v1 ordinal fits i64"),
            ),
        ),
    ]);
    identity_digest(&domain("k-in-k/input-lineage/v1"), &payload)
}

/// Derives one generated sentence lineage ID.
pub fn generated_lineage_id(identity: &GeneratedIdentity) -> Result<Digest, IdentityError> {
    identity_digest(&domain("k-in-k/generated-lineage/v1"), &identity.to_json())
}

fn identity_digest(domain: &DigestDomain, value: &SemanticJson) -> Result<Digest, IdentityError> {
    digest(domain, value).map_err(|error| {
        IdentityError::new(
            IdentityErrorKind::MalformedValue,
            format!("identity payload is not valid semantic JSON: {error}"),
        )
    })
}

pub(crate) fn domain(value: &str) -> DigestDomain {
    DigestDomain::new(value).expect("frozen identity domain is valid")
}

pub(crate) fn object<const N: usize>(fields: [(&str, SemanticJson); N]) -> SemanticJson {
    SemanticJson::Object(
        fields
            .into_iter()
            .map(|(name, value)| (name.to_owned(), value))
            .collect(),
    )
}

pub(crate) fn exact_object<'a>(
    value: &'a SemanticJson,
    expected: &[&str],
    context: &str,
) -> Result<&'a BTreeMap<String, SemanticJson>, IdentityError> {
    let fields = value
        .as_object()
        .ok_or_else(|| malformed(format!("{context} must be an object")))?;
    let actual: BTreeSet<&str> = fields.keys().map(String::as_str).collect();
    let expected: BTreeSet<&str> = expected.iter().copied().collect();
    if actual != expected {
        return Err(malformed(format!("{context} has unsupported fields")));
    }
    Ok(fields)
}

pub(crate) fn nonempty_string(
    value: Option<&SemanticJson>,
    field: &str,
) -> Result<String, IdentityError> {
    let value = value
        .and_then(SemanticJson::as_str)
        .ok_or_else(|| malformed(format!("{field} must be a string")))?;
    if value.is_empty() {
        return Err(malformed(format!("{field} must not be empty")));
    }
    Ok(value.to_owned())
}

pub(crate) fn parse_digest(
    value: Option<&SemanticJson>,
    field: &str,
) -> Result<Digest, IdentityError> {
    let value = value
        .and_then(SemanticJson::as_str)
        .ok_or_else(|| malformed(format!("{field} must be a digest")))?;
    Digest::parse(value).map_err(|_| malformed(format!("{field} must be lowercase SHA-256")))
}

pub(crate) fn parse_u64(value: Option<&SemanticJson>, field: &str) -> Result<u64, IdentityError> {
    let value = value
        .and_then(SemanticJson::as_i64)
        .ok_or_else(|| malformed(format!("{field} must be an integer")))?;
    u64::try_from(value).map_err(|_| malformed(format!("{field} must be nonnegative")))
}

pub(crate) fn malformed(detail: impl Into<String>) -> IdentityError {
    IdentityError::new(IdentityErrorKind::MalformedValue, detail)
}
