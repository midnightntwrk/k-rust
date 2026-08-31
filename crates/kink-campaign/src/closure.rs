use crate::ReplayVersionRegistry;
use crate::receipt::{domain, validate_campaign_schema};
use kink_portable::{Digest, SemanticJson, digest_without_field, parse_json};
use std::fmt;

/// Exact finite BAG-16 portable closure root.
///
/// BAG-16 is explicitly a bundled deterministic finite authority. This type
/// validates the complete resolver roots, recursive registry, referenced root
/// keys, and the registered closure identity without promoting any of them to
/// native execution evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PortableClosureRoot {
    /// Complete validated closure value.
    pub value: SemanticJson,
    /// Rederived closure identity.
    pub closure_id: Digest,
}

impl PortableClosureRoot {
    /// Validates one exact registered BAG-16 closure envelope.
    pub fn from_json(value: &SemanticJson) -> Result<Self, ClosureFailure> {
        validate_campaign_schema(
            value,
            "https://starstream.dev/k-in-k/backend-agnostic/v1/portable-closure-root.schema.json",
        )
        .map_err(|detail| ClosureFailure::new(ClosureFailureKind::InvalidShape, detail))?;
        let fields = value.as_object().expect("closure schema checked");
        let claimed = parse_digest_field(fields, "closureId")?;
        let closure_id = digest_without_field(
            &domain("k-in-k/portable-closure-root/v1"),
            value,
            "closureId",
        )
        .map_err(|error| {
            ClosureFailure::new(ClosureFailureKind::InvalidShape, error.to_string())
        })?;
        if claimed != closure_id {
            return Err(ClosureFailure::new(
                ClosureFailureKind::IdentityMismatch,
                "closureId drift",
            ));
        }

        let expected_roles = bundled_json(include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-artifact-role-specs.json"
        ))?;
        let expected_catalog = bundled_json(include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-artifact-catalog.json"
        ))?;
        if fields.get("artifactRoleSpecs") != Some(&expected_roles)
            || fields.get("artifactCatalog") != Some(&expected_catalog)
        {
            return Err(ClosureFailure::new(
                ClosureFailureKind::ResolverAuthorityMismatch,
                "closure does not embed the exact frozen role registry and artifact catalog",
            ));
        }
        let registry = ReplayVersionRegistry::from_json(
            fields.get("registry").expect("closure schema checked"),
        )
        .map_err(|error| {
            ClosureFailure::new(
                ClosureFailureKind::RegistryMismatch,
                format!("recursive registry rejected: {error}"),
            )
        })?;
        let catalog_entries = expected_catalog
            .as_object()
            .and_then(|catalog| catalog.get("entries"))
            .and_then(SemanticJson::as_array)
            .expect("bundled catalog shape is frozen");
        let contains_key = |key: &SemanticJson| {
            let Some(key_fields) = key.as_object() else {
                return false;
            };
            catalog_entries.iter().any(|entry| {
                let Some(entry_fields) = entry.as_object() else {
                    return false;
                };
                entry_fields.get("role") == key_fields.get("role")
                    && entry_fields.get("digest") == key_fields.get("digest")
            })
        };
        if !contains_key(fields.get("receipt").expect("closure schema checked"))
            || !matches!(fields.get("result"), Some(SemanticJson::Null))
                && !contains_key(fields.get("result").expect("closure schema checked"))
            || !fields
                .get("cacheRecords")
                .and_then(SemanticJson::as_array)
                .expect("closure schema checked")
                .iter()
                .all(contains_key)
        {
            return Err(ClosureFailure::new(
                ClosureFailureKind::CatalogClosureMismatch,
                "closure root, receipt, or cache record is absent from the active catalog",
            ));
        }
        let registry_key = SemanticJson::Object(
            [
                (
                    "digest".to_owned(),
                    SemanticJson::String(registry.registry_id.to_string()),
                ),
                (
                    "role".to_owned(),
                    SemanticJson::String("replay-version-registry".to_owned()),
                ),
            ]
            .into_iter()
            .collect(),
        );
        if !contains_key(&registry_key) {
            return Err(ClosureFailure::new(
                ClosureFailureKind::RegistryMismatch,
                "recursive registry is absent from the active catalog",
            ));
        }
        let vectors = bundled_json(include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/vectors/bag16-branch-collection-vectors.json"
        ))?;
        let registered = vectors
            .as_object()
            .and_then(|root| root.get("roots"))
            .and_then(SemanticJson::as_object)
            .is_some_and(|roots| {
                roots
                    .values()
                    .any(|item| item.as_str() == Some(closure_id.as_str()))
            });
        if !registered {
            return Err(ClosureFailure::new(
                ClosureFailureKind::FiniteAuthorityMismatch,
                "closure is not one of the exact registered BAG-16 finite roots",
            ));
        }
        Ok(Self {
            value: value.clone(),
            closure_id,
        })
    }
}

fn bundled_json(bytes: &[u8]) -> Result<SemanticJson, ClosureFailure> {
    parse_json(bytes).map_err(|error| {
        ClosureFailure::new(
            ClosureFailureKind::InvalidShape,
            format!("bundled closure authority is invalid: {error}"),
        )
    })
}

fn parse_digest_field(
    fields: &std::collections::BTreeMap<String, SemanticJson>,
    name: &str,
) -> Result<Digest, ClosureFailure> {
    fields
        .get(name)
        .and_then(SemanticJson::as_str)
        .and_then(|value| Digest::parse(value).ok())
        .ok_or_else(|| {
            ClosureFailure::new(
                ClosureFailureKind::InvalidShape,
                format!("{name} is not lowercase SHA-256"),
            )
        })
}

/// Closed portable closure failures.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClosureFailureKind {
    /// Schema or restricted-JSON validation failed.
    InvalidShape,
    /// The closure self-ID drifted.
    IdentityMismatch,
    /// Resolver registry or catalog differs from the frozen authority.
    ResolverAuthorityMismatch,
    /// A referenced artifact is outside the active catalog.
    CatalogClosureMismatch,
    /// Recursive registry validation or catalog binding failed.
    RegistryMismatch,
    /// The root is outside the registered deterministic finite set.
    FiniteAuthorityMismatch,
}

/// Typed closure failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClosureFailure {
    kind: ClosureFailureKind,
    detail: String,
}

impl ClosureFailure {
    fn new(kind: ClosureFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Decision-bearing failure classification.
    #[must_use]
    pub const fn kind(&self) -> ClosureFailureKind {
        self.kind
    }
}

impl fmt::Display for ClosureFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for ClosureFailure {}
