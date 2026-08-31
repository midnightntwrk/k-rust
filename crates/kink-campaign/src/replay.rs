use crate::receipt::{domain, validate_campaign_schema};
use kink_portable::{
    Digest, SemanticJson, canonical_json, digest, digest_without_field, parse_json,
};
use std::fmt;

/// A replay record whose cycle-free invocation and completed self-ID have been rederived.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReplayManifest {
    /// Complete portable replay value.
    pub value: SemanticJson,
    /// Request identity excluding result/output expectations.
    pub invocation_digest: Digest,
    /// Completed replay identity including result/output expectations.
    pub replay_id: Digest,
}

impl ReplayManifest {
    /// Validates replay step pairing and rederives both identities in DAG order.
    pub fn from_json(value: &SemanticJson) -> Result<Self, ReplayFailure> {
        validate_campaign_schema(
            value,
            "https://starstream.dev/k-in-k/backend-agnostic/v1/replay-manifest.schema.json",
        )
        .map_err(|detail| ReplayFailure::new(ReplayFailureKind::InvalidShape, detail))?;
        let SemanticJson::Object(fields) = value else {
            return Err(ReplayFailure::new(
                ReplayFailureKind::InvalidShape,
                "replay manifest must be an object",
            ));
        };
        let expected_invocation = digest_field(fields, "invocationDigest")?;
        let expected_replay = digest_field(fields, "replayId")?;
        if !fields.contains_key("expectedResultDigest") {
            return Err(ReplayFailure::new(
                ReplayFailureKind::InvalidShape,
                "completed replay must contain expectedResultDigest",
            ));
        }
        let Some(SemanticJson::Array(steps)) = fields.get("steps") else {
            return Err(ReplayFailure::new(
                ReplayFailureKind::InvalidStep,
                "replay steps must be an array",
            ));
        };
        for step in steps {
            let Some(step_fields) = step.as_object() else {
                return Err(ReplayFailure::new(
                    ReplayFailureKind::InvalidStep,
                    "every replay step must be an object",
                ));
            };
            if !matches!(
                step_fields.get("inputArtifacts"),
                Some(SemanticJson::Array(_))
            ) || !matches!(
                step_fields.get("expectedArtifacts"),
                Some(SemanticJson::Array(_))
            ) {
                return Err(ReplayFailure::new(
                    ReplayFailureKind::UnpairedStepEdges,
                    "every replay step needs inputArtifacts and expectedArtifacts arrays",
                ));
            }
        }
        let mut invocation_projection = fields.clone();
        invocation_projection.remove("replayId");
        invocation_projection.remove("invocationDigest");
        invocation_projection.remove("expectedResultDigest");
        let Some(SemanticJson::Array(projected_steps)) = invocation_projection.get_mut("steps")
        else {
            return Err(ReplayFailure::new(
                ReplayFailureKind::InvalidStep,
                "replay steps disappeared during projection",
            ));
        };
        for step in projected_steps {
            let Some(step_fields) = mutable_object(step) else {
                return Err(ReplayFailure::new(
                    ReplayFailureKind::InvalidStep,
                    "every replay step must be an object",
                ));
            };
            step_fields.remove("expectedArtifacts");
        }
        let invocation_digest = digest(
            &domain("k-in-k/replay-invocation/v1"),
            &SemanticJson::Object(invocation_projection),
        )
        .map_err(|error| {
            ReplayFailure::new(
                ReplayFailureKind::InvalidShape,
                format!("replay invocation is not valid semantic JSON: {error}"),
            )
        })?;
        if invocation_digest != expected_invocation {
            return Err(ReplayFailure::new(
                ReplayFailureKind::InvocationDigestMismatch,
                "invocationDigest does not match the cycle-free projection",
            ));
        }
        let replay_id =
            digest_without_field(&domain("k-in-k/replay-manifest/v1"), value, "replayId").map_err(
                |_| {
                    ReplayFailure::new(
                        ReplayFailureKind::InvalidShape,
                        "replayId projection is unavailable",
                    )
                },
            )?;
        if replay_id != expected_replay {
            return Err(ReplayFailure::new(
                ReplayFailureKind::ReplayDigestMismatch,
                "replayId does not match the completed replay record",
            ));
        }
        if !registered_artifact("replay-manifest", &replay_id, replay_catalogs())? {
            return Err(ReplayFailure::new(
                ReplayFailureKind::FiniteAuthorityMismatch,
                "replay is outside the registered frozen finite catalogs",
            ));
        }
        Ok(Self {
            value: value.clone(),
            invocation_digest,
            replay_id,
        })
    }
}

/// Exact recursive schema/operation registry used by report publication.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReplayVersionRegistry {
    /// Complete validated registry.
    pub value: SemanticJson,
    /// Rederived registry identity.
    pub registry_id: Digest,
}

impl ReplayVersionRegistry {
    /// Validates either frozen v1 or BAG-16 v2 dispatch and its self-ID.
    pub fn from_json(value: &SemanticJson) -> Result<Self, ReplayFailure> {
        let version = value
            .as_object()
            .and_then(|fields| fields.get("schemaVersion"));
        let (reference, domain_name) = match version {
            Some(SemanticJson::Integer(1)) => (
                "https://starstream.dev/k-in-k/backend-agnostic/v1/replay-version-registry.schema.json",
                "k-in-k/replay-version-registry/v1",
            ),
            Some(SemanticJson::Integer(2)) => (
                "https://starstream.dev/k-in-k/backend-agnostic/v2/replay-version-registry-v2.schema.json",
                "k-in-k/replay-version-registry/v2",
            ),
            _ => {
                return Err(ReplayFailure::new(
                    ReplayFailureKind::InvalidRegistry,
                    "unsupported replay registry version",
                ));
            }
        };
        validate_campaign_schema(value, reference)
            .map_err(|detail| ReplayFailure::new(ReplayFailureKind::InvalidRegistry, detail))?;
        let fields = value.as_object().expect("registry schema checked");
        let claimed = digest_field(fields, "registryId")?;
        let registry_id =
            digest_without_field(&domain(domain_name), value, "registryId").map_err(|error| {
                ReplayFailure::new(ReplayFailureKind::InvalidRegistry, error.to_string())
            })?;
        if claimed != registry_id {
            return Err(ReplayFailure::new(
                ReplayFailureKind::RegistryDigestMismatch,
                "registryId drift",
            ));
        }
        let registered = match version {
            Some(SemanticJson::Integer(1)) => {
                registry_id.as_str()
                    == "4445cd71e7e61d755a67cfa7cca13f2c1ec00504f76dcf32eb64e6e88a26cbf7"
            }
            Some(SemanticJson::Integer(2)) => registered_registry_subset(value)?,
            _ => false,
        };
        if !registered {
            return Err(ReplayFailure::new(
                ReplayFailureKind::FiniteAuthorityMismatch,
                "registry is outside the exact frozen recursive registry set",
            ));
        }
        for (name, key_name) in [("schemas", "schemaId"), ("operations", "operationKind")] {
            let items = match fields.get(name) {
                Some(SemanticJson::Array(items)) => items,
                _ => unreachable!("registry schema checked"),
            };
            let mut previous: Option<String> = None;
            for item in items {
                let item_fields = item.as_object().expect("registry schema checked");
                let primary = item_fields
                    .get(key_name)
                    .and_then(SemanticJson::as_str)
                    .expect("registry schema checked");
                let canonical = format!(
                    "{primary}\0{}",
                    canonical_json(item).map_err(|error| ReplayFailure::new(
                        ReplayFailureKind::InvalidRegistry,
                        error.to_string()
                    ))?
                );
                if previous.as_ref().is_some_and(|value| value >= &canonical) {
                    return Err(ReplayFailure::new(
                        ReplayFailureKind::InvalidRegistryOrder,
                        "registry arrays must be strictly sorted and duplicate-free",
                    ));
                }
                previous = Some(canonical);
            }
        }
        Ok(Self {
            value: value.clone(),
            registry_id,
        })
    }
}

fn replay_catalogs() -> &'static [&'static [u8]] {
    &[
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/artifact-catalog.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/execution-artifact-catalog.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag15-replay-artifact-catalog.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-artifact-catalog.json"
        ),
    ]
}

fn registered_registry_subset(value: &SemanticJson) -> Result<bool, ReplayFailure> {
    const REGISTRIES: &[&[u8]] = &[
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-bounded.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-corpus-failures.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-corpus-stop.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-corpus-two-execution.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-empty.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-existential.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-failed-execution-root.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-oracle-concrete.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-oracle-pattern-false-coverage.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-oracle-pattern.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-oracle-predicate.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-oracle-reachability.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry-pattern-root.json"
        ),
        include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-replay-version-registry.json"
        ),
    ];
    for bytes in REGISTRIES {
        let registered = parse_json(bytes).map_err(|error| {
            ReplayFailure::new(
                ReplayFailureKind::InvalidRegistry,
                format!("bundled recursive registry is invalid: {error}"),
            )
        })?;
        if &registered == value {
            return Ok(true);
        }
    }
    Ok(false)
}

fn registered_artifact(
    role: &str,
    digest: &Digest,
    catalogs: &[&[u8]],
) -> Result<bool, ReplayFailure> {
    for bytes in catalogs {
        let catalog = parse_json(bytes).map_err(|error| {
            ReplayFailure::new(
                ReplayFailureKind::InvalidRegistry,
                format!("bundled artifact catalog is invalid: {error}"),
            )
        })?;
        let Some(entries) = catalog
            .as_object()
            .and_then(|fields| fields.get("entries"))
            .and_then(SemanticJson::as_array)
        else {
            return Err(ReplayFailure::new(
                ReplayFailureKind::InvalidRegistry,
                "bundled artifact catalog has no entries",
            ));
        };
        if entries.iter().any(|entry| {
            let Some(entry) = entry.as_object() else {
                return false;
            };
            entry.get("role").and_then(SemanticJson::as_str) == Some(role)
                && entry.get("digest").and_then(SemanticJson::as_str) == Some(digest.as_str())
        }) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn mutable_object(
    value: &mut SemanticJson,
) -> Option<&mut std::collections::BTreeMap<String, SemanticJson>> {
    match value {
        SemanticJson::Object(fields) => Some(fields),
        _ => None,
    }
}

fn digest_field(
    fields: &std::collections::BTreeMap<String, SemanticJson>,
    name: &str,
) -> Result<Digest, ReplayFailure> {
    fields
        .get(name)
        .and_then(SemanticJson::as_str)
        .ok_or_else(|| {
            ReplayFailure::new(
                ReplayFailureKind::InvalidShape,
                format!("{name} must be a digest string"),
            )
        })
        .and_then(|value| {
            Digest::parse(value).map_err(|_| {
                ReplayFailure::new(
                    ReplayFailureKind::InvalidShape,
                    format!("{name} is not lowercase SHA-256"),
                )
            })
        })
}

/// Closed replay failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReplayFailureKind {
    /// Replay root or identity field shape is invalid.
    InvalidShape,
    /// A replay step is malformed.
    InvalidStep,
    /// Step input/expected edges are not both explicit.
    UnpairedStepEdges,
    /// The cycle-free invocation identity drifted.
    InvocationDigestMismatch,
    /// The completed replay identity drifted.
    ReplayDigestMismatch,
    /// Recursive registry shape/version is invalid.
    InvalidRegistry,
    /// Recursive registry identity drifted.
    RegistryDigestMismatch,
    /// Registry entries are reordered or duplicated.
    InvalidRegistryOrder,
    /// The replay or registry is outside the bundled finite authority.
    FiniteAuthorityMismatch,
}

/// Typed replay failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReplayFailure {
    kind: ReplayFailureKind,
    detail: String,
}

impl ReplayFailure {
    fn new(kind: ReplayFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Decision-bearing classification.
    #[must_use]
    pub const fn kind(&self) -> ReplayFailureKind {
        self.kind
    }
}

impl fmt::Display for ReplayFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for ReplayFailure {}
