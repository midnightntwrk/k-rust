use crate::receipt::{domain, validate_campaign_schema};
use kink_portable::{Digest, SemanticJson, digest_without_field, parse_json};
use std::fmt;

/// One occurrence-scoped BAG-16 derivation result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BranchDecision {
    /// At least one validated witness exists.
    Match,
    /// Trustworthy complete finite absence.
    NoMatch,
    /// Bound, solver, pending, or local error made absence indeterminate.
    Unknown,
    /// Shared/global setup failed.
    Error,
}

/// Global execution collection stop.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CollectionStop {
    /// Clean exhaustive stop.
    Exhausted,
    /// Existential search stopped after a validated witness.
    MatchFound,
    /// A declared resource/query/solver bound stopped search.
    Bounded,
    /// Backend/worker/infrastructure stopped the collection.
    Error,
}

/// Portable collection inputs in semantic visit order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BranchCollection {
    /// Occurrence-scoped path decisions in semantic visit order.
    pub visited: Vec<BranchDecision>,
    /// Explicit discovered but unvisited work count.
    pub pending_work: u64,
    /// Exact global stop.
    pub stop: CollectionStop,
    /// Required marker for a clean exhausted zero-visit collection.
    pub empty_search_marker: bool,
}

/// A schema-exact BAG-16 collection with its rederived identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PortableBranchCollection {
    /// Complete validated portable value.
    pub value: SemanticJson,
    /// Rederived collection identity.
    pub collection_id: Digest,
}

impl PortableBranchCollection {
    /// Validates the frozen collection shape, identity, and empty-exhaustion rule.
    pub fn from_json(value: &SemanticJson) -> Result<Self, CollectionFailure> {
        validate_campaign_schema(
            value,
            "https://starstream.dev/k-in-k/backend-agnostic/v1/branch-trace-collection.schema.json",
        )
        .map_err(|detail| {
            CollectionFailure::new(CollectionFailureKind::InvalidPortableCollection, detail)
        })?;
        let fields = value.as_object().expect("collection schema checked");
        let claimed = fields
            .get("collectionId")
            .and_then(SemanticJson::as_str)
            .and_then(|value| Digest::parse(value).ok())
            .ok_or_else(|| {
                CollectionFailure::new(
                    CollectionFailureKind::InvalidPortableCollection,
                    "collectionId is invalid",
                )
            })?;
        let collection_id = digest_without_field(
            &domain("k-in-k/branch-trace-collection/v1"),
            value,
            "collectionId",
        )
        .map_err(|error| {
            CollectionFailure::new(
                CollectionFailureKind::InvalidPortableCollection,
                error.to_string(),
            )
        })?;
        if claimed != collection_id {
            return Err(CollectionFailure::new(
                CollectionFailureKind::CollectionIdentityMismatch,
                "collectionId drift",
            ));
        }
        let catalog = parse_json(include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/fixtures/bag16-artifact-catalog.json"
        ))
        .map_err(|error| {
            CollectionFailure::new(
                CollectionFailureKind::InvalidPortableCollection,
                format!("bundled BAG-16 catalog is invalid: {error}"),
            )
        })?;
        let registered = catalog
            .as_object()
            .and_then(|catalog| catalog.get("entries"))
            .and_then(SemanticJson::as_array)
            .is_some_and(|entries| {
                entries.iter().any(|entry| {
                    let Some(entry) = entry.as_object() else {
                        return false;
                    };
                    entry.get("role").and_then(SemanticJson::as_str)
                        == Some("branch-trace-collection")
                        && entry.get("digest").and_then(SemanticJson::as_str)
                            == Some(collection_id.as_str())
                })
            });
        if !registered {
            return Err(CollectionFailure::new(
                CollectionFailureKind::FiniteAuthorityMismatch,
                "collection is outside the registered BAG-16 finite catalog",
            ));
        }
        let empty =
            matches!(fields.get("visited"), Some(SemanticJson::Array(items)) if items.is_empty());
        let pending_zero = fields
            .get("pendingWork")
            .and_then(SemanticJson::as_object)
            .and_then(|pending| pending.get("discoveredCount"))
            == Some(&SemanticJson::Integer(0));
        let exhausted = fields
            .get("stopReason")
            .and_then(SemanticJson::as_object)
            .and_then(|stop| stop.get("kind"))
            .and_then(SemanticJson::as_str)
            == Some("search-exhausted");
        if empty
            && pending_zero
            && exhausted
            && matches!(fields.get("emptySearchDecision"), Some(SemanticJson::Null))
        {
            return Err(CollectionFailure::new(
                CollectionFailureKind::MissingEmptySearchMarker,
                "clean zero-visit exhaustion requires an empty-search decision",
            ));
        }
        Ok(Self {
            value: value.clone(),
            collection_id,
        })
    }
}

/// Derived corpus/pattern outcome.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CollectionDecision {
    /// A validated match dominates local uncertainty.
    Match,
    /// Clean exhaustive complete absence.
    NoMatch,
    /// Absence is not established.
    Unknown,
    /// Global/shared setup is untrustworthy.
    Error,
}

/// Folds an occurrence collection without inferring exhaustion from emptiness.
pub fn derive_collection_decision(
    collection: &BranchCollection,
) -> Result<CollectionDecision, CollectionFailure> {
    if collection.visited.is_empty()
        && collection.stop == CollectionStop::Exhausted
        && collection.pending_work == 0
        && !collection.empty_search_marker
    {
        return Err(CollectionFailure::new(
            CollectionFailureKind::MissingEmptySearchMarker,
            "clean zero-visit exhaustion requires the explicit empty-search marker",
        ));
    }
    if collection.visited.contains(&BranchDecision::Match) {
        return Ok(CollectionDecision::Match);
    }
    if collection.stop == CollectionStop::Error {
        return Ok(CollectionDecision::Error);
    }
    if collection.pending_work != 0
        || collection.stop != CollectionStop::Exhausted
        || collection
            .visited
            .iter()
            .any(|item| matches!(item, BranchDecision::Unknown | BranchDecision::Error))
    {
        return Ok(CollectionDecision::Unknown);
    }
    Ok(CollectionDecision::NoMatch)
}

/// Closed collection failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CollectionFailureKind {
    /// Zero-visit exhaustion omitted its explicit marker.
    MissingEmptySearchMarker,
    /// The BAG-16 collection does not satisfy its exact schema.
    InvalidPortableCollection,
    /// The collection self-identity drifted.
    CollectionIdentityMismatch,
    /// The collection is outside the bundled deterministic finite authority.
    FiniteAuthorityMismatch,
}

/// Typed collection failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollectionFailure {
    kind: CollectionFailureKind,
    detail: String,
}

impl CollectionFailure {
    fn new(kind: CollectionFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Decision-bearing classification.
    #[must_use]
    pub const fn kind(&self) -> CollectionFailureKind {
        self.kind
    }
}

impl fmt::Display for CollectionFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for CollectionFailure {}
