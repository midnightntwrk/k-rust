//! Backend-neutral portable values, identities, and artifact ingress.
//!
//! This crate deliberately implements only the frozen portable v1 surface.
//! Native K forms must enter through a future coverage-checked adapter.

mod artifact;
mod definition;
mod durable_artifact;
mod identity;
mod json;

pub use artifact::{
    ArtifactCatalogEntry, ArtifactStore, InMemoryArtifactStore, IngressedArtifact,
    RepositoryResolver, RoleSpecRegistry, ingest_artifact,
};
pub use definition::{
    Attribute, GeneratedIdentity, GeneratedRole, Location, Module, PortableDefinition, Provenance,
    Sentence, SentenceKind, SentenceValue, Term, TermNode,
};
pub use durable_artifact::{
    DurableArtifactAuthority, DurableArtifactConflictState, DurableArtifactFailpoint,
    DurableArtifactFailure, DurableArtifactFailureKind, DurableArtifactInput,
    DurableArtifactPublication, DurableArtifactStore, DurableProcessLock,
    PreparedArtifactTransaction,
};
pub use identity::{
    BaselineFamily, DefinitionIdentitySummary, IdentityError, IdentityErrorKind,
    LegacySentenceAnchor, baseline_family_id, generated_lineage_id, input_lineage_id,
};
pub use json::{
    Digest, DigestDomain, JsonFailure, JsonFailureKind, SemanticJson, canonical_json,
    canonical_json_bytes, digest, digest_without_field, parse_json, sha256_bytes,
};
