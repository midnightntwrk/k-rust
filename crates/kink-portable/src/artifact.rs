use crate::definition::PortableDefinition;
use crate::identity::{IdentityErrorKind, domain, exact_object, nonempty_string};
use crate::json::{
    Digest, DigestDomain, SemanticJson, canonical_json_bytes, digest, parse_json, sha256_bytes,
};
use kink_contracts::{
    ArtifactAvailability, ArtifactFailure, ArtifactFailureKind, ArtifactLocator, ContentModel,
    MediaType, ResolverId,
};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug, Eq, PartialEq)]
enum Projection {
    Complete,
    WithoutField,
    DefinitionSummary,
    SelectFields(Vec<String>),
    Field(String),
    OpaqueEnvelope,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RoleSpec {
    content_model: ContentModel,
    media_type: MediaType,
    digest_domain: DigestDomain,
    projection: Projection,
    self_id_field: Option<String>,
    schema: Option<String>,
}

/// Closed role registry loaded from the frozen `artifact-role-specs.json`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleSpecRegistry {
    specs: BTreeMap<String, RoleSpec>,
    schemas: BTreeMap<String, (String, serde_json::Value)>,
}

impl RoleSpecRegistry {
    /// Parses the strict frozen role registry.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ArtifactFailure> {
        let value = parse_json(bytes).map_err(|error| {
            ArtifactFailure::new(ArtifactFailureKind::MalformedJson, error.to_string())
        })?;
        let fields = exact_object(&value, &["schemaVersion", "specs"], "role registry")
            .map_err(identity_artifact_failure)?;
        if fields.get("schemaVersion").and_then(SemanticJson::as_i64) != Some(1) {
            return Err(ArtifactFailure::new(
                ArtifactFailureKind::UnsupportedForm,
                "unsupported role-registry schemaVersion",
            ));
        }
        let rows = fields
            .get("specs")
            .and_then(SemanticJson::as_array)
            .ok_or_else(|| {
                ArtifactFailure::new(
                    ArtifactFailureKind::MalformedJson,
                    "role registry specs must be an array",
                )
            })?;
        let mut specs = BTreeMap::new();
        for row in rows {
            let row_fields = row.as_object().ok_or_else(|| {
                ArtifactFailure::new(
                    ArtifactFailureKind::MalformedJson,
                    "role spec must be an object",
                )
            })?;
            let allowed = [
                "role",
                "contentModel",
                "mediaType",
                "schema",
                "digestDomain",
                "projection",
                "selfIdField",
            ];
            if row_fields.len() != allowed.len()
                || allowed.iter().any(|field| !row_fields.contains_key(*field))
            {
                return Err(ArtifactFailure::new(
                    ArtifactFailureKind::MalformedJson,
                    "role spec has unsupported fields",
                ));
            }
            let role = required_string(row_fields.get("role"), "role")?;
            let content_model = ContentModel::parse(&required_string(
                row_fields.get("contentModel"),
                "contentModel",
            )?)?;
            let media_type =
                MediaType::parse(&required_string(row_fields.get("mediaType"), "mediaType")?)?;
            match (content_model, media_type) {
                (ContentModel::CanonicalJson, MediaType::ApplicationJson)
                | (ContentModel::OpaqueBytes, MediaType::ApplicationOctetStream) => {}
                _ => {
                    return Err(ArtifactFailure::new(
                        ArtifactFailureKind::MediaTypeMismatch,
                        format!("role {role} has an invalid content/media pairing"),
                    ));
                }
            }
            let digest_domain = DigestDomain::new(required_string(
                row_fields.get("digestDomain"),
                "digestDomain",
            )?)
            .map_err(|error| {
                ArtifactFailure::new(ArtifactFailureKind::MalformedJson, error.to_string())
            })?;
            let projection = parse_projection(
                row_fields
                    .get("projection")
                    .ok_or_else(|| malformed_artifact("role spec lacks projection"))?,
            )?;
            let self_id_field = match row_fields.get("selfIdField") {
                Some(SemanticJson::Null) => None,
                Some(SemanticJson::String(value)) if !value.is_empty() => Some(value.clone()),
                _ => return Err(malformed_artifact("selfIdField must be string or null")),
            };
            let schema = match row_fields.get("schema") {
                Some(SemanticJson::Null) => None,
                Some(SemanticJson::String(value)) if !value.is_empty() => Some(value.clone()),
                _ => return Err(malformed_artifact("schema must be string or null")),
            };
            if matches!(content_model, ContentModel::CanonicalJson) != schema.is_some() {
                return Err(malformed_artifact(
                    "role schema presence disagrees with its content model",
                ));
            }
            if specs
                .insert(
                    role.clone(),
                    RoleSpec {
                        content_model,
                        media_type,
                        digest_domain,
                        projection,
                        self_id_field,
                        schema,
                    },
                )
                .is_some()
            {
                return Err(ArtifactFailure::new(
                    ArtifactFailureKind::Conflict,
                    format!("role registry repeats {role}"),
                ));
            }
        }
        if specs.is_empty() {
            return Err(malformed_artifact("role registry is empty"));
        }
        Ok(Self {
            specs,
            schemas: BTreeMap::new(),
        })
    }

    /// Loads the registry from the frozen package below a repository root.
    pub fn from_repository_root(root: &Path) -> Result<Self, ArtifactFailure> {
        let path =
            root.join("investigations/backend-agnostic-goal-closure/artifact-role-specs.json");
        let bytes = fs::read(&path).map_err(|error| {
            ArtifactFailure::new(
                if error.kind() == std::io::ErrorKind::NotFound {
                    ArtifactFailureKind::MissingArtifact
                } else {
                    ArtifactFailureKind::Io
                },
                format!("{}: {error}", path.display()),
            )
        })?;
        let mut registry = Self::from_bytes(&bytes)?;
        let schema_root = root.join("investigations/backend-agnostic-goal-closure/schemas");
        for entry in fs::read_dir(&schema_root)
            .map_err(|error| ArtifactFailure::new(ArtifactFailureKind::Io, error.to_string()))?
        {
            let entry = entry.map_err(|error| {
                ArtifactFailure::new(ArtifactFailureKind::Io, error.to_string())
            })?;
            let path = entry.path();
            if path.extension().and_then(|value| value.to_str()) != Some("json") {
                continue;
            }
            let schema: serde_json::Value =
                serde_json::from_slice(&fs::read(&path).map_err(|error| {
                    ArtifactFailure::new(ArtifactFailureKind::Io, error.to_string())
                })?)
                .map_err(|error| malformed_artifact(error.to_string()))?;
            let id = schema
                .get("$id")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| malformed_artifact(format!("{} lacks $id", path.display())))?
                .to_owned();
            let name = path
                .file_name()
                .and_then(|value| value.to_str())
                .ok_or_else(|| malformed_artifact("schema filename is not UTF-8"))?
                .to_owned();
            registry.schemas.insert(name, (id, schema));
        }
        Ok(registry)
    }

    /// Reports whether a role exists in the frozen registry.
    #[must_use]
    pub fn contains(&self, role: &str) -> bool {
        self.specs.contains_key(role)
    }
}

/// One concrete catalog entry after closed metadata validation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactCatalogEntry {
    /// Frozen role name.
    pub role: String,
    /// Role-typed semantic identity.
    pub digest: Digest,
    /// Content model declared by the catalog.
    pub content_model: ContentModel,
    /// Media type declared by the catalog.
    pub media_type: MediaType,
    /// SHA-256 over exact returned bytes.
    pub content_sha256: Digest,
    /// Validated normalized locator.
    pub locator: ArtifactLocator,
}

impl ArtifactCatalogEntry {
    /// Parses one exact v1 concrete catalog entry.
    pub fn from_json(value: &SemanticJson) -> Result<Self, ArtifactFailure> {
        let fields = value
            .as_object()
            .ok_or_else(|| malformed_artifact("catalog entry must be an object"))?;
        let expected = [
            "role",
            "digest",
            "contentModel",
            "mediaType",
            "contentSha256",
            "availability",
            "logicalPath",
            "resolverId",
        ];
        if fields.len() != expected.len()
            || expected.iter().any(|field| !fields.contains_key(*field))
        {
            return Err(malformed_artifact("catalog entry has unsupported fields"));
        }
        let availability =
            match required_string(fields.get("availability"), "availability")?.as_str() {
                "bundled" => ArtifactAvailability::Bundled,
                "external-required" => ArtifactAvailability::ExternalRequired,
                other => {
                    return Err(ArtifactFailure::new(
                        ArtifactFailureKind::UnsupportedForm,
                        format!("unsupported availability {other}"),
                    ));
                }
            };
        let resolver = match required_string(fields.get("resolverId"), "resolverId")?.as_str() {
            "repo-v1" => ResolverId::RepoV1,
            "rust-artifact-store-v1" => ResolverId::RustArtifactStoreV1,
            other => {
                return Err(ArtifactFailure::new(
                    ArtifactFailureKind::UnsupportedForm,
                    format!("unsupported resolver {other}"),
                ));
            }
        };
        let logical_path = required_string(fields.get("logicalPath"), "logicalPath")?;
        Ok(Self {
            role: required_string(fields.get("role"), "role")?,
            digest: parse_artifact_digest(fields.get("digest"), "digest")?,
            content_model: ContentModel::parse(&required_string(
                fields.get("contentModel"),
                "contentModel",
            )?)?,
            media_type: MediaType::parse(&required_string(fields.get("mediaType"), "mediaType")?)?,
            content_sha256: parse_artifact_digest(fields.get("contentSha256"), "contentSha256")?,
            locator: ArtifactLocator::parse(&logical_path, resolver, availability)?,
        })
    }
}

/// A successfully verified artifact. Construction is all-or-none.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IngressedArtifact {
    /// Exact catalog metadata used for verification.
    pub entry: ArtifactCatalogEntry,
    /// Exact bytes returned by the locator.
    pub bytes: Vec<u8>,
    /// Restricted JSON value for canonical-JSON roles.
    pub semantic_json: Option<SemanticJson>,
}

/// Verifies bytes against catalog metadata and the frozen role registry.
pub fn ingest_artifact(
    registry: &RoleSpecRegistry,
    entry: &ArtifactCatalogEntry,
    bytes: Vec<u8>,
) -> Result<IngressedArtifact, ArtifactFailure> {
    if sha256_bytes(&bytes) != entry.content_sha256 {
        return Err(ArtifactFailure::new(
            ArtifactFailureKind::ContentHashMismatch,
            "returned bytes differ from contentSha256",
        ));
    }
    let spec = registry.specs.get(&entry.role).ok_or_else(|| {
        ArtifactFailure::new(
            ArtifactFailureKind::UnknownRole,
            format!("unknown artifact role {}", entry.role),
        )
    })?;
    if spec.content_model != entry.content_model {
        return Err(ArtifactFailure::new(
            ArtifactFailureKind::ContentModelMismatch,
            "catalog and role-registry content models disagree",
        ));
    }
    if spec.media_type != entry.media_type {
        return Err(ArtifactFailure::new(
            ArtifactFailureKind::MediaTypeMismatch,
            "catalog and role-registry media types disagree",
        ));
    }
    let semantic_json = match spec.content_model {
        ContentModel::CanonicalJson => {
            let value = parse_json(&bytes).map_err(|error| {
                ArtifactFailure::new(ArtifactFailureKind::MalformedJson, error.to_string())
            })?;
            let canonical = canonical_json_bytes(&value).map_err(|error| {
                ArtifactFailure::new(ArtifactFailureKind::MalformedJson, error.to_string())
            })?;
            if canonical != bytes {
                return Err(ArtifactFailure::new(
                    ArtifactFailureKind::NonCanonicalBytes,
                    "JSON bytes are decodable but not exactly canonical",
                ));
            }
            validate_schema(registry, spec, &value)?;
            let projection = project(&value, spec)?;
            let derived = digest(&spec.digest_domain, &projection).map_err(|error| {
                ArtifactFailure::new(
                    ArtifactFailureKind::SemanticDigestMismatch,
                    error.to_string(),
                )
            })?;
            if derived != entry.digest {
                return Err(ArtifactFailure::new(
                    ArtifactFailureKind::SemanticDigestMismatch,
                    "role-specific semantic digest mismatch",
                ));
            }
            if let Some(field) = &spec.self_id_field {
                let embedded = value
                    .as_object()
                    .and_then(|fields| fields.get(field))
                    .and_then(SemanticJson::as_str)
                    .ok_or_else(|| {
                        ArtifactFailure::new(
                            ArtifactFailureKind::SemanticDigestMismatch,
                            format!("missing embedded self-ID {field}"),
                        )
                    })?;
                if embedded != entry.digest.as_str() {
                    return Err(ArtifactFailure::new(
                        ArtifactFailureKind::SemanticDigestMismatch,
                        format!("embedded self-ID {field} disagrees with catalog"),
                    ));
                }
            }
            Some(value)
        }
        ContentModel::OpaqueBytes => {
            let envelope = crate::identity::object([
                ("role", SemanticJson::String(entry.role.clone())),
                (
                    "mediaType",
                    SemanticJson::String(entry.media_type.as_str().to_owned()),
                ),
                (
                    "contentSha256",
                    SemanticJson::String(entry.content_sha256.to_string()),
                ),
            ]);
            if digest(&domain("k-in-k/opaque-artifact/v1"), &envelope).map_err(|error| {
                ArtifactFailure::new(
                    ArtifactFailureKind::SemanticDigestMismatch,
                    error.to_string(),
                )
            })? != entry.digest
            {
                return Err(ArtifactFailure::new(
                    ArtifactFailureKind::SemanticDigestMismatch,
                    "opaque artifact envelope digest mismatch",
                ));
            }
            None
        }
    };
    Ok(IngressedArtifact {
        entry: entry.clone(),
        bytes,
        semantic_json,
    })
}

fn project(value: &SemanticJson, spec: &RoleSpec) -> Result<SemanticJson, ArtifactFailure> {
    let fields = value.as_object().ok_or_else(|| {
        ArtifactFailure::new(
            ArtifactFailureKind::SemanticDigestMismatch,
            "canonical artifact root must be an object",
        )
    })?;
    match &spec.projection {
        Projection::Complete => Ok(value.clone()),
        Projection::WithoutField => {
            let field = spec
                .self_id_field
                .as_ref()
                .ok_or_else(|| malformed_artifact("without-field projection lacks selfIdField"))?;
            if !fields.contains_key(field) {
                return Err(ArtifactFailure::new(
                    ArtifactFailureKind::SemanticDigestMismatch,
                    format!("projection field {field} is absent"),
                ));
            }
            let mut result = fields.clone();
            result.remove(field);
            Ok(SemanticJson::Object(result))
        }
        Projection::SelectFields(names) => {
            let mut result = BTreeMap::new();
            for name in names {
                result.insert(
                    name.clone(),
                    fields.get(name).cloned().ok_or_else(|| {
                        ArtifactFailure::new(
                            ArtifactFailureKind::SemanticDigestMismatch,
                            format!("projection field {name} is absent"),
                        )
                    })?,
                );
            }
            Ok(SemanticJson::Object(result))
        }
        Projection::Field(name) => fields.get(name).cloned().ok_or_else(|| {
            ArtifactFailure::new(
                ArtifactFailureKind::SemanticDigestMismatch,
                format!("projection field {name} is absent"),
            )
        }),
        Projection::DefinitionSummary => definition_summary_projection(value),
        Projection::OpaqueEnvelope => Err(malformed_artifact(
            "opaque projection cannot be applied to canonical JSON",
        )),
    }
}

fn definition_summary_projection(value: &SemanticJson) -> Result<SemanticJson, ArtifactFailure> {
    PortableDefinition::from_json(value)
        .map(|definition| definition.identity_summary().identity_payload())
        .map_err(|error| {
            let kind = match error.kind() {
                IdentityErrorKind::MalformedValue => ArtifactFailureKind::MalformedJson,
                IdentityErrorKind::UnsupportedForm => ArtifactFailureKind::UnsupportedForm,
                IdentityErrorKind::NonCanonicalSet
                | IdentityErrorKind::DigestMismatch
                | IdentityErrorKind::IllFormed => ArtifactFailureKind::SemanticDigestMismatch,
            };
            ArtifactFailure::new(kind, format!("portable definition rejected: {error}"))
        })
}

fn validate_schema(
    registry: &RoleSpecRegistry,
    spec: &RoleSpec,
    value: &SemanticJson,
) -> Result<(), ArtifactFailure> {
    let reference = spec.schema.as_ref().ok_or_else(|| {
        ArtifactFailure::new(
            ArtifactFailureKind::UnsupportedForm,
            "canonical role lacks a registered schema",
        )
    })?;
    if registry.schemas.is_empty() {
        return Err(ArtifactFailure::new(
            ArtifactFailureKind::UnsupportedForm,
            "schema-backed ingress requires a repository-loaded registry",
        ));
    }
    let (filename, fragment) = reference
        .split_once('#')
        .map_or((reference.as_str(), ""), |(file, fragment)| {
            (file, fragment)
        });
    let (schema_id, _) = registry.schemas.get(filename).ok_or_else(|| {
        ArtifactFailure::new(
            ArtifactFailureKind::UnsupportedForm,
            format!("role schema {filename} is unavailable"),
        )
    })?;
    let schema_reference = if fragment.is_empty() {
        schema_id.clone()
    } else {
        format!("{schema_id}#{fragment}")
    };
    let mut options = jsonschema::options().with_draft(jsonschema::Draft::Draft202012);
    for (id, schema) in registry.schemas.values() {
        let resource = jsonschema::Resource::from_contents(schema.clone()).map_err(|error| {
            malformed_artifact(format!("invalid schema resource {id}: {error}"))
        })?;
        options = options.with_resource(id.clone(), resource);
    }
    let root = serde_json::json!({"$ref": schema_reference});
    let validator = options
        .build(&root)
        .map_err(|error| malformed_artifact(format!("role schema could not compile: {error}")))?;
    let instance = value.to_serde_value().map_err(|error| {
        ArtifactFailure::new(ArtifactFailureKind::MalformedJson, error.to_string())
    })?;
    if let Err(error) = validator.validate(&instance) {
        return Err(ArtifactFailure::new(
            ArtifactFailureKind::MalformedJson,
            format!("role schema rejected artifact: {error}"),
        ));
    }
    Ok(())
}

fn parse_projection(value: &SemanticJson) -> Result<Projection, ArtifactFailure> {
    let fields = value
        .as_object()
        .ok_or_else(|| malformed_artifact("projection must be an object"))?;
    let kind = required_string(fields.get("kind"), "projection kind")?;
    match kind.as_str() {
        "complete" if fields.len() == 1 => Ok(Projection::Complete),
        "without-field" if fields.len() == 1 => Ok(Projection::WithoutField),
        "definition-summary" if fields.len() == 1 => Ok(Projection::DefinitionSummary),
        "opaque-envelope" if fields.len() == 1 => Ok(Projection::OpaqueEnvelope),
        "field" if fields.len() == 2 => Ok(Projection::Field(required_string(
            fields.get("field"),
            "projection field",
        )?)),
        "select-fields" if fields.len() == 2 => {
            let values = fields
                .get("fields")
                .and_then(SemanticJson::as_array)
                .ok_or_else(|| malformed_artifact("projection fields must be an array"))?;
            let names = values
                .iter()
                .map(|value| required_string(Some(value), "projection field"))
                .collect::<Result<_, _>>()?;
            Ok(Projection::SelectFields(names))
        }
        _ => Err(ArtifactFailure::new(
            ArtifactFailureKind::UnsupportedForm,
            format!("unsupported role projection {kind}"),
        )),
    }
}

/// Repository resolver enforcing real-root containment and regular files.
#[derive(Clone, Debug)]
pub struct RepositoryResolver {
    real_root: PathBuf,
}

impl RepositoryResolver {
    /// Canonicalizes the reviewed repository root once.
    pub fn new(root: &Path) -> Result<Self, ArtifactFailure> {
        let real_root = fs::canonicalize(root)
            .map_err(|error| ArtifactFailure::new(ArtifactFailureKind::Io, error.to_string()))?;
        if !real_root.is_dir() {
            return Err(ArtifactFailure::new(
                ArtifactFailureKind::NotRegularFile,
                "repository root is not a directory",
            ));
        }
        Ok(Self { real_root })
    }

    /// Fetches one validated `repo://` locator.
    pub fn fetch(&self, locator: &ArtifactLocator) -> Result<Vec<u8>, ArtifactFailure> {
        if !locator.is_repo() {
            return Err(ArtifactFailure::new(
                ArtifactFailureKind::ResolverMismatch,
                "repo-v1 cannot dereference artifact://",
            ));
        }
        let lexical = self.real_root.join(locator.tail());
        let resolved = fs::canonicalize(&lexical).map_err(|error| {
            ArtifactFailure::new(
                if error.kind() == std::io::ErrorKind::NotFound {
                    ArtifactFailureKind::MissingArtifact
                } else {
                    ArtifactFailureKind::Io
                },
                error.to_string(),
            )
        })?;
        if !resolved.starts_with(&self.real_root) {
            return Err(ArtifactFailure::new(
                ArtifactFailureKind::SymlinkEscape,
                "repo locator resolves outside the reviewed repository root",
            ));
        }
        let metadata = fs::metadata(&resolved)
            .map_err(|error| ArtifactFailure::new(ArtifactFailureKind::Io, error.to_string()))?;
        if !metadata.is_file() {
            return Err(ArtifactFailure::new(
                ArtifactFailureKind::NotRegularFile,
                "repo locator does not resolve to a regular file",
            ));
        }
        fs::read(resolved)
            .map_err(|error| ArtifactFailure::new(ArtifactFailureKind::Io, error.to_string()))
    }
}

/// Minimal future-store seam. The locator remains a complete semantic-neutral key.
pub trait ArtifactStore {
    /// Fetches exact bytes for one validated `artifact://` locator.
    fn fetch(&self, locator: &ArtifactLocator) -> Result<Vec<u8>, ArtifactFailure>;
}

/// Deterministic in-memory implementation used by zero-backend tests.
#[derive(Clone, Debug, Default)]
pub struct InMemoryArtifactStore {
    values: BTreeMap<String, Vec<u8>>,
}

impl InMemoryArtifactStore {
    /// Publishes bytes immutably; same-key conflicts reject.
    pub fn insert(
        &mut self,
        locator: &ArtifactLocator,
        bytes: Vec<u8>,
    ) -> Result<(), ArtifactFailure> {
        if !locator.is_artifact() {
            return Err(ArtifactFailure::new(
                ArtifactFailureKind::ResolverMismatch,
                "artifact store accepts only artifact:// locators",
            ));
        }
        let key = locator.normalized();
        if let Some(existing) = self.values.get(&key) {
            if existing != &bytes {
                return Err(ArtifactFailure::new(
                    ArtifactFailureKind::Conflict,
                    "immutable artifact locator already contains different bytes",
                ));
            }
            return Ok(());
        }
        self.values.insert(key, bytes);
        Ok(())
    }
}

impl ArtifactStore for InMemoryArtifactStore {
    fn fetch(&self, locator: &ArtifactLocator) -> Result<Vec<u8>, ArtifactFailure> {
        if !locator.is_artifact() {
            return Err(ArtifactFailure::new(
                ArtifactFailureKind::ResolverMismatch,
                "artifact store accepts only artifact:// locators",
            ));
        }
        self.values
            .get(&locator.normalized())
            .cloned()
            .ok_or_else(|| {
                ArtifactFailure::new(
                    ArtifactFailureKind::MissingArtifact,
                    "artifact locator is not present",
                )
            })
    }
}

fn required_string(value: Option<&SemanticJson>, field: &str) -> Result<String, ArtifactFailure> {
    nonempty_string(value, field).map_err(identity_artifact_failure)
}

fn parse_artifact_digest(
    value: Option<&SemanticJson>,
    field: &str,
) -> Result<Digest, ArtifactFailure> {
    let value = required_string(value, field)?;
    Digest::parse(&value).map_err(|error| malformed_artifact(error.to_string()))
}

fn identity_artifact_failure(error: crate::IdentityError) -> ArtifactFailure {
    ArtifactFailure::new(ArtifactFailureKind::MalformedJson, error.to_string())
}

fn malformed_artifact(detail: impl Into<String>) -> ArtifactFailure {
    ArtifactFailure::new(ArtifactFailureKind::MalformedJson, detail)
}

#[cfg(test)]
mod tests {
    use super::*;
    use kink_contracts::{ArtifactAvailability, ResolverId};
    use std::sync::atomic::{AtomicU64, Ordering};

    static TEMP_ID: AtomicU64 = AtomicU64::new(0);

    fn workspace_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .ancestors()
            .nth(2)
            .expect("workspace layout")
            .to_path_buf()
    }

    #[test]
    fn loads_the_complete_frozen_role_registry() {
        let registry = RoleSpecRegistry::from_repository_root(&workspace_root())
            .expect("frozen registry must load");
        assert!(registry.contains("definition"));
        assert!(registry.contains("execution-profile"));
        assert!(!registry.contains("invented-role"));
    }

    #[test]
    fn repo_resolver_fetches_a_regular_bundled_file() {
        let locator = ArtifactLocator::parse(
            "repo://investigations/backend-agnostic-goal-closure/material/mutation-selector.json",
            ResolverId::RepoV1,
            ArtifactAvailability::Bundled,
        )
        .expect("frozen locator is valid");
        let bytes = RepositoryResolver::new(&workspace_root())
            .and_then(|resolver| resolver.fetch(&locator))
            .expect("bundled file resolves");
        assert!(!bytes.is_empty());
    }

    #[test]
    fn catalog_driven_canonical_ingress_checks_schema_and_semantic_identity() {
        let root = workspace_root();
        let registry =
            RoleSpecRegistry::from_repository_root(&root).expect("frozen registry must load");
        let catalog = parse_json(
            &fs::read(root.join(
                "investigations/backend-agnostic-goal-closure/fixtures/artifact-catalog.json",
            ))
            .expect("catalog fixture"),
        )
        .expect("catalog is restricted JSON");
        let entries = catalog
            .as_object()
            .and_then(|fields| fields.get("entries"))
            .and_then(SemanticJson::as_array)
            .expect("catalog entries");
        let row = entries
            .iter()
            .find(|value| {
                let fields = value.as_object().expect("catalog row");
                fields.get("role").and_then(SemanticJson::as_str) == Some("mutation-selector")
                    && fields.get("availability").and_then(SemanticJson::as_str) == Some("bundled")
            })
            .expect("bundled mutation selector");
        let entry = ArtifactCatalogEntry::from_json(row).expect("catalog row validates");
        let bytes = RepositoryResolver::new(&root)
            .and_then(|resolver| resolver.fetch(&entry.locator))
            .expect("catalog locator resolves");
        let artifact =
            ingest_artifact(&registry, &entry, bytes).expect("schema and both identities validate");
        assert!(artifact.semantic_json.is_some());
    }

    #[test]
    fn catalog_driven_definition_ingress_rederives_the_full_semantic_graph() {
        let root = workspace_root();
        let registry =
            RoleSpecRegistry::from_repository_root(&root).expect("frozen registry must load");
        let catalog = parse_json(
            &fs::read(root.join(
                "investigations/backend-agnostic-goal-closure/fixtures/bag14-cache-artifact-catalog.json",
            ))
            .expect("cache catalog fixture"),
        )
        .expect("cache catalog is restricted JSON");
        let row = catalog
            .as_object()
            .and_then(|fields| fields.get("entries"))
            .and_then(SemanticJson::as_array)
            .and_then(|entries| {
                entries.iter().find(|value| {
                    let fields = value.as_object().expect("catalog row");
                    fields.get("role").and_then(SemanticJson::as_str) == Some("definition")
                        && fields.get("availability").and_then(SemanticJson::as_str)
                            == Some("bundled")
                })
            })
            .expect("bundled definition entry");
        let entry = ArtifactCatalogEntry::from_json(row).expect("definition catalog row");
        let bytes = RepositoryResolver::new(&root)
            .and_then(|resolver| resolver.fetch(&entry.locator))
            .expect("definition locator resolves");
        let artifact = ingest_artifact(&registry, &entry, bytes)
            .expect("definition schema and every semantic linkage validate");
        assert!(artifact.semantic_json.is_some());
    }

    #[test]
    fn in_memory_store_is_immutable_and_artifact_only() {
        let locator = ArtifactLocator::parse(
            "artifact://profiles/execution.bin",
            ResolverId::RustArtifactStoreV1,
            ArtifactAvailability::ExternalRequired,
        )
        .expect("store locator is valid");
        let mut store = InMemoryArtifactStore::default();
        store
            .insert(&locator, b"one".to_vec())
            .expect("first insert");
        assert_eq!(store.fetch(&locator).expect("stored bytes"), b"one");
        assert_eq!(
            store
                .insert(&locator, b"two".to_vec())
                .expect_err("conflict must reject")
                .kind(),
            ArtifactFailureKind::Conflict
        );
    }

    #[cfg(unix)]
    #[test]
    fn repo_resolver_rejects_symlink_escape_and_non_file_targets() {
        use std::os::unix::fs::symlink;

        let token = format!(
            "kink-portable-{}-{}",
            std::process::id(),
            TEMP_ID.fetch_add(1, Ordering::Relaxed)
        );
        let root = std::env::temp_dir().join(format!("{token}-root"));
        let outside = std::env::temp_dir().join(format!("{token}-outside"));
        fs::create_dir_all(root.join("directory")).expect("temporary root");
        fs::write(&outside, b"outside").expect("temporary outside file");
        symlink(&outside, root.join("escape")).expect("temporary symlink");
        let resolver = RepositoryResolver::new(&root).expect("temporary repository root");
        let escape = ArtifactLocator::parse(
            "repo://escape",
            ResolverId::RepoV1,
            ArtifactAvailability::Bundled,
        )
        .expect("lexical escape locator");
        let directory = ArtifactLocator::parse(
            "repo://directory",
            ResolverId::RepoV1,
            ArtifactAvailability::Bundled,
        )
        .expect("lexical directory locator");
        assert_eq!(
            resolver
                .fetch(&escape)
                .expect_err("escape must reject")
                .kind(),
            ArtifactFailureKind::SymlinkEscape
        );
        assert_eq!(
            resolver
                .fetch(&directory)
                .expect_err("directory must reject")
                .kind(),
            ArtifactFailureKind::NotRegularFile
        );
        fs::remove_dir_all(root).expect("temporary root cleanup");
        fs::remove_file(outside).expect("temporary outside cleanup");
    }

    #[test]
    fn alternate_json_bytes_reject_before_semantic_acceptance() {
        let registry = RoleSpecRegistry::from_repository_root(&workspace_root())
            .expect("frozen registry must load");
        let value = parse_json(br#"{"compatibility":"portable"}"#).expect("fixture value");
        let semantic_digest = digest(&domain("k-in-k/compatibility-profile/v1"), &value)
            .expect("parsed compatibility profile is valid semantic JSON");
        let bytes = b"{ \"compatibility\": \"portable\" }".to_vec();
        let locator = ArtifactLocator::parse(
            "repo://synthetic/noncanonical.json",
            ResolverId::RepoV1,
            ArtifactAvailability::Bundled,
        )
        .expect("synthetic locator");
        let entry = ArtifactCatalogEntry {
            role: "compatibility-profile".to_owned(),
            digest: semantic_digest,
            content_model: ContentModel::CanonicalJson,
            media_type: MediaType::ApplicationJson,
            content_sha256: sha256_bytes(&bytes),
            locator,
        };
        assert_eq!(
            ingest_artifact(&registry, &entry, bytes)
                .expect_err("alternate encoding must reject")
                .kind(),
            ArtifactFailureKind::NonCanonicalBytes
        );
    }

    #[test]
    fn refreshed_definition_artifacts_reject_stale_nested_semantic_identities() {
        let root = workspace_root();
        let registry =
            RoleSpecRegistry::from_repository_root(&root).expect("frozen registry must load");
        let mut value = parse_json(
            &fs::read(root.join("crates/kink-patch/tests/data/semantic-definition-memory.json"))
                .expect("definition fixture"),
        )
        .expect("definition fixture is restricted JSON");
        let definition = PortableDefinition::from_json(&value).expect("fixture definition");
        let stale_fingerprint = Digest::parse(&"0".repeat(64)).expect("test digest");

        let mut stale_summary = definition.identity_summary();
        stale_summary.modules[0].sentence_content_fingerprints[0] = stale_fingerprint.clone();
        let refreshed_outer_digest = digest(
            &domain("k-in-k/definition/v1"),
            &stale_summary.identity_payload(),
        )
        .expect("summary is semantic JSON");

        let SemanticJson::Object(definition_fields) = &mut value else {
            panic!("definition fixture root");
        };
        definition_fields.insert(
            "definitionDigest".to_owned(),
            SemanticJson::String(refreshed_outer_digest.to_string()),
        );
        let SemanticJson::Array(modules) = definition_fields
            .get_mut("modules")
            .expect("definition modules")
        else {
            panic!("definition modules array");
        };
        let SemanticJson::Object(module) = &mut modules[0] else {
            panic!("definition module");
        };
        let SemanticJson::Array(sentences) = module.get_mut("sentences").expect("sentences") else {
            panic!("module sentences array");
        };
        let SemanticJson::Object(sentence) = &mut sentences[0] else {
            panic!("definition sentence");
        };
        let SemanticJson::Object(provenance) =
            sentence.get_mut("provenance").expect("sentence provenance")
        else {
            panic!("sentence provenance object");
        };
        provenance.insert(
            "contentFingerprint".to_owned(),
            SemanticJson::String(stale_fingerprint.to_string()),
        );

        let bytes = canonical_json_bytes(&value).expect("mutant remains semantic JSON");
        let locator = ArtifactLocator::parse(
            "repo://synthetic/stale-definition.json",
            ResolverId::RepoV1,
            ArtifactAvailability::Bundled,
        )
        .expect("synthetic locator");
        for role in ["definition", "instrumented-definition", "mutant-definition"] {
            let entry = ArtifactCatalogEntry {
                role: role.to_owned(),
                digest: refreshed_outer_digest.clone(),
                content_model: ContentModel::CanonicalJson,
                media_type: MediaType::ApplicationJson,
                content_sha256: sha256_bytes(&bytes),
                locator: locator.clone(),
            };
            assert_eq!(
                ingest_artifact(&registry, &entry, bytes.clone())
                    .expect_err("stale nested identity must reject even after outer refresh")
                    .kind(),
                ArtifactFailureKind::SemanticDigestMismatch,
                "role {role}"
            );
        }
    }
}
