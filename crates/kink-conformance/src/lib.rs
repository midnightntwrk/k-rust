//! Zero-backend discovery and frozen-vector import support.

use kink_contracts::{ConformanceFailure, ConformanceFailureKind};
use kink_portable::{
    Digest, DigestDomain, PortableDefinition, SemanticJson, canonical_json, digest, parse_json,
};
use serde::Deserialize;
use serde_json::{Map, Value};
use std::collections::BTreeSet;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};

/// Version pinned by the portable conformance package.
pub const PACKAGE_VERSION: &str = "backend-agnostic-k-in-k-v1";

/// Repository-relative path of the frozen conformance package.
pub const PACKAGE_RELATIVE_PATH: &str = "investigations/backend-agnostic-goal-closure";

/// Repository-relative path of the canonicalization vectors.
pub const CANONICALIZATION_VECTORS_RELATIVE_PATH: &str =
    "investigations/backend-agnostic-goal-closure/vectors/canonicalization-vectors.json";

/// Repository-relative path of the identity vectors.
pub const IDENTITY_VECTORS_RELATIVE_PATH: &str =
    "investigations/backend-agnostic-goal-closure/vectors/identity-vectors.json";

/// One frozen vector case, including its unchanged expected fields.
#[derive(Clone, Debug, PartialEq)]
pub struct FrozenCase {
    id: String,
    record: Map<String, Value>,
}

impl FrozenCase {
    /// Returns the stable case identifier.
    #[must_use]
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Returns a field exactly as supplied by the frozen vector.
    #[must_use]
    pub fn field(&self, name: &str) -> Option<&Value> {
        self.record.get(name)
    }
}

/// Imported canonicalization vectors whose expectations remain data, not implementation output.
#[derive(Clone, Debug, PartialEq)]
pub struct CanonicalizationVectors {
    package_version: String,
    cases: Vec<FrozenCase>,
}

impl CanonicalizationVectors {
    /// Returns the pinned package version.
    #[must_use]
    pub fn package_version(&self) -> &str {
        &self.package_version
    }

    /// Returns cases in their frozen declaration order.
    #[must_use]
    pub fn cases(&self) -> &[FrozenCase] {
        &self.cases
    }

    /// Finds a case without changing declaration order.
    #[must_use]
    pub fn case(&self, id: &str) -> Option<&FrozenCase> {
        self.cases.iter().find(|case| case.id == id)
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
struct CanonicalizationEnvelope {
    schema_version: u64,
    package_version: String,
    cases: Vec<Map<String, Value>>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
struct IdentityEnvelope {
    schema_version: u64,
    package_version: String,
    digest_domain: String,
    cases: Vec<Map<String, Value>>,
}

/// Located immutable package inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConformancePackage {
    repository_root: PathBuf,
    package_root: PathBuf,
}

impl ConformancePackage {
    /// Locates the package from the repository that built this crate.
    pub fn discover() -> Result<Self, ConformanceFailure> {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let repository_root = manifest_dir.ancestors().nth(2).ok_or_else(|| {
            ConformanceFailure::new(
                ConformanceFailureKind::PackageNotFound,
                "crate manifest is not below the expected workspace layout",
            )
            .at_path(manifest_dir)
        })?;
        Self::from_repository_root(repository_root)
    }

    /// Locates the package below an explicit repository root.
    pub fn from_repository_root(
        repository_root: impl AsRef<Path>,
    ) -> Result<Self, ConformanceFailure> {
        let repository_root = repository_root.as_ref().to_path_buf();
        let package_root = repository_root.join(PACKAGE_RELATIVE_PATH);
        if !package_root.is_dir() {
            return Err(ConformanceFailure::new(
                ConformanceFailureKind::PackageNotFound,
                "frozen conformance package directory is absent",
            )
            .at_path(package_root));
        }
        Ok(Self {
            repository_root,
            package_root,
        })
    }

    /// Returns the repository root used for resolution.
    #[must_use]
    pub fn repository_root(&self) -> &Path {
        &self.repository_root
    }

    /// Imports the frozen canonicalization vector envelope.
    pub fn canonicalization_vectors(&self) -> Result<CanonicalizationVectors, ConformanceFailure> {
        let path = self
            .package_root
            .join("vectors/canonicalization-vectors.json");
        let bytes = fs::read(&path).map_err(|error| {
            let kind = if error.kind() == std::io::ErrorKind::NotFound {
                ConformanceFailureKind::InputNotFound
            } else {
                ConformanceFailureKind::InputRead
            };
            ConformanceFailure::new(kind, error.to_string()).at_path(&path)
        })?;
        let envelope: CanonicalizationEnvelope =
            serde_json::from_slice(&bytes).map_err(|error| {
                ConformanceFailure::new(ConformanceFailureKind::MalformedInput, error.to_string())
                    .at_path(&path)
            })?;
        if envelope.schema_version != 1 {
            return Err(ConformanceFailure::new(
                ConformanceFailureKind::MalformedInput,
                format!("unsupported schemaVersion {}", envelope.schema_version),
            )
            .at_path(path));
        }
        if envelope.package_version != PACKAGE_VERSION {
            return Err(ConformanceFailure::new(
                ConformanceFailureKind::MalformedInput,
                format!("unsupported packageVersion {}", envelope.package_version),
            )
            .at_path(path));
        }
        if envelope.cases.is_empty() {
            return Err(ConformanceFailure::new(
                ConformanceFailureKind::MalformedInput,
                "canonicalization vector has no cases",
            )
            .at_path(path));
        }

        let mut ids = BTreeSet::new();
        let mut cases = Vec::with_capacity(envelope.cases.len());
        for record in envelope.cases {
            let Some(id) = record.get("id").and_then(Value::as_str) else {
                return Err(ConformanceFailure::new(
                    ConformanceFailureKind::MalformedInput,
                    "canonicalization case has no string id",
                )
                .at_path(path));
            };
            if !ids.insert(id.to_owned()) {
                return Err(ConformanceFailure::new(
                    ConformanceFailureKind::MalformedInput,
                    format!("duplicate canonicalization case id {id}"),
                )
                .at_path(path));
            }
            cases.push(FrozenCase {
                id: id.to_owned(),
                record,
            });
        }

        Ok(CanonicalizationVectors {
            package_version: envelope.package_version,
            cases,
        })
    }

    /// Imports the frozen identity vector envelope.
    pub fn identity_vectors(&self) -> Result<CanonicalizationVectors, ConformanceFailure> {
        let path = self.package_root.join("vectors/identity-vectors.json");
        let bytes = self.read(&path)?;
        let envelope: IdentityEnvelope = serde_json::from_slice(&bytes).map_err(|error| {
            ConformanceFailure::new(ConformanceFailureKind::MalformedInput, error.to_string())
                .at_path(&path)
        })?;
        if envelope.schema_version != 1
            || envelope.package_version != PACKAGE_VERSION
            || envelope.digest_domain != "k-in-k/semantic-lineage/v1"
        {
            return Err(ConformanceFailure::new(
                ConformanceFailureKind::MalformedInput,
                "identity vector envelope version/domain mismatch",
            )
            .at_path(path));
        }
        self.finish_cases(envelope.package_version, envelope.cases, path)
    }

    fn finish_cases(
        &self,
        package_version: String,
        records: Vec<Map<String, Value>>,
        path: PathBuf,
    ) -> Result<CanonicalizationVectors, ConformanceFailure> {
        if records.is_empty() {
            return Err(ConformanceFailure::new(
                ConformanceFailureKind::MalformedInput,
                "vector has no cases",
            )
            .at_path(path));
        }
        let mut ids = BTreeSet::new();
        let mut cases = Vec::with_capacity(records.len());
        for record in records {
            let Some(id) = record.get("id").and_then(Value::as_str) else {
                return Err(ConformanceFailure::new(
                    ConformanceFailureKind::MalformedInput,
                    "vector case has no string id",
                )
                .at_path(path));
            };
            if !ids.insert(id.to_owned()) {
                return Err(ConformanceFailure::new(
                    ConformanceFailureKind::MalformedInput,
                    format!("duplicate vector case id {id}"),
                )
                .at_path(path));
            }
            cases.push(FrozenCase {
                id: id.to_owned(),
                record,
            });
        }
        Ok(CanonicalizationVectors {
            package_version,
            cases,
        })
    }

    fn read(&self, path: &Path) -> Result<Vec<u8>, ConformanceFailure> {
        fs::read(path).map_err(|error| {
            let kind = if error.kind() == std::io::ErrorKind::NotFound {
                ConformanceFailureKind::InputNotFound
            } else {
                ConformanceFailureKind::InputRead
            };
            ConformanceFailure::new(kind, error.to_string()).at_path(path)
        })
    }

    fn semantic_json(&self, relative: &str) -> Result<SemanticJson, ConformanceFailure> {
        let path = self.package_root.join(relative);
        let bytes = self.read(&path)?;
        parse_json(&bytes).map_err(|error| {
            ConformanceFailure::new(ConformanceFailureKind::MalformedInput, error.to_string())
                .at_path(path)
        })
    }
}

/// Supported CLI operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConformanceCommand {
    /// List imported vector families.
    List,
    /// Check frozen vector envelopes.
    Check,
}

/// Parsed CLI invocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Invocation {
    /// Optional repository root override.
    pub repository_root: Option<PathBuf>,
    /// Requested operation.
    pub command: ConformanceCommand,
}

fn mismatch(detail: impl Into<String>) -> ConformanceFailure {
    ConformanceFailure::new(ConformanceFailureKind::ConformanceMismatch, detail)
}

fn portable(value: &Value) -> Result<SemanticJson, ConformanceFailure> {
    let bytes = serde_json::to_vec(value).map_err(|error| {
        ConformanceFailure::new(ConformanceFailureKind::MalformedInput, error.to_string())
    })?;
    parse_json(&bytes).map_err(|error| {
        ConformanceFailure::new(ConformanceFailureKind::MalformedInput, error.to_string())
    })
}

fn frozen_domain(value: &str) -> Result<DigestDomain, ConformanceFailure> {
    DigestDomain::new(value).map_err(|error| {
        ConformanceFailure::new(ConformanceFailureKind::MalformedInput, error.to_string())
    })
}

fn expected_digest(value: &Value) -> Result<Digest, ConformanceFailure> {
    Digest::parse(
        value
            .as_str()
            .ok_or_else(|| mismatch("expected digest is not a string"))?,
    )
    .map_err(|error| mismatch(error.to_string()))
}

fn check_canonicalization(vectors: &CanonicalizationVectors) -> Result<(), ConformanceFailure> {
    if vectors.cases().len() != 9 {
        return Err(mismatch("canonicalization vector count drift"));
    }
    for case in vectors.cases() {
        let field = |name| {
            case.field(name)
                .ok_or_else(|| mismatch(format!("{} lacks {name}", case.id())))
        };
        match case.id() {
            "object-key-order-is-irrelevant" => {
                let values = field("values")?
                    .as_array()
                    .ok_or_else(|| mismatch("values must be an array"))?;
                let domain = frozen_domain(
                    field("domain")?
                        .as_str()
                        .ok_or_else(|| mismatch("domain must be a string"))?,
                )?;
                let expected_json = field("expectedCanonicalJson")?
                    .as_str()
                    .ok_or_else(|| mismatch("expectedCanonicalJson must be a string"))?;
                let expected = expected_digest(field("expectedSha256")?)?;
                for value in values {
                    let value = portable(value)?;
                    if canonical_json(&value).map_err(|error| mismatch(error.to_string()))?
                        != expected_json
                        || digest(&domain, &value).map_err(|error| mismatch(error.to_string()))?
                            != expected
                    {
                        return Err(mismatch("object key-order vector mismatch"));
                    }
                }
            }
            "array-order-is-semantic" => {
                let values = field("values")?
                    .as_array()
                    .ok_or_else(|| mismatch("values must be an array"))?;
                let expected = field("expectedSha256")?
                    .as_array()
                    .ok_or_else(|| mismatch("expectedSha256 must be an array"))?;
                let domain = frozen_domain(
                    field("domain")?
                        .as_str()
                        .ok_or_else(|| mismatch("domain must be a string"))?,
                )?;
                let actual = values
                    .iter()
                    .map(|value| {
                        portable(value).and_then(|value| {
                            digest(&domain, &value).map_err(|error| mismatch(error.to_string()))
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let expected = expected
                    .iter()
                    .map(expected_digest)
                    .collect::<Result<Vec<_>, _>>()?;
                if actual != expected || actual[0] == actual[1] {
                    return Err(mismatch("array order vector mismatch"));
                }
            }
            "digest-domains-are-separated" => {
                let domains = field("domains")?
                    .as_array()
                    .ok_or_else(|| mismatch("domains must be an array"))?;
                let expected = field("expectedSha256")?
                    .as_array()
                    .ok_or_else(|| mismatch("expectedSha256 must be an array"))?;
                let value = portable(field("value")?)?;
                for (domain_value, expected_value) in domains.iter().zip(expected) {
                    let actual = digest(
                        &frozen_domain(
                            domain_value
                                .as_str()
                                .ok_or_else(|| mismatch("domain must be a string"))?,
                        )?,
                        &value,
                    )
                    .map_err(|error| mismatch(error.to_string()))?;
                    if actual != expected_digest(expected_value)? {
                        return Err(mismatch("domain separation vector mismatch"));
                    }
                }
            }
            "canonical-edit-order" => {
                let edits = field("unorderedEdits")?
                    .as_array()
                    .ok_or_else(|| mismatch("unorderedEdits must be an array"))?;
                let expected = field("expectedOrder")?
                    .as_array()
                    .ok_or_else(|| mismatch("expectedOrder must be an array"))?;
                let mut order: Vec<usize> = (0..edits.len()).collect();
                order.sort_by_key(|index| {
                    let edit = edits[*index].as_object().expect("frozen edit object");
                    (
                        edit.get("targetLineage")
                            .and_then(Value::as_str)
                            .unwrap_or_default()
                            .to_owned(),
                        edit.get("targetPath")
                            .map(|value| serde_json::to_string(value).expect("frozen path"))
                            .unwrap_or_default(),
                    )
                });
                let expected: Vec<usize> = expected
                    .iter()
                    .map(|value| {
                        value
                            .as_u64()
                            .and_then(|value| usize::try_from(value).ok())
                            .ok_or_else(|| mismatch("expectedOrder item must be nonnegative"))
                    })
                    .collect::<Result<_, _>>()?;
                if order != expected {
                    return Err(mismatch("canonical edit order mismatch"));
                }
            }
            "unicode-nfc-and-control-escaping" => {
                let value = portable(field("value")?)?;
                let expected_json = field("expectedCanonicalJson")?
                    .as_str()
                    .ok_or_else(|| mismatch("expectedCanonicalJson must be a string"))?;
                let domain = frozen_domain(
                    field("domain")?
                        .as_str()
                        .ok_or_else(|| mismatch("domain must be a string"))?,
                )?;
                if canonical_json(&value).map_err(|error| mismatch(error.to_string()))?
                    != expected_json
                    || digest(&domain, &value).map_err(|error| mismatch(error.to_string()))?
                        != expected_digest(field("expectedSha256")?)?
                {
                    return Err(mismatch("Unicode/control vector mismatch"));
                }
            }
            "signed-64-boundaries" => {
                for value in field("valid")?
                    .as_array()
                    .ok_or_else(|| mismatch("valid must be an array"))?
                {
                    portable(value)?;
                }
                for value in field("invalidDecimal")?
                    .as_array()
                    .ok_or_else(|| mismatch("invalidDecimal must be an array"))?
                {
                    if parse_json(
                        value
                            .as_str()
                            .ok_or_else(|| mismatch("invalid decimal must be string"))?
                            .as_bytes(),
                    )
                    .is_ok()
                    {
                        return Err(mismatch("out-of-range integer was accepted"));
                    }
                }
            }
            "duplicate-keys-rejected" => {
                if parse_json(
                    field("invalidJson")?
                        .as_str()
                        .ok_or_else(|| mismatch("invalidJson must be string"))?
                        .as_bytes(),
                )
                .is_ok()
                {
                    return Err(mismatch("duplicate keys were accepted"));
                }
            }
            "non-nfc-rejected" => {
                let scalars = field("invalidCodePoints")?
                    .as_array()
                    .ok_or_else(|| mismatch("invalidCodePoints must be an array"))?;
                let text: String = scalars
                    .iter()
                    .map(|value| {
                        value
                            .as_u64()
                            .and_then(|value| u32::try_from(value).ok())
                            .and_then(char::from_u32)
                            .ok_or_else(|| mismatch("invalid code point fixture"))
                    })
                    .collect::<Result<_, _>>()?;
                let encoded = serde_json::to_vec(&text).expect("Rust string serializes");
                if parse_json(&encoded).is_ok() {
                    return Err(mismatch("non-NFC string was accepted"));
                }
            }
            "in-memory-portable-domain" => {
                if field("acceptedExactTypes")?.as_array().map(Vec::len) != Some(6)
                    || field("reasonCodes")?.as_array().map(Vec::len) != Some(7)
                    || field("sharedAcyclicReferences")?.as_str() != Some("accepted-by-value")
                    || field("cycles")?.as_str() != Some("rejected")
                {
                    return Err(mismatch("in-memory domain declaration drift"));
                }
            }
            other => {
                return Err(mismatch(format!(
                    "unrecognized canonicalization case {other}"
                )));
            }
        }
    }
    Ok(())
}

fn check_identity(
    package: &ConformancePackage,
    vectors: &CanonicalizationVectors,
) -> Result<(), ConformanceFailure> {
    if vectors.cases().len() != 7 {
        return Err(mismatch("identity vector count drift"));
    }
    for case in vectors.cases() {
        let left = case
            .field("left")
            .and_then(Value::as_object)
            .ok_or_else(|| mismatch("identity left must be object"))?;
        let right = case
            .field("right")
            .and_then(Value::as_object)
            .ok_or_else(|| mismatch("identity right must be object"))?;
        let expected = case
            .field("expected")
            .and_then(Value::as_object)
            .ok_or_else(|| mismatch("identity expected must be object"))?;
        let anchor = |side: &Map<String, Value>| {
            let names: &[&str] = if side.contains_key("transformationId") {
                &[
                    "transformationId",
                    "parents",
                    "anchorIdentity",
                    "role",
                    "ordinal",
                ]
            } else {
                &[
                    "module",
                    "source",
                    "location",
                    "kind",
                    "sourceOccurrenceOrdinal",
                ]
            };
            names
                .iter()
                .map(|name| {
                    side.get(*name).cloned().unwrap_or_else(|| {
                        if *name == "sourceOccurrenceOrdinal" {
                            Value::from(0)
                        } else {
                            Value::Null
                        }
                    })
                })
                .collect::<Vec<_>>()
        };
        let same_lineage = anchor(left) == anchor(right);
        if expected.get("sameLineage").and_then(Value::as_bool) != Some(same_lineage) {
            return Err(mismatch(format!("{} lineage mismatch", case.id())));
        }
        if let Some(expected_body) = expected.get("sameBody").and_then(Value::as_bool)
            && (left.get("body") == right.get("body")) != expected_body
        {
            return Err(mismatch(format!("{} body mismatch", case.id())));
        }
        if let Some(expected_content) = expected.get("sameContent").and_then(Value::as_bool) {
            let keys = ["module", "source", "location", "kind", "label", "body"];
            let same = keys.iter().all(|key| left.get(*key) == right.get(*key));
            if same != expected_content {
                return Err(mismatch(format!("{} content mismatch", case.id())));
            }
        }
    }

    let fixture = package.semantic_json("fixtures/semantic-identity.json")?;
    let root = fixture
        .as_object()
        .ok_or_else(|| mismatch("identity fixture must be object"))?;
    let inputs = root
        .get("digestInputs")
        .and_then(SemanticJson::as_object)
        .ok_or_else(|| mismatch("identity digestInputs must be object"))?;
    let checks = [
        (
            "baselineFamily",
            "baselineFamilyId",
            "k-in-k/baseline-family/v1",
        ),
        ("definition", "definitionDigest", "k-in-k/definition/v1"),
        (
            "transformation",
            "transformationId",
            "k-in-k/transformation/v1",
        ),
        (
            "generatedLineage",
            "generatedLineageId",
            "k-in-k/generated-lineage/v1",
        ),
    ];
    for (input, output, domain_name) in checks {
        let mut payload = inputs
            .get(input)
            .cloned()
            .ok_or_else(|| mismatch(format!("missing identity input {input}")))?;
        if input == "baselineFamily" {
            let fields = payload.as_object().expect("frozen family object");
            let mut entries = fields
                .get("entryModules")
                .and_then(SemanticJson::as_array)
                .expect("frozen entries")
                .to_vec();
            entries.sort_by_key(|value| value.as_str().unwrap_or_default().to_owned());
            let mut normalized = fields.clone();
            normalized.insert("entryModules".to_owned(), SemanticJson::Array(entries));
            payload = SemanticJson::Object(normalized);
        }
        let expected = root
            .get(output)
            .and_then(SemanticJson::as_str)
            .ok_or_else(|| mismatch(format!("missing identity output {output}")))?;
        if digest(&frozen_domain(domain_name)?, &payload)
            .map_err(|error| mismatch(error.to_string()))?
            .as_str()
            != expected
        {
            return Err(mismatch(format!("{output} derivation mismatch")));
        }
    }

    let sentence = root
        .get("sentences")
        .and_then(SemanticJson::as_array)
        .and_then(|values| values.first())
        .and_then(SemanticJson::as_object)
        .ok_or_else(|| mismatch("identity fixture lacks its source sentence"))?;
    let sentence_content = inputs
        .get("sentenceContent")
        .and_then(SemanticJson::as_object)
        .ok_or_else(|| mismatch("identity fixture lacks sentenceContent"))?;
    let lineage = digest(
        &frozen_domain("k-in-k/input-lineage/v1")?,
        inputs
            .get("inputLineage")
            .ok_or_else(|| mismatch("identity fixture lacks inputLineage"))?,
    )
    .map_err(|error| mismatch(error.to_string()))?;
    if sentence.get("lineageId").and_then(SemanticJson::as_str) != Some(lineage.as_str())
        || sentence_content
            .get("lineageId")
            .and_then(SemanticJson::as_str)
            != Some(lineage.as_str())
    {
        return Err(mismatch("input lineage derivation or linkage mismatch"));
    }
    let body = digest(
        &frozen_domain("k-in-k/sentence-body/v1")?,
        inputs
            .get("sentenceBody")
            .ok_or_else(|| mismatch("identity fixture lacks sentenceBody"))?,
    )
    .map_err(|error| mismatch(error.to_string()))?;
    if sentence
        .get("bodyFingerprint")
        .and_then(SemanticJson::as_str)
        != Some(body.as_str())
        || sentence_content
            .get("bodyFingerprint")
            .and_then(SemanticJson::as_str)
            != Some(body.as_str())
    {
        return Err(mismatch("body fingerprint derivation or linkage mismatch"));
    }
    let content = digest(
        &frozen_domain("k-in-k/sentence-content/v1")?,
        inputs
            .get("sentenceContent")
            .ok_or_else(|| mismatch("identity fixture lacks sentenceContent"))?,
    )
    .map_err(|error| mismatch(error.to_string()))?;
    let definition_input = inputs
        .get("definition")
        .and_then(SemanticJson::as_object)
        .ok_or_else(|| mismatch("identity fixture lacks definition input"))?;
    let linked_content = definition_input
        .get("modules")
        .and_then(SemanticJson::as_array)
        .and_then(|modules| modules.first())
        .and_then(SemanticJson::as_object)
        .and_then(|module| module.get("sentenceContentFingerprints"))
        .and_then(SemanticJson::as_array)
        .and_then(|values| values.first())
        .and_then(SemanticJson::as_str);
    if sentence
        .get("contentFingerprint")
        .and_then(SemanticJson::as_str)
        != Some(content.as_str())
        || linked_content != Some(content.as_str())
    {
        return Err(mismatch(
            "content fingerprint derivation or linkage mismatch",
        ));
    }

    let input_value = package.semantic_json("fixtures/semantic-definition-memory.json")?;
    let output_value =
        package.semantic_json("fixtures/semantic-definition-identity-output.json")?;
    let input_definition = PortableDefinition::from_json(&input_value)
        .map_err(|error| mismatch(format!("identity input definition: {error}")))?;
    let output_definition = PortableDefinition::from_json(&output_value)
        .map_err(|error| mismatch(format!("identity output definition: {error}")))?;
    let generated_id = root
        .get("generatedLineageId")
        .and_then(SemanticJson::as_str)
        .ok_or_else(|| mismatch("identity fixture lacks generatedLineageId"))?;
    let generated = output_definition
        .modules
        .iter()
        .flat_map(|module| module.sentences.iter())
        .find(|sentence| sentence.provenance.lineage_id.as_str() == generated_id)
        .and_then(|sentence| sentence.generated_identity.as_ref())
        .ok_or_else(|| mismatch("generated lineage does not resolve in reviewed output"))?;
    if generated.parent_lineages.is_empty()
        && !input_definition
            .modules
            .iter()
            .any(|module| module.fingerprint == generated.anchor_identity)
    {
        return Err(mismatch(
            "parentless generated anchor is absent from reviewed input modules",
        ));
    }
    let evidence = root
        .get("transformationEvidence")
        .and_then(SemanticJson::as_object)
        .ok_or_else(|| mismatch("identity fixture lacks transformationEvidence"))?;
    let evidence_digest = |name: &str| {
        evidence
            .get(name)
            .and_then(SemanticJson::as_object)
            .and_then(|value| value.get("digest"))
            .and_then(SemanticJson::as_str)
    };
    if evidence_digest("inputDefinition") != Some(input_definition.definition_digest.as_str())
        || evidence_digest("outputDefinition") != Some(output_definition.definition_digest.as_str())
    {
        return Err(mismatch(
            "transformation evidence does not bind the reviewed definitions",
        ));
    }
    for name in [
        "semantic-definition-memory.json",
        "semantic-definition-counter.json",
        "semantic-definition-generated.json",
        "semantic-definition-identity-output.json",
    ] {
        let value = package.semantic_json(&format!("fixtures/{name}"))?;
        PortableDefinition::from_json(&value)
            .map_err(|error| mismatch(format!("{name}: {error}")))?;
    }
    Ok(())
}

impl Invocation {
    /// Parses arguments after the executable name.
    pub fn parse(args: impl IntoIterator<Item = OsString>) -> Result<Self, ConformanceFailure> {
        let mut args = args.into_iter();
        let mut repository_root = None;
        let first = args.next().ok_or_else(|| {
            ConformanceFailure::new(
                ConformanceFailureKind::MissingInput,
                "expected [--repository PATH] <list|check>",
            )
        })?;

        let command_value = if first == "--repository" {
            let root = args.next().ok_or_else(|| {
                ConformanceFailure::new(
                    ConformanceFailureKind::MissingInput,
                    "--repository requires a path",
                )
            })?;
            repository_root = Some(PathBuf::from(root));
            args.next().ok_or_else(|| {
                ConformanceFailure::new(
                    ConformanceFailureKind::MissingInput,
                    "expected list or check after --repository PATH",
                )
            })?
        } else {
            first
        };

        let command = match command_value.to_str() {
            Some("list") => ConformanceCommand::List,
            Some("check") => ConformanceCommand::Check,
            _ => {
                return Err(ConformanceFailure::new(
                    ConformanceFailureKind::UnexpectedInput,
                    format!("unsupported command {}", command_value.to_string_lossy()),
                ));
            }
        };
        if let Some(unexpected) = args.next() {
            return Err(ConformanceFailure::new(
                ConformanceFailureKind::UnexpectedInput,
                format!("unexpected argument {}", unexpected.to_string_lossy()),
            ));
        }
        Ok(Self {
            repository_root,
            command,
        })
    }
}

/// Runs one invocation and returns its stable stdout line.
pub fn run(invocation: &Invocation) -> Result<String, ConformanceFailure> {
    let package = match &invocation.repository_root {
        Some(root) => ConformancePackage::from_repository_root(root),
        None => ConformancePackage::discover(),
    }?;
    let vectors = package.canonicalization_vectors()?;
    let case_count = vectors.cases().len();
    Ok(match invocation.command {
        ConformanceCommand::List => {
            let identities = package.identity_vectors()?;
            format!(
                "canonicalization-vectors\tvectors/canonicalization-vectors.json\t{case_count}\nidentity-vectors\tvectors/identity-vectors.json\t{}",
                identities.cases().len()
            )
        }
        ConformanceCommand::Check => {
            check_canonicalization(&vectors)?;
            let identities = package.identity_vectors()?;
            check_identity(&package, &identities)?;
            format!(
                "PASS canonicalization-vectors: {case_count} cases; identity-vectors: {} cases; portable-definitions: 4 fixtures",
                identities.cases().len()
            )
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn imports_frozen_expected_fields_without_recomputing_them() {
        let vectors = ConformancePackage::discover()
            .and_then(|package| package.canonicalization_vectors())
            .expect("the repository carries the frozen conformance vector");
        let case = vectors
            .case("object-key-order-is-irrelevant")
            .expect("the frozen case is present");
        assert_eq!(
            case.field("expectedCanonicalJson").and_then(Value::as_str),
            Some("{\"a\":1,\"nested\":{\"a\":null,\"b\":true},\"z\":3}")
        );
        assert_eq!(vectors.package_version(), PACKAGE_VERSION);
    }

    #[test]
    fn rejects_unexpected_cli_input_with_a_typed_failure() {
        let failure = Invocation::parse([OsString::from("unknown")])
            .expect_err("unknown commands must reject");
        assert_eq!(failure.kind(), ConformanceFailureKind::UnexpectedInput);
        assert_eq!(failure.kind().exit_code(), 2);
    }
}
