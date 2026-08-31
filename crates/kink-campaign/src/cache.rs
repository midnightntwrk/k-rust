use crate::receipt::{
    ArtifactKey, OperationReceipt, ProducerStatus, ScriptedReceipt, ValidatedPortableReceipt,
    domain, object, parse_artifact_key, string, validate_v1_schema,
};
use kink_portable::{Digest, SemanticJson, digest, digest_without_field, parse_json};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// The two raw BAG-14 request-key families.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum KeyKind {
    /// One isolated execution request.
    ExecutionAttempt,
    /// One typed oracle evaluation request.
    OracleEvaluation,
}

impl KeyKind {
    const fn domain(self) -> &'static str {
        match self {
            Self::ExecutionAttempt => "k-in-k/execution-attempt-key/v1",
            Self::OracleEvaluation => "k-in-k/oracle-evaluation-key/v1",
        }
    }

    const fn schema_reference(self) -> &'static str {
        match self {
            Self::ExecutionAttempt => {
                "https://starstream.dev/k-in-k/backend-agnostic/v1/cache-semantics.schema.json#/$defs/executionAttemptKey"
            }
            Self::OracleEvaluation => {
                "https://starstream.dev/k-in-k/backend-agnostic/v1/cache-semantics.schema.json#/$defs/oracleEvaluationKey"
            }
        }
    }

    const fn as_str(self) -> &'static str {
        match self {
            Self::ExecutionAttempt => "execution-attempt",
            Self::OracleEvaluation => "oracle-evaluation",
        }
    }
}

/// A schema-exact, cycle-free request key with a rederived identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RequestKey {
    kind: KeyKind,
    value: SemanticJson,
    key_digest: Digest,
}

impl RequestKey {
    /// Builds a key from the exact request payload without `keyDigest`.
    ///
    /// The derived digest is inserted and the completed value must satisfy the
    /// operation-specific closed schema. Arbitrary object payloads are rejected.
    pub fn new(kind: KeyKind, request_without_digest: SemanticJson) -> Result<Self, CacheFailure> {
        let SemanticJson::Object(mut fields) = request_without_digest else {
            return Err(CacheFailure::new(
                CacheFailureKind::InvalidKey,
                "request key payload must be an object",
            ));
        };
        if fields.contains_key("keyDigest") {
            return Err(CacheFailure::new(
                CacheFailureKind::ForbiddenKeyField,
                "request constructor accepts a payload without keyDigest",
            ));
        }
        let payload = SemanticJson::Object(fields.clone());
        let key_digest = digest(&domain(kind.domain()), &payload).map_err(|error| {
            CacheFailure::new(
                CacheFailureKind::InvalidKey,
                format!("request key is not valid semantic JSON: {error}"),
            )
        })?;
        fields.insert(
            "keyDigest".to_owned(),
            SemanticJson::String(key_digest.to_string()),
        );
        Self::from_portable_json(kind, &SemanticJson::Object(fields))
    }

    /// Parses an exact frozen request key and rederives its self identity.
    pub fn from_portable_json(kind: KeyKind, value: &SemanticJson) -> Result<Self, CacheFailure> {
        validate_v1_schema(value, kind.schema_reference())
            .map_err(|detail| CacheFailure::new(CacheFailureKind::InvalidKey, detail))?;
        let fields = value.as_object().expect("request schema checked");
        let expected = parse_digest(fields.get("keyDigest"), "keyDigest")?;
        let derived =
            digest_without_field(&domain(kind.domain()), value, "keyDigest").map_err(|error| {
                CacheFailure::new(
                    CacheFailureKind::InvalidKey,
                    format!("request key identity projection failed: {error}"),
                )
            })?;
        if expected != derived {
            return Err(CacheFailure::new(
                CacheFailureKind::KeyDigestMismatch,
                "keyDigest does not match the exact request payload",
            ));
        }
        Ok(Self {
            kind,
            value: value.clone(),
            key_digest: derived,
        })
    }

    /// Key family.
    #[must_use]
    pub const fn kind(&self) -> KeyKind {
        self.kind
    }

    /// Complete self-identified portable key.
    #[must_use]
    pub fn as_json(&self) -> &SemanticJson {
        &self.value
    }

    /// Rederived request identity.
    #[must_use]
    pub fn key_digest(&self) -> &Digest {
        &self.key_digest
    }
}

/// Positive completion class of an immutable record.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CompletionClass {
    /// Complete reusable semantic result.
    SemanticResult,
    /// Complete attempt stopped at the exact requested bounds.
    ExactBoundedAttempt,
    /// Diagnostic result, never reusable.
    DiagnosticOnly,
}

impl CompletionClass {
    fn parse(value: &str) -> Option<Self> {
        Some(match value {
            "semantic-result" => Self::SemanticResult,
            "exact-bounded-attempt" => Self::ExactBoundedAttempt,
            "diagnostic-only" => Self::DiagnosticOnly,
            _ => return None,
        })
    }
}

/// Resolver-relative material gate, excluded from request identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MaterialEligibility {
    /// Every required artifact is byte- and semantic-verified under the active resolver.
    Eligible,
    /// An external-required artifact is not currently resolvable.
    ExternalUnavailable,
    /// Produced material failed verification and cannot become a record.
    Invalid,
}

/// Intrinsic cache reuse class.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReuseClass {
    /// Reusable complete semantic result.
    SemanticResult,
    /// Reusable only for an exact same-bounds request.
    ExactBoundedAttempt,
    /// Not reusable.
    NotReusable,
}

impl ReuseClass {
    fn parse(value: &str) -> Option<Self> {
        Some(match value {
            "semantic-result" => Self::SemanticResult,
            "exact-bounded-attempt" => Self::ExactBoundedAttempt,
            "not-reusable" => Self::NotReusable,
            _ => return None,
        })
    }
}

/// Evidence supplied while parsing a frozen cache record.
///
/// Both arms are fail-closed. Finite rows are matched against the bundled
/// registry; receipt-backed records additionally require the exact receipt and
/// wrapper pair and a reviewed frozen pair identity. There is deliberately no
/// caller-constructible native-authority arm.
#[derive(Clone, Copy, Debug)]
pub enum PortableProductionWitness<'a> {
    /// Validate against the bundled BAG-14 finite registry.
    BundledFiniteVector,
    /// Validate exact BAG-15 receipt/wrapper production correspondence.
    BundledOperationReceipt {
        /// Complete portable operation receipt.
        receipt: &'a SemanticJson,
        /// Sole result wrapper published by the receipt.
        result: &'a SemanticJson,
    },
}

/// One immutable per-attempt or oracle cache record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CacheRecord {
    key: RequestKey,
    terminal_record: SemanticJson,
    produced_artifacts: Vec<ArtifactKey>,
    completion: CompletionClass,
    material: MaterialEligibility,
    reuse_class: ReuseClass,
    production_receipt: Option<Digest>,
    record_id: Digest,
    value: SemanticJson,
}

impl CacheRecord {
    /// Parses and independently validates one exact BAG-14 cache record.
    pub fn from_portable_json(
        value: &SemanticJson,
        witness: PortableProductionWitness<'_>,
    ) -> Result<Self, CacheFailure> {
        validate_v1_schema(
            value,
            "https://starstream.dev/k-in-k/backend-agnostic/v1/cache-semantics.schema.json#/$defs/cacheRecord",
        )
        .map_err(|detail| CacheFailure::new(CacheFailureKind::InvalidRecord, detail))?;
        let fields = value.as_object().expect("cache record schema checked");
        let kind = match fields.get("kind").and_then(SemanticJson::as_str) {
            Some("execution-attempt") => KeyKind::ExecutionAttempt,
            Some("oracle-evaluation") => KeyKind::OracleEvaluation,
            _ => unreachable!("cache record schema checked"),
        };
        let key = RequestKey::from_portable_json(
            kind,
            fields.get("key").expect("cache record schema checked"),
        )?;
        let repeated_key = parse_digest(fields.get("keyDigest"), "keyDigest")?;
        if repeated_key != *key.key_digest() {
            return Err(CacheFailure::new(
                CacheFailureKind::KeyDigestMismatch,
                "cache record and nested key identities disagree",
            ));
        }
        let terminal_record = fields
            .get("terminalRecord")
            .expect("cache record schema checked")
            .clone();
        let produced_artifacts = fields
            .get("producedArtifacts")
            .and_then(SemanticJson::as_array)
            .expect("cache record schema checked")
            .iter()
            .map(|item| {
                parse_artifact_key(item).ok_or_else(|| {
                    CacheFailure::new(
                        CacheFailureKind::InvalidRecord,
                        "producedArtifacts contains an invalid key",
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let completion_fields = fields
            .get("completion")
            .and_then(SemanticJson::as_object)
            .expect("cache record schema checked");
        let completion = completion_fields
            .get("evidenceClass")
            .and_then(SemanticJson::as_str)
            .and_then(CompletionClass::parse)
            .expect("cache record schema checked");
        let material = match completion_fields
            .get("materialClosure")
            .and_then(SemanticJson::as_str)
        {
            Some("repo-complete") => MaterialEligibility::Eligible,
            Some("external-required") => MaterialEligibility::ExternalUnavailable,
            _ => unreachable!("cache record schema checked"),
        };
        validate_completion_correspondence(kind, completion, &terminal_record)?;
        let execution_conformance = completion_fields
            .get("executionConformance")
            .and_then(SemanticJson::as_str)
            .expect("cache record schema checked");
        if execution_conformance == "native-proven" {
            return Err(CacheFailure::new(
                CacheFailureKind::NativeAuthorityUnavailable,
                "portable finite/receipt witnesses cannot establish native production",
            ));
        }
        let production = fields
            .get("productionEvidence")
            .and_then(SemanticJson::as_object)
            .expect("cache record schema checked");
        let production_receipt = match witness {
            PortableProductionWitness::BundledFiniteVector => {
                validate_finite_vector(
                    production,
                    key.key_digest(),
                    &terminal_record,
                    &produced_artifacts,
                )?;
                None
            }
            PortableProductionWitness::BundledOperationReceipt { receipt, result } => {
                let validated = OperationReceipt::validate_portable_bundle(receipt, result)
                    .map_err(|error| {
                        CacheFailure::new(
                            CacheFailureKind::InvalidProduction,
                            format!("operation production rejected: {error}"),
                        )
                    })?;
                validate_receipt_production(
                    production,
                    &validated,
                    &key,
                    &terminal_record,
                    &produced_artifacts,
                )?;
                Some(validated.receipt_id().clone())
            }
        };
        let authority_proven = execution_conformance == "finite-vector-proven";
        let derived_reuse = derive_reuse(completion, material, authority_proven);
        let claimed_reuse = fields
            .get("reuseClass")
            .and_then(SemanticJson::as_str)
            .and_then(ReuseClass::parse)
            .expect("cache record schema checked");
        if claimed_reuse != derived_reuse {
            return Err(CacheFailure::new(
                CacheFailureKind::ReuseMismatch,
                "reuseClass does not follow completion, material, and authority",
            ));
        }
        let expected_record = parse_digest(fields.get("recordId"), "recordId")?;
        let record_id = digest_without_field(&domain("k-in-k/cache-record/v1"), value, "recordId")
            .map_err(|error| {
                CacheFailure::new(
                    CacheFailureKind::InvalidRecord,
                    format!("cache record identity projection failed: {error}"),
                )
            })?;
        if expected_record != record_id {
            return Err(CacheFailure::new(
                CacheFailureKind::RecordDigestMismatch,
                "recordId does not match the exact immutable record",
            ));
        }
        Ok(Self {
            key,
            terminal_record,
            produced_artifacts,
            completion,
            material,
            reuse_class: derived_reuse,
            production_receipt,
            record_id,
            value: value.clone(),
        })
    }

    /// Constructs a non-reusable scripted record for boundary and quarantine tests.
    ///
    /// This path never accepts finite or native authority and therefore cannot
    /// create a reusable record.
    pub fn scripted_diagnostic(
        key: RequestKey,
        terminal_record: SemanticJson,
        produced_artifacts: Vec<ArtifactKey>,
        material: MaterialEligibility,
        receipt: &ScriptedReceipt,
    ) -> Result<Self, CacheFailure> {
        if receipt.status != ProducerStatus::Complete {
            return Err(CacheFailure::new(
                CacheFailureKind::ProducerFailed,
                "a failed producer cannot publish a cache record",
            ));
        }
        if receipt.producer.evidence() != kink_contracts::EvidenceClass::Scripted
            || receipt.producer.native_conformance() != kink_contracts::NativeConformance::NotProven
        {
            return Err(CacheFailure::new(
                CacheFailureKind::NativeAuthorityUnavailable,
                "scripted constructor accepts only scripted/not-proven producers",
            ));
        }
        let output = receipt.output.as_ref().ok_or_else(|| {
            CacheFailure::new(
                CacheFailureKind::MissingOutput,
                "complete producer has no wrapper",
            )
        })?;
        if output.produced_artifacts != produced_artifacts {
            return Err(CacheFailure::new(
                CacheFailureKind::OutputMismatch,
                "cache outputs differ from the producing wrapper",
            ));
        }
        let mut unique = BTreeSet::new();
        if !produced_artifacts.iter().all(|item| unique.insert(item)) {
            return Err(CacheFailure::new(
                CacheFailureKind::DuplicateOutput,
                "cache outputs contain a duplicate artifact",
            ));
        }
        if material == MaterialEligibility::Invalid {
            return Err(CacheFailure::new(
                CacheFailureKind::InvalidMaterial,
                "one or more produced artifacts failed material validation",
            ));
        }
        validate_v1_schema(
            &terminal_record,
            match key.kind() {
                KeyKind::ExecutionAttempt => "https://starstream.dev/k-in-k/backend-agnostic/v1/cache-semantics.schema.json#/$defs/executionTerminalRecord",
                KeyKind::OracleEvaluation => "https://starstream.dev/k-in-k/backend-agnostic/v1/cache-semantics.schema.json#/$defs/oracleTerminalRecord",
            },
        )
        .map_err(|detail| CacheFailure::new(CacheFailureKind::InvalidRecord, detail))?;
        validate_completion_correspondence(
            key.kind(),
            CompletionClass::DiagnosticOnly,
            &terminal_record,
        )?;
        let value = object([
            ("key", key.as_json().clone()),
            ("keyDigest", string(key.key_digest().as_str())),
            ("kind", string(key.kind().as_str())),
            ("terminalRecord", terminal_record.clone()),
            (
                "producedArtifacts",
                SemanticJson::Array(
                    produced_artifacts
                        .iter()
                        .map(ArtifactKey::to_json)
                        .collect(),
                ),
            ),
            ("productionReceipt", string(receipt.receipt_id.as_str())),
            ("schemaVersion", SemanticJson::Integer(1)),
        ]);
        let record_id =
            digest(&domain("k-in-k/scripted-cache-diagnostic/v1"), &value).map_err(|error| {
                CacheFailure::new(CacheFailureKind::InvalidRecord, error.to_string())
            })?;
        Ok(Self {
            key,
            terminal_record,
            produced_artifacts,
            completion: CompletionClass::DiagnosticOnly,
            material,
            reuse_class: ReuseClass::NotReusable,
            production_receipt: Some(receipt.receipt_id.clone()),
            record_id,
            value,
        })
    }

    /// Exact request key.
    #[must_use]
    pub fn key(&self) -> &RequestKey {
        &self.key
    }

    /// Exact typed terminal/result record.
    #[must_use]
    pub fn terminal_record(&self) -> &SemanticJson {
        &self.terminal_record
    }

    /// Complete ordered produced artifacts.
    #[must_use]
    pub fn produced_artifacts(&self) -> &[ArtifactKey] {
        &self.produced_artifacts
    }

    /// Positive completion class.
    #[must_use]
    pub const fn completion(&self) -> CompletionClass {
        self.completion
    }

    /// Resolver-relative material eligibility observed at validation time.
    #[must_use]
    pub const fn material(&self) -> MaterialEligibility {
        self.material
    }

    /// Intrinsic reuse class rederived from validated evidence.
    #[must_use]
    pub const fn reuse_class(&self) -> ReuseClass {
        self.reuse_class
    }

    /// Producing receipt identity for a receipt-backed record.
    #[must_use]
    pub fn production_receipt(&self) -> Option<&Digest> {
        self.production_receipt.as_ref()
    }

    /// Immutable record identity.
    #[must_use]
    pub fn record_id(&self) -> &Digest {
        &self.record_id
    }

    /// Validated record representation.
    #[must_use]
    pub fn as_json(&self) -> &SemanticJson {
        &self.value
    }
}

fn validate_completion_correspondence(
    kind: KeyKind,
    completion: CompletionClass,
    terminal: &SemanticJson,
) -> Result<(), CacheFailure> {
    let terminal_kind = terminal
        .as_object()
        .and_then(|fields| fields.get("kind"))
        .and_then(SemanticJson::as_str)
        .ok_or_else(|| {
            CacheFailure::new(
                CacheFailureKind::InvalidRecord,
                "terminalRecord has no kind",
            )
        })?;
    let valid = match (kind, completion) {
        (KeyKind::ExecutionAttempt, CompletionClass::ExactBoundedAttempt) => {
            terminal_kind == "bounded-stop"
        }
        (KeyKind::ExecutionAttempt, CompletionClass::DiagnosticOnly) => {
            terminal_kind == "diagnostic-only"
        }
        (KeyKind::ExecutionAttempt, CompletionClass::SemanticResult) => {
            matches!(terminal_kind, "normal" | "stuck" | "semantic-crash")
        }
        (KeyKind::OracleEvaluation, CompletionClass::SemanticResult) => {
            matches!(terminal_kind, "baseline-gate" | "comparison")
        }
        (KeyKind::OracleEvaluation, _) => false,
    };
    if valid {
        Ok(())
    } else {
        Err(CacheFailure::new(
            CacheFailureKind::CompletionMismatch,
            "completion evidence class is incompatible with terminalRecord",
        ))
    }
}

fn derive_reuse(
    completion: CompletionClass,
    material: MaterialEligibility,
    authority_proven: bool,
) -> ReuseClass {
    if material != MaterialEligibility::Eligible || !authority_proven {
        return ReuseClass::NotReusable;
    }
    match completion {
        CompletionClass::SemanticResult => ReuseClass::SemanticResult,
        CompletionClass::ExactBoundedAttempt => ReuseClass::ExactBoundedAttempt,
        CompletionClass::DiagnosticOnly => ReuseClass::NotReusable,
    }
}

fn validate_finite_vector(
    production: &BTreeMap<String, SemanticJson>,
    key_digest: &Digest,
    terminal: &SemanticJson,
    outputs: &[ArtifactKey],
) -> Result<(), CacheFailure> {
    if production.get("mode").and_then(SemanticJson::as_str) != Some("finite-vector") {
        return Err(CacheFailure::new(
            CacheFailureKind::InvalidProduction,
            "finite witness cannot validate receipt-backed production",
        ));
    }
    let registry = parse_json(include_bytes!(
        "../../../investigations/backend-agnostic-goal-closure/vectors/cache-semantics-vectors.json"
    ))
    .map_err(|error| {
        CacheFailure::new(
            CacheFailureKind::InvalidProduction,
            format!("bundled finite registry is invalid: {error}"),
        )
    })?;
    let vector_id = production
        .get("vectorId")
        .and_then(SemanticJson::as_str)
        .expect("cache record schema checked");
    let vector = registry
        .as_object()
        .and_then(|fields| fields.get("finiteVectorRegistry"))
        .and_then(SemanticJson::as_object)
        .and_then(|vectors| vectors.get(vector_id))
        .and_then(SemanticJson::as_object)
        .ok_or_else(|| {
            CacheFailure::new(
                CacheFailureKind::InvalidProduction,
                "vectorId is not in the bundled finite registry",
            )
        })?;
    if vector.get("kind").and_then(SemanticJson::as_str) != Some("cache-record") {
        return Err(CacheFailure::new(
            CacheFailureKind::InvalidProduction,
            "finite vector does not authorize a cache record",
        ));
    }
    let expected_outputs = SemanticJson::Array(outputs.iter().map(ArtifactKey::to_json).collect());
    if production.get("outputKeys") != Some(&expected_outputs) {
        return Err(CacheFailure::new(
            CacheFailureKind::OutputMismatch,
            "finite production outputKeys differ from the cache record",
        ));
    }
    let expected_roles = SemanticJson::Array(
        outputs
            .iter()
            .map(|key| SemanticJson::String(key.role.clone()))
            .collect(),
    );
    if vector.get("outputRoles") != Some(&expected_roles) {
        return Err(CacheFailure::new(
            CacheFailureKind::OutputMismatch,
            "finite vector output role sequence differs from the cache record",
        ));
    }
    let input_digest = production
        .get("inputDigest")
        .and_then(SemanticJson::as_str)
        .expect("cache record schema checked");
    let row = vector
        .get("rows")
        .and_then(SemanticJson::as_array)
        .and_then(|rows| {
            rows.iter().find(|row| {
                let Some(fields) = row.as_object() else {
                    return false;
                };
                fields
                    .get("inputs")
                    .and_then(SemanticJson::as_object)
                    .and_then(|inputs| inputs.get("keyDigest"))
                    .and_then(SemanticJson::as_str)
                    == Some(key_digest.as_str())
                    && fields.get("inputDigest").and_then(SemanticJson::as_str)
                        == Some(input_digest)
            })
        })
        .and_then(SemanticJson::as_object)
        .ok_or_else(|| {
            CacheFailure::new(
                CacheFailureKind::InvalidProduction,
                "finite production does not match one exact registered input row",
            )
        })?;
    if row.get("terminalRecord") != Some(terminal)
        || row.get("outputKeys") != Some(&expected_outputs)
    {
        return Err(CacheFailure::new(
            CacheFailureKind::InvalidProduction,
            "finite row terminal or ordered outputs differ from the record",
        ));
    }
    Ok(())
}

fn validate_receipt_production(
    production: &BTreeMap<String, SemanticJson>,
    receipt: &ValidatedPortableReceipt,
    key: &RequestKey,
    terminal: &SemanticJson,
    outputs: &[ArtifactKey],
) -> Result<(), CacheFailure> {
    if production.get("mode").and_then(SemanticJson::as_str) != Some("operation-receipt") {
        return Err(CacheFailure::new(
            CacheFailureKind::InvalidProduction,
            "operation receipt witness cannot validate finite-vector production",
        ));
    }
    let receipt_key = production
        .get("receipt")
        .and_then(parse_artifact_key)
        .expect("cache record schema checked");
    let result_key = production
        .get("result")
        .and_then(parse_artifact_key)
        .expect("cache record schema checked");
    if receipt_key.role != "operation-receipt"
        || receipt_key.digest != *receipt.receipt_id()
        || result_key != *receipt.result()
    {
        return Err(CacheFailure::new(
            CacheFailureKind::InvalidProduction,
            "record productionEvidence does not name the supplied receipt/wrapper",
        ));
    }
    if !BUNDLED_RECEIPT_RESULTS
        .iter()
        .any(|(known_receipt, known_result)| {
            known_receipt == &receipt_key.digest.as_str()
                && known_result == &result_key.digest.as_str()
        })
    {
        return Err(CacheFailure::new(
            CacheFailureKind::InvalidProduction,
            "receipt/wrapper pair is not a reviewed bundled finite production",
        ));
    }
    let wrapper = receipt.wrapper().as_object().expect("wrapper validated");
    match key.kind() {
        KeyKind::ExecutionAttempt => {
            if receipt.operation() != crate::receipt::OperationKind::ExecutionAttempt
                || result_key.role != "execution-attempt-result"
                || wrapper.get("keyDigest").and_then(SemanticJson::as_str)
                    != Some(key.key_digest().as_str())
            {
                return Err(CacheFailure::new(
                    CacheFailureKind::InvalidProduction,
                    "execution cache record names another key or operation",
                ));
            }
        }
        KeyKind::OracleEvaluation => {
            let expected_role = match key
                .as_json()
                .as_object()
                .and_then(|fields| fields.get("evaluationKind"))
                .and_then(SemanticJson::as_str)
            {
                Some("baseline-admission") => "baseline-admission-result",
                Some("baseline-mutant-comparison") => "oracle-comparison-production-result",
                _ => unreachable!("oracle key schema checked"),
            };
            if result_key.role != expected_role
                || wrapper.get("evaluationKey") != Some(key.as_json())
            {
                return Err(CacheFailure::new(
                    CacheFailureKind::InvalidProduction,
                    "oracle cache record names another key or wrapper family",
                ));
            }
        }
    }
    let expected_outputs = SemanticJson::Array(outputs.iter().map(ArtifactKey::to_json).collect());
    if wrapper.get("terminalRecord") != Some(terminal)
        || wrapper.get("producedArtifacts") != Some(&expected_outputs)
    {
        return Err(CacheFailure::new(
            CacheFailureKind::OutputMismatch,
            "receipt wrapper terminal or ordered outputs differ from the record",
        ));
    }
    Ok(())
}

const BUNDLED_RECEIPT_RESULTS: &[(&str, &str)] = &[
    (
        "1e8b6ff98974326cf07d527d3999159090067db49cef14e5183e7ba59c858781",
        "e36085047711a44910d0c4dd7e1fa2e11e142daf69e477253991ed29371c8684",
    ),
    (
        "972e83349a21a131f1c29b1ed49df92e15e59839e3fab1d708bb54df423e8b1a",
        "66fbc9c90f7a0eee2a47ec015951d230ab38b201d8178c79af514159f299414f",
    ),
    (
        "cdc06b66db2f2490079f0934540dd7e04b44cf4a990a05e078222d68d6fca404",
        "a9725f51f41e20d709a25f7efb308b9c550bcd73af718f36741b80e1ec28c332",
    ),
    (
        "1c2c972889a026848854335836bee6a3485b643d74992e1460047bdd19f01e87",
        "1a4abd9c4a6bbeb959751df02b7bf537fec8494760cd44d073ac29f0b5a65d44",
    ),
    (
        "7b902bdf4e1c5d5d324ba0eb0ba6c5f0ce6825d253f3db55e79a110e2b72ba83",
        "ff55a7933fd12e42927e236e5cf10f7be85ed0ecb5e3a1c68a5a7d2e093aec35",
    ),
    (
        "d35629386231fb8abd08336730cb7f31edfdd7975bd505d37c7a56b9060c014f",
        "aaf46685595c384089f2150ed928889bd723b315986c250d07e4e602357ecd88",
    ),
    (
        "88d0e0360d5c49f759417c3193c4214e8d9915f0f782b1b24c81de465dd1e89f",
        "4a51e874d5b6f00d7fbb4e800ac7ebd4a929f221c4b6eebf84fd7ed8d22bb9e0",
    ),
    (
        "af91490c696b732e5f859226ca18be779533cd11a94f21f175c654100595bb92",
        "421d99f76880ef96e9625a92b127a186d1478318bebf42b794eee9916bf3561b",
    ),
    (
        "103a09b9f7511ec81512d2b95823ac0a798ca1c156511713372c0eef11091075",
        "fe5e4fb62bc2f579aabe17994a2be8d1cc77875a4a7ef417a4a718f2c1c35cd9",
    ),
    (
        "a40c6f33392d85ffe60690ef24bb32676edf1589a34c62cf51cd76c0c4c17b4d",
        "e3d2e90a74bcf0ac4633b913ca454e1b6a5e0f006e5425c975cb49c6b24986b2",
    ),
    (
        "4973c4afded001fd53e850f21804d8a353858e8af9e751e26b322032a6251b9a",
        "d1172b217483375d3f76a1087d9b010299dffc8dcf655e72c4d6c0c4575fc786",
    ),
    (
        "a92970403fc8725887d09127bf4549a84d56bdc0e7f32d87f4de0815d9c3dddc",
        "4857154d4006c4091c2f1b4285e31fd5e553c3ac0f42200e466949a8bde5cfa6",
    ),
];

/// Result of an atomic in-memory publication request.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Publication {
    /// New immutable record inserted.
    Published,
    /// Exact repeat of the already-published record.
    AlreadyPresent,
    /// Same-key conflict quarantined; no candidate is reusable.
    Quarantined,
}

/// In-memory cache seam with permanent same-key conflict quarantine.
#[derive(Clone, Debug, Default)]
pub struct CacheStore {
    active: BTreeMap<Digest, CacheRecord>,
    quarantined: BTreeSet<Digest>,
}

impl CacheStore {
    /// Atomically publishes a previously validated immutable record.
    pub fn publish(&mut self, record: CacheRecord) -> Publication {
        let key = record.key.key_digest.clone();
        if self.quarantined.contains(&key) {
            return Publication::Quarantined;
        }
        match self.active.get(&key) {
            None => {
                self.active.insert(key, record);
                Publication::Published
            }
            Some(existing) if existing == &record => Publication::AlreadyPresent,
            Some(_) => {
                self.active.remove(&key);
                self.quarantined.insert(key);
                Publication::Quarantined
            }
        }
    }

    /// Returns a reusable record only when the key is active, unquarantined, and reusable.
    #[must_use]
    pub fn reusable(&self, key: &Digest) -> Option<&CacheRecord> {
        if self.quarantined.contains(key) {
            return None;
        }
        self.active
            .get(key)
            .filter(|record| record.reuse_class != ReuseClass::NotReusable)
    }

    /// Reports whether conflicting validated values permanently quarantined this key.
    #[must_use]
    pub fn is_quarantined(&self, key: &Digest) -> bool {
        self.quarantined.contains(key)
    }
}

fn parse_digest(value: Option<&SemanticJson>, name: &str) -> Result<Digest, CacheFailure> {
    Digest::parse(value.and_then(SemanticJson::as_str).ok_or_else(|| {
        CacheFailure::new(
            CacheFailureKind::InvalidRecord,
            format!("{name} must be a digest string"),
        )
    })?)
    .map_err(|_| {
        CacheFailure::new(
            CacheFailureKind::InvalidRecord,
            format!("{name} is not lowercase SHA-256"),
        )
    })
}

/// Closed cache validation/publication failures.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CacheFailureKind {
    /// Raw key is not one exact request-key shape.
    InvalidKey,
    /// Constructor received a forbidden identity/result field.
    ForbiddenKeyField,
    /// A key self-ID or repeated key digest drifted.
    KeyDigestMismatch,
    /// Cache record is outside the exact frozen shape.
    InvalidRecord,
    /// Cache record self identity drifted.
    RecordDigestMismatch,
    /// Completion class and terminal/result arm disagree.
    CompletionMismatch,
    /// Claimed intrinsic reuse differs from derived reuse.
    ReuseMismatch,
    /// Finite or receipt production authority is absent or contradictory.
    InvalidProduction,
    /// Native authority is not constructible through the portable API.
    NativeAuthorityUnavailable,
    /// Failed producer attempted publication.
    ProducerFailed,
    /// Complete producer has no wrapper.
    MissingOutput,
    /// Wrapper/cache output sequences differ.
    OutputMismatch,
    /// Output sequence repeats an artifact.
    DuplicateOutput,
    /// Produced material failed validation.
    InvalidMaterial,
}

/// Typed cache failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CacheFailure {
    kind: CacheFailureKind,
    detail: String,
}

impl CacheFailure {
    fn new(kind: CacheFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Decision-bearing classification.
    #[must_use]
    pub const fn kind(&self) -> CacheFailureKind {
        self.kind
    }
}

impl fmt::Display for CacheFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for CacheFailure {}
