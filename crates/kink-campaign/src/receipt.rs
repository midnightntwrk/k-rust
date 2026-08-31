use kink_contracts::{Completeness, ContentModel, EvidenceClass, MediaType, NativeConformance};
use kink_portable::{
    Digest, DigestDomain, IngressedArtifact, SemanticJson, canonical_json_bytes, digest,
    digest_without_field, parse_json, sha256_bytes,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// A role-typed semantic artifact identity.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ArtifactKey {
    /// Registered artifact role.
    pub role: String,
    /// Role-domain semantic digest.
    pub digest: Digest,
}

impl ArtifactKey {
    /// Constructs a key and rejects role spellings outside the portable registry grammar.
    pub fn new(role: impl Into<String>, digest: Digest) -> Result<Self, InvocationFailure> {
        let role = role.into();
        if role.is_empty()
            || !role
                .bytes()
                .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
        {
            return Err(InvocationFailure::new(
                InvocationFailureKind::InvalidArtifactRole,
                "artifact role is not lowercase ASCII kebab-case",
            ));
        }
        Ok(Self { role, digest })
    }

    pub(crate) fn to_json(&self) -> SemanticJson {
        object([
            ("digest", string(self.digest.as_str())),
            ("role", string(&self.role)),
        ])
    }
}

/// A typed dataflow edge.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactEdge {
    /// Operation-specific edge role.
    pub edge_role: String,
    /// Referenced artifact.
    pub artifact: ArtifactKey,
}

/// The seven frozen BAG-15 operations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OperationKind {
    /// Mutation materialization.
    MutationMaterialization,
    /// Isolated execution attempt.
    ExecutionAttempt,
    /// Oracle operand production.
    OracleOperandProduction,
    /// Baseline oracle admission.
    BaselineAdmission,
    /// Baseline-mutant oracle comparison.
    OracleComparison,
    /// Schedule-specific campaign derivation.
    CampaignDerivation,
    /// Final report publication.
    ReportPublication,
}

impl OperationKind {
    /// Frozen operation spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MutationMaterialization => "mutation-materialization",
            Self::ExecutionAttempt => "execution-attempt",
            Self::OracleOperandProduction => "oracle-operand-production",
            Self::BaselineAdmission => "baseline-admission",
            Self::OracleComparison => "oracle-comparison",
            Self::CampaignDerivation => "campaign-derivation",
            Self::ReportPublication => "report-publication",
        }
    }

    /// The sole wrapper role a complete invocation may publish.
    #[must_use]
    pub const fn output_role(self) -> &'static str {
        match self {
            Self::MutationMaterialization => "mutation-materialization-result",
            Self::ExecutionAttempt => "execution-attempt-result",
            Self::OracleOperandProduction => "oracle-operand-production-result",
            Self::BaselineAdmission => "baseline-admission-result",
            Self::OracleComparison => "oracle-comparison-production-result",
            Self::CampaignDerivation => "campaign-derivation-result",
            Self::ReportPublication => "report-publication-result",
        }
    }
}

/// Exact adapter identity carried by an operation request.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdapterContract {
    /// Stable adapter ID.
    pub adapter_id: String,
    /// Positive adapter contract version.
    pub adapter_version: u32,
}

/// A cycle-free operation request. It contains no output or expected-result identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OperationInvocation {
    /// Operation kind.
    pub operation_kind: OperationKind,
    /// Positive operation contract version.
    pub operation_version: u32,
    /// Adapter contract.
    pub adapter: AdapterContract,
    /// Closed operation-specific parameters.
    pub parameters: SemanticJson,
    /// Ordered typed inputs.
    pub inputs: Vec<ArtifactEdge>,
    /// Ordered child receipt keys.
    pub child_receipts: Vec<ArtifactEdge>,
    /// Derived cycle-free identity.
    pub invocation_digest: Digest,
}

impl OperationInvocation {
    /// Validates and derives an operation invocation.
    pub fn new(
        operation_kind: OperationKind,
        operation_version: u32,
        adapter: AdapterContract,
        parameters: SemanticJson,
        inputs: Vec<ArtifactEdge>,
        child_receipts: Vec<ArtifactEdge>,
    ) -> Result<Self, InvocationFailure> {
        if operation_version == 0 || adapter.adapter_version == 0 {
            return Err(InvocationFailure::new(
                InvocationFailureKind::InvalidVersion,
                "operation and adapter versions must be positive",
            ));
        }
        if !matches!(parameters, SemanticJson::Object(_)) {
            return Err(InvocationFailure::new(
                InvocationFailureKind::InvalidParameters,
                "operation parameters must be a closed object",
            ));
        }
        let output_roles = vec![string(operation_kind.output_role())];
        let value = object([
            (
                "adapterContract",
                object([
                    ("adapterId", string(&adapter.adapter_id)),
                    ("adapterVersion", integer(adapter.adapter_version)),
                ]),
            ),
            (
                "childReceipts",
                SemanticJson::Array(child_receipts.iter().map(edge_json).collect()),
            ),
            (
                "inputs",
                SemanticJson::Array(inputs.iter().map(edge_json).collect()),
            ),
            ("operationKind", string(operation_kind.as_str())),
            ("operationVersion", integer(operation_version)),
            ("outputRoles", SemanticJson::Array(output_roles)),
            ("parameters", parameters.clone()),
            ("schemaVersion", SemanticJson::Integer(1)),
        ]);
        let invocation_digest =
            digest(&domain("k-in-k/operation-invocation/v1"), &value).map_err(|error| {
                InvocationFailure::new(
                    InvocationFailureKind::InvalidShape,
                    format!("operation invocation is not valid semantic JSON: {error}"),
                )
            })?;
        Ok(Self {
            operation_kind,
            operation_version,
            adapter,
            parameters,
            inputs,
            child_receipts,
            invocation_digest,
        })
    }
}

fn edge_json(edge: &ArtifactEdge) -> SemanticJson {
    let key = if edge.artifact.role == "operation-receipt" {
        "receipt"
    } else {
        "artifact"
    };
    object([
        ("edgeRole", string(&edge.edge_role)),
        (key, edge.artifact.to_json()),
    ])
}

/// Operation producer identity and authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Producer {
    /// Stable producer ID.
    producer_id: String,
    /// Positive producer implementation version.
    producer_version: u32,
    /// Evidence authority.
    evidence: EvidenceClass,
    /// Native conformance remains separate from evidence class.
    native_conformance: NativeConformance,
}

impl Producer {
    /// A deterministic scripted producer, which can never claim native proof.
    #[must_use]
    pub fn scripted(id: impl Into<String>, version: u32) -> Self {
        Self {
            producer_id: id.into(),
            producer_version: version,
            evidence: EvidenceClass::Scripted,
            native_conformance: NativeConformance::NotProven,
        }
    }

    /// Returns the evidence class fixed by this producer constructor.
    #[must_use]
    pub const fn evidence(&self) -> EvidenceClass {
        self.evidence
    }

    /// Returns the native-conformance class fixed by this producer constructor.
    #[must_use]
    pub const fn native_conformance(&self) -> NativeConformance {
        self.native_conformance
    }
}

/// Receipt producer state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProducerStatus {
    /// Production completed and exactly one wrapper exists.
    Complete,
    /// Production failed and no output exists.
    Failed,
}

/// The single wrapper published by a complete operation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReceiptOutput {
    /// Wrapper identity.
    pub wrapper: ArtifactKey,
    /// Nested semantic terminal, when the operation has one.
    pub semantic_terminal: Option<ArtifactKey>,
    /// Exact ordered nested artifacts.
    pub produced_artifacts: Vec<ArtifactKey>,
    /// Result completeness.
    pub completeness: Completeness,
}

/// Exact BAG-15 receipt validation namespace.
///
/// Portable receipts are returned as [`ValidatedPortableReceipt`]. Scripted
/// diagnostics use the explicitly nonportable [`ScriptedReceipt`] seam, so a
/// reduced internal value cannot be mistaken for the frozen receipt shape.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OperationReceipt;

/// An explicitly nonportable scripted receipt used only at the diagnostic seam.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScriptedReceipt {
    pub(crate) invocation: OperationInvocation,
    pub(crate) producer: Producer,
    pub(crate) status: ProducerStatus,
    pub(crate) output: Option<ReceiptOutput>,
    pub(crate) receipt_id: Digest,
}

/// A schema-exact portable receipt and its independently validated result wrapper.
///
/// This type deliberately carries no native authority. The constructor rejects
/// `native-proven`, and cache reuse additionally requires a frozen production
/// witness selected by the cache module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidatedPortableReceipt {
    receipt_id: Digest,
    invocation_digest: Digest,
    operation: OperationKind,
    result: ArtifactKey,
    semantic_terminal: SemanticJson,
    wrapper: SemanticJson,
}

/// Maximal checked input tuple for a future native pattern-compiler receipt.
///
/// The frozen registry deliberately has no compiler-receipt role, schema, digest
/// domain, diagnostics field, or positive compiler fixture. Consequently this
/// value is only a checked candidate: it revalidates the supplied source,
/// normalized plan, named query, and compiler-profile artifacts and their
/// nested identities against frozen role projections, but it does not prove
/// catalog/registry membership or resolver eligibility, is not a receipt, and
/// carries no native authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckedCompilerReceiptCandidate {
    source: ArtifactKey,
    plan: ArtifactKey,
    query: ArtifactKey,
    compiler_profile: ArtifactKey,
    entry_module: String,
    exported_name: String,
}

impl CheckedCompilerReceiptCandidate {
    /// Revalidates every frozen artifact and the complete source/plan/query join.
    pub fn validate_frozen_inputs(
        source: &IngressedArtifact,
        plan: &IngressedArtifact,
        query: &IngressedArtifact,
        compiler_profile: &IngressedArtifact,
    ) -> Result<Self, InvocationFailure> {
        revalidate_frozen_artifact(source, "pattern-source")?;
        revalidate_frozen_artifact(plan, "pattern-plan")?;
        revalidate_frozen_artifact(query, "pattern-query")?;
        revalidate_frozen_artifact(compiler_profile, "pattern-compiler-profile")?;

        let query_value = query.semantic_json.as_ref().expect("role checked above");
        let query_fields = query_value.as_object().expect("schema checked above");
        let nested_source = query_fields
            .get("patternSource")
            .and_then(parse_artifact_key)
            .expect("schema checked above");
        let nested_plan = query_fields
            .get("patternPlan")
            .and_then(parse_artifact_key)
            .expect("schema checked above");
        if nested_source.role != source.entry.role
            || nested_source.digest != source.entry.digest
            || nested_plan.role != plan.entry.role
            || nested_plan.digest != plan.entry.digest
        {
            return Err(InvocationFailure::new(
                InvocationFailureKind::CompilerInputMismatch,
                "pattern query does not bind the supplied source and normalized plan",
            ));
        }
        let entry_module = query_fields
            .get("entryModule")
            .and_then(SemanticJson::as_str)
            .expect("schema checked above")
            .to_owned();
        let exported_name = query_fields
            .get("exportedName")
            .and_then(SemanticJson::as_str)
            .expect("schema checked above")
            .to_owned();
        Ok(Self {
            source: artifact_key(source),
            plan: artifact_key(plan),
            query: artifact_key(query),
            compiler_profile: artifact_key(compiler_profile),
            entry_module,
            exported_name,
        })
    }

    /// Rederived exact source key.
    #[must_use]
    pub fn source(&self) -> &ArtifactKey {
        &self.source
    }

    /// Rederived exact normalized-plan key.
    #[must_use]
    pub fn plan(&self) -> &ArtifactKey {
        &self.plan
    }

    /// Rederived exact named-query key.
    #[must_use]
    pub fn query(&self) -> &ArtifactKey {
        &self.query
    }

    /// Rederived exact compiler-profile key.
    #[must_use]
    pub fn compiler_profile(&self) -> &ArtifactKey {
        &self.compiler_profile
    }

    /// Entry module bound by the self-identified query.
    #[must_use]
    pub fn entry_module(&self) -> &str {
        &self.entry_module
    }

    /// Exported name bound by the self-identified query.
    #[must_use]
    pub fn exported_name(&self) -> &str {
        &self.exported_name
    }
}

impl ValidatedPortableReceipt {
    /// Receipt identity rederived from the exact portable value.
    #[must_use]
    pub fn receipt_id(&self) -> &Digest {
        &self.receipt_id
    }

    /// Cycle-free invocation identity rederived from the nested invocation.
    #[must_use]
    pub fn invocation_digest(&self) -> &Digest {
        &self.invocation_digest
    }

    /// Frozen operation family.
    #[must_use]
    pub const fn operation(&self) -> OperationKind {
        self.operation
    }

    /// Sole result-wrapper key.
    #[must_use]
    pub fn result(&self) -> &ArtifactKey {
        &self.result
    }

    /// Exact semantic terminal repeated by the receipt.
    #[must_use]
    pub fn semantic_terminal(&self) -> &SemanticJson {
        &self.semantic_terminal
    }

    /// Independently schema- and identity-validated wrapper.
    #[must_use]
    pub fn wrapper(&self) -> &SemanticJson {
        &self.wrapper
    }
}

impl OperationReceipt {
    /// Validates one frozen portable receipt without treating it as native authority.
    pub fn validate_portable_json(value: &SemanticJson) -> Result<Digest, InvocationFailure> {
        let fields = value.as_object().ok_or_else(|| {
            InvocationFailure::new(
                InvocationFailureKind::InvalidShape,
                "operation receipt must be an object",
            )
        })?;
        let invocation = fields
            .get("invocation")
            .and_then(SemanticJson::as_object)
            .ok_or_else(|| {
                InvocationFailure::new(
                    InvocationFailureKind::InvalidShape,
                    "receipt invocation must be an object",
                )
            })?;
        let invocation_value = fields.get("invocation").expect("checked above");
        let expected_invocation = parse_digest_field(fields, "invocationDigest")?;
        let nested_invocation = parse_digest_field(invocation, "invocationDigest")?;
        let derived_invocation = digest_without_field(
            &domain("k-in-k/operation-invocation/v1"),
            invocation_value,
            "invocationDigest",
        )
        .map_err(|_| {
            InvocationFailure::new(
                InvocationFailureKind::InvalidShape,
                "invocation self-ID projection failed",
            )
        })?;
        if expected_invocation != nested_invocation || expected_invocation != derived_invocation {
            return Err(InvocationFailure::new(
                InvocationFailureKind::DigestMismatch,
                "receipt and invocation identities disagree",
            ));
        }
        let operation = invocation
            .get("operationKind")
            .and_then(SemanticJson::as_str)
            .and_then(parse_operation)
            .ok_or_else(|| {
                InvocationFailure::new(
                    InvocationFailureKind::InvalidShape,
                    "operationKind is not one of the seven registered operations",
                )
            })?;
        let Some(SemanticJson::Array(output_roles)) = invocation.get("outputRoles") else {
            return Err(InvocationFailure::new(
                InvocationFailureKind::InvalidShape,
                "outputRoles must be an array",
            ));
        };
        if output_roles.as_slice() != [string(operation.output_role())] {
            return Err(InvocationFailure::new(
                InvocationFailureKind::WrongOutputRole,
                "invocation must request exactly its operation-specific wrapper",
            ));
        }
        let status = fields
            .get("producerStatus")
            .and_then(SemanticJson::as_str)
            .ok_or_else(|| {
                InvocationFailure::new(
                    InvocationFailureKind::InvalidShape,
                    "producerStatus must be a string",
                )
            })?;
        let Some(SemanticJson::Array(outputs)) = fields.get("outputs") else {
            return Err(InvocationFailure::new(
                InvocationFailureKind::InvalidShape,
                "receipt outputs must be an array",
            ));
        };
        match status {
            "complete" => {
                if outputs.len() != 1 {
                    return Err(InvocationFailure::new(
                        InvocationFailureKind::WrongOutputArity,
                        "complete receipt must publish exactly one wrapper",
                    ));
                }
                let actual_role = outputs[0]
                    .as_object()
                    .and_then(|edge| edge.get("artifact"))
                    .and_then(SemanticJson::as_object)
                    .and_then(|artifact| artifact.get("role"))
                    .and_then(SemanticJson::as_str);
                if actual_role != Some(operation.output_role()) {
                    return Err(InvocationFailure::new(
                        InvocationFailureKind::WrongOutputRole,
                        "complete receipt wrapper does not match the operation",
                    ));
                }
            }
            "failed" => {
                if !outputs.is_empty()
                    || !matches!(fields.get("semanticTerminal"), Some(SemanticJson::Null))
                {
                    return Err(InvocationFailure::new(
                        InvocationFailureKind::FailedProducerOutput,
                        "failed producer must publish no output or semantic terminal",
                    ));
                }
            }
            _ => {
                return Err(InvocationFailure::new(
                    InvocationFailureKind::InvalidShape,
                    "producerStatus must be complete or failed",
                ));
            }
        }
        let execution_conformance = fields
            .get("producer")
            .and_then(SemanticJson::as_object)
            .and_then(|producer| producer.get("executionConformance"))
            .and_then(SemanticJson::as_str);
        if execution_conformance == Some("native-proven") {
            return Err(InvocationFailure::new(
                InvocationFailureKind::NativeAuthorityMismatch,
                "portable receipt validation cannot establish native authority",
            ));
        }
        validate_v1_schema(
            value,
            "https://starstream.dev/k-in-k/backend-agnostic/v1/operation-receipt.schema.json",
        )
        .map_err(|detail| InvocationFailure::new(InvocationFailureKind::InvalidShape, detail))?;
        let expected_receipt = parse_digest_field(fields, "receiptId")?;
        let derived_receipt =
            digest_without_field(&domain("k-in-k/operation-receipt/v1"), value, "receiptId")
                .map_err(|_| {
                    InvocationFailure::new(
                        InvocationFailureKind::InvalidShape,
                        "receipt self-ID projection failed",
                    )
                })?;
        if expected_receipt != derived_receipt {
            return Err(InvocationFailure::new(
                InvocationFailureKind::DigestMismatch,
                "receiptId does not match the normalized receipt",
            ));
        }
        Ok(derived_receipt)
    }

    /// Validates a frozen receipt together with the only wrapper it publishes.
    ///
    /// The operation-specific schema validates parameters, input edges, child
    /// receipts, wrapper role, terminal arm, and failure placement. Rust then
    /// rederives both identities and all receipt/wrapper repetitions.
    pub fn validate_portable_bundle(
        receipt: &SemanticJson,
        wrapper: &SemanticJson,
    ) -> Result<ValidatedPortableReceipt, InvocationFailure> {
        let receipt_id = Self::validate_portable_json(receipt)?;
        let receipt_fields = receipt.as_object().expect("receipt schema checked");
        let invocation = receipt_fields
            .get("invocation")
            .and_then(SemanticJson::as_object)
            .expect("receipt schema checked");
        let operation = invocation
            .get("operationKind")
            .and_then(SemanticJson::as_str)
            .and_then(parse_operation)
            .expect("receipt schema checked");
        if receipt_fields
            .get("producerStatus")
            .and_then(SemanticJson::as_str)
            != Some("complete")
        {
            return Err(InvocationFailure::new(
                InvocationFailureKind::FailedProducerOutput,
                "failed producer has no result wrapper to validate",
            ));
        }
        let wrapper_reference = format!(
            "https://starstream.dev/k-in-k/backend-agnostic/v1/{}.schema.json",
            operation.output_role()
        );
        validate_v1_schema(wrapper, &wrapper_reference).map_err(|detail| {
            InvocationFailure::new(InvocationFailureKind::InvalidShape, detail)
        })?;
        let wrapper_fields = wrapper.as_object().expect("wrapper schema checked");
        let result_id = parse_digest_field(wrapper_fields, "resultId")?;
        let derived_result = digest_without_field(
            &domain(&format!("k-in-k/{}/v1", operation.output_role())),
            wrapper,
            "resultId",
        )
        .map_err(|error| {
            InvocationFailure::new(
                InvocationFailureKind::InvalidShape,
                format!("result wrapper self-ID projection failed: {error}"),
            )
        })?;
        if result_id != derived_result {
            return Err(InvocationFailure::new(
                InvocationFailureKind::DigestMismatch,
                "resultId does not match the normalized operation wrapper",
            ));
        }
        let output = receipt_fields
            .get("outputs")
            .and_then(SemanticJson::as_array)
            .and_then(|outputs| outputs.first())
            .and_then(SemanticJson::as_object)
            .and_then(|edge| edge.get("artifact"))
            .and_then(parse_artifact_key)
            .expect("complete receipt schema checked");
        if output.role != operation.output_role() || output.digest != result_id {
            return Err(InvocationFailure::new(
                InvocationFailureKind::DigestMismatch,
                "receipt output does not identify the supplied wrapper",
            ));
        }
        let invocation_digest = parse_digest_field(invocation, "invocationDigest")?;
        if wrapper_fields
            .get("invocationDigest")
            .and_then(SemanticJson::as_str)
            != Some(invocation_digest.as_str())
        {
            return Err(InvocationFailure::new(
                InvocationFailureKind::DigestMismatch,
                "wrapper names another operation invocation",
            ));
        }
        let terminal_field = match operation {
            OperationKind::ExecutionAttempt
            | OperationKind::BaselineAdmission
            | OperationKind::OracleComparison => "terminalRecord",
            OperationKind::MutationMaterialization
            | OperationKind::OracleOperandProduction
            | OperationKind::CampaignDerivation
            | OperationKind::ReportPublication => "outcome",
        };
        let semantic_terminal = wrapper_fields
            .get(terminal_field)
            .expect("wrapper schema checked");
        if receipt_fields.get("semanticTerminal") != Some(semantic_terminal) {
            return Err(InvocationFailure::new(
                InvocationFailureKind::WrapperCorrespondence,
                "receipt semanticTerminal differs from the supplied wrapper",
            ));
        }
        let expected_failure = selected_failure(semantic_terminal);
        if receipt_fields.get("failure") != Some(expected_failure) {
            return Err(InvocationFailure::new(
                InvocationFailureKind::WrapperCorrespondence,
                "receipt failure differs from the supplied wrapper terminal",
            ));
        }
        if operation != OperationKind::ExecutionAttempt
            && wrapper_fields.get("failure") != Some(expected_failure)
        {
            return Err(InvocationFailure::new(
                InvocationFailureKind::WrapperCorrespondence,
                "wrapper top-level failure differs from its terminal",
            ));
        }
        Ok(ValidatedPortableReceipt {
            receipt_id,
            invocation_digest,
            operation,
            result: output,
            semantic_terminal: semantic_terminal.clone(),
            wrapper: wrapper.clone(),
        })
    }
}

impl ScriptedReceipt {
    /// Constructs a nonportable complete scripted receipt for diagnostic seams.
    pub fn complete(
        invocation: OperationInvocation,
        producer: Producer,
        output: ReceiptOutput,
    ) -> Result<Self, InvocationFailure> {
        if output.wrapper.role != invocation.operation_kind.output_role() {
            return Err(InvocationFailure::new(
                InvocationFailureKind::WrongOutputRole,
                "wrapper role does not match the operation registry",
            ));
        }
        let mut unique = BTreeSet::new();
        if !output
            .produced_artifacts
            .iter()
            .all(|key| unique.insert(key.clone()))
        {
            return Err(InvocationFailure::new(
                InvocationFailureKind::DuplicateOutput,
                "produced artifact sequence contains a duplicate",
            ));
        }
        if producer.native_conformance == NativeConformance::NativeProven
            && producer.evidence != EvidenceClass::NativeProven
        {
            return Err(InvocationFailure::new(
                InvocationFailureKind::NativeAuthorityMismatch,
                "native conformance requires native-proven evidence",
            ));
        }
        let receipt_id = scripted_receipt_id(
            &invocation,
            &producer,
            ProducerStatus::Complete,
            Some(&output),
        );
        Ok(Self {
            invocation,
            producer,
            status: ProducerStatus::Complete,
            output: Some(output),
            receipt_id,
        })
    }

    /// Constructs a nonportable failed scripted receipt with no wrapper or terminal.
    #[must_use]
    pub fn failed(invocation: OperationInvocation, producer: Producer) -> Self {
        let receipt_id = scripted_receipt_id(&invocation, &producer, ProducerStatus::Failed, None);
        Self {
            invocation,
            producer,
            status: ProducerStatus::Failed,
            output: None,
            receipt_id,
        }
    }
}

fn scripted_receipt_id(
    invocation: &OperationInvocation,
    producer: &Producer,
    status: ProducerStatus,
    output: Option<&ReceiptOutput>,
) -> Digest {
    let output = output.map_or(SemanticJson::Null, |value| {
        object([
            ("wrapper", value.wrapper.to_json()),
            (
                "semanticTerminal",
                value
                    .semantic_terminal
                    .as_ref()
                    .map_or(SemanticJson::Null, ArtifactKey::to_json),
            ),
            (
                "producedArtifacts",
                SemanticJson::Array(
                    value
                        .produced_artifacts
                        .iter()
                        .map(ArtifactKey::to_json)
                        .collect(),
                ),
            ),
            (
                "completeness",
                string(completeness_name(value.completeness)),
            ),
        ])
    });
    let value = object([
        (
            "invocationDigest",
            string(invocation.invocation_digest.as_str()),
        ),
        ("output", output),
        (
            "producer",
            object([
                ("producerId", string(&producer.producer_id)),
                ("producerVersion", integer(producer.producer_version)),
                ("evidence", string(evidence_name(producer.evidence))),
                (
                    "nativeConformance",
                    string(match producer.native_conformance {
                        NativeConformance::NotProven => "not-proven",
                        NativeConformance::NativeProven => "native-proven",
                    }),
                ),
            ]),
        ),
        (
            "producerStatus",
            string(match status {
                ProducerStatus::Complete => "complete",
                ProducerStatus::Failed => "failed",
            }),
        ),
        ("schemaVersion", SemanticJson::Integer(1)),
    ]);
    digest(&domain("k-in-k/scripted-operation-receipt/v1"), &value)
        .expect("validated scripted receipt fields form semantic JSON")
}

fn parse_operation(value: &str) -> Option<OperationKind> {
    Some(match value {
        "mutation-materialization" => OperationKind::MutationMaterialization,
        "execution-attempt" => OperationKind::ExecutionAttempt,
        "oracle-operand-production" => OperationKind::OracleOperandProduction,
        "baseline-admission" => OperationKind::BaselineAdmission,
        "oracle-comparison" => OperationKind::OracleComparison,
        "campaign-derivation" => OperationKind::CampaignDerivation,
        "report-publication" => OperationKind::ReportPublication,
        _ => return None,
    })
}

fn parse_digest_field(
    fields: &BTreeMap<String, SemanticJson>,
    name: &str,
) -> Result<Digest, InvocationFailure> {
    let value = fields
        .get(name)
        .and_then(SemanticJson::as_str)
        .ok_or_else(|| {
            InvocationFailure::new(
                InvocationFailureKind::InvalidShape,
                format!("{name} must be a digest string"),
            )
        })?;
    Digest::parse(value).map_err(|_| {
        InvocationFailure::new(
            InvocationFailureKind::InvalidShape,
            format!("{name} is not lowercase SHA-256"),
        )
    })
}

pub(crate) fn object<const N: usize>(values: [(&str, SemanticJson); N]) -> SemanticJson {
    SemanticJson::Object(
        values
            .into_iter()
            .map(|(key, value)| (key.to_owned(), value))
            .collect::<BTreeMap<_, _>>(),
    )
}

pub(crate) fn string(value: &str) -> SemanticJson {
    SemanticJson::String(value.to_owned())
}

pub(crate) fn integer(value: u32) -> SemanticJson {
    SemanticJson::Integer(i64::from(value))
}

pub(crate) fn domain(value: &str) -> DigestDomain {
    DigestDomain::new(value).expect("static portable digest domain is valid")
}

pub(crate) fn parse_artifact_key(value: &SemanticJson) -> Option<ArtifactKey> {
    let fields = value.as_object()?;
    let role = fields.get("role")?.as_str()?;
    let digest = Digest::parse(fields.get("digest")?.as_str()?).ok()?;
    ArtifactKey::new(role, digest).ok()
}

fn artifact_key(artifact: &IngressedArtifact) -> ArtifactKey {
    ArtifactKey {
        role: artifact.entry.role.clone(),
        digest: artifact.entry.digest.clone(),
    }
}

/// Independently revalidates one supplied artifact against an admitted frozen projection.
///
/// `IngressedArtifact` has public fields for transport, so native validator
/// boundaries must not treat construction of that value alone as evidence.
/// This check does not prove catalog/registry membership or resolver eligibility.
pub(crate) fn revalidate_frozen_artifact(
    artifact: &IngressedArtifact,
    expected_role: &str,
) -> Result<(), InvocationFailure> {
    if artifact.entry.role != expected_role {
        return Err(InvocationFailure::new(
            InvocationFailureKind::CompilerInputMismatch,
            format!("expected {expected_role}, received {}", artifact.entry.role),
        ));
    }
    let content_sha256 = sha256_bytes(&artifact.bytes);
    if content_sha256 != artifact.entry.content_sha256 {
        return Err(InvocationFailure::new(
            InvocationFailureKind::DigestMismatch,
            format!("{expected_role} byte digest drift"),
        ));
    }
    let structured = match expected_role {
        "compatibility-profile" => Some((
            "https://starstream.dev/k-in-k/backend-agnostic/v1/compatibility-profile.schema.json",
            "k-in-k/compatibility-profile/v1",
            None,
        )),
        "pattern-plan" => Some((
            "https://starstream.dev/k-in-k/backend-agnostic/v1/pattern-plan.schema.json",
            "k-in-k/pattern-plan/v1",
            Some("patternPlanDigest"),
        )),
        "pattern-query" => Some((
            "https://starstream.dev/k-in-k/backend-agnostic/v1/pattern-query.schema.json",
            "k-in-k/pattern-query/v1",
            Some("queryId"),
        )),
        "predicate-plan" => Some((
            "https://starstream.dev/k-in-k/backend-agnostic/v1/predicate-semantics.schema.json#/$defs/plan",
            "k-in-k/predicate-plan/v1",
            Some("planId"),
        )),
        "predicate-query" => Some((
            "https://starstream.dev/k-in-k/backend-agnostic/v1/predicate-semantics.schema.json#/$defs/query",
            "k-in-k/predicate-query/v1",
            Some("queryId"),
        )),
        "reachability-plan" => Some((
            "https://starstream.dev/k-in-k/backend-agnostic/v1/reachability-semantics.schema.json#/$defs/plan",
            "k-in-k/reachability-plan/v1",
            Some("planId"),
        )),
        "reachability-query" => Some((
            "https://starstream.dev/k-in-k/backend-agnostic/v1/reachability-semantics.schema.json#/$defs/query",
            "k-in-k/reachability-query/v1",
            Some("queryId"),
        )),
        _ => None,
    };
    if let Some((reference, digest_domain, self_id)) = structured {
        if artifact.entry.content_model != ContentModel::CanonicalJson
            || artifact.entry.media_type != MediaType::ApplicationJson
        {
            return Err(InvocationFailure::new(
                InvocationFailureKind::InvalidShape,
                format!("{expected_role} content model or media type drift"),
            ));
        }
        let value = parse_json(&artifact.bytes).map_err(|error| {
            InvocationFailure::new(
                InvocationFailureKind::InvalidShape,
                format!("{expected_role} is not restricted JSON: {error}"),
            )
        })?;
        if canonical_json_bytes(&value).map_err(|error| {
            InvocationFailure::new(InvocationFailureKind::InvalidShape, error.to_string())
        })? != artifact.bytes
            || artifact.semantic_json.as_ref() != Some(&value)
        {
            return Err(InvocationFailure::new(
                InvocationFailureKind::InvalidShape,
                format!("{expected_role} bytes are not exact canonical JSON"),
            ));
        }
        validate_v1_schema(&value, reference).map_err(|detail| {
            InvocationFailure::new(InvocationFailureKind::InvalidShape, detail)
        })?;
        let derived = if let Some(field) = self_id {
            digest_without_field(&domain(digest_domain), &value, field).map_err(|error| {
                InvocationFailure::new(
                    InvocationFailureKind::InvalidShape,
                    format!("{expected_role} identity projection failed: {error}"),
                )
            })?
        } else {
            digest(&domain(digest_domain), &value).map_err(|error| {
                InvocationFailure::new(
                    InvocationFailureKind::InvalidShape,
                    format!("{expected_role} identity projection failed: {error}"),
                )
            })?
        };
        if derived != artifact.entry.digest {
            return Err(InvocationFailure::new(
                InvocationFailureKind::DigestMismatch,
                format!("{expected_role} semantic identity drift"),
            ));
        }
        if let Some(field) = self_id
            && value
                .as_object()
                .and_then(|fields| fields.get(field))
                .and_then(SemanticJson::as_str)
                != Some(derived.as_str())
        {
            return Err(InvocationFailure::new(
                InvocationFailureKind::DigestMismatch,
                format!("{expected_role} embedded self-ID drift"),
            ));
        }
        return Ok(());
    }

    if !matches!(
        expected_role,
        "pattern-source"
            | "pattern-compiler-profile"
            | "oracle-projection-source"
            | "oracle-projection-plan"
            | "oracle-projection-query"
            | "reachability-source"
            | "predicate-source"
            | "oracle-comparison-spec"
            | "execution-profile"
            | "solver-profile"
            | "oracle-conformance-suite"
    ) {
        return Err(InvocationFailure::new(
            InvocationFailureKind::InvalidShape,
            format!("{expected_role} has no admitted NR-03 identity projection"),
        ));
    }

    if artifact.entry.content_model != ContentModel::OpaqueBytes
        || artifact.entry.media_type != MediaType::ApplicationOctetStream
    {
        return Err(InvocationFailure::new(
            InvocationFailureKind::InvalidShape,
            format!("{expected_role} content model or media type drift"),
        ));
    }

    if artifact.semantic_json.is_some() {
        return Err(InvocationFailure::new(
            InvocationFailureKind::InvalidShape,
            format!("opaque {expected_role} unexpectedly carries semantic JSON"),
        ));
    }
    let envelope = object([
        ("contentSha256", string(content_sha256.as_str())),
        ("mediaType", string("application/octet-stream")),
        ("role", string(expected_role)),
    ]);
    let derived = digest(&domain("k-in-k/opaque-artifact/v1"), &envelope).map_err(|error| {
        InvocationFailure::new(InvocationFailureKind::InvalidShape, error.to_string())
    })?;
    if derived != artifact.entry.digest {
        return Err(InvocationFailure::new(
            InvocationFailureKind::DigestMismatch,
            format!("{expected_role} opaque-envelope identity drift"),
        ));
    }
    Ok(())
}

fn selected_failure(terminal: &SemanticJson) -> &SemanticJson {
    terminal
        .as_object()
        .and_then(|fields| {
            fields
                .get("failure")
                .filter(|value| value.as_object().is_some())
                .or_else(|| {
                    fields
                        .get("outcome")
                        .and_then(SemanticJson::as_object)
                        .and_then(|outcome| outcome.get("failure"))
                        .filter(|value| value.as_object().is_some())
                })
        })
        .unwrap_or(&SemanticJson::Null)
}

const V1_SCHEMAS: &[&str] = &[
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/common.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/cache-semantics.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/oracle-semantics.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/mutation-materialization-result.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/execution-attempt-result.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/oracle-operand-production-result.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/baseline-admission-result.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/oracle-comparison-production-result.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/campaign-derivation-result.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/report-publication-result.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/operation-receipt.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/replay-manifest.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/replay-version-registry.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/reachability-semantics.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/predicate-semantics.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/event-trace.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/pattern-result.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/terminal-state.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/semantic-crash.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/provenance-mutation-report.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/compatibility-profile.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/pattern-plan.schema.json"
    ),
    include_str!(
        "../../../investigations/backend-agnostic-goal-closure/schemas/pattern-query.schema.json"
    ),
];

pub(crate) fn validate_v1_schema(value: &SemanticJson, reference: &str) -> Result<(), String> {
    let mut options = jsonschema::options().with_draft(jsonschema::Draft::Draft202012);
    for encoded in V1_SCHEMAS {
        let schema: serde_json::Value = serde_json::from_str(encoded)
            .map_err(|error| format!("bundled schema is malformed: {error}"))?;
        let id = schema
            .get("$id")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| "bundled schema has no $id".to_owned())?
            .to_owned();
        let resource = jsonschema::Resource::from_contents(schema)
            .map_err(|error| format!("bundled schema resource is invalid: {error}"))?;
        options = options.with_resource(id, resource);
    }
    let root = serde_json::json!({"$ref": reference});
    let validator = options
        .build(&root)
        .map_err(|error| format!("portable schema could not compile: {error}"))?;
    let instance = value
        .to_serde_value()
        .map_err(|error| format!("portable value is invalid: {error}"))?;
    validator
        .validate(&instance)
        .map_err(|error| format!("portable schema rejected value: {error}"))
}

/// Validates against the complete frozen v1/v2 campaign schema closure.
pub(crate) fn validate_campaign_schema(
    value: &SemanticJson,
    reference: &str,
) -> Result<(), String> {
    const EXTRA_SCHEMAS: &[&str] = &[
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/bag16-common.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/branch-trace-collection.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/cache-semantics-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/corpus-component-invocation.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/corpus-component-result.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/corpus-derivation-result.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/corpus-manifest-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/corpus-result-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/execution-attempt-result-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/execution-test-invocation-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/operation-receipt-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/pattern-result-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/operation-invocation-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/event-trace-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/artifact-catalog-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/artifact-role-specs-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/replay-version-registry-v2.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/portable-closure-root.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/empty-search-decision.schema.json"
        ),
        include_str!(
            "../../../investigations/backend-agnostic-goal-closure/schemas/pattern-evaluation-result.schema.json"
        ),
    ];
    let mut options = jsonschema::options().with_draft(jsonschema::Draft::Draft202012);
    for encoded in EXTRA_SCHEMAS {
        let schema: serde_json::Value = serde_json::from_str(encoded)
            .map_err(|error| format!("bundled schema is malformed: {error}"))?;
        let id = schema
            .get("$id")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| "bundled schema has no $id".to_owned())?
            .to_owned();
        let resource = jsonschema::Resource::from_contents(schema)
            .map_err(|error| format!("bundled schema resource is invalid: {error}"))?;
        options = options.with_resource(id, resource);
    }
    // The v1 validator owns the shared resources. Compile the requested v2
    // root after adding all v1 resources to the same resolver.
    for encoded in V1_SCHEMAS {
        let schema: serde_json::Value = serde_json::from_str(encoded)
            .map_err(|error| format!("bundled schema is malformed: {error}"))?;
        let id = schema
            .get("$id")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| "bundled schema has no $id".to_owned())?
            .to_owned();
        let resource = jsonschema::Resource::from_contents(schema)
            .map_err(|error| format!("bundled schema resource is invalid: {error}"))?;
        options = options.with_resource(id, resource);
    }
    let schema = serde_json::json!({"$ref": reference});
    let validator = options
        .build(&schema)
        .map_err(|error| format!("portable schema could not compile: {error}"))?;
    let instance = value
        .to_serde_value()
        .map_err(|error| format!("semantic JSON conversion failed: {error}"))?;
    validator
        .validate(&instance)
        .map_err(|error| format!("portable schema rejected value: {error}"))
}

pub(crate) const fn completeness_name(value: Completeness) -> &'static str {
    match value {
        Completeness::CompleteFinite => "complete-finite",
        Completeness::Incomplete => "incomplete",
        Completeness::Unknown => "unknown",
    }
}

pub(crate) const fn evidence_name(value: EvidenceClass) -> &'static str {
    match value {
        EvidenceClass::Portable => "portable",
        EvidenceClass::FiniteVector => "finite-vector",
        EvidenceClass::Scripted => "scripted",
        EvidenceClass::Incomplete => "incomplete",
        EvidenceClass::Unknown => "unknown",
        EvidenceClass::NotProven => "not-proven",
        EvidenceClass::NativeProven => "native-proven",
    }
}

/// Closed invocation/receipt failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InvocationFailureKind {
    /// A version is zero.
    InvalidVersion,
    /// Parameters are not an object.
    InvalidParameters,
    /// An artifact role is outside the registry grammar.
    InvalidArtifactRole,
    /// The wrapper role does not match the operation.
    WrongOutputRole,
    /// The produced sequence repeats an artifact key.
    DuplicateOutput,
    /// Evidence and native-conformance claims disagree.
    NativeAuthorityMismatch,
    /// A structured receipt is malformed.
    InvalidShape,
    /// A self-ID or repeated digest drifted.
    DigestMismatch,
    /// A wrapper array does not have exactly one item.
    WrongOutputArity,
    /// Failed producer carried output or a terminal.
    FailedProducerOutput,
    /// A receipt and its independently supplied wrapper disagree.
    WrapperCorrespondence,
    /// A future compiler-receipt candidate does not bind one exact frozen input tuple.
    CompilerInputMismatch,
}

/// Typed invocation/receipt failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InvocationFailure {
    kind: InvocationFailureKind,
    detail: String,
}

impl InvocationFailure {
    fn new(kind: InvocationFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Decision-bearing classification.
    #[must_use]
    pub const fn kind(&self) -> InvocationFailureKind {
        self.kind
    }
}

impl fmt::Display for InvocationFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for InvocationFailure {}
