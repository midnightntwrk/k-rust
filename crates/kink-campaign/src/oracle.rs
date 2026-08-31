use crate::receipt::{
    domain, object, parse_artifact_key, revalidate_frozen_artifact, string, validate_v1_schema,
};
use crate::{ArtifactKey, OracleOutcome};
use kink_contracts::{Completeness, EvidenceClass, NativeConformance};
use kink_portable::{
    Digest, IngressedArtifact, SemanticJson, digest, digest_without_field, parse_json,
};
use std::fmt;

/// The six frozen BAG-12 oracle kinds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OracleKind {
    /// Exit/stop class and declared object-program exit code.
    ExitStop,
    /// Whole final term or ordered typed final-term paths.
    FinalResult,
    /// Ordered semantic-output bytes or UTF-8-normalized channels.
    ConcreteOutput,
    /// Finite reachability truth.
    Reachability,
    /// Execution-pattern outcome, optionally with complete bindings.
    ExecutionPattern,
    /// Structured-predicate Bool.
    StructuredPredicate,
}

/// Exact built-in BAG-12 normal-side comparison closure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PortableOracleComparison {
    /// Rederived comparison identity.
    pub comparison_id: Digest,
    /// Rederived decision.
    pub outcome: OracleOutcome,
}

/// The four frozen K-authored evaluator-conformance operation families.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvaluatorConformanceOperation {
    /// K-authored projection.
    Projection,
    /// K-authored reachability query.
    ReachabilityQuery,
    /// K-authored structured-predicate query.
    PredicateQuery,
    /// K-authored comparison.
    Comparison,
}

/// Schema- and identity-checked evaluator-conformance candidate.
///
/// This value deliberately carries no [`EvaluatorAuthority`]. It proves only
/// that one `conformant` record and its complete supplied artifact closure agree
/// structurally and cryptographically under the admitted frozen projections.
/// It does not prove catalog/registry membership or resolver eligibility.
/// Native production and independent qualification remain separate sealed
/// prerequisites.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckedEvaluatorConformanceCandidate {
    conformance_id: Digest,
    operation: EvaluatorConformanceOperation,
    compiler_id: String,
    compiler_version: String,
    evaluator_id: String,
    evaluator_version: String,
    roots: Vec<ArtifactKey>,
}

impl CheckedEvaluatorConformanceCandidate {
    /// Validates the exact frozen schema, outer self-ID, and supplied root closure.
    pub fn validate_frozen_candidate(
        value: &SemanticJson,
        artifacts: &[IngressedArtifact],
    ) -> Result<Self, OracleFailure> {
        validate_v1_schema(
            value,
            "https://starstream.dev/k-in-k/backend-agnostic/v1/oracle-semantics.schema.json#/$defs/evaluatorConformance",
        )
        .map_err(|detail| {
            OracleFailure::new(OracleFailureKind::InvalidPortableArtifact, detail)
        })?;
        let conformance_id = rederive_id(
            value,
            "conformanceId",
            "k-in-k/oracle-evaluator-conformance/v1",
        )?;
        let fields = value.as_object().expect("schema checked");
        if fields.get("result").and_then(SemanticJson::as_str) != Some("conformant") {
            return Err(OracleFailure::new(
                OracleFailureKind::EvaluatorNonconformant,
                "a nonconformant evaluator record is negative evidence",
            ));
        }
        let operation = match fields
            .get("operationKind")
            .and_then(SemanticJson::as_str)
            .expect("schema checked")
        {
            "projection" => EvaluatorConformanceOperation::Projection,
            "reachability-query" => EvaluatorConformanceOperation::ReachabilityQuery,
            "predicate-query" => EvaluatorConformanceOperation::PredicateQuery,
            "comparison" => EvaluatorConformanceOperation::Comparison,
            _ => unreachable!("schema closes operation kinds"),
        };
        let text = |name: &str| {
            fields
                .get(name)
                .and_then(SemanticJson::as_str)
                .expect("schema checked")
        };
        let compiler_id = text("compilerId");
        let compiler_version = text("compilerVersion");
        let evaluator_id = text("evaluatorId");
        let evaluator_version = text("evaluatorVersion");
        if compiler_version == "pending" || evaluator_version == "pending" {
            return Err(OracleFailure::new(
                OracleFailureKind::PlaceholderVersion,
                "conformant evidence must bind non-placeholder compiler and evaluator versions",
            ));
        }

        let mut roots = Vec::new();
        for name in ["source", "plan", "query", "comparisonArtifact"] {
            if let Some(value) = fields.get(name) {
                roots.push(parse_artifact_key(value).ok_or_else(|| {
                    OracleFailure::new(
                        OracleFailureKind::InvalidPortableArtifact,
                        format!("{name} is not an artifact key"),
                    )
                })?);
            }
        }
        for (name, role) in [
            ("compatibilityProfileDigest", "compatibility-profile"),
            ("executionProfileDigest", "execution-profile"),
            ("solverProfileDigest", "solver-profile"),
        ] {
            let digest = Digest::parse(text(name)).expect("schema checked");
            roots.push(ArtifactKey::new(role, digest).expect("static role is valid"));
        }
        roots.push(
            fields
                .get("conformanceSuite")
                .and_then(parse_artifact_key)
                .expect("schema checked"),
        );
        let mut distinct = std::collections::BTreeSet::new();
        if !roots.iter().all(|key| distinct.insert(key.clone())) {
            return Err(OracleFailure::new(
                OracleFailureKind::ConformanceRootMismatch,
                "evaluator conformance repeats a typed root",
            ));
        }
        if artifacts.len() != roots.len() {
            return Err(OracleFailure::new(
                OracleFailureKind::ConformanceRootMismatch,
                "resolved artifact closure is not exact",
            ));
        }
        for root in &roots {
            let mut matches = artifacts.iter().filter(|artifact| {
                artifact.entry.role == root.role && artifact.entry.digest == root.digest
            });
            let artifact = matches.next().ok_or_else(|| {
                OracleFailure::new(
                    OracleFailureKind::ConformanceRootMismatch,
                    format!("missing resolved {} root", root.role),
                )
            })?;
            if matches.next().is_some() {
                return Err(OracleFailure::new(
                    OracleFailureKind::ConformanceRootMismatch,
                    format!("duplicate resolved {} root", root.role),
                ));
            }
            revalidate_frozen_artifact(artifact, &root.role).map_err(|error| {
                OracleFailure::new(
                    OracleFailureKind::InvalidPortableArtifact,
                    error.to_string(),
                )
            })?;
        }
        validate_query_roots(operation, fields, artifacts)?;
        Ok(Self {
            conformance_id,
            operation,
            compiler_id: compiler_id.to_owned(),
            compiler_version: compiler_version.to_owned(),
            evaluator_id: evaluator_id.to_owned(),
            evaluator_version: evaluator_version.to_owned(),
            roots,
        })
    }

    /// Rederived conformance-record identity.
    #[must_use]
    pub fn conformance_id(&self) -> &Digest {
        &self.conformance_id
    }

    /// Frozen operation family.
    #[must_use]
    pub const fn operation(&self) -> EvaluatorConformanceOperation {
        self.operation
    }

    /// Exact compiler implementation identity.
    #[must_use]
    pub fn compiler(&self) -> (&str, &str) {
        (&self.compiler_id, &self.compiler_version)
    }

    /// Exact evaluator implementation identity.
    #[must_use]
    pub fn evaluator(&self) -> (&str, &str) {
        (&self.evaluator_id, &self.evaluator_version)
    }

    /// Complete supplied typed root closure validated for this candidate.
    #[must_use]
    pub fn roots(&self) -> &[ArtifactKey] {
        &self.roots
    }
}

/// Complete frozen BAG-12 finite-evidence closure.
///
/// Unlike [`PortableOracleComparison`], this boundary also requires the
/// independently derived baseline gate and the exact outer failure/side
/// placement registered by the frozen finite oracle authority. It accepts no
/// caller assertion of finite or native authority: the complete artifact-key
/// tuple must occur in `oracle-semantics-vectors.json`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PortableOracleEvidence {
    /// Registered evidence-case name, retained only as diagnostic provenance.
    pub case_id: String,
    /// Closed outer outcome.
    pub outcome: OracleOutcome,
    /// Rederived declaration identity.
    pub declaration_id: Digest,
    /// Rederived baseline-gate identity.
    pub baseline_gate_id: Digest,
    /// Rederived comparison identity when comparison completed.
    pub comparison_id: Option<Digest>,
}

impl PortableOracleEvidence {
    /// Validates the complete finite declaration/gate/sides/comparison/outer graph.
    #[allow(clippy::too_many_arguments)]
    pub fn from_frozen_vector(
        declaration: &SemanticJson,
        baseline_gate: &SemanticJson,
        baseline_operand: Option<&SemanticJson>,
        baseline_crash: Option<&SemanticJson>,
        mutant_operand: Option<&SemanticJson>,
        mutant_crash: Option<&SemanticJson>,
        comparison: Option<&SemanticJson>,
        outer_result: &SemanticJson,
    ) -> Result<Self, OracleFailure> {
        validate_v1_schema(
            declaration,
            "https://starstream.dev/k-in-k/backend-agnostic/v1/oracle-semantics.schema.json#/$defs/declaration",
        )
        .map_err(|detail| {
            OracleFailure::new(OracleFailureKind::InvalidPortableArtifact, detail)
        })?;
        validate_v1_schema(
            baseline_gate,
            "https://starstream.dev/k-in-k/backend-agnostic/v1/oracle-semantics.schema.json#/$defs/baselineGateResult",
        )
        .map_err(|detail| {
            OracleFailure::new(OracleFailureKind::InvalidPortableArtifact, detail)
        })?;
        let declaration_fields = declaration.as_object().expect("schema checked");
        let kind = parse_kind(
            declaration_fields
                .get("kind")
                .and_then(SemanticJson::as_str)
                .expect("schema checked"),
        )?;
        let declaration_id =
            rederive_id(declaration, "declarationId", "k-in-k/oracle-declaration/v1")?;
        let baseline_gate_id = rederive_id(
            baseline_gate,
            "gateResultId",
            "k-in-k/baseline-oracle-gate-result/v1",
        )?;
        let baseline_id =
            validate_optional_operand(kind, "baseline", &declaration_id, baseline_operand)?;
        let mutant_id = validate_optional_operand(kind, "mutant", &declaration_id, mutant_operand)?;
        let baseline_crash_id = validate_optional_crash(baseline_crash)?;
        let mutant_crash_id = validate_optional_crash(mutant_crash)?;
        if comparison.is_some()
            && (baseline_id.is_some() == baseline_crash_id.is_some()
                || mutant_id.is_some() == mutant_crash_id.is_some())
        {
            return Err(OracleFailure::new(
                OracleFailureKind::OracleRootMismatch,
                "a completed comparison requires exactly one value per side",
            ));
        }
        let comparison_id = if let Some(value) = comparison {
            validate_v1_schema(
                value,
                "https://starstream.dev/k-in-k/backend-agnostic/v1/oracle-semantics.schema.json#/$defs/comparison",
            )
            .map_err(|detail| {
                OracleFailure::new(OracleFailureKind::InvalidPortableArtifact, detail)
            })?;
            Some(rederive_id(
                value,
                "comparisonId",
                "k-in-k/oracle-comparison-result/v1",
            )?)
        } else {
            None
        };

        let vectors = parse_json(include_bytes!(
            "../../../investigations/backend-agnostic-goal-closure/vectors/oracle-semantics-vectors.json"
        ))
        .map_err(|error| {
            OracleFailure::new(
                OracleFailureKind::InvalidPortableArtifact,
                format!("bundled oracle registry is invalid: {error}"),
            )
        })?;
        let cases = vectors
            .as_object()
            .and_then(|fields| fields.get("evidenceCases"))
            .and_then(SemanticJson::as_array)
            .expect("bundled oracle registry shape is frozen");
        let matching = cases.iter().find(|case| {
            let Some(fields) = case.as_object() else {
                return false;
            };
            registered_key_digest(fields.get("declaration")) == Some(declaration_id.as_str())
                && registered_key_digest(fields.get("baselineGate"))
                    == Some(baseline_gate_id.as_str())
                && registered_optional_digest(fields.get("baselineOperand"))
                    == baseline_id.as_ref().map(Digest::as_str)
                && registered_optional_digest(fields.get("mutantOperand"))
                    == mutant_id.as_ref().map(Digest::as_str)
                && registered_optional_digest(fields.get("comparison"))
                    == comparison_id.as_ref().map(Digest::as_str)
                && fields.get("outerResult") == Some(outer_result)
        });
        let fields = matching.and_then(SemanticJson::as_object).ok_or_else(|| {
            OracleFailure::new(
                OracleFailureKind::FiniteAuthorityMismatch,
                "oracle graph is not one exact registered frozen finite row",
            )
        })?;
        if fields.get("kind").and_then(SemanticJson::as_str) != Some(kind_name(kind)) {
            return Err(OracleFailure::new(
                OracleFailureKind::OracleRootMismatch,
                "registered oracle kind drift",
            ));
        }
        validate_registered_outer_crashes(outer_result, baseline_crash_id, mutant_crash_id)?;

        let outcome = match fields
            .get("expectedOutcome")
            .and_then(SemanticJson::as_str)
            .expect("bundled oracle row is frozen")
        {
            "agree" => OracleOutcome::Agree,
            "distinguish" => OracleOutcome::Distinguish,
            "incomparable" => OracleOutcome::Incomparable,
            "unknown" => OracleOutcome::Unknown,
            _ => unreachable!("bundled oracle outcome is frozen"),
        };
        if outer_result
            .as_object()
            .and_then(|outer| outer.get("outcome"))
            .and_then(SemanticJson::as_str)
            != Some(outcome_name(outcome))
        {
            return Err(OracleFailure::new(
                OracleFailureKind::OracleOutcomeMismatch,
                "outer outcome does not equal the registered derived outcome",
            ));
        }
        if baseline_gate
            .as_object()
            .and_then(|gate| gate.get("status"))
            .and_then(SemanticJson::as_str)
            != Some("accepted")
        {
            return Err(OracleFailure::new(
                OracleFailureKind::BaselineGateRejected,
                "a rejected baseline gate cannot authorize mutant comparison",
            ));
        }
        if let (Some(left), Some(right), Some(comparison_value)) =
            (baseline_operand, mutant_operand, comparison)
        {
            let derived =
                PortableOracleComparison::from_json(declaration, left, right, comparison_value)?;
            if derived.outcome != outcome {
                return Err(OracleFailure::new(
                    OracleFailureKind::OracleOutcomeMismatch,
                    "inner and outer comparison outcomes disagree",
                ));
            }
        }
        Ok(Self {
            case_id: fields
                .get("id")
                .and_then(SemanticJson::as_str)
                .expect("bundled oracle row is frozen")
                .to_owned(),
            outcome,
            declaration_id,
            baseline_gate_id,
            comparison_id,
        })
    }
}

impl PortableOracleComparison {
    /// Validates declaration, both operands, comparison roots and identities.
    pub fn from_json(
        declaration: &SemanticJson,
        baseline: &SemanticJson,
        mutant: &SemanticJson,
        comparison: &SemanticJson,
    ) -> Result<Self, OracleFailure> {
        for (value, reference) in [
            (
                declaration,
                "https://starstream.dev/k-in-k/backend-agnostic/v1/oracle-semantics.schema.json#/$defs/declaration",
            ),
            (
                baseline,
                "https://starstream.dev/k-in-k/backend-agnostic/v1/oracle-semantics.schema.json#/$defs/operand",
            ),
            (
                mutant,
                "https://starstream.dev/k-in-k/backend-agnostic/v1/oracle-semantics.schema.json#/$defs/operand",
            ),
            (
                comparison,
                "https://starstream.dev/k-in-k/backend-agnostic/v1/oracle-semantics.schema.json#/$defs/comparison",
            ),
        ] {
            validate_v1_schema(value, reference).map_err(|detail| {
                OracleFailure::new(OracleFailureKind::InvalidPortableArtifact, detail)
            })?;
        }
        let declaration_fields = declaration.as_object().expect("schema checked");
        let kind = parse_kind(
            declaration_fields
                .get("kind")
                .and_then(SemanticJson::as_str)
                .expect("schema checked"),
        )?;
        let declaration_id =
            rederive_id(declaration, "declarationId", "k-in-k/oracle-declaration/v1")?;
        let baseline_id = rederive_id(baseline, "operandId", "k-in-k/oracle-operand/v1")?;
        let mutant_id = rederive_id(mutant, "operandId", "k-in-k/oracle-operand/v1")?;
        let baseline_fields = baseline.as_object().expect("schema checked");
        let mutant_fields = mutant.as_object().expect("schema checked");
        if nested_digest(baseline_fields, "declaration") != Some(declaration_id.as_str())
            || nested_digest(mutant_fields, "declaration") != Some(declaration_id.as_str())
        {
            return Err(OracleFailure::new(
                OracleFailureKind::OracleRootMismatch,
                "operand declaration drift",
            ));
        }
        let left = baseline_fields
            .get("normalizedValue")
            .expect("schema checked");
        let right = mutant_fields
            .get("normalizedValue")
            .expect("schema checked");
        validate_normalized_value(kind, left)?;
        validate_normalized_value(kind, right)?;
        let projection_id = declaration_fields
            .get("projectionSpec")
            .and_then(SemanticJson::as_object)
            .and_then(|fields| fields.get("projectionId"))
            .and_then(SemanticJson::as_str)
            .ok_or_else(|| {
                OracleFailure::new(
                    OracleFailureKind::NativeAuthorityUnavailable,
                    "K-authored projection remains not-proven",
                )
            })?;
        let comparator_id = declaration_fields
            .get("comparisonSpec")
            .and_then(SemanticJson::as_object)
            .and_then(|fields| fields.get("comparatorId"))
            .and_then(SemanticJson::as_str)
            .ok_or_else(|| {
                OracleFailure::new(
                    OracleFailureKind::NativeAuthorityUnavailable,
                    "K-authored comparator remains not-proven",
                )
            })?;
        let normalized_digest = |value: &SemanticJson| {
            digest(
                &domain("k-in-k/oracle-normalized-value/v1"),
                &object([
                    ("kind", string(kind_name(kind))),
                    ("normalizedValue", value.clone()),
                    ("projectionId", string(projection_id)),
                ]),
            )
            .map_err(|error| {
                OracleFailure::new(
                    OracleFailureKind::InvalidPortableArtifact,
                    error.to_string(),
                )
            })
        };
        let expected_digests = SemanticJson::Array(vec![
            string(normalized_digest(left)?.as_str()),
            string(normalized_digest(right)?.as_str()),
        ]);
        let fields = comparison.as_object().expect("schema checked");
        let sides = fields
            .get("sides")
            .and_then(|value| match value {
                SemanticJson::Array(items) => Some(items),
                _ => None,
            })
            .expect("schema checked");
        let side_digest = |index: usize| {
            sides[index]
                .as_object()
                .and_then(|side| side.get("normalOperand"))
                .and_then(SemanticJson::as_object)
                .and_then(|key| key.get("digest"))
                .and_then(SemanticJson::as_str)
        };
        if fields
            .get("declaration")
            .and_then(SemanticJson::as_object)
            .and_then(|key| key.get("digest"))
            .and_then(SemanticJson::as_str)
            != Some(declaration_id.as_str())
            || side_digest(0) != Some(baseline_id.as_str())
            || side_digest(1) != Some(mutant_id.as_str())
            || fields.get("projectionId").and_then(SemanticJson::as_str) != Some(projection_id)
            || fields.get("comparatorId").and_then(SemanticJson::as_str) != Some(comparator_id)
            || fields.get("normalizedValueDigests") != Some(&expected_digests)
        {
            return Err(OracleFailure::new(
                OracleFailureKind::OracleRootMismatch,
                "comparison roots, sides, or normalized digests drift",
            ));
        }
        let outcome = if comparable_value(kind, projection_id, left)
            == comparable_value(kind, projection_id, right)
        {
            OracleOutcome::Agree
        } else {
            OracleOutcome::Distinguish
        };
        let outcome_name = if outcome == OracleOutcome::Agree {
            "agree"
        } else {
            "distinguish"
        };
        if fields.get("outcome").and_then(SemanticJson::as_str) != Some(outcome_name) {
            return Err(OracleFailure::new(
                OracleFailureKind::OracleOutcomeMismatch,
                "comparison outcome is not rederived",
            ));
        }
        let comparison_id = rederive_id(
            comparison,
            "comparisonId",
            "k-in-k/oracle-comparison-result/v1",
        )?;
        Ok(Self {
            comparison_id,
            outcome,
        })
    }
}

fn comparable_value(kind: OracleKind, projection: &str, value: &SemanticJson) -> SemanticJson {
    let fields = value.as_object().expect("kind value checked");
    match kind {
        OracleKind::FinalResult => fields
            .get(if projection == "whole-portable-term-v1" {
                "term"
            } else {
                "paths"
            })
            .cloned()
            .unwrap_or(SemanticJson::Null),
        OracleKind::Reachability => fields.get("status").cloned().unwrap_or(SemanticJson::Null),
        OracleKind::ExecutionPattern => {
            if projection == "pattern-outcome-bindings-v1" {
                object([
                    (
                        "bindingTuples",
                        fields
                            .get("bindingTuples")
                            .cloned()
                            .unwrap_or(SemanticJson::Null),
                    ),
                    (
                        "outcome",
                        fields.get("outcome").cloned().unwrap_or(SemanticJson::Null),
                    ),
                ])
            } else {
                fields.get("outcome").cloned().unwrap_or(SemanticJson::Null)
            }
        }
        OracleKind::StructuredPredicate => {
            fields.get("result").cloned().unwrap_or(SemanticJson::Null)
        }
        OracleKind::ConcreteOutput => {
            let channels = fields
                .get("channels")
                .and_then(SemanticJson::as_array)
                .expect("kind value checked");
            SemanticJson::Array(
                channels
                    .iter()
                    .map(|channel| {
                        let fields = channel.as_object().expect("kind value checked");
                        if projection == "ordered-output-utf8-lines-v1" {
                            object([
                                (
                                    "mediaType",
                                    fields.get("mediaType").cloned().expect("schema checked"),
                                ),
                                ("name", fields.get("name").cloned().expect("schema checked")),
                                (
                                    "text",
                                    fields
                                        .get("text")
                                        .and_then(SemanticJson::as_str)
                                        .map(|text| {
                                            string(&text.replace("\r\n", "\n").replace('\r', "\n"))
                                        })
                                        .unwrap_or(SemanticJson::Null),
                                ),
                            ])
                        } else {
                            object([
                                (
                                    "contentSha256",
                                    fields
                                        .get("contentSha256")
                                        .cloned()
                                        .expect("schema checked"),
                                ),
                                (
                                    "mediaType",
                                    fields.get("mediaType").cloned().expect("schema checked"),
                                ),
                                ("name", fields.get("name").cloned().expect("schema checked")),
                            ])
                        }
                    })
                    .collect(),
            )
        }
        OracleKind::ExitStop => value.clone(),
    }
}

fn validate_optional_operand(
    kind: OracleKind,
    side: &str,
    declaration_id: &Digest,
    operand: Option<&SemanticJson>,
) -> Result<Option<Digest>, OracleFailure> {
    let Some(operand) = operand else {
        return Ok(None);
    };
    validate_v1_schema(
        operand,
        "https://starstream.dev/k-in-k/backend-agnostic/v1/oracle-semantics.schema.json#/$defs/operand",
    )
    .map_err(|detail| {
        OracleFailure::new(OracleFailureKind::InvalidPortableArtifact, detail)
    })?;
    let fields = operand.as_object().expect("schema checked");
    if nested_digest(fields, "declaration") != Some(declaration_id.as_str())
        || fields
            .get("subject")
            .and_then(SemanticJson::as_object)
            .and_then(|subject| subject.get("side"))
            .and_then(SemanticJson::as_str)
            != Some(side)
    {
        return Err(OracleFailure::new(
            OracleFailureKind::OracleRootMismatch,
            format!("{side} operand declaration or subject drift"),
        ));
    }
    validate_normalized_value(kind, fields.get("normalizedValue").expect("schema checked"))?;
    rederive_id(operand, "operandId", "k-in-k/oracle-operand/v1").map(Some)
}

fn validate_optional_crash(crash: Option<&SemanticJson>) -> Result<Option<Digest>, OracleFailure> {
    let Some(crash) = crash else {
        return Ok(None);
    };
    validate_v1_schema(
        crash,
        "https://starstream.dev/k-in-k/backend-agnostic/v1/semantic-crash.schema.json",
    )
    .map_err(|detail| OracleFailure::new(OracleFailureKind::InvalidPortableArtifact, detail))?;
    rederive_id(crash, "crashDigest", "k-in-k/semantic-crash/v1").map(Some)
}

fn registered_key_digest(value: Option<&SemanticJson>) -> Option<&str> {
    value
        .and_then(SemanticJson::as_object)
        .and_then(|key| key.get("digest"))
        .and_then(SemanticJson::as_str)
}

fn registered_optional_digest(value: Option<&SemanticJson>) -> Option<&str> {
    match value {
        None | Some(SemanticJson::Null) => None,
        Some(value) => registered_key_digest(Some(value)),
    }
}

fn validate_query_roots(
    operation: EvaluatorConformanceOperation,
    fields: &std::collections::BTreeMap<String, SemanticJson>,
    artifacts: &[IngressedArtifact],
) -> Result<(), OracleFailure> {
    if !matches!(
        operation,
        EvaluatorConformanceOperation::ReachabilityQuery
            | EvaluatorConformanceOperation::PredicateQuery
    ) {
        return Ok(());
    }
    let source = fields
        .get("source")
        .and_then(parse_artifact_key)
        .expect("schema checked");
    let plan = fields
        .get("plan")
        .and_then(parse_artifact_key)
        .expect("schema checked");
    let query = fields
        .get("query")
        .and_then(parse_artifact_key)
        .expect("schema checked");
    let query_value = artifacts
        .iter()
        .find(|artifact| artifact.entry.role == query.role && artifact.entry.digest == query.digest)
        .and_then(|artifact| artifact.semantic_json.as_ref())
        .and_then(SemanticJson::as_object)
        .expect("exact structured query closure checked");
    let nested_source = query_value
        .get("source")
        .and_then(parse_artifact_key)
        .expect("query schema checked");
    let nested_plan = query_value
        .get("plan")
        .and_then(parse_artifact_key)
        .expect("query schema checked");
    if nested_source != source || nested_plan != plan {
        return Err(OracleFailure::new(
            OracleFailureKind::ConformanceRootMismatch,
            "self-identified query source/plan roots disagree with evaluator conformance",
        ));
    }
    Ok(())
}

fn validate_registered_outer_crashes(
    outer: &SemanticJson,
    baseline: Option<Digest>,
    mutant: Option<Digest>,
) -> Result<(), OracleFailure> {
    let fields = outer.as_object().ok_or_else(|| {
        OracleFailure::new(
            OracleFailureKind::InvalidPortableArtifact,
            "outer result must be an object",
        )
    })?;
    let outer_crash = |name: &str| {
        fields
            .get(name)
            .and_then(SemanticJson::as_object)
            .and_then(|side| side.get("semanticCrash"))
            .and_then(SemanticJson::as_object)
            .and_then(|key| key.get("digest"))
            .and_then(SemanticJson::as_str)
    };
    if outer_crash("baselineSide") != baseline.as_ref().map(Digest::as_str)
        || outer_crash("mutantSide") != mutant.as_ref().map(Digest::as_str)
    {
        return Err(OracleFailure::new(
            OracleFailureKind::OracleRootMismatch,
            "outer semantic-crash side drift",
        ));
    }
    Ok(())
}

const fn outcome_name(outcome: OracleOutcome) -> &'static str {
    match outcome {
        OracleOutcome::Agree => "agree",
        OracleOutcome::Distinguish => "distinguish",
        OracleOutcome::Incomparable => "incomparable",
        OracleOutcome::Unknown => "unknown",
        OracleOutcome::Error => "error",
        OracleOutcome::Timeout => "timeout",
        OracleOutcome::Skipped => "skipped",
    }
}

fn nested_digest<'a>(
    fields: &'a std::collections::BTreeMap<String, SemanticJson>,
    name: &str,
) -> Option<&'a str> {
    fields
        .get(name)
        .and_then(SemanticJson::as_object)
        .and_then(|key| key.get("digest"))
        .and_then(SemanticJson::as_str)
}

fn rederive_id(
    value: &SemanticJson,
    field: &str,
    domain_name: &str,
) -> Result<Digest, OracleFailure> {
    let claimed = value
        .as_object()
        .and_then(|fields| fields.get(field))
        .and_then(SemanticJson::as_str)
        .and_then(|value| Digest::parse(value).ok())
        .ok_or_else(|| {
            OracleFailure::new(
                OracleFailureKind::InvalidPortableArtifact,
                format!("{field} is invalid"),
            )
        })?;
    let actual = digest_without_field(&domain(domain_name), value, field).map_err(|error| {
        OracleFailure::new(
            OracleFailureKind::InvalidPortableArtifact,
            error.to_string(),
        )
    })?;
    if claimed != actual {
        return Err(OracleFailure::new(
            OracleFailureKind::OracleIdentityMismatch,
            format!("{field} drift"),
        ));
    }
    Ok(actual)
}

fn parse_kind(value: &str) -> Result<OracleKind, OracleFailure> {
    Ok(match value {
        "exit-stop" => OracleKind::ExitStop,
        "final-result" => OracleKind::FinalResult,
        "concrete-output" => OracleKind::ConcreteOutput,
        "reachability" => OracleKind::Reachability,
        "execution-pattern" => OracleKind::ExecutionPattern,
        "structured-predicate" => OracleKind::StructuredPredicate,
        _ => {
            return Err(OracleFailure::new(
                OracleFailureKind::InvalidKindValue,
                "unknown oracle kind",
            ));
        }
    })
}
const fn kind_name(kind: OracleKind) -> &'static str {
    match kind {
        OracleKind::ExitStop => "exit-stop",
        OracleKind::FinalResult => "final-result",
        OracleKind::ConcreteOutput => "concrete-output",
        OracleKind::Reachability => "reachability",
        OracleKind::ExecutionPattern => "execution-pattern",
        OracleKind::StructuredPredicate => "structured-predicate",
    }
}

/// Declaration-owned semantic-crash comparison policy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CrashPolicy {
    /// A crash is outside the admitted operand domain.
    Reject,
    /// Equal crash identities agree; unequal crashes distinguish.
    CompareIdentity,
    /// Any baseline/mutant crash-shape difference distinguishes.
    Distinguish,
}

/// One exact declaration-scoped semantic side.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OracleSide {
    /// Kind-validated normalized value.
    Normal {
        /// Closed normalized value supplied by the kind-specific portable evaluator.
        value: SemanticJson,
        /// Completeness of the value's producing finite input.
        completeness: Completeness,
    },
    /// Proven object-language crash operand.
    SemanticCrash(ArtifactKey),
    /// Operand production was semantically unknown.
    Unknown,
    /// Operand production failed in infrastructure/backend code.
    Error,
}

/// Authority carried by the evaluator, distinct from production provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluatorAuthority {
    /// Evidence class.
    evidence: EvidenceClass,
    /// Native conformance gate.
    native_conformance: NativeConformance,
    /// Exact production receipt, when one exists.
    production_receipt: Option<ArtifactKey>,
}

impl EvaluatorAuthority {
    /// Bundled finite authority. It never proves native semantics.
    #[must_use]
    pub fn finite_vector() -> Self {
        Self {
            evidence: EvidenceClass::FiniteVector,
            native_conformance: NativeConformance::NotProven,
            production_receipt: None,
        }
    }

    /// Validates a K-authored evaluator gate.
    pub fn validate_k_authored(&self) -> Result<(), OracleFailure> {
        if self.evidence != EvidenceClass::NativeProven
            || self.native_conformance != NativeConformance::NativeProven
            || self.production_receipt.is_none()
        {
            return Err(OracleFailure::new(
                OracleFailureKind::NativeAuthorityUnavailable,
                "K-authored evaluation requires conformant authority and a distinct production receipt",
            ));
        }
        Ok(())
    }
}

/// Compares two already kind-validated supplied sides.
///
/// This function performs no K parsing, projection, solver work, or discovery.
pub fn compare_supplied(
    kind: OracleKind,
    crash_policy: CrashPolicy,
    baseline: &OracleSide,
    mutant: &OracleSide,
) -> Result<OracleOutcome, OracleFailure> {
    match (baseline, mutant) {
        (OracleSide::Error, _) | (_, OracleSide::Error) => Ok(OracleOutcome::Error),
        (OracleSide::Unknown, _) | (_, OracleSide::Unknown) => Ok(OracleOutcome::Unknown),
        (
            OracleSide::Normal {
                completeness: left_completeness,
                ..
            },
            OracleSide::Normal {
                completeness: right_completeness,
                ..
            },
        ) if *left_completeness != Completeness::CompleteFinite
            || *right_completeness != Completeness::CompleteFinite =>
        {
            Ok(OracleOutcome::Unknown)
        }
        (OracleSide::Normal { value: left, .. }, OracleSide::Normal { value: right, .. }) => {
            validate_normalized_value(kind, left)?;
            validate_normalized_value(kind, right)?;
            Ok(if left == right {
                OracleOutcome::Agree
            } else {
                OracleOutcome::Distinguish
            })
        }
        (OracleSide::SemanticCrash(left), OracleSide::SemanticCrash(right)) => match crash_policy {
            CrashPolicy::Reject => Err(OracleFailure::new(
                OracleFailureKind::CrashRejected,
                "declaration terminal policy rejects semantic crashes",
            )),
            CrashPolicy::CompareIdentity | CrashPolicy::Distinguish => Ok(if left == right {
                OracleOutcome::Agree
            } else {
                OracleOutcome::Distinguish
            }),
        },
        (OracleSide::SemanticCrash(_), OracleSide::Normal { .. })
        | (OracleSide::Normal { .. }, OracleSide::SemanticCrash(_)) => match crash_policy {
            CrashPolicy::Reject => Err(OracleFailure::new(
                OracleFailureKind::CrashRejected,
                "declaration terminal policy rejects semantic crashes",
            )),
            CrashPolicy::CompareIdentity => Ok(OracleOutcome::Incomparable),
            CrashPolicy::Distinguish => Ok(OracleOutcome::Distinguish),
        },
    }
}

fn validate_normalized_value(kind: OracleKind, value: &SemanticJson) -> Result<(), OracleFailure> {
    let Some(fields) = value.as_object() else {
        // Reduced scripted values are retained only for the nonportable unit
        // seam. Portable operand ingress is schema-exact and always supplies
        // the structured kind-specific object validated below.
        return Ok(());
    };
    let valid = match kind {
        OracleKind::ExitStop => {
            exact_keys(fields, &["exitCode", "terminalClass"])
                && matches!(
                    fields.get("terminalClass").and_then(SemanticJson::as_str),
                    Some("normal" | "stuck")
                )
                && matches!(
                    fields.get("exitCode"),
                    Some(SemanticJson::Null | SemanticJson::Integer(_))
                )
        }
        OracleKind::FinalResult => {
            exact_keys(fields, &["projection", "term", "terminalState"])
                || exact_keys(fields, &["paths", "projection", "terminalState"])
        }
        OracleKind::ConcreteOutput => {
            exact_keys(fields, &["channels"])
                && matches!(fields.get("channels"), Some(SemanticJson::Array(items)) if !items.is_empty())
        }
        OracleKind::Reachability => {
            exact_keys(fields, &["status", "witnesses"])
                && matches!(
                    fields.get("status").and_then(SemanticJson::as_str),
                    Some("reached" | "not-reached")
                )
        }
        OracleKind::ExecutionPattern => {
            exact_keys(fields, &["bindingTuples", "outcome", "patternResult"])
                && matches!(
                    fields.get("outcome").and_then(SemanticJson::as_str),
                    Some("match" | "no-match" | "unknown" | "error")
                )
        }
        OracleKind::StructuredPredicate => {
            exact_keys(
                fields,
                &[
                    "bindings",
                    "bindingsDigest",
                    "input",
                    "inputProjectionDigest",
                    "query",
                    "result",
                ],
            ) && matches!(fields.get("result"), Some(SemanticJson::Bool(_)))
        }
    };
    if !valid {
        return Err(OracleFailure::new(
            OracleFailureKind::InvalidKindValue,
            "normal value does not have the exact shape for its oracle kind",
        ));
    }
    Ok(())
}

fn exact_keys(
    fields: &std::collections::BTreeMap<String, SemanticJson>,
    expected: &[&str],
) -> bool {
    fields.len() == expected.len() && expected.iter().all(|name| fields.contains_key(*name))
}

/// Closed oracle failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OracleFailureKind {
    /// K-authored evaluator lacks independent conformance and production authority.
    NativeAuthorityUnavailable,
    /// Declaration policy rejects a crash operand.
    CrashRejected,
    /// A normal value does not belong to the selected oracle family.
    InvalidKindValue,
    /// A frozen declaration, operand, or comparison failed schema validation.
    InvalidPortableArtifact,
    /// A declaration, operand, or comparison self-ID drifted.
    OracleIdentityMismatch,
    /// Declaration, side, projection, comparator, or normalized digest drifted.
    OracleRootMismatch,
    /// The claimed comparison decision differs from the derived decision.
    OracleOutcomeMismatch,
    /// The complete graph is not one registered frozen finite evidence row.
    FiniteAuthorityMismatch,
    /// A baseline gate did not authorize comparison.
    BaselineGateRejected,
    /// The evaluator suite reported negative conformance evidence.
    EvaluatorNonconformant,
    /// A conformant claim retained a frozen placeholder implementation version.
    PlaceholderVersion,
    /// A conformance record and its exact resolved artifact closure disagree.
    ConformanceRootMismatch,
}

/// Typed oracle failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OracleFailure {
    kind: OracleFailureKind,
    detail: String,
}

impl OracleFailure {
    fn new(kind: OracleFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Decision-bearing classification.
    #[must_use]
    pub const fn kind(&self) -> OracleFailureKind {
        self.kind
    }
}

impl fmt::Display for OracleFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for OracleFailure {}
