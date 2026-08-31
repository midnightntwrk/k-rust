use crate::receipt::{ArtifactKey, OperationInvocation, parse_artifact_key, validate_v1_schema};
use kink_contracts::{Completeness, EvidenceClass, NativeConformance};
use kink_portable::{Digest, SemanticJson};
use std::fmt;

/// Frozen execution bound classifications from BAG-10/BAG-14.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BoundedClassification {
    /// Maximum semantic depth reached.
    DepthLimit,
    /// Time budget reached.
    TimeLimit,
    /// Branch budget reached.
    BranchLimit,
    /// Result budget reached.
    ResultLimit,
    /// Another declared resource budget reached.
    ResourceLimit,
    /// Solver could not decide the request under the exact bounds.
    SolverUnknown,
}

impl BoundedClassification {
    fn parse(value: &str) -> Option<Self> {
        Some(match value {
            "depth-limit" => Self::DepthLimit,
            "time-limit" => Self::TimeLimit,
            "branch-limit" => Self::BranchLimit,
            "result-limit" => Self::ResultLimit,
            "resource-limit" => Self::ResourceLimit,
            "solver-unknown" => Self::SolverUnknown,
            _ => return None,
        })
    }
}

/// BAG-10 stages reachable from an execution worker.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WorkerFailureStage {
    /// Lowering stopped before execution.
    Lowering,
    /// Semantic execution stopped or failed.
    Execution,
    /// The worker, backend process, storage, or transport failed.
    Infrastructure,
}

/// Closed BAG-10 classifications reachable from an execution worker.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WorkerFailureClassification {
    /// Lowering or execution time budget.
    TimeLimit,
    /// Lowering or execution resource budget.
    ResourceLimit,
    /// Execution depth budget.
    DepthLimit,
    /// Execution branch budget.
    BranchLimit,
    /// Execution result budget.
    ResultLimit,
    /// Solver returned unknown.
    SolverUnknown,
    /// Backend semantic processing failed.
    BackendError,
    /// Worker process could not launch.
    ProcessLaunch,
    /// Worker I/O failed.
    Io,
    /// A required artifact was corrupt.
    ArtifactCorruption,
    /// Worker disappeared before publishing a complete result.
    WorkerLost,
    /// Internal infrastructure invariant failed.
    Internal,
}

/// Exact BAG-10 execution placement.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WorkerFailureContext {
    /// Baseline execution; scope is the campaign.
    BaselineExecution,
    /// Mutant execution; scope is the mutant.
    MutantExecution,
}

/// Retry policy frozen by BAG-10.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Retryability {
    /// Repeating the same input cannot repair the failure.
    Never,
    /// Retry is meaningful only after changing an explicit resource budget.
    SameInputAfterResourceChange,
    /// Retry is meaningful only after external repair.
    AfterExternalRepair,
}

/// A schema-exact, taxonomy-authorized BAG-10 execution failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Bag10ExecutionFailure {
    stage: WorkerFailureStage,
    classification: WorkerFailureClassification,
    context: WorkerFailureContext,
    retryability: Retryability,
    value: SemanticJson,
}

impl Bag10ExecutionFailure {
    /// Parses a closed baseline- or mutant-execution failure placement.
    pub fn from_json(value: &SemanticJson) -> Result<Self, WorkerFailure> {
        let fields = value.as_object().ok_or_else(|| {
            WorkerFailure::new(
                WorkerFailureKind::InvalidFailure,
                "BAG-10 execution failure must be an object",
            )
        })?;
        let context = match fields.get("context").and_then(SemanticJson::as_str) {
            Some("baseline-execution") => WorkerFailureContext::BaselineExecution,
            Some("mutant-execution") => WorkerFailureContext::MutantExecution,
            _ => {
                return Err(WorkerFailure::new(
                    WorkerFailureKind::InvalidFailure,
                    "failure is not in a worker execution context",
                ));
            }
        };
        let reference = match context {
            WorkerFailureContext::BaselineExecution => {
                "https://starstream.dev/k-in-k/backend-agnostic/v1/common.schema.json#/$defs/baselineExecutionFailure"
            }
            WorkerFailureContext::MutantExecution => {
                "https://starstream.dev/k-in-k/backend-agnostic/v1/common.schema.json#/$defs/mutantExecutionFailure"
            }
        };
        validate_v1_schema(value, reference)
            .map_err(|detail| WorkerFailure::new(WorkerFailureKind::InvalidFailure, detail))?;
        let stage = match fields.get("stage").and_then(SemanticJson::as_str) {
            Some("lowering") => WorkerFailureStage::Lowering,
            Some("execution") => WorkerFailureStage::Execution,
            Some("infrastructure") => WorkerFailureStage::Infrastructure,
            _ => unreachable!("context-specific schema checked"),
        };
        let classification = match fields.get("classification").and_then(SemanticJson::as_str) {
            Some("time-limit") => WorkerFailureClassification::TimeLimit,
            Some("resource-limit") => WorkerFailureClassification::ResourceLimit,
            Some("depth-limit") => WorkerFailureClassification::DepthLimit,
            Some("branch-limit") => WorkerFailureClassification::BranchLimit,
            Some("result-limit") => WorkerFailureClassification::ResultLimit,
            Some("solver-unknown") => WorkerFailureClassification::SolverUnknown,
            Some("backend-error") => WorkerFailureClassification::BackendError,
            Some("process-launch") => WorkerFailureClassification::ProcessLaunch,
            Some("io") => WorkerFailureClassification::Io,
            Some("artifact-corruption") => WorkerFailureClassification::ArtifactCorruption,
            Some("worker-lost") => WorkerFailureClassification::WorkerLost,
            Some("internal") => WorkerFailureClassification::Internal,
            _ => unreachable!("context-specific schema checked"),
        };
        let retryability = match fields.get("retryability").and_then(SemanticJson::as_str) {
            Some("never") => Retryability::Never,
            Some("same-input-after-resource-change") => Retryability::SameInputAfterResourceChange,
            Some("after-external-repair") => Retryability::AfterExternalRepair,
            _ => unreachable!("context-specific schema checked"),
        };
        Ok(Self {
            stage,
            classification,
            context,
            retryability,
            value: value.clone(),
        })
    }

    /// Taxonomy stage.
    #[must_use]
    pub const fn stage(&self) -> WorkerFailureStage {
        self.stage
    }

    /// Taxonomy classification.
    #[must_use]
    pub const fn classification(&self) -> WorkerFailureClassification {
        self.classification
    }

    /// Exact baseline/mutant placement.
    #[must_use]
    pub const fn context(&self) -> WorkerFailureContext {
        self.context
    }

    /// Frozen retry policy.
    #[must_use]
    pub const fn retryability(&self) -> Retryability {
        self.retryability
    }

    /// Validated portable representation.
    #[must_use]
    pub fn as_json(&self) -> &SemanticJson {
        &self.value
    }
}

/// The semantic terminal of one isolated execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WorkerTerminal {
    /// Ordinary object-language completion.
    Normal(ArtifactKey),
    /// Semantically stuck completion.
    Stuck(ArtifactKey),
    /// Proven object-language crash; never an infrastructure failure.
    SemanticCrash(ArtifactKey),
    /// A declared bound stopped execution.
    Bounded {
        /// Closed bound classification.
        classification: BoundedClassification,
        /// Exact bounds profile.
        bounds_digest: Digest,
        /// Exact BAG-10 failure placement.
        failure: Bag10ExecutionFailure,
    },
    /// A solver or incomplete result prevented a semantic conclusion.
    Unknown(Bag10ExecutionFailure),
    /// A trustworthy typed semantic request error.
    Error(Bag10ExecutionFailure),
    /// Worker/backend/infrastructure failure.
    Infrastructure(Bag10ExecutionFailure),
}

impl WorkerTerminal {
    /// Parses the exact BAG-14 execution terminal record union.
    pub fn from_portable_json(value: &SemanticJson) -> Result<Self, WorkerFailure> {
        validate_v1_schema(
            value,
            "https://starstream.dev/k-in-k/backend-agnostic/v1/cache-semantics.schema.json#/$defs/executionTerminalRecord",
        )
        .map_err(|detail| WorkerFailure::new(WorkerFailureKind::InvalidTerminal, detail))?;
        let fields = value
            .as_object()
            .expect("execution terminal schema checked");
        match fields.get("kind").and_then(SemanticJson::as_str) {
            Some("normal") => Ok(Self::Normal(parse_terminal_artifact(fields, "terminal")?)),
            Some("stuck") => Ok(Self::Stuck(parse_terminal_artifact(fields, "terminal")?)),
            Some("semantic-crash") => Ok(Self::SemanticCrash(parse_terminal_artifact(
                fields, "crash",
            )?)),
            Some("bounded-stop") => {
                let classification = fields
                    .get("classification")
                    .and_then(SemanticJson::as_str)
                    .and_then(BoundedClassification::parse)
                    .expect("execution terminal schema checked");
                let bounds_digest = Digest::parse(
                    fields
                        .get("boundsDigest")
                        .and_then(SemanticJson::as_str)
                        .expect("execution terminal schema checked"),
                )
                .expect("execution terminal schema checked");
                let failure = Bag10ExecutionFailure::from_json(
                    fields
                        .get("failure")
                        .expect("execution terminal schema checked"),
                )?;
                Ok(Self::Bounded {
                    classification,
                    bounds_digest,
                    failure,
                })
            }
            Some("diagnostic-only") => {
                let failure = Bag10ExecutionFailure::from_json(
                    fields
                        .get("failure")
                        .expect("execution terminal schema checked"),
                )?;
                match (failure.stage(), failure.classification()) {
                    (_, WorkerFailureClassification::SolverUnknown) => Ok(Self::Unknown(failure)),
                    (WorkerFailureStage::Infrastructure, _) => Ok(Self::Infrastructure(failure)),
                    _ => Ok(Self::Error(failure)),
                }
            }
            _ => unreachable!("execution terminal schema checked"),
        }
    }
}

fn parse_terminal_artifact(
    fields: &std::collections::BTreeMap<String, SemanticJson>,
    name: &str,
) -> Result<ArtifactKey, WorkerFailure> {
    fields
        .get(name)
        .and_then(parse_artifact_key)
        .ok_or_else(|| {
            WorkerFailure::new(
                WorkerFailureKind::InvalidTerminal,
                format!("{name} is not a typed artifact key"),
            )
        })
}

/// Closed result kind, kept separate even when two variants are non-reusable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WorkerResultKind {
    /// Normal terminal.
    Normal,
    /// Stuck terminal.
    Stuck,
    /// Semantic crash terminal.
    SemanticCrash,
    /// Bounded stop.
    Bounded,
    /// Semantically unknown result.
    Unknown,
    /// Typed request or semantic processing error.
    Error,
    /// Infrastructure failure.
    Infrastructure,
}

/// Typed worker result returned across the scripted boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WorkerResult {
    terminal: WorkerTerminal,
    outputs: Vec<ArtifactKey>,
    completeness: Completeness,
    evidence: EvidenceClass,
    native_conformance: NativeConformance,
}

impl WorkerResult {
    /// Creates a result while fixing its authority to scripted/not-proven.
    #[must_use]
    pub fn scripted(
        terminal: WorkerTerminal,
        outputs: Vec<ArtifactKey>,
        completeness: Completeness,
    ) -> Self {
        Self {
            terminal,
            outputs,
            completeness,
            evidence: EvidenceClass::Scripted,
            native_conformance: NativeConformance::NotProven,
        }
    }

    /// Returns the stable terminal family.
    #[must_use]
    pub const fn kind(&self) -> WorkerResultKind {
        match self.terminal {
            WorkerTerminal::Normal(_) => WorkerResultKind::Normal,
            WorkerTerminal::Stuck(_) => WorkerResultKind::Stuck,
            WorkerTerminal::SemanticCrash(_) => WorkerResultKind::SemanticCrash,
            WorkerTerminal::Bounded { .. } => WorkerResultKind::Bounded,
            WorkerTerminal::Unknown(_) => WorkerResultKind::Unknown,
            WorkerTerminal::Error(_) => WorkerResultKind::Error,
            WorkerTerminal::Infrastructure(_) => WorkerResultKind::Infrastructure,
        }
    }

    /// Exact typed terminal.
    #[must_use]
    pub fn terminal(&self) -> &WorkerTerminal {
        &self.terminal
    }

    /// Ordered produced artifacts.
    #[must_use]
    pub fn outputs(&self) -> &[ArtifactKey] {
        &self.outputs
    }

    /// Completeness independent of terminal kind.
    #[must_use]
    pub const fn completeness(&self) -> Completeness {
        self.completeness
    }

    /// Scripted evidence cannot be promoted through the public API.
    #[must_use]
    pub const fn evidence(&self) -> EvidenceClass {
        self.evidence
    }

    /// Scripted execution is always native not-proven.
    #[must_use]
    pub const fn native_conformance(&self) -> NativeConformance {
        self.native_conformance
    }

    /// Returns true only for terminal kinds with a semantic artifact.
    #[must_use]
    pub const fn has_semantic_terminal(&self) -> bool {
        matches!(
            self.terminal,
            WorkerTerminal::Normal(_) | WorkerTerminal::Stuck(_) | WorkerTerminal::SemanticCrash(_)
        )
    }
}

/// One scripted request/result pair.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScriptedExecution {
    /// Cycle-free request.
    pub invocation: OperationInvocation,
    /// Typed result.
    pub result: WorkerResult,
}

/// Backend-neutral deterministic scripted boundary.
pub trait ScriptedBoundary {
    /// Supplemental implementation error. It must never be parsed as semantic evidence.
    type Error: std::error::Error + Send + Sync + 'static;

    /// Executes one cycle-free request.
    fn execute(&mut self, invocation: &OperationInvocation) -> Result<WorkerResult, Self::Error>;
}

/// Closed worker parsing failures.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WorkerFailureKind {
    /// Terminal record is outside the exact frozen union.
    InvalidTerminal,
    /// Failure is outside an exact BAG-10 execution placement.
    InvalidFailure,
}

/// Typed worker validation failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WorkerFailure {
    kind: WorkerFailureKind,
    detail: String,
}

impl WorkerFailure {
    fn new(kind: WorkerFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Decision-bearing failure class.
    #[must_use]
    pub const fn kind(&self) -> WorkerFailureKind {
        self.kind
    }
}

impl fmt::Display for WorkerFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for WorkerFailure {}

impl fmt::Display for WorkerResultKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}
