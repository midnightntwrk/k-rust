//! Backend-neutral campaign, receipt, cache, replay, and report layer.
//!
//! This crate deliberately stops at the portable worker boundary. Scripted
//! and finite-vector results can exercise the complete orchestration shell,
//! but only a future receipt-checked native adapter can supply native proof.

mod cache;
mod campaign;
mod closure;
mod collection;
mod durable_cache;
mod oracle;
mod receipt;
mod replay;
mod worker;

pub use cache::{
    CacheFailure, CacheFailureKind, CacheRecord, CacheStore, CompletionClass, KeyKind,
    MaterialEligibility, PortableProductionWitness, Publication, RequestKey, ReuseClass,
};
pub use campaign::{
    BaselineAdmission, CampaignFailure, CampaignFailureKind, CampaignReport, MutantPlan,
    MutantReport, MutantStatus, OracleOutcome, PortableCampaignReport, PortablePublishedReport,
    Rational, ScheduleMode, Score, TestPlan, derive_mutant_report, score, validate_baseline,
};
pub use closure::{ClosureFailure, ClosureFailureKind, PortableClosureRoot};
pub use collection::{
    BranchCollection, BranchDecision, CollectionDecision, CollectionFailure, CollectionFailureKind,
    CollectionStop, PortableBranchCollection, derive_collection_decision,
};
pub use durable_cache::{
    DurableArtifactInput, DurableCacheFailpoint, DurableCacheFailure, DurableCacheFailureKind,
    DurableCachePublication, DurableCacheStore, DurableConflictState,
};
pub use oracle::{
    CheckedEvaluatorConformanceCandidate, CrashPolicy, EvaluatorAuthority,
    EvaluatorConformanceOperation, OracleFailure, OracleFailureKind, OracleKind, OracleSide,
    PortableOracleComparison, PortableOracleEvidence, compare_supplied,
};
pub use receipt::{
    AdapterContract, ArtifactEdge, ArtifactKey, CheckedCompilerReceiptCandidate, InvocationFailure,
    InvocationFailureKind, OperationInvocation, OperationKind, OperationReceipt, Producer,
    ProducerStatus, ReceiptOutput, ScriptedReceipt, ValidatedPortableReceipt,
};
pub use replay::{ReplayFailure, ReplayFailureKind, ReplayManifest, ReplayVersionRegistry};
pub use worker::{
    Bag10ExecutionFailure, BoundedClassification, Retryability, ScriptedBoundary,
    ScriptedExecution, WorkerFailure, WorkerFailureClassification, WorkerFailureContext,
    WorkerFailureKind, WorkerFailureStage, WorkerResult, WorkerResultKind, WorkerTerminal,
};
