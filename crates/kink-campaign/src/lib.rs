//! Mutant classification, scheduling, scoring and oracle comparison.
//!
//! Callers supply already-evaluated oracle sides and per-test outcomes; this
//! crate folds them into mutant statuses and a score. It performs no K
//! execution, caching or provenance bookkeeping.

mod campaign;
mod oracle;

pub use campaign::{
    BaselineAdmission, CampaignFailure, CampaignFailureKind, ExecutionFailureKind, ManifestTest,
    MutantPlan, MutantReport, MutantScopeFailure, MutantStatus, OracleOutcome, Rational,
    ScheduleMode, Score, TestPlan, TestRun, derive_mutant_report, score, validate_baseline,
};
pub use oracle::{
    CrashPolicy, OracleFailure, OracleFailureKind, OracleKind, OracleSide, compare_supplied,
};
