//! Mutation campaigns: running, oracle comparison, classification, scheduling and scoring.
//!
//! [`run_campaign`] compiles the baseline and each mutant through kink-native, executes
//! every test, and maps each run to typed [`OracleSide`]s without ever turning incomplete
//! evidence into a value. [`compare_supplied`] compares two sides of one declaration, and
//! [`derive_mutant_report`] and [`score`] fold the outcomes into mutant statuses and a
//! score. There is no caching or provenance bookkeeping.

mod campaign;
mod oracle;
mod runner;

pub use campaign::{
    BaselineAdmission, CampaignFailure, CampaignFailureKind, ExecutionFailureKind, ManifestTest,
    MutantId, MutantPlan, MutantReport, MutantScopeFailure, MutantStatus, OracleOutcome, Rational,
    ScheduleMode, Score, TestPlan, TestRun, derive_mutant_report, score, validate_baseline,
};
pub use oracle::{
    CrashPolicy, ExitStop, FinalResult, OracleFailure, OracleFailureKind, OracleKind, OracleSide,
    OracleValue, PatternValue, TerminalClass, compare_supplied,
};
pub use runner::{
    Campaign, CampaignRun, MutantRun, OracleDeclaration, Projection, SideRun, StateProjection,
    TestCase, TestEvidence, pattern_side, run_campaign, slot_outcome, state_side,
};
