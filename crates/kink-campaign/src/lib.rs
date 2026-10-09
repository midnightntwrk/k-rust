//! Mutation campaigns: running, oracle comparison, classification, scheduling and scoring.
//!
//! [`run_campaign`] compiles the baseline and each mutant through kink-native, executes
//! every test, and maps each run to typed [`OracleSide`]s without ever turning incomplete
//! evidence into a value. [`compare_supplied`] compares two sides of one declaration, and
//! [`derive_mutant_report`] and [`score`] fold the outcomes into mutant statuses and a
//! score. [`tally`] counts its exclusions from the generation and run; show it beside the ratio.

mod campaign;
mod manifest;
mod oracle;
pub use manifest::{CampaignManifest, ManifestError, ManifestInput, OperatorId, campaign_manifest};
mod report;
pub use report::{CAMPAIGN_REPORT_VERSION, CampaignReport, ReportError, campaign_report};
mod replay;
pub use replay::{ReplayDeclaration, ReplayOutcome, ReplayRefusal, replay};
mod runner;
pub mod selection;
pub use selection::{Coupled, MutantSelection, Sel, SelectionPolicy};

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
    Campaign, CampaignOptions, CampaignRun, MutantRun, OracleDeclaration, Projection, SideRun,
    StateProjection, Tally, TestCase, TestEvidence, pattern_side, run_campaign, run_campaign_with,
    slot_outcome, state_side, tally,
};
