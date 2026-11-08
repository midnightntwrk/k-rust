//! Mutation campaigns: running, oracle comparison, classification, scheduling and scoring.
//!
//! [`run_campaign`] compiles the baseline and each mutant through kink-native, executes
//! every test, and maps each run to typed [`OracleSide`]s without ever turning incomplete
//! evidence into a value. [`compare_supplied`] compares two sides of one declaration, and
//! [`derive_mutant_report`] and [`score`] fold the outcomes into mutant statuses and a
//! score. [`tally`] counts its exclusions from the generation and run; show it beside the ratio.
//! [`identity`] holds kink's build identity (the running executable's digest, which guards all of
//! kink's verdict code) and kink's semantics identity (the versions of its versioned algorithms).
//! Every store honoured without re-deriving its verdicts (kink-corpus stores, kink-flow's caches
//! and run document) is bound to both, and under the Z3 profile to the Z3 build its verdicts were
//! decided on ([`identity::z3_difference`]); campaign manifests name the semantics identity and
//! the Z3 build but not kink's build, so campaign reports stay independent of kink's executable.

mod campaign;
mod cells;
pub mod condition;
pub use cells::{
    CellLayout, CellLayoutRefusal, CellProjection, Collection, CollectionKind, LaidOutCell,
    Through, UnobservedPosition,
};
pub use condition::{StopOracle, StopWhen};
pub mod identity;
pub mod observation;
pub use identity::{
    KINK_IDENTITY, RESULT_SCHEMA_VERSION, identity_difference, kink_build, kink_identity,
    writer_difference, z3_build, z3_difference,
};
pub use observation::{
    BaselineRecord, CYCLE_STATES, ChannelEnd, ChannelRecord, ChannelSets, Closure, Comparison,
    Element, Evaluated, Horizon, Log, OBSERVATION_VERSION, Observation, ObservationEvaluator,
    ObservationFunctions, ObservationVerdict, Observe, ObserveFunctions, Opened, Opening, Outside,
    PathRecord, PointClass, Position, Stutter,
};
mod manifest;
mod oracle;
mod plan;
pub use manifest::{
    CAMPAIGN_MANIFEST_VERSION, CampaignManifest, ManifestError, ManifestInput, ManifestOperator,
    MultiManifestInput, OperatorId, campaign_manifest, campaign_manifest_multi,
    campaign_manifest_multi_with_budget, campaign_manifest_multi_with_options, same_admission,
};
pub use plan::{BudgetMutants, CampaignPlan, CampaignPlanError, campaign_plan};
mod report;
pub use report::{
    CAMPAIGN_REPORT_VERSION, CampaignReport, ReportError, campaign_report, campaign_report_multi,
    report_status_name, report_tally,
};
mod replay;
pub use replay::{
    ReplayDeclaration, ReplayOperator, ReplayOutcome, ReplayRefusal, replay, replay_with_budget,
    replay_with_options,
};
mod runner;
pub mod selection;
pub mod state_match;
pub use selection::{CompiledEdit, Coupled, MutantSelection, Sel, SelectionPolicy, Witness};
pub use state_match::{MatchAnswer, MatchUnknown, StoppedMatch, judge_matches};

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
    AHEAD_PER_WORKER, BaselineRecording, BaselineSession, CallRecording, Campaign, CampaignOptions,
    CampaignRun, ClaimFreeMutant, CrossCause, CrossEnd, CrossRefusal, FirstTests, LeafCensus,
    MutantAdmission, MutantRefusal, MutantRun, MutantStage, ONE_SIDED_VERSION, ObservedDifference,
    OneSided, OracleDeclaration, Projection, RunNotes, RunOptions, RunRecording, RunStop,
    STOP_VERSION, SideRun, StateProjection, Stop, Tally, TestCase, TestEvidence, WorkBudget,
    claim_free_mutant, mutant_compiles, observed_difference, pattern_side, run_campaign,
    run_campaign_multi, run_campaign_multi_ordered, run_campaign_multi_with, run_campaign_with,
    slot_outcome, state_side, tally,
};
