use kink_portable::Digest;
use std::collections::BTreeSet;
use std::fmt;

/// Campaign scheduling policy. It never participates in raw attempt identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScheduleMode {
    /// Stop after the first killing test in manifest order.
    FirstKill,
    /// Run every selected test.
    Full,
}

/// Typed outcome of one declaration-scoped oracle slot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OracleOutcome {
    /// Complete agreement.
    Agree,
    /// Complete semantic distinction; the only killing outcome.
    Distinguish,
    /// Two complete sides cannot be compared under the declaration; folds to
    /// `Error`, because more bounds never settle it.
    Incomparable,
    /// A declared time bound prevented a conclusion.
    Timeout,
    /// Incomplete/solver/bounded evidence prevented a conclusion.
    Unknown,
    /// Untrustworthy worker/backend/infrastructure result.
    Error,
    /// Slot was not selected because first-kill stopped earlier.
    Skipped,
}

/// Final candidate classification. There is deliberately no equivalence status.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MutantStatus {
    /// At least one oracle distinguished the mutant.
    Killed,
    /// Every selected oracle completed and agreed.
    Survived,
    /// Validation or compilation rejected the mutant.
    Invalid,
    /// A time limit prevented a conclusion.
    Timeout,
    /// Another declared limit or indeterminate evidence prevented a conclusion.
    Unknown,
    /// Infrastructure, backend, worker or oracle-declaration failure.
    Error,
}

/// A failure that invalidates every test's evidence for one mutant.
///
/// It dominates every oracle outcome, including a kill: a distinction computed
/// against a rejected, unlowered or corrupted mutant says nothing about the
/// mutant that is reported. Only `Infrastructure` can arise after execution
/// began; every other kind stops the mutant before any test runs, so a plan
/// carrying one lists no tests.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MutantScopeFailure {
    /// Validation, lowering or backend compilation rejected the mutant.
    Rejected,
    /// Lowering or validation of the mutant does not terminate.
    LoweringNontermination,
    /// A declared time limit was reached while lowering the mutant.
    LoweringTimeLimit,
    /// A declared resource bound was reached while lowering the mutant.
    LoweringResourceLimit,
    /// Infrastructure failure or artifact corruption affecting the whole mutant.
    Infrastructure,
}

impl MutantScopeFailure {
    /// Status of a mutant with this failure, whatever its oracles reported.
    #[must_use]
    pub const fn status(self) -> MutantStatus {
        match self {
            Self::Rejected | Self::LoweringNontermination => MutantStatus::Invalid,
            Self::LoweringTimeLimit => MutantStatus::Timeout,
            Self::LoweringResourceLimit => MutantStatus::Unknown,
            Self::Infrastructure => MutantStatus::Error,
        }
    }

    /// Whether the mutant stopped before execution, so no test can have run.
    const fn precedes_execution(self) -> bool {
        !matches!(self, Self::Infrastructure)
    }
}

/// Why one test's mutant execution produced no operand for any of its slots.
///
/// Bounded or indeterminate evidence that still yields an operand belongs in
/// the slot outcome (`OracleSide::Unknown` or an incomplete `Normal`), not here.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionFailureKind {
    /// The run could not decide how to proceed, for example a solver step.
    Indeterminate,
    /// A declared step, depth or other resource bound stopped the run.
    ResourceLimit,
    /// A declared wall-clock limit stopped the run.
    TimeLimit,
    /// The worker, backend or other infrastructure failed during the run.
    Infrastructure,
}

impl ExecutionFailureKind {
    /// Status this failed test contributes to the inconclusive fold.
    #[must_use]
    pub const fn status(self) -> MutantStatus {
        match self {
            Self::Indeterminate | Self::ResourceLimit => MutantStatus::Unknown,
            Self::TimeLimit => MutantStatus::Timeout,
            Self::Infrastructure => MutantStatus::Error,
        }
    }
}

/// What one test's mutant execution produced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TestRun {
    /// The run produced operands; one outcome per declared oracle slot.
    Compared(Vec<OracleOutcome>),
    /// The run produced no operand, so no slot was compared.
    Failed(ExecutionFailureKind),
}

/// One manifest-ordered test and what its mutant execution produced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TestPlan {
    /// Unique manifest test ID.
    pub test_id: String,
    /// Slot outcomes, or the failure that prevented them.
    pub run: TestRun,
}

/// One selected test of the campaign's test manifest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ManifestTest {
    /// Unique manifest test ID.
    pub test_id: String,
    /// Number of declared oracle slots; at least one.
    pub slot_count: usize,
}

/// A mutation candidate ready for scheduling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MutantPlan {
    /// Stable mutant identity.
    pub mutant_id: Digest,
    /// Every manifest test in manifest order, or none when a mutant-scope
    /// failure stopped the mutant before execution began. A mutant rejected,
    /// or whose lowering did not finish, never ran, so it must list none.
    pub tests: Vec<TestPlan>,
    /// Failure invalidating every test's evidence; it decides the status.
    pub mutant_failure: Option<MutantScopeFailure>,
}

/// One scheduled mutant result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MutantReport {
    /// Mutant identity.
    pub mutant_id: Digest,
    /// Final closed classification.
    pub status: MutantStatus,
    /// Tests actually executed in manifest order.
    pub executed_test_ids: Vec<String>,
    /// Exact killing-test prefix or full list; empty unless `Killed`.
    pub killing_test_ids: Vec<String>,
    /// Explicit skipped suffix under first-kill.
    pub skipped_test_ids: Vec<String>,
}

/// Precedence of a status in the oracle fold; the fold keeps the maximum.
///
/// A kill stands on its own complete evidence, so it beats any inconclusive
/// outcome; complete agreement is what remains when nothing else was seen.
const fn fold_rank(status: MutantStatus) -> u8 {
    match status {
        MutantStatus::Survived => 0,
        MutantStatus::Unknown => 1,
        MutantStatus::Timeout => 2,
        MutantStatus::Error => 3,
        MutantStatus::Killed => 4,
        // Never produced by a slot or a failed test.
        MutantStatus::Invalid => 5,
    }
}

/// Status one compared slot contributes to the fold.
const fn slot_status(outcome: OracleOutcome) -> MutantStatus {
    match outcome {
        OracleOutcome::Agree => MutantStatus::Survived,
        OracleOutcome::Distinguish => MutantStatus::Killed,
        OracleOutcome::Incomparable | OracleOutcome::Error => MutantStatus::Error,
        OracleOutcome::Timeout => MutantStatus::Timeout,
        OracleOutcome::Unknown => MutantStatus::Unknown,
        // Rejected as input before the fold.
        OracleOutcome::Skipped => MutantStatus::Error,
    }
}

fn fold(left: MutantStatus, right: MutantStatus) -> MutantStatus {
    if fold_rank(right) > fold_rank(left) {
        right
    } else {
        left
    }
}

fn invalid_manifest(detail: &str) -> CampaignFailure {
    CampaignFailure::new(CampaignFailureKind::InvalidManifest, detail)
}

/// Rejects a manifest, or a plan that does not match it, before any fold.
fn check_plan(plan: &MutantPlan, manifest: &[ManifestTest]) -> Result<(), CampaignFailure> {
    let mut unique = BTreeSet::new();
    if manifest.is_empty()
        || !manifest
            .iter()
            .all(|test| test.slot_count > 0 && unique.insert(test.test_id.as_str()))
    {
        return Err(invalid_manifest(
            "the manifest must be nonempty, unique, and declare an oracle slot per test",
        ));
    }
    if let Some(failure) = plan.mutant_failure {
        if plan.tests.is_empty() {
            return Ok(());
        }
        if failure.precedes_execution() {
            return Err(invalid_manifest(
                "a mutant rejected or not lowered cannot carry executed tests",
            ));
        }
    }
    if plan.tests.len() != manifest.len() {
        return Err(invalid_manifest(
            "mutant tests differ from the selected-test manifest",
        ));
    }
    for (test, declared) in plan.tests.iter().zip(manifest) {
        if test.test_id != declared.test_id {
            return Err(invalid_manifest(
                "mutant tests differ from the selected-test manifest order",
            ));
        }
        if let TestRun::Compared(outcomes) = &test.run {
            if outcomes.len() != declared.slot_count {
                return Err(invalid_manifest(
                    "compared outcomes differ from the declared oracle slots",
                ));
            }
            if outcomes.contains(&OracleOutcome::Skipped) {
                return Err(CampaignFailure::new(
                    CampaignFailureKind::FabricatedSkip,
                    "input outcomes may not pre-mark a selected oracle as skipped",
                ));
            }
        }
    }
    Ok(())
}

/// Derives a deterministic schedule result without creating suffix work.
///
/// The plan must list every manifest test in order with one outcome per
/// declared slot, or no tests when a mutant-scope failure stopped the mutant
/// before execution; only an `Infrastructure` failure may accompany executed
/// tests. The status is one fold with a single precedence: a
/// mutant-scope failure, then any distinguishing slot (killed), then error
/// (including incomparable slots and failed infrastructure runs), timeout and
/// unknown, and complete agreement (survived) only when nothing else was seen.
pub fn derive_mutant_report(
    plan: &MutantPlan,
    manifest: &[ManifestTest],
    schedule: ScheduleMode,
) -> Result<MutantReport, CampaignFailure> {
    check_plan(plan, manifest)?;

    let mut executed = Vec::new();
    let mut killing = Vec::new();
    let mut status = MutantStatus::Survived;
    for test in &plan.tests {
        if schedule == ScheduleMode::FirstKill && !killing.is_empty() {
            break;
        }
        executed.push(test.test_id.clone());
        let test_status = match &test.run {
            TestRun::Compared(outcomes) => outcomes
                .iter()
                .map(|outcome| slot_status(*outcome))
                .fold(MutantStatus::Survived, fold),
            TestRun::Failed(kind) => kind.status(),
        };
        if test_status == MutantStatus::Killed {
            killing.push(test.test_id.clone());
        }
        status = fold(status, test_status);
    }
    if let Some(failure) = plan.mutant_failure {
        status = failure.status();
        killing.clear();
    }
    let skipped_test_ids = manifest[executed.len()..]
        .iter()
        .map(|test| test.test_id.clone())
        .collect();
    Ok(MutantReport {
        mutant_id: plan.mutant_id.clone(),
        status,
        executed_test_ids: executed,
        killing_test_ids: killing,
        skipped_test_ids,
    })
}

/// Baseline admission result, evaluated before mutant work.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BaselineAdmission {
    /// Validation and every declaration-scoped gate succeeded.
    Accepted,
    /// IR/lowering/backend validation failed.
    Invalid,
    /// At least one baseline oracle gate rejected.
    OracleFailed,
    /// Admission could not produce trustworthy evidence.
    Error,
}

/// Enforces the baseline-before-mutants gate.
pub fn validate_baseline(admission: BaselineAdmission) -> Result<(), CampaignFailure> {
    match admission {
        BaselineAdmission::Accepted => Ok(()),
        BaselineAdmission::Invalid => Err(CampaignFailure::new(
            CampaignFailureKind::BaselineInvalid,
            "baseline validation rejected before mutant scoring",
        )),
        BaselineAdmission::OracleFailed => Err(CampaignFailure::new(
            CampaignFailureKind::BaselineOracleFailed,
            "a baseline declaration-scoped oracle gate rejected",
        )),
        BaselineAdmission::Error => Err(CampaignFailure::new(
            CampaignFailureKind::BaselineError,
            "baseline admission did not produce trustworthy evidence",
        )),
    }
}

/// Exact reduced score ratio.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Rational {
    /// Reduced numerator.
    pub numerator: u64,
    /// Positive reduced denominator.
    pub denominator: u64,
}

/// Mutation score and explicit denominator counts.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Score {
    /// Number of killed mutants.
    pub killed: u64,
    /// Number of survived mutants.
    pub survived: u64,
    /// `killed + survived`.
    pub denominator: u64,
    /// Exact reduced score, or null when the denominator is zero.
    pub ratio: Option<Rational>,
}

/// Scores only killed and survived mutants.
#[must_use]
pub fn score(statuses: &[MutantStatus]) -> Score {
    let killed = statuses
        .iter()
        .filter(|status| **status == MutantStatus::Killed)
        .count() as u64;
    let survived = statuses
        .iter()
        .filter(|status| **status == MutantStatus::Survived)
        .count() as u64;
    let denominator = killed + survived;
    let ratio = if denominator == 0 {
        None
    } else {
        let divisor = gcd(killed, denominator);
        Some(Rational {
            numerator: killed / divisor,
            denominator: denominator / divisor,
        })
    };
    Score {
        killed,
        survived,
        denominator,
        ratio,
    }
}

const fn gcd(mut left: u64, mut right: u64) -> u64 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    if left == 0 { 1 } else { left }
}

/// Closed campaign failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CampaignFailureKind {
    /// Manifest test/slot shape is invalid, or a plan does not match it.
    InvalidManifest,
    /// A selected input was already marked skipped.
    FabricatedSkip,
    /// Baseline validation rejected.
    BaselineInvalid,
    /// Baseline oracle gate rejected.
    BaselineOracleFailed,
    /// Baseline admission had an infrastructure/backend failure.
    BaselineError,
}

/// Typed campaign failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CampaignFailure {
    kind: CampaignFailureKind,
    detail: String,
}

impl CampaignFailure {
    fn new(kind: CampaignFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Decision-bearing classification.
    #[must_use]
    pub const fn kind(&self) -> CampaignFailureKind {
        self.kind
    }
}

impl fmt::Display for CampaignFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for CampaignFailure {}
