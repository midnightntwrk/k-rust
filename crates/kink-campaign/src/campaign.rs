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
    /// Two complete sides cannot be compared under the declaration.
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
    /// Another declared limit or incomparable result prevented a conclusion.
    Unknown,
    /// Infrastructure/backend/worker failure.
    Error,
}

/// One manifest-ordered test and its declaration-slot outcomes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TestPlan {
    /// Unique manifest test ID.
    pub test_id: String,
    /// Ordered nonempty oracle-slot outcomes.
    pub oracle_outcomes: Vec<OracleOutcome>,
}

/// A mutation candidate ready for scheduling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MutantPlan {
    /// Stable mutant identity.
    pub mutant_id: Digest,
    /// Manifest-ordered unique tests.
    pub tests: Vec<TestPlan>,
    /// Validation-stage classification, if execution must not begin.
    pub preclassified: Option<MutantStatus>,
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
    /// Exact killing-test prefix or full list.
    pub killing_test_ids: Vec<String>,
    /// Explicit skipped suffix under first-kill.
    pub skipped_test_ids: Vec<String>,
}

/// Derives a deterministic schedule result without creating suffix work.
pub fn derive_mutant_report(
    plan: &MutantPlan,
    schedule: ScheduleMode,
) -> Result<MutantReport, CampaignFailure> {
    let mut unique = BTreeSet::new();
    if plan.tests.is_empty()
        || !plan
            .tests
            .iter()
            .all(|test| !test.oracle_outcomes.is_empty() && unique.insert(test.test_id.as_str()))
    {
        return Err(CampaignFailure::new(
            CampaignFailureKind::InvalidManifest,
            "tests must be nonempty, unique, and contain an oracle declaration",
        ));
    }
    if let Some(status) = plan.preclassified {
        if matches!(status, MutantStatus::Killed | MutantStatus::Survived) {
            return Err(CampaignFailure::new(
                CampaignFailureKind::InvalidPreclassification,
                "killed and survived require scheduled oracle evidence",
            ));
        }
        return Ok(MutantReport {
            mutant_id: plan.mutant_id.clone(),
            status,
            executed_test_ids: Vec::new(),
            killing_test_ids: Vec::new(),
            skipped_test_ids: plan.tests.iter().map(|test| test.test_id.clone()).collect(),
        });
    }

    let mut executed = Vec::new();
    let mut killing = Vec::new();
    let mut seen_timeout = false;
    let mut seen_unknown = false;
    let mut seen_error = false;
    let mut first_kill = None;
    for (ordinal, test) in plan.tests.iter().enumerate() {
        if schedule == ScheduleMode::FirstKill && first_kill.is_some() {
            break;
        }
        if test.oracle_outcomes.contains(&OracleOutcome::Skipped) {
            return Err(CampaignFailure::new(
                CampaignFailureKind::FabricatedSkip,
                "input outcomes may not pre-mark a selected oracle as skipped",
            ));
        }
        executed.push(test.test_id.clone());
        if test.oracle_outcomes.contains(&OracleOutcome::Distinguish) {
            killing.push(test.test_id.clone());
            first_kill = Some(ordinal);
        } else if test.oracle_outcomes.contains(&OracleOutcome::Error) {
            seen_error = true;
        } else if test.oracle_outcomes.contains(&OracleOutcome::Timeout) {
            seen_timeout = true;
        } else if test.oracle_outcomes.iter().any(|outcome| {
            matches!(
                outcome,
                OracleOutcome::Unknown | OracleOutcome::Incomparable
            )
        }) {
            seen_unknown = true;
        }
    }
    let status = if !killing.is_empty() {
        MutantStatus::Killed
    } else if seen_error {
        MutantStatus::Error
    } else if seen_timeout {
        MutantStatus::Timeout
    } else if seen_unknown {
        MutantStatus::Unknown
    } else {
        MutantStatus::Survived
    };
    let skipped_test_ids = plan.tests[executed.len()..]
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
    /// Manifest test/slot shape is invalid.
    InvalidManifest,
    /// A conclusive status was supplied without oracle evidence.
    InvalidPreclassification,
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
