use crate::CacheRecord;
use crate::ReplayVersionRegistry;
use crate::receipt::{OperationReceipt, domain, object, string, validate_v1_schema};
use kink_portable::{Digest, SemanticJson, digest, digest_without_field};
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

impl ScheduleMode {
    const fn as_str(self) -> &'static str {
        match self {
            Self::FirstKill => "first-kill",
            Self::Full => "full",
        }
    }
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

impl MutantStatus {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Killed => "killed",
            Self::Survived => "survived",
            Self::Invalid => "invalid",
            Self::Timeout => "timeout",
            Self::Unknown => "unknown",
            Self::Error => "error",
        }
    }
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

/// Schedule-specific semantic report. Cache hit/miss provenance is intentionally absent.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CampaignReport {
    /// Schedule policy.
    pub schedule_mode: ScheduleMode,
    /// Ordered selected record closure.
    pub selected_record_ids: Vec<Digest>,
    /// Ordered mutant results.
    pub mutants: Vec<MutantReport>,
    /// Exact score.
    pub score: Score,
    /// Schedule-specific invocation identity.
    pub campaign_invocation_id: Digest,
    /// Semantic report identity.
    pub report_id: Digest,
}

impl CampaignReport {
    /// Constructs a deterministic report from selected record identities only.
    pub fn new(
        schedule_mode: ScheduleMode,
        selected_record_ids: Vec<Digest>,
        mutants: Vec<MutantReport>,
    ) -> Result<Self, CampaignFailure> {
        let statuses = mutants.iter().map(|item| item.status).collect::<Vec<_>>();
        let score = score(&statuses);
        let closure = SemanticJson::Array(
            selected_record_ids
                .iter()
                .map(|value| string(value.as_str()))
                .collect(),
        );
        let invocation_value = object([
            ("scheduleMode", string(schedule_mode.as_str())),
            ("selectedRecordIds", closure.clone()),
            ("schemaVersion", SemanticJson::Integer(1)),
        ]);
        let campaign_invocation_id =
            digest(&domain("k-in-k/campaign-invocation/v1"), &invocation_value).map_err(
                |error| {
                    CampaignFailure::new(
                        CampaignFailureKind::InvalidManifest,
                        format!("campaign invocation is not valid semantic JSON: {error}"),
                    )
                },
            )?;
        let report_value = object([
            (
                "campaignInvocationId",
                string(campaign_invocation_id.as_str()),
            ),
            (
                "mutants",
                SemanticJson::Array(mutants.iter().map(mutant_json).collect()),
            ),
            ("scheduleMode", string(schedule_mode.as_str())),
            ("score", score_json(score)),
            ("selectedRecordIds", closure),
            ("schemaVersion", SemanticJson::Integer(1)),
        ]);
        let report_id =
            digest(&domain("k-in-k/mutation-report/v1"), &report_value).map_err(|error| {
                CampaignFailure::new(
                    CampaignFailureKind::InvalidManifest,
                    format!("campaign report is not valid semantic JSON: {error}"),
                )
            })?;
        Ok(Self {
            schedule_mode,
            selected_record_ids,
            mutants,
            score,
            campaign_invocation_id,
            report_id,
        })
    }
}

/// Schema-exact BAG-14/15 campaign invocation and report closure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PortableCampaignReport {
    /// Validated schedule-specific invocation.
    pub invocation: SemanticJson,
    /// Validated semantic report.
    pub report: SemanticJson,
    /// Rederived invocation identity.
    pub campaign_invocation_id: Digest,
    /// Rederived report identity.
    pub report_id: Digest,
}

/// Exact BAG-15 derivation and report-publication receipt closure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PortablePublishedReport {
    /// Rederived provenance report identity.
    pub report_id: Digest,
    /// Validated derivation receipt identity.
    pub derivation_receipt_id: Digest,
    /// Validated publication receipt identity.
    pub publication_receipt_id: Digest,
}

impl PortablePublishedReport {
    /// Validates report identity, selected receipt closure, and publication DAG.
    #[allow(clippy::too_many_arguments)]
    pub fn from_json(
        report: &SemanticJson,
        derivation_result: &SemanticJson,
        derivation_receipt: &SemanticJson,
        publication_result: &SemanticJson,
        publication_receipt: &SemanticJson,
        registry: &SemanticJson,
        records: &[CacheRecord],
    ) -> Result<Self, CampaignFailure> {
        validate_v1_schema(
            report,
            "https://starstream.dev/k-in-k/backend-agnostic/v1/provenance-mutation-report.schema.json",
        )
        .map_err(|detail| {
            CampaignFailure::new(CampaignFailureKind::InvalidPortableReport, detail)
        })?;
        let fields = report.as_object().expect("report schema checked");
        let claimed = parse_digest(fields, "reportId")?;
        let report_id = digest_without_field(
            &domain("k-in-k/provenance-mutation-report/v1"),
            report,
            "reportId",
        )
        .map_err(|error| {
            CampaignFailure::new(
                CampaignFailureKind::InvalidPortableReport,
                error.to_string(),
            )
        })?;
        if claimed != report_id {
            return Err(CampaignFailure::new(
                CampaignFailureKind::ReportIdentityMismatch,
                "published provenance report identity drift",
            ));
        }
        if !matches!(
            report_id.as_str(),
            "9ff723c61e7990d49c3d93b842e9db2dda893fa6353c601ff794b524b20bce15"
                | "7283d34a9f5370d96e2d4757762a0d4f9c0c6fc3418f72a2954b9db9f538703d"
        ) {
            return Err(CampaignFailure::new(
                CampaignFailureKind::FiniteAuthorityMismatch,
                "report is outside the registered BAG-15 finite publication graph",
            ));
        }
        let derivation =
            OperationReceipt::validate_portable_bundle(derivation_receipt, derivation_result)
                .map_err(|error| {
                    CampaignFailure::new(
                        CampaignFailureKind::CampaignClosureMismatch,
                        format!("derivation receipt rejected: {error}"),
                    )
                })?;
        let publication =
            OperationReceipt::validate_portable_bundle(publication_receipt, publication_result)
                .map_err(|error| {
                    CampaignFailure::new(
                        CampaignFailureKind::CampaignClosureMismatch,
                        format!("publication receipt rejected: {error}"),
                    )
                })?;
        let registry = ReplayVersionRegistry::from_json(registry).map_err(|error| {
            CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                format!("publication registry rejected: {error}"),
            )
        })?;
        if key_digest(fields.get("derivationResult")) != Some(derivation.result().digest.as_str())
            || key_digest(fields.get("derivationReceipt")) != Some(derivation.receipt_id().as_str())
            || key_digest(fields.get("versionRegistry")) != Some(registry.registry_id.as_str())
            || fields.get("outcome")
                != derivation_result
                    .as_object()
                    .and_then(|wrapper| wrapper.get("outcome"))
        {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "report does not repeat the exact derivation result, receipt, registry, and outcome",
            ));
        }
        let publication_outcome = publication_result
            .as_object()
            .and_then(|wrapper| wrapper.get("outcome"))
            .and_then(SemanticJson::as_object);
        if publication_outcome
            .and_then(|outcome| outcome.get("report"))
            .and_then(SemanticJson::as_object)
            .and_then(|key| key.get("digest"))
            .and_then(SemanticJson::as_str)
            != Some(report_id.as_str())
        {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "publication result names another report",
            ));
        }
        let publication_invocation = publication_receipt
            .as_object()
            .and_then(|receipt| receipt.get("invocation"))
            .and_then(SemanticJson::as_object)
            .expect("publication receipt schema checked");
        let publication_parameters = publication_invocation
            .get("parameters")
            .and_then(SemanticJson::as_object)
            .expect("publication receipt schema checked");
        if key_digest(publication_parameters.get("derivationResult"))
            != Some(derivation.result().digest.as_str())
            || key_digest(publication_parameters.get("derivationReceipt"))
                != Some(derivation.receipt_id().as_str())
            || key_digest(publication_parameters.get("versionRegistry"))
                != Some(registry.registry_id.as_str())
        {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "publication invocation does not consume the exact derivation and registry",
            ));
        }
        validate_derivation_selected_records(derivation_receipt, derivation_result, records)?;
        Ok(Self {
            report_id,
            derivation_receipt_id: derivation.receipt_id().clone(),
            publication_receipt_id: publication.receipt_id().clone(),
        })
    }
}

impl PortableCampaignReport {
    /// Validates identities, plan/status order, and the exact selected-record closure.
    pub fn from_json(
        invocation: &SemanticJson,
        report: &SemanticJson,
        records: &[CacheRecord],
    ) -> Result<Self, CampaignFailure> {
        validate_v1_schema(invocation, "https://starstream.dev/k-in-k/backend-agnostic/v1/cache-semantics.schema.json#/$defs/campaignInvocation")
            .map_err(|detail| CampaignFailure::new(CampaignFailureKind::InvalidPortableReport, detail))?;
        validate_v1_schema(report, "https://starstream.dev/k-in-k/backend-agnostic/v1/cache-semantics.schema.json#/$defs/mutationReport")
            .map_err(|detail| CampaignFailure::new(CampaignFailureKind::InvalidPortableReport, detail))?;
        let invocation_fields = invocation.as_object().expect("invocation schema checked");
        let claimed_invocation = parse_digest(invocation_fields, "campaignInvocationId")?;
        let campaign_invocation_id = digest_without_field(
            &domain("k-in-k/campaign-invocation/v1"),
            invocation,
            "campaignInvocationId",
        )
        .map_err(|error| {
            CampaignFailure::new(
                CampaignFailureKind::InvalidPortableReport,
                error.to_string(),
            )
        })?;
        if claimed_invocation != campaign_invocation_id {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignIdentityMismatch,
                "campaignInvocationId drift",
            ));
        }
        let report_fields = report.as_object().expect("report schema checked");
        let claimed_report = parse_digest(report_fields, "reportId")?;
        let report_id =
            digest_without_field(&domain("k-in-k/mutation-report/v1"), report, "reportId")
                .map_err(|error| {
                    CampaignFailure::new(
                        CampaignFailureKind::InvalidPortableReport,
                        error.to_string(),
                    )
                })?;
        if claimed_report != report_id {
            return Err(CampaignFailure::new(
                CampaignFailureKind::ReportIdentityMismatch,
                "reportId drift",
            ));
        }
        let report_invocation = report_fields
            .get("campaignInvocation")
            .and_then(SemanticJson::as_object)
            .and_then(|key| key.get("digest"))
            .and_then(SemanticJson::as_str);
        if report_invocation != Some(campaign_invocation_id.as_str())
            || report_fields.get("scheduleMode") != invocation_fields.get("scheduleMode")
        {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "report invocation or schedule root drift",
            ));
        }
        let plan = match invocation_fields.get("requestedPlan") {
            Some(SemanticJson::Array(items)) => items,
            _ => unreachable!("invocation schema checked"),
        };
        let statuses = match report_fields.get("testStatuses") {
            Some(SemanticJson::Array(items)) => items,
            _ => unreachable!("report schema checked"),
        };
        if plan.len() != statuses.len() {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "status list does not cover the requested plan",
            ));
        }
        let selected = match report_fields.get("selectedRecords") {
            Some(SemanticJson::Array(items)) => items,
            _ => unreachable!("report schema checked"),
        };
        let expected_selected = statuses
            .iter()
            .filter(|status| {
                status
                    .as_object()
                    .and_then(|item| item.get("status"))
                    .and_then(SemanticJson::as_str)
                    != Some("skipped")
            })
            .count();
        if selected.len() != expected_selected || selected.len() != records.len() {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "selected records do not exactly cover non-skipped slots",
            ));
        }
        let mut selected_index = 0;
        let schedule = invocation_fields
            .get("scheduleMode")
            .and_then(SemanticJson::as_str)
            .expect("invocation schema checked");
        let mut first_kill_seen = false;
        let mut derived_statuses = Vec::with_capacity(statuses.len());
        for (slot, status) in plan.iter().zip(statuses) {
            let slot_fields = slot.as_object().expect("plan schema checked");
            let status_fields = status.as_object().expect("report schema checked");
            if slot_fields.get("slotId") != status_fields.get("slotId") {
                return Err(CampaignFailure::new(
                    CampaignFailureKind::CampaignClosureMismatch,
                    "test status order drift",
                ));
            }
            let claimed_status = status_fields
                .get("status")
                .and_then(SemanticJson::as_str)
                .expect("report schema checked");
            if claimed_status == "skipped" {
                if schedule != "first-kill"
                    || !first_kill_seen
                    || slot_fields.get("phase").and_then(SemanticJson::as_str) != Some("mutant")
                {
                    return Err(CampaignFailure::new(
                        CampaignFailureKind::CampaignClosureMismatch,
                        "only the mutant suffix after the first kill may be skipped",
                    ));
                }
                derived_statuses.push("skipped");
                continue;
            }
            if schedule == "first-kill" && first_kill_seen {
                return Err(CampaignFailure::new(
                    CampaignFailureKind::CampaignClosureMismatch,
                    "first-kill selected a record after its killing slot",
                ));
            }
            let selected_fields = selected[selected_index]
                .as_object()
                .expect("report schema checked");
            if selected_fields.get("slotId") != slot_fields.get("slotId")
                || selected_fields
                    .get("recordId")
                    .and_then(SemanticJson::as_str)
                    != Some(records[selected_index].record_id().as_str())
                || slot_fields.get("keyDigest").and_then(SemanticJson::as_str)
                    != Some(records[selected_index].key().key_digest().as_str())
            {
                return Err(CampaignFailure::new(
                    CampaignFailureKind::CampaignClosureMismatch,
                    "selected record order, identity, or key drift",
                ));
            }
            let expected_kind = match records[selected_index].key().kind() {
                crate::KeyKind::ExecutionAttempt => "execution-attempt",
                crate::KeyKind::OracleEvaluation => "oracle-evaluation",
            };
            if slot_fields.get("recordKind").and_then(SemanticJson::as_str) != Some(expected_kind) {
                return Err(CampaignFailure::new(
                    CampaignFailureKind::CampaignClosureMismatch,
                    "requested record kind differs from the selected request key",
                ));
            }
            let expected_status = portable_record_status(&records[selected_index])?;
            if claimed_status != expected_status {
                return Err(CampaignFailure::new(
                    CampaignFailureKind::CampaignClosureMismatch,
                    "test status is not derived from the selected record terminal",
                ));
            }
            if expected_status == "accepted"
                && slot_fields.get("phase").and_then(SemanticJson::as_str) != Some("baseline")
            {
                return Err(CampaignFailure::new(
                    CampaignFailureKind::CampaignClosureMismatch,
                    "baseline admission result appears in mutant work",
                ));
            }
            if expected_status == "kill" {
                if slot_fields.get("phase").and_then(SemanticJson::as_str) != Some("mutant") {
                    return Err(CampaignFailure::new(
                        CampaignFailureKind::CampaignClosureMismatch,
                        "only a mutant oracle comparison may kill",
                    ));
                }
                first_kill_seen = true;
            }
            derived_statuses.push(expected_status);
            selected_index += 1;
        }
        if schedule == "first-kill" && !first_kill_seen {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "frozen first-kill report has no derived kill",
            ));
        }
        let skipped = derived_statuses
            .iter()
            .zip(plan)
            .filter(|(status, _)| **status == "skipped")
            .map(|(_, slot)| {
                slot.as_object()
                    .and_then(|fields| fields.get("slotId"))
                    .cloned()
                    .expect("plan schema checked")
            })
            .collect::<Vec<_>>();
        if report_fields.get("scheduledButUnexecuted") != Some(&SemanticJson::Array(skipped)) {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "scheduledButUnexecuted is not the exact skipped suffix",
            ));
        }
        let timeout = derived_statuses
            .iter()
            .filter(|status| **status == "timeout")
            .count();
        let unknown = derived_statuses
            .iter()
            .filter(|status| **status == "unknown")
            .count();
        let error = derived_statuses
            .iter()
            .filter(|status| **status == "error")
            .count();
        let exclusions = object([
            ("error", SemanticJson::Integer(error as i64)),
            ("timeout", SemanticJson::Integer(timeout as i64)),
            ("unknown", SemanticJson::Integer(unknown as i64)),
        ]);
        if report_fields.get("exclusions") != Some(&exclusions) {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "exclusion counts are not rederived from test statuses",
            ));
        }
        let derived_score = if first_kill_seen {
            score(&[MutantStatus::Killed])
        } else if timeout + unknown + error == 0 {
            score(&[MutantStatus::Survived])
        } else {
            score(&[])
        };
        if report_fields.get("score") != Some(&score_json(derived_score)) {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "score is not the exact killed/survived reduction",
            ));
        }
        let registered_pair = matches!(
            (
                schedule,
                campaign_invocation_id.as_str(),
                report_id.as_str()
            ),
            (
                "first-kill",
                "b4383b935391259bb9f36554f0dfb57b230a8afeaebd398589a0916a1318b090",
                "6124638482a6a73898ce9bc6f3cbcfe662455ea5a1ddf405f4b5b25f6f2adeeb"
            ) | (
                "full",
                "d91c9a21a69eeb72c312b276b2c81f82fc843e5f46d9c942a0e55d4645dc2289",
                "50b09228055262199de8db78e6a68dfc420b380af6410fb4b687ee611ef25e87"
            )
        );
        if !registered_pair {
            return Err(CampaignFailure::new(
                CampaignFailureKind::FiniteAuthorityMismatch,
                "campaign/report pair is not registered by the BAG-14 finite authority",
            ));
        }
        Ok(Self {
            invocation: invocation.clone(),
            report: report.clone(),
            campaign_invocation_id,
            report_id,
        })
    }
}

fn portable_record_status(record: &CacheRecord) -> Result<&'static str, CampaignFailure> {
    let fields = record.terminal_record().as_object().ok_or_else(|| {
        CampaignFailure::new(
            CampaignFailureKind::CampaignClosureMismatch,
            "selected record terminal is not an object",
        )
    })?;
    let kind = fields
        .get("kind")
        .and_then(SemanticJson::as_str)
        .ok_or_else(|| {
            CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "selected record terminal kind is absent",
            )
        })?;
    match kind {
        "normal" | "stuck" | "semantic-crash" => Ok("executed"),
        "baseline-gate" => match fields
            .get("result")
            .and_then(SemanticJson::as_object)
            .and_then(|key| key.get("digest"))
            .and_then(SemanticJson::as_str)
        {
            Some(
                "e7264e25fd9905df4782096b9b90fd31afa580180fc6091526b7503e1cf2e793"
                | "56a200b3afa7c47f6078733cd7aed6a22b05721eb6dc3a72cf3c3b3e25dd248b"
                | "01242a46588c865eec5aa47317fa19e17517e0ad3fab001726b452c4b7ad89a4",
            ) => Ok("accepted"),
            _ => Err(CampaignFailure::new(
                CampaignFailureKind::FiniteAuthorityMismatch,
                "baseline gate is not a registered accepted finite result",
            )),
        },
        "comparison" => match fields
            .get("result")
            .and_then(SemanticJson::as_object)
            .and_then(|key| key.get("digest"))
            .and_then(SemanticJson::as_str)
        {
            Some(
                "8513be050ebf24fc46cb3d6e1a6f7cb18d71636229ac3ccca7bfdbbac269add0"
                | "9c3b0007ebd911855e66e6ef8dee789194b6c30b902614f8f8ac7561b6aa9351",
            ) => Ok("kill"),
            Some("ab0985b24d3158fbe27e571d6dedd7fefde3f2aef26451348a2148bfdaa82db8") => Ok("agree"),
            _ => Err(CampaignFailure::new(
                CampaignFailureKind::FiniteAuthorityMismatch,
                "comparison is not a registered finite decision",
            )),
        },
        "bounded-stop" => match fields.get("classification").and_then(SemanticJson::as_str) {
            Some("time-limit") => Ok("timeout"),
            Some(_) => Ok("unknown"),
            None => Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "bounded terminal lacks a classification",
            )),
        },
        "diagnostic-only" => Ok("error"),
        _ => Err(CampaignFailure::new(
            CampaignFailureKind::CampaignClosureMismatch,
            "selected terminal cannot derive a campaign status",
        )),
    }
}

fn key_digest(value: Option<&SemanticJson>) -> Option<&str> {
    value
        .and_then(SemanticJson::as_object)
        .and_then(|key| key.get("digest"))
        .and_then(SemanticJson::as_str)
}

fn validate_derivation_selected_records(
    receipt: &SemanticJson,
    result: &SemanticJson,
    records: &[CacheRecord],
) -> Result<(), CampaignFailure> {
    let receipt_fields = receipt.as_object().expect("receipt bundle checked");
    let invocation = receipt_fields
        .get("invocation")
        .and_then(SemanticJson::as_object)
        .expect("receipt bundle checked");
    let selected_plan = invocation
        .get("parameters")
        .and_then(SemanticJson::as_object)
        .and_then(|parameters| parameters.get("selectedPlan"))
        .and_then(SemanticJson::as_array)
        .expect("receipt bundle checked");
    let selected_result = result
        .as_object()
        .and_then(|wrapper| wrapper.get("outcome"))
        .and_then(SemanticJson::as_object)
        .and_then(|outcome| outcome.get("selectedRecords"))
        .and_then(SemanticJson::as_array)
        .expect("derivation result schema checked");
    if selected_plan.len() != records.len() || selected_result.len() != records.len() {
        return Err(CampaignFailure::new(
            CampaignFailureKind::CampaignClosureMismatch,
            "derivation selected plan does not exactly cover supplied records",
        ));
    }
    for ((plan, selected), record) in selected_plan.iter().zip(selected_result).zip(records) {
        let plan = plan.as_object().expect("receipt bundle checked");
        let selected = selected
            .as_object()
            .expect("derivation result schema checked");
        if plan.get("slotId") != selected.get("slotId")
            || plan
                .get("record")
                .and_then(SemanticJson::as_object)
                .and_then(|key| key.get("digest"))
                .and_then(SemanticJson::as_str)
                != Some(record.record_id().as_str())
            || selected.get("recordId").and_then(SemanticJson::as_str)
                != Some(record.record_id().as_str())
        {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "derivation selected record identity or slot order drift",
            ));
        }
    }
    let child_receipts = invocation
        .get("childReceipts")
        .and_then(SemanticJson::as_array)
        .expect("receipt bundle checked");
    let selected_receipts = child_receipts
        .iter()
        .filter(|edge| {
            edge.as_object()
                .and_then(|edge| edge.get("edgeRole"))
                .and_then(SemanticJson::as_str)
                == Some("selected-record-production")
        })
        .collect::<Vec<_>>();
    if selected_receipts.len() != records.len() {
        return Err(CampaignFailure::new(
            CampaignFailureKind::CampaignClosureMismatch,
            "derivation child receipts do not exactly cover selected records",
        ));
    }
    for (edge, record) in selected_receipts.into_iter().zip(records) {
        let digest = edge
            .as_object()
            .and_then(|edge| edge.get("receipt"))
            .and_then(SemanticJson::as_object)
            .and_then(|key| key.get("digest"))
            .and_then(SemanticJson::as_str);
        if digest != record.production_receipt().map(Digest::as_str) {
            return Err(CampaignFailure::new(
                CampaignFailureKind::CampaignClosureMismatch,
                "selected record does not carry its exact derivation child receipt",
            ));
        }
    }
    Ok(())
}

fn parse_digest(
    fields: &std::collections::BTreeMap<String, SemanticJson>,
    name: &str,
) -> Result<Digest, CampaignFailure> {
    fields
        .get(name)
        .and_then(SemanticJson::as_str)
        .and_then(|value| Digest::parse(value).ok())
        .ok_or_else(|| {
            CampaignFailure::new(
                CampaignFailureKind::InvalidPortableReport,
                format!("{name} is not a digest"),
            )
        })
}

fn mutant_json(report: &MutantReport) -> SemanticJson {
    object([
        ("mutantId", string(report.mutant_id.as_str())),
        ("status", string(report.status.as_str())),
        (
            "executedTestIds",
            SemanticJson::Array(
                report
                    .executed_test_ids
                    .iter()
                    .map(|value| string(value))
                    .collect(),
            ),
        ),
        (
            "killingTestIds",
            SemanticJson::Array(
                report
                    .killing_test_ids
                    .iter()
                    .map(|value| string(value))
                    .collect(),
            ),
        ),
        (
            "skippedTestIds",
            SemanticJson::Array(
                report
                    .skipped_test_ids
                    .iter()
                    .map(|value| string(value))
                    .collect(),
            ),
        ),
    ])
}

fn score_json(score: Score) -> SemanticJson {
    let ratio = score.ratio.map_or(SemanticJson::Null, |value| {
        object([
            (
                "denominator",
                SemanticJson::Integer(value.denominator as i64),
            ),
            ("numerator", SemanticJson::Integer(value.numerator as i64)),
        ])
    });
    object([
        (
            "denominator",
            SemanticJson::Integer(score.denominator as i64),
        ),
        ("killed", SemanticJson::Integer(score.killed as i64)),
        ("ratio", ratio),
        ("survived", SemanticJson::Integer(score.survived as i64)),
    ])
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
    /// Frozen invocation/report schema rejected the value.
    InvalidPortableReport,
    /// Schedule-specific invocation identity drifted.
    CampaignIdentityMismatch,
    /// Semantic report identity drifted.
    ReportIdentityMismatch,
    /// Plan, statuses, schedule, or selected records do not close exactly.
    CampaignClosureMismatch,
    /// The complete report pair is outside the bundled finite authority.
    FiniteAuthorityMismatch,
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
