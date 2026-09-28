//! Runs a campaign through kink-native and maps each run to typed oracle sides.
//!
//! The baseline and every mutant execute every test with one observed, time-bounded
//! [`ExecutionAdapter`] run (under `FirstKill`, a mutant only through its first killing
//! test), read through the kink-native bridge. Each declared oracle
//! turns the bridged paths into one [`OracleSide`]; each mapping is an exhaustive
//! `match` that never turns incomplete evidence into a value:
//!
//! - A state oracle (exit stop or final result) needs every path complete and a
//!   collection that stopped for lack of work. The PathSet run
//!   qualifies, because k-rust's merging of converging branches keeps every distinct final
//!   state. Any other stop is `Error` for an error or a cancelled leaf (until upstream tells
//!   cancellation from timeout), and `Unknown` otherwise, including a backend diagnostic.
//! - A single crash terminal is a `SemanticCrash` side carrying its terminal term; a
//!   crash among several terminals is `Unknown`.
//! - A terminal term with a free variable is `Unknown`. A symbolic run's complete stuck leaf
//!   stands for all of its instances, so its term is not one value: comparing such terms
//!   structurally, or classifying them, is not a comparison of the values the programs compute.
//! - An undefined step (a feasible `Trivial` leaf, `PathStop::UndefinedStep`) is a complete
//!   terminal. Its exit stop is the class `UndefinedStep` without a code, and its final result
//!   is its last configuration, the pre-step term, as for a stuck terminal.
//! - A pattern oracle is `kink_pattern::evaluate_with` over the paths with
//!   `BackendRelations` on the backend that ran the test. Relations use k-rust's unifier
//!   and, in a Z3 build, exact solver queries; undecided relations are `Unknown`. `Unknown` and `Error`
//!   evaluations and pattern failures are never values, and declared bindings need
//!   complete exhaustive coverage. Binding sets containing symbolic terms or witnesses
//!   with assumptions are `Unknown`: a set of symbolic terms is not a value of any instance.
//!   A `Match` needs witnesses on real prefixes only
//!   (`PathStop::has_real_prefix`): the bridge makes a vacuous leaf, and a symbolic
//!   or constrained leaf not shown feasible, `SolverUnknown`, and every path of a run with a
//!   backend diagnostic `BackendLimit`, and an occurrence there is no witness.
//!
//! A test whose initial state has an element or set variable is symbolic: its verdict is a
//! claim about every ground instance, and k-rust's answer supports that claim only while the
//! definition's trusted claims (`total`, `functional`, `preserves-definedness`, lemmas, ...)
//! hold. The baseline's are its author's, and every baseline test runs on the baseline as
//! written. A mutant's patch can falsify them, so a mutant runs its symbolic tests on its
//! withdrawn definition ([`kink_patch::ClaimSupport::withdraw`]): the patch plus the removal
//! of every claim whose support the patch touched. A mutant whose patch writes a claim itself,
//! or touches a lemma's support, has no such definition, and its symbolic tests are
//! `Failed(UnsupportedClaims)`. A ground test compares two concrete runs, what the backend
//! computed for each definition as written, so it runs on the mutant as written.
//!
//! A run the watchdog cancelled is `TestRun::Failed(TimeLimit)`; an adapter or bridge
//! failure is `TestRun::Failed(Infrastructure)`. A rejected mutant runs nothing. The
//! mutants are the candidates of one folded generation derived from the campaign's own
//! baseline, and only a complete, nonempty generation is scored.
//!
//! A mutant is Killed only through a test with one of three forms of `Distinguish`:
//! (i) a state-slot `Distinguish`, which means the ground terminal sets differ;
//! (ii) a pattern-slot `Distinguish` on a test that also has a state-slot `Distinguish`;
//! or (iii) a pattern-slot `Distinguish` on a test for which `certify_difference` returned
//! `Proved`. `Proved` means some ground instance of the test's initial state has, as the
//! two definitions run in k-rust, a baseline state sequence that no mutant-side sequence
//! equals, or the reverse. The certificate is per test, not per slot: it does not show that
//! the credited pattern slot observed the proved difference (EI-T03). A pattern-slot
//! `Distinguish` meeting none of these cases becomes `Unknown`, and the check is recorded in
//! `MutantRun::certificate_checks`. Every certificate failure in the sequence run, facts,
//! internalization or proof is `NotProved` and so `Unknown`, never a kill. A certificate bug
//! can lose a kill but never add one.

use std::collections::BTreeSet;

use k_rust::backend::{Backend, BackendOptions, TransitionIdOutput};
use k_rust::kore::{
    ast::{Pattern, Sort},
    parser::parse_definition,
    walk,
};
use kink_native::bridge::{BridgeContext, BridgeFailure, BridgedPaths, paths_from_execution};
use kink_native::execution::{
    ExecutionAdapter, ExecutionAdapterFailure, ExecutionBudget, SolverProfile,
};
use kink_native::execution_difference::{
    DefinitionFacts, DifferenceCertificate, NotProvedReason, StateSequences, certify_difference,
    definition_facts,
};
use kink_native::feasibility::with_backend_relations;
use kink_native::observation::{ObservationFailure, PayloadSource};
use kink_native::{
    ManifestFailure, MutantRejection, NativeValidator, ObservedRule, ValidatedDefinition,
};
use kink_patch::{
    CandidateDisposition, CandidateGeneration, ClaimSupport, Patch, SentenceRef, Withdrawal,
};
use kink_pattern::{
    CollectionStop, Evaluation, EvaluationContext, EvaluationOptions, EventVocabulary,
    ExecutionTerminal, ExecutionTerminalKind, PathStop, PatternFailure, PatternOutcome,
    PatternPlan, SearchPolicy, SymbolSorts, evaluate_with,
};

use crate::campaign::check_manifest;
use crate::oracle::OracleFailure;
use crate::{
    BaselineAdmission, CampaignFailure, CampaignFailureKind, CrashPolicy, ExecutionFailureKind,
    ExitStop, FinalResult, ManifestTest, MutantId, MutantPlan, MutantReport, MutantScopeFailure,
    MutantStatus, OracleFailureKind, OracleKind, OracleOutcome, OracleSide, OracleValue,
    PatternValue, ScheduleMode, Score, TerminalClass, TestPlan, TestRun, compare_supplied,
    derive_mutant_report, score, validate_baseline,
};

/// What a state oracle reads from each complete terminal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StateProjection {
    /// The terminal class, and the `\dv{SortInt{}}` value of the one cell with this KORE
    /// symbol (for example `Lbl'-LT-'exit-code'-GT-'`) when a cell is declared. A missing,
    /// repeated or non-`Int` cell, or a code outside `i64`, is a projection failure.
    ExitStop {
        exit_code_cell: Option<String>,
    },
    WholeTerm,
    /// The subterms at these child-index paths (`kore::walk::children`). The paths must be
    /// nonempty, sorted and prefix-free, and there must be at least one.
    TermPaths(Vec<Vec<u32>>),
}

/// What one oracle reads from a run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Projection {
    State(StateProjection),
    /// The plan's outcome over the run's observed events. `with_bindings` adds the
    /// witness binding tuples, which need complete coverage.
    Pattern {
        plan: PatternPlan,
        with_bindings: bool,
    },
}

/// One oracle slot of a test. Its kind follows from its projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OracleDeclaration {
    crash_policy: CrashPolicy,
    projection: Projection,
}

impl OracleDeclaration {
    /// Checks that term paths are nonempty, sorted and prefix-free.
    pub fn new(crash_policy: CrashPolicy, projection: Projection) -> Result<Self, OracleFailure> {
        if let Projection::State(StateProjection::TermPaths(paths)) = &projection {
            let ordered = paths
                .windows(2)
                .all(|pair| pair[0] < pair[1] && !pair[1].starts_with(&pair[0]));
            if paths.is_empty() || paths.iter().any(Vec::is_empty) || !ordered {
                return Err(OracleFailure::new(
                    OracleFailureKind::InvalidDeclaration,
                    "term paths must be nonempty, sorted and prefix-free",
                ));
            }
        }
        Ok(Self {
            crash_policy,
            projection,
        })
    }

    #[must_use]
    pub const fn kind(&self) -> OracleKind {
        match &self.projection {
            Projection::State(StateProjection::ExitStop { .. }) => OracleKind::ExitStop,
            Projection::State(StateProjection::WholeTerm | StateProjection::TermPaths(_)) => {
                OracleKind::FinalResult
            }
            Projection::Pattern { .. } => OracleKind::ExecutionPattern,
        }
    }

    #[must_use]
    pub const fn crash_policy(&self) -> CrashPolicy {
        self.crash_policy
    }

    #[must_use]
    pub const fn projection(&self) -> &Projection {
        &self.projection
    }
}

/// One test: an initial configuration and its oracle slots, at least one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TestCase {
    pub id: String,
    pub initial_state: Pattern,
    pub oracles: Vec<OracleDeclaration>,
}

/// Everything a campaign runs against. Every compiled side executes `module`, observes
/// `observed_rules` (resolved to that side's own rule identities), and classifies its
/// ground terminal terms with `classify`. A test whose initial state has an element or set
/// variable, free or bound, is symbolic; a mutant runs it on its withdrawn definition (see the
/// module documentation). Its terminal terms with free variables reach `classify` too (the
/// bridge's contract then applies), but a state oracle over them is `Unknown`.
pub struct Campaign<'a> {
    pub validator: &'a NativeValidator,
    pub module: &'a str,
    pub observed_rules: &'a [ObservedRule],
    /// The vocabulary of observed events that pattern plans are evaluated against.
    pub vocabulary: &'a EventVocabulary,
    pub classify: &'a dyn Fn(&Pattern) -> ExecutionTerminalKind,
    pub tests: &'a [TestCase],
    pub budget: ExecutionBudget,
}

/// What one test's run on one compiled side produced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SideRun {
    /// One side per declared oracle.
    Sides { sides: Vec<OracleSide> },
    /// The run produced no operand.
    Failed(ExecutionFailureKind),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TestEvidence {
    pub test_id: String,
    pub run: SideRun,
}

/// A per-test execution-difference proof consulted for pattern-slot disagreements.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertificateCheck {
    /// The test whose pattern slots disagreed.
    pub test_id: String,
    /// The proof, or the reason it failed closed.
    pub certificate: DifferenceCertificate,
    /// Pattern slot indices changed from `Distinguish` to `Unknown`, in ascending order.
    pub demoted_slots: Vec<usize>,
}

/// One mutant's operator, written baseline sentences, plan, report and runs. A coupled
/// mutant is one `MutantRun` regardless of its edit count. Runs are in manifest order:
/// none for a test planned as `SkippedAfterKill`, and none at all when a mutant-scope
/// failure stopped it before execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MutantRun {
    pub operator: String,
    pub written_sentences: Vec<SentenceRef>,
    pub plan: MutantPlan,
    pub report: MutantReport,
    pub evidence: Vec<TestEvidence>,
    /// Checks consulted for this mutant, in manifest order.
    pub certificate_checks: Vec<CertificateCheck>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CampaignRun {
    pub baseline: Vec<TestEvidence>,
    /// In candidate order: `mutants[index]` is `MutantId(index)`, the generation's
    /// `candidates[index]`.
    pub mutants: Vec<MutantRun>,
    /// `None` when the generation is not scored (see [`run_campaign`]): its mutants still
    /// run and have statuses, but they are not every mutant the operator selects, or there
    /// are none, so no score is claimed over them. Show [`tally`] beside the ratio.
    pub score: Option<Score>,
}

/// Counts the candidate statuses and selected origins left out of a score.
///
/// Mutant counts are per candidate: a candidate is one distinct applicable patch and the unit
/// of [`MutantStatus`] and [`Score`]. An origin folded onto that candidate adds no mutant.
/// Rejections are per selected origin, including NoChange: [`CandidateGeneration::dispositions`]
/// is per origin, and rejected patches are not retained as candidates. The two units must not
/// be summed. Whenever `run.score` is `Some`, `killed` and `survived` equal its counts.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Tally {
    /// Killed candidate mutants.
    pub killed: u64,
    /// Survived candidate mutants.
    pub survived: u64,
    /// Candidates whose compiled definitions equal the baseline.
    pub equivalent: u64,
    /// Invalid candidate mutants.
    pub invalid: u64,
    /// Timed out candidate mutants.
    pub timeout: u64,
    /// Unknown candidate mutants.
    pub unknown: u64,
    /// Error candidate mutants.
    pub error: u64,
    /// Rejected selected origins, including NoChange; this uses a different unit from mutants.
    pub rejected_origins: u64,
}

/// Counts statuses and rejected origins even when the generation has no score.
/// Returns `None` when the run's mutant count does not match the generation's candidates.
#[must_use]
pub fn tally(generation: &CandidateGeneration<'_>, run: &CampaignRun) -> Option<Tally> {
    if run.mutants.len() != generation.candidates().len() {
        return None;
    }
    let mut tally = Tally::default();
    for mutant in &run.mutants {
        match mutant.report.status {
            MutantStatus::Killed => tally.killed += 1,
            MutantStatus::Survived => tally.survived += 1,
            MutantStatus::Equivalent => tally.equivalent += 1,
            MutantStatus::Invalid => tally.invalid += 1,
            MutantStatus::Timeout => tally.timeout += 1,
            MutantStatus::Unknown => tally.unknown += 1,
            MutantStatus::Error => tally.error += 1,
        }
    }
    tally.rejected_origins = generation
        .dispositions()
        .iter()
        .filter(|disposition| matches!(disposition, CandidateDisposition::Rejected(_)))
        .count() as u64;
    Some(tally)
}

/// Runs the baseline, admits it, then runs every candidate of a folded `generation` as a
/// mutant, and scores the result when the generation is scored.
///
/// A `CandidateGeneration` only comes out of `Selection::fold`, so an unfolded selection
/// cannot be run. It must have been derived from the validator's own baseline
/// (`CandidateGeneration::derived_from`); a generation of any other baseline, even an
/// equal clone, is refused as `ForeignGeneration` before anything compiles.
///
/// A generation is scored only as `CandidateGeneration::scored` decides: selection
/// considered its whole declared input and at least one candidate exists. An incomplete
/// generation (a non-exhaustive discovery or a candidate cap) or a failed selection has no
/// score (review P2.2, plan row C4); a selection that returned `Err` has no generation at
/// all. An empty generation, where nothing was selected or every origin was rejected, has
/// no score either, rather than a claim over zero mutants.
///
/// The baseline must compile, and every one of its sides must be a value or a crash its
/// declaration admits; otherwise no mutant is validated. Under `Full` every test runs on
/// every mutant. Under `FirstKill` a mutant stops after its first killing test, and its
/// plan lists each remaining test as `SkippedAfterKill`; its report and status are the
/// ones the same schedule derives from running every test.
///
/// Campaigns admit only `BeforeTerm` payloads, whose values are projections of
/// the pre-step execution state. Rule-variable payloads depend on each side's
/// rule; rule predicates depend on the solver profile and rule phrasing; effects
/// cannot be bridged into patterns; whole constrained states carry path conditions
/// whose syntax depends on the solver profile and `requires` phrasing.
///
/// A mutant is Killed only through a test with (i) a state-slot `Distinguish`, meaning its
/// ground terminal sets differ; (ii) a pattern-slot `Distinguish` on a test that also has a
/// state-slot `Distinguish`; or (iii) a pattern-slot `Distinguish` on a test for which
/// `certify_difference` returned `Proved`. `Proved` means some ground instance of the test's
/// initial state has, as the two definitions run in k-rust, a baseline state sequence that no
/// mutant-side sequence equals, or the reverse. The certificate is per test, not per slot:
/// it does not show that the credited pattern slot observed the proved difference (EI-T03).
/// A pattern-slot `Distinguish` meeting none of these cases becomes `Unknown`, with the check
/// recorded in `MutantRun::certificate_checks`. Every certificate failure in the sequence run,
/// facts, internalization or proof is `NotProved` and so `Unknown`, never a kill. A certificate
/// bug can lose a kill but never add one.
pub fn run_campaign(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    schedule: ScheduleMode,
) -> Result<CampaignRun, CampaignFailure> {
    let manifest = campaign
        .tests
        .iter()
        .map(|test| ManifestTest {
            test_id: test.id.clone(),
            slot_count: test.oracles.len(),
        })
        .collect::<Vec<_>>();
    check_manifest(&manifest)?;
    for observed in campaign.observed_rules {
        for event in &observed.domain_events {
            for source in &event.payload {
                if let Some(reason) = campaign_payload_refusal(source) {
                    return Err(CampaignFailure::new(
                        CampaignFailureKind::InvalidDeclaration,
                        format!("{:?}: {reason}", observed.rule),
                    ));
                }
            }
        }
    }
    if !generation.derived_from(campaign.validator.baseline()) {
        return Err(CampaignFailure::new(
            CampaignFailureKind::ForeignGeneration,
            "the generation was derived from another baseline than the validator's",
        ));
    }
    let symbolic = campaign
        .tests
        .iter()
        .map(|test| !test.initial_state.variable_occurrences().is_empty())
        .collect::<Vec<_>>();
    let support = symbolic
        .contains(&true)
        .then(|| ClaimSupport::new(campaign.validator.baseline()));

    let Ok(baseline) = campaign.validator.compile_baseline() else {
        return Err(admission_failure(BaselineAdmission::Invalid));
    };
    let mut runtime = match Runtime::prepare(campaign, &baseline, None) {
        Ok(runtime) => runtime,
        Err(Preparation::UnknownRule(rule)) => {
            return Err(CampaignFailure::new(
                CampaignFailureKind::InvalidDeclaration,
                format!("{rule:?} is not a written baseline rule"),
            ));
        }
        Err(Preparation::Infrastructure) => {
            return Err(admission_failure(BaselineAdmission::Error));
        }
    };
    let baseline_runs = campaign
        .tests
        .iter()
        .map(|test| runtime.run(campaign, test))
        .collect::<Vec<_>>();
    let baseline_evidence = baseline_runs
        .iter()
        .map(|(evidence, _)| evidence.clone())
        .collect::<Vec<_>>();
    validate_baseline(admit(campaign.tests, &baseline_evidence))?;
    let mut certifier = Certifier {
        runtime: &mut runtime,
        branches: baseline_runs
            .into_iter()
            .map(|(_, branches)| branches)
            .collect(),
        sequences: vec![None; campaign.tests.len()],
    };

    let mut runs = Vec::with_capacity(generation.candidates().len());
    for (index, candidate) in generation.candidates().iter().enumerate() {
        let (tests, mutant_failure, evidence, claims, certificate_checks) = run_mutant(
            campaign,
            &candidate.patch,
            &baseline,
            &baseline_evidence,
            schedule,
            (support.as_ref(), &symbolic),
            &mut certifier,
        );
        let plan = MutantPlan {
            mutant_id: MutantId(index),
            tests,
            mutant_failure,
            claims,
        };
        let report = derive_mutant_report(&plan, &manifest, schedule)?;
        runs.push(MutantRun {
            operator: candidate.operator.clone(),
            written_sentences: candidate.patch.written_sentences(),
            plan,
            report,
            evidence,
            certificate_checks,
        });
    }
    let statuses = runs.iter().map(|run| run.report.status).collect::<Vec<_>>();
    Ok(CampaignRun {
        baseline: baseline_evidence,
        mutants: runs,
        score: generation.scored().then(|| score(&statuses)),
    })
}

fn campaign_payload_refusal(source: &PayloadSource) -> Option<&'static str> {
    match source {
        PayloadSource::BindingValue(_) | PayloadSource::BindingVariable(_) => {
            Some("positional rule-variable payload")
        }
        PayloadSource::IntroducedPredicate(_) => {
            Some("rule predicates depend on the solver profile and the rule's phrasing (F6)")
        }
        PayloadSource::Effect(_) => Some("effect payloads cannot be bridged into patterns"),
        PayloadSource::BeforeState | PayloadSource::AfterState => Some(
            "whole constrained states carry path conditions whose syntax depends on the solver profile and on requires phrasing",
        ),
        PayloadSource::BindingValueNamed(_) => Some(
            "rule-variable payloads are resolved against each side's rule (CPL-T01); declare a BeforeTerm path",
        ),
        PayloadSource::BeforeTerm(_) => None,
    }
}

fn admission_failure(admission: BaselineAdmission) -> CampaignFailure {
    validate_baseline(admission).expect_err("a rejected admission")
}

/// A baseline side that failed is `Error`; one that is bounded, unknown or a crash its
/// declaration rejects is `OracleFailed`.
fn admit(tests: &[TestCase], evidence: &[TestEvidence]) -> BaselineAdmission {
    let mut admission = BaselineAdmission::Accepted;
    for (test, evidence) in tests.iter().zip(evidence) {
        let SideRun::Sides { sides, .. } = &evidence.run else {
            return BaselineAdmission::Error;
        };
        for (declaration, side) in test.oracles.iter().zip(sides) {
            match side {
                OracleSide::Error => return BaselineAdmission::Error,
                OracleSide::Timeout | OracleSide::Unknown => {
                    admission = BaselineAdmission::OracleFailed;
                }
                OracleSide::SemanticCrash(_)
                    if declaration.crash_policy() == CrashPolicy::Reject =>
                {
                    admission = BaselineAdmission::OracleFailed;
                }
                OracleSide::SemanticCrash(_) | OracleSide::Normal(_) => {}
            }
        }
    }
    admission
}

/// Baseline sequence evidence is shared across every mutant and filled only when needed.
struct Certifier<'a> {
    runtime: &'a mut Runtime,
    branches: Vec<Option<Vec<Vec<TransitionIdOutput>>>>,
    sequences: Vec<Option<Result<StateSequences, NotProvedReason>>>,
}

impl Certifier<'_> {
    fn sequences(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        index: usize,
    ) -> Result<StateSequences, NotProvedReason> {
        if self.sequences[index].is_none() {
            self.sequences[index] = Some(
                self.branches[index]
                    .as_ref()
                    .ok_or(NotProvedReason::Backend)
                    .and_then(|expected| self.runtime.sequences(campaign, test, expected)),
            );
        }
        self.sequences[index].clone().expect("filled above")
    }
}

/// A mutant's tests, its mutant-scope failure, its runs and its claim withdrawal. Under
/// `FirstKill` it stops after the first killing test and plans every later test as
/// `SkippedAfterKill`.
///
/// A mutant-scope failure overrides every test outcome, a kill included
/// ([`derive_mutant_report`]). `FirstKill`'s early stop gives `Full`'s status only because no
/// such failure can arise once a test has run: had a skipped test raised one, `Full` would
/// report it where `FirstKill` reports the kill. This is structural: the failure comes only
/// from preparing the mutant, before any test runs, and [`run_tests`] has no way to report
/// one. A later mutant-scope failure must end the mutant's tests under both schedules alike,
/// or make `FirstKill` run every test.
fn run_mutant(
    campaign: &Campaign<'_>,
    patch: &Patch,
    compiled_baseline: &ValidatedDefinition,
    baseline: &[TestEvidence],
    schedule: ScheduleMode,
    (support, symbolic): (Option<&ClaimSupport>, &[bool]),
    certifier: &mut Certifier<'_>,
) -> (
    Vec<TestPlan>,
    Option<MutantScopeFailure>,
    Vec<TestEvidence>,
    Withdrawal,
    Vec<CertificateCheck>,
) {
    match prepare_mutant(campaign, patch, compiled_baseline, support) {
        Err(failure) => (
            Vec::new(),
            Some(failure),
            Vec::new(),
            Withdrawal::default(),
            Vec::new(),
        ),
        Ok((mut sides, claims)) => {
            let (tests, evidence, checks) = run_tests(
                campaign, &mut sides, symbolic, baseline, schedule, certifier,
            );
            (tests, None, evidence, claims, checks)
        }
    }
}

/// Validates and compiles the mutant side, then, when a test is symbolic (`support` is
/// given), the side its symbolic tests run on; or the mutant-scope failure.
fn prepare_mutant(
    campaign: &Campaign<'_>,
    patch: &Patch,
    compiled_baseline: &ValidatedDefinition,
    support: Option<&ClaimSupport>,
) -> Result<(MutantSides, Withdrawal), MutantScopeFailure> {
    let side = campaign
        .validator
        .validate(patch)
        .map_err(|rejection| MutantScopeFailure::from(&rejection))?;
    match kink_native::equivalent_compilation(compiled_baseline, &side) {
        Ok(true) => return Err(MutantScopeFailure::EquivalentCompilation),
        Ok(false) => {}
        Err(_) => return Err(MutantScopeFailure::Infrastructure),
    }
    // The baseline resolved every position, so a failure here is the mutant side's.
    let patched = Runtime::prepare(campaign, &side, Some(compiled_baseline))
        .map_err(|_| MutantScopeFailure::Infrastructure)?;
    let Some(support) = support else {
        return Ok((
            MutantSides {
                patched,
                symbolic: SymbolicSide::Patched,
            },
            Withdrawal::default(),
        ));
    };
    // The patch applied during validation, so it applies here too.
    let claims = support
        .withdraw(campaign.validator.baseline(), patch)
        .map_err(|_| MutantScopeFailure::Infrastructure)?;
    let symbolic = if !claims.trusted() {
        SymbolicSide::Unsupported
    } else if let Some(withdrawing) = claims.patch() {
        match campaign.validator.validate(withdrawing) {
            Ok(side) => SymbolicSide::Withdrawn(Box::new(
                Runtime::prepare(campaign, &side, Some(compiled_baseline))
                    .map_err(|_| MutantScopeFailure::Infrastructure)?,
            )),
            Err(_) => SymbolicSide::Unsupported,
        }
    } else {
        SymbolicSide::Patched
    };
    Ok((MutantSides { patched, symbolic }, claims))
}

/// A prepared mutant: the patched definition, and what its symbolic tests run on.
struct MutantSides {
    patched: Runtime,
    symbolic: SymbolicSide,
}

enum SymbolicSide {
    /// The patched definition: no test is symbolic, or the patch touched no claim's support.
    Patched,
    /// The withdrawn definition.
    Withdrawn(Box<Runtime>),
    /// No definition whose trusted claims are all supported: symbolic tests do not run.
    Unsupported,
}

impl MutantSides {
    fn run(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        symbolic: bool,
    ) -> (TestEvidence, Option<Vec<Vec<TransitionIdOutput>>>) {
        match (&mut self.symbolic, symbolic) {
            (SymbolicSide::Withdrawn(runtime), true) => runtime.run(campaign, test),
            (SymbolicSide::Unsupported, true) => (
                TestEvidence {
                    test_id: test.id.clone(),
                    run: SideRun::Failed(ExecutionFailureKind::UnsupportedClaims),
                },
                None,
            ),
            _ => self.patched.run(campaign, test),
        }
    }

    fn sequences(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        symbolic: bool,
        expected: &[Vec<TransitionIdOutput>],
    ) -> Result<StateSequences, NotProvedReason> {
        match (&mut self.symbolic, symbolic) {
            (SymbolicSide::Withdrawn(runtime), true) => runtime.sequences(campaign, test, expected),
            // An unsupported symbolic side has already produced Failed(UnsupportedClaims).
            (SymbolicSide::Unsupported, true) => Err(NotProvedReason::Backend),
            _ => self.patched.sequences(campaign, test, expected),
        }
    }

    fn facts(&mut self, symbolic: bool) -> Result<DefinitionFacts, NotProvedReason> {
        match (&mut self.symbolic, symbolic) {
            (SymbolicSide::Withdrawn(runtime), true) => runtime.facts(),
            // An unsupported symbolic side has already produced Failed(UnsupportedClaims).
            (SymbolicSide::Unsupported, true) => Err(NotProvedReason::Backend),
            _ => self.patched.facts(),
        }
    }
}

/// A prepared mutant's test plans and runs, in manifest order.
fn run_tests(
    campaign: &Campaign<'_>,
    sides: &mut MutantSides,
    symbolic: &[bool],
    baseline: &[TestEvidence],
    schedule: ScheduleMode,
    certifier: &mut Certifier<'_>,
) -> (Vec<TestPlan>, Vec<TestEvidence>, Vec<CertificateCheck>) {
    let mut tests = Vec::with_capacity(campaign.tests.len());
    let mut evidence = Vec::with_capacity(campaign.tests.len());
    let mut checks = Vec::new();
    let mut killed = false;
    for (index, ((test, baseline), symbolic)) in campaign
        .tests
        .iter()
        .zip(baseline)
        .zip(symbolic)
        .enumerate()
    {
        if killed {
            tests.push(TestPlan {
                test_id: test.id.clone(),
                run: TestRun::SkippedAfterKill,
            });
            continue;
        }
        let (mutant, branches) = sides.run(campaign, test, *symbolic);
        let mut run = match (&baseline.run, &mutant.run) {
            (_, SideRun::Failed(kind)) => TestRun::Failed(*kind),
            (
                SideRun::Sides {
                    sides: baseline, ..
                },
                SideRun::Sides { sides: mutant, .. },
            ) => TestRun::Compared(
                test.oracles
                    .iter()
                    .zip(baseline.iter().zip(mutant))
                    .map(|(declaration, (baseline, mutant))| {
                        slot_outcome(declaration, baseline, mutant)
                    })
                    .collect(),
            ),
            // Admission refused a failed baseline run.
            (SideRun::Failed(_), SideRun::Sides { .. }) => {
                TestRun::Failed(ExecutionFailureKind::Infrastructure)
            }
        };
        if let TestRun::Compared(outcomes) = &mut run {
            let has_pattern_difference =
                test.oracles
                    .iter()
                    .zip(outcomes.iter())
                    .any(|(declaration, outcome)| {
                        matches!(declaration.projection(), Projection::Pattern { .. })
                            && *outcome == OracleOutcome::Distinguish
                    });
            let has_state_difference =
                test.oracles
                    .iter()
                    .zip(outcomes.iter())
                    .any(|(declaration, outcome)| {
                        matches!(declaration.projection(), Projection::State(_))
                            && *outcome == OracleOutcome::Distinguish
                    });
            if has_pattern_difference && !has_state_difference {
                let certificate = (|| {
                    let baseline_sequences = certifier.sequences(campaign, test, index)?;
                    let expected = branches.as_ref().ok_or(NotProvedReason::Backend)?;
                    let mutant_sequences = sides.sequences(campaign, test, *symbolic, expected)?;
                    let baseline_facts = certifier.runtime.facts()?;
                    let mutant_facts = sides.facts(*symbolic)?;
                    Ok(certify_difference(
                        &mut certifier.runtime.backend,
                        &test.initial_state,
                        &baseline_facts,
                        &mutant_facts,
                        &baseline_sequences,
                        &mutant_sequences,
                    ))
                })()
                .unwrap_or_else(DifferenceCertificate::NotProved);
                let mut demoted_slots = Vec::new();
                if matches!(certificate, DifferenceCertificate::NotProved(_)) {
                    for (index, (declaration, outcome)) in
                        test.oracles.iter().zip(outcomes.iter_mut()).enumerate()
                    {
                        if matches!(declaration.projection(), Projection::Pattern { .. })
                            && *outcome == OracleOutcome::Distinguish
                        {
                            *outcome = OracleOutcome::Unknown;
                            demoted_slots.push(index);
                        }
                    }
                }
                checks.push(CertificateCheck {
                    test_id: test.id.clone(),
                    certificate,
                    demoted_slots,
                });
            }
        }
        killed = schedule == ScheduleMode::FirstKill && run.kills();
        tests.push(TestPlan {
            test_id: test.id.clone(),
            run,
        });
        evidence.push(mutant);
    }
    (tests, evidence, checks)
}

/// Why a compiled side cannot run.
enum Preparation {
    /// An observed position names no authored baseline rule: a declaration error.
    UnknownRule(SentenceRef),
    Infrastructure,
}

/// One compiled side: its backend, reused across tests, and its evaluation context.
struct Runtime {
    backend: Backend,
    adapter: ExecutionAdapter,
    context: EvaluationContext,
    facts: Option<Result<DefinitionFacts, NotProvedReason>>,
}

impl Runtime {
    /// Parses the side's KORE once, for both its symbol sorts and its backend, and
    /// installs the observed rules under the side's own rule identities. A mutant side
    /// (`anchor` is the compiled baseline) observes the rules its patch did not change by their
    /// content ([`kink_native::NativeValidator::observation_manifest_anchored`]).
    fn prepare(
        campaign: &Campaign<'_>,
        side: &ValidatedDefinition,
        anchor: Option<&ValidatedDefinition>,
    ) -> Result<Self, Preparation> {
        let manifest = match anchor {
            None => campaign
                .validator
                .observation_manifest(side, campaign.observed_rules),
            Some(baseline) => campaign.validator.observation_manifest_anchored(
                baseline,
                side,
                campaign.observed_rules,
            ),
        }
        .map_err(|failure| match failure {
            ManifestFailure::UnknownRule(rule) => Preparation::UnknownRule(rule),
            ManifestFailure::Identity { .. } | ManifestFailure::Installation(_) => {
                Preparation::Infrastructure
            }
        })?;
        let parsed = parse_definition(&side.artifacts().definition_kore)
            .map_err(|_| Preparation::Infrastructure)?;
        let symbol_sorts = SymbolSorts::from_definition(&parsed);
        let backend = Backend::from_definition(parsed, campaign.module, BackendOptions::default())
            .map_err(|_| Preparation::Infrastructure)?;
        let context = EvaluationContext {
            test_id: String::new(),
            bounds: campaign.budget.bounds(),
            vocabulary: campaign.vocabulary.clone(),
            selected_rules: manifest.rules().cloned().collect(),
            symbol_sorts,
        };
        // Pin the build's profile so the adapter can detect an unexpected backend profile.
        let profile = SolverProfile::BUILD;
        Ok(Self {
            backend,
            adapter: ExecutionAdapter::with_profile(manifest, profile),
            context,
            facts: None,
        })
    }

    fn facts(&mut self) -> Result<DefinitionFacts, NotProvedReason> {
        if self.facts.is_none() {
            self.facts = Some(definition_facts(&mut self.backend));
        }
        self.facts.clone().expect("filled above")
    }

    fn sequences(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        expected: &[Vec<TransitionIdOutput>],
    ) -> Result<StateSequences, NotProvedReason> {
        self.adapter.state_sequences(
            &mut self.backend,
            &test.initial_state,
            campaign.budget,
            expected,
        )
    }

    fn run(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
    ) -> (TestEvidence, Option<Vec<Vec<TransitionIdOutput>>>) {
        let mut branches = None;
        let run =
            match self
                .adapter
                .execute(&mut self.backend, &test.initial_state, campaign.budget)
            {
                Err(failure) => SideRun::Failed((&failure).into()),
                // The watchdog fired: whatever the leaves say, the run was cut short.
                Ok(execution) if execution.timed_out() => {
                    SideRun::Failed(ExecutionFailureKind::TimeLimit)
                }
                Ok(execution) => {
                    self.context.test_id.clone_from(&test.id);
                    let bridged = paths_from_execution(
                        &execution,
                        &BridgeContext {
                            test_id: &test.id,
                            classify: campaign.classify,
                            sorts: &self.context.symbol_sorts,
                        },
                    );
                    match bridged {
                        Err(failure) => SideRun::Failed((&failure).into()),
                        Ok(bridged) => {
                            branches = Some(
                                execution
                                    .leaves()
                                    .iter()
                                    .map(|leaf| leaf.branch.identity.clone())
                                    .collect(),
                            );
                            SideRun::Sides {
                                sides: test
                                    .oracles
                                    .iter()
                                    .map(|declaration| self.side(declaration, test, &bridged))
                                    .collect(),
                            }
                        }
                    }
                }
            };
        (
            TestEvidence {
                test_id: test.id.clone(),
                run,
            },
            branches,
        )
    }

    fn side(
        &mut self,
        declaration: &OracleDeclaration,
        test: &TestCase,
        bridged: &BridgedPaths,
    ) -> OracleSide {
        match declaration.projection() {
            Projection::State(projection) => state_side(projection, bridged),
            Projection::Pattern {
                plan,
                with_bindings,
            } => match with_backend_relations(&mut self.backend, &test.initial_state, |relations| {
                evaluate_with(
                    &self.context,
                    plan,
                    &bridged.paths,
                    &bridged.collection,
                    None,
                    EvaluationOptions {
                        stable_path_keys: true,
                        search_policy: SearchPolicy::Exhaustive,
                        input_error: false,
                    },
                    relations,
                )
            }) {
                Ok(evaluation) => pattern_side(&evaluation, *with_bindings),
                Err(_) => OracleSide::Error,
            },
        }
    }
}

/// The comparison of one slot. A comparison failure (a crash the declaration rejects, or
/// values of the wrong kind or shape) is `Error`, never a dropped slot.
#[must_use]
pub fn slot_outcome(
    declaration: &OracleDeclaration,
    baseline: &OracleSide,
    mutant: &OracleSide,
) -> OracleOutcome {
    compare_supplied(
        declaration.kind(),
        declaration.crash_policy(),
        baseline,
        mutant,
    )
    .unwrap_or(OracleOutcome::Error)
}

/// The failed side of the most severe incomplete stop: error, then timeout, then unknown.
fn failed_side(sides: impl Iterator<Item = OracleSide>) -> Option<OracleSide> {
    const fn rank(side: &OracleSide) -> u8 {
        match side {
            OracleSide::Error => 2,
            OracleSide::Timeout => 1,
            _ => 0,
        }
    }
    sides.max_by_key(rank)
}

/// The side an incomplete path stop stands for. Exhaustive over `PathStop`.
const fn path_stop_side(stop: PathStop) -> OracleSide {
    match stop {
        PathStop::Error => OracleSide::Error,
        PathStop::TimeLimit => OracleSide::Timeout,
        // A complete stop on a path not marked complete is not evidence either.
        PathStop::Terminal
        | PathStop::Stuck
        | PathStop::UndefinedStep
        | PathStop::MatchFound
        | PathStop::DepthLimit
        | PathStop::BranchLimit
        | PathStop::ResultLimit
        | PathStop::ResourceLimit
        | PathStop::SolverUnknown
        | PathStop::BackendLimit => OracleSide::Unknown,
    }
}

/// The side of a collection stop. A PathSet run records clean exhaustion;
/// an unrecorded stop remains unknown.
const fn collection_stop_side(stop: CollectionStop) -> Option<OracleSide> {
    match stop {
        CollectionStop::SearchExhausted => None,
        CollectionStop::ExhaustionUnrecorded => Some(OracleSide::Unknown),
        CollectionStop::Error => Some(OracleSide::Error),
        CollectionStop::TimeLimit => Some(OracleSide::Timeout),
        CollectionStop::MatchFound
        | CollectionStop::DepthLimit
        | CollectionStop::BranchLimit
        | CollectionStop::ResultLimit
        | CollectionStop::ResourceLimit
        | CollectionStop::SolverUnknown
        | CollectionStop::BackendLimit => Some(OracleSide::Unknown),
    }
}

/// The side of a state oracle over one run's bridged paths; see the module documentation.
#[must_use]
pub fn state_side(projection: &StateProjection, bridged: &BridgedPaths) -> OracleSide {
    let incomplete = bridged
        .paths
        .iter()
        .filter(|path| !path.complete)
        .map(|path| path_stop_side(path.stop))
        .chain(collection_stop_side(bridged.collection.stop));
    if let Some(side) = failed_side(incomplete) {
        return side;
    }
    let Some(terminals) = bridged
        .paths
        .iter()
        .map(|path| path.execution_terminal.as_ref())
        .collect::<Option<Vec<_>>>()
        .filter(|terminals| !terminals.is_empty())
    else {
        return OracleSide::Error;
    };
    if terminals
        .iter()
        .any(|terminal| !terminal.state.free_variables().is_empty())
    {
        return OracleSide::Unknown;
    }
    if terminals
        .iter()
        .any(|terminal| terminal.kind == ExecutionTerminalKind::SemanticCrash)
    {
        // Mixed crash and normal terminal sets are not modelled.
        return match terminals.as_slice() {
            [terminal] => OracleSide::SemanticCrash(terminal.state.clone()),
            _ => OracleSide::Unknown,
        };
    }
    project(projection, &terminals).map_or(OracleSide::Error, OracleSide::Normal)
}

/// Projects complete, non-crash terminals; `None` is a projection failure.
fn project(projection: &StateProjection, terminals: &[&ExecutionTerminal]) -> Option<OracleValue> {
    Some(match projection {
        StateProjection::ExitStop { exit_code_cell } => OracleValue::ExitStop(
            terminals
                .iter()
                .map(|terminal| {
                    Some(ExitStop {
                        class: match terminal.kind {
                            ExecutionTerminalKind::Normal => TerminalClass::Normal,
                            ExecutionTerminalKind::Stuck => TerminalClass::Stuck,
                            ExecutionTerminalKind::UndefinedStep => TerminalClass::UndefinedStep,
                            ExecutionTerminalKind::SemanticCrash => return None,
                        },
                        code: match (exit_code_cell, terminal.kind) {
                            (_, ExecutionTerminalKind::UndefinedStep) | (None, _) => None,
                            (Some(cell), _) => Some(exit_code(&terminal.state, cell)?),
                        },
                    })
                })
                .collect::<Option<BTreeSet<_>>>()?,
        ),
        StateProjection::WholeTerm => OracleValue::FinalResult(FinalResult::WholeTerm(
            terminals
                .iter()
                .map(|terminal| terminal.state.clone())
                .collect(),
        )),
        StateProjection::TermPaths(paths) => OracleValue::FinalResult(FinalResult::TermPaths(
            terminals
                .iter()
                .map(|terminal| {
                    paths
                        .iter()
                        .map(|path| Some((path.clone(), subterm(&terminal.state, path)?.clone())))
                        .collect::<Option<Vec<_>>>()
                })
                .collect::<Option<BTreeSet<_>>>()?,
        )),
    })
}

fn subterm<'a>(term: &'a Pattern, path: &[u32]) -> Option<&'a Pattern> {
    path.iter().try_fold(term, |term, step| {
        walk::children(term)
            .get(usize::try_from(*step).ok()?)
            .copied()
    })
}

/// The `Int` held by the only application of `cell` in `term`.
fn exit_code(term: &Pattern, cell: &str) -> Option<i64> {
    let mut found = Vec::new();
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if let Pattern::Application { symbol, arguments } = term
            && symbol.name == cell
        {
            found.push(arguments.as_slice());
        }
        pending.extend(walk::children(term));
    }
    let [[Pattern::DomainValue { sort, value }]] = found.as_slice() else {
        return None;
    };
    let int = Sort::Application {
        name: "SortInt".to_owned(),
        arguments: Vec::new(),
    };
    if *sort != int {
        return None;
    }
    value.as_utf8().ok()?.parse().ok()
}

/// The side of a pattern oracle. Exhaustive over `PatternOutcome`.
///
/// A pattern failure is `Error`, never a value that could distinguish. A match needs at
/// least one witness and every witness on a real prefix; otherwise the side is `Unknown`.
/// Declared bindings need complete coverage from an exhaustive evaluation; without it the
/// side is `Unknown`, so a match with bindings never meets a match without them. A witness
/// with assumptions or a binding term with a free variable also makes declared bindings
/// `Unknown`: a set of symbolic terms is not a value of any instance.
#[must_use]
pub fn pattern_side(
    evaluation: &Result<Evaluation, PatternFailure>,
    with_bindings: bool,
) -> OracleSide {
    let Ok(evaluation) = evaluation else {
        return OracleSide::Error;
    };
    let complete =
        evaluation.complete_coverage && evaluation.search_policy == SearchPolicy::Exhaustive;
    let witnessed = !evaluation.witnesses.is_empty()
        && evaluation
            .witnesses
            .iter()
            .all(|witness| witness.stop_reason.has_real_prefix());
    let value = match evaluation.outcome {
        PatternOutcome::Error => return OracleSide::Error,
        PatternOutcome::Unknown => return OracleSide::Unknown,
        // `evaluate` returns `NoMatch` only with complete coverage, and `Match` only with
        // witnesses on real prefixes; these guard the value.
        PatternOutcome::NoMatch if complete => PatternValue::NoMatch,
        PatternOutcome::Match if !witnessed => return OracleSide::Unknown,
        PatternOutcome::Match if !with_bindings => PatternValue::Match { bindings: None },
        PatternOutcome::Match
            if evaluation.witnesses.iter().any(|witness| {
                !witness.assumptions.is_empty()
                    || witness
                        .bindings
                        .iter()
                        .any(|binding| !binding.term.free_variables().is_empty())
            }) =>
        {
            return OracleSide::Unknown;
        }
        PatternOutcome::Match if complete => PatternValue::Match {
            bindings: Some(
                evaluation
                    .witnesses
                    .iter()
                    .map(|witness| witness.bindings.clone())
                    .collect(),
            ),
        },
        PatternOutcome::NoMatch | PatternOutcome::Match => return OracleSide::Unknown,
    };
    OracleSide::Normal(OracleValue::Pattern(value))
}

impl From<&ExecutionAdapterFailure> for ExecutionFailureKind {
    fn from(failure: &ExecutionAdapterFailure) -> Self {
        match failure {
            ExecutionAdapterFailure::Observation(ObservationFailure::MissingPayloadSource(_)) => {
                Self::UnresolvedObservation
            }
            ExecutionAdapterFailure::SolverProfileMismatch
            | ExecutionAdapterFailure::InvalidState(_)
            | ExecutionAdapterFailure::Backend(_)
            | ExecutionAdapterFailure::ContractViolation(_)
            | ExecutionAdapterFailure::UninhabitedVariable(_)
            | ExecutionAdapterFailure::Observation(_) => Self::Infrastructure,
        }
    }
}

impl From<&BridgeFailure> for ExecutionFailureKind {
    fn from(failure: &BridgeFailure) -> Self {
        match failure {
            BridgeFailure::NoLeaves
            | BridgeFailure::ContractViolation(_)
            | BridgeFailure::UnsupportedPayload
            | BridgeFailure::UndecodablePayload(_)
            | BridgeFailure::UndecodableState(_)
            | BridgeFailure::UndecidedStateSort
            | BridgeFailure::DuplicatePathIdentity(_)
            | BridgeFailure::ClassifiedUndefinedStep => Self::Infrastructure,
        }
    }
}

impl From<&MutantRejection> for MutantScopeFailure {
    fn from(rejection: &MutantRejection) -> Self {
        match rejection {
            // Unreachable for a candidate that generation pre-applied, and mapped anyway.
            MutantRejection::Patch(_) | MutantRejection::Compilation(_) => Self::Rejected,
        }
    }
}
