//! Runs a campaign through kink-native and maps each run to typed oracle sides.
//!
//! The baseline and every mutant execute every test with one primary time-bounded
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
//! - A pattern oracle evaluates declared predicates of consecutive configurations.
//!   Both sides use the baseline signature, evaluation context and solver, with the same
//!   pair existential flag. A witness and complete contrary coverage prove an observation
//!   difference for some ground instance; an undecided presence, relation or discard is
//!   Unknown. Bindings require complete coverage, ground terms and definition independence.
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
//! equals, or the reverse. Each pattern slot observes its own declared execution difference.
//! A pattern-slot
//! `Distinguish` meeting none of these cases becomes `Unknown`, and the check is recorded in
//! `MutantRun::certificate_checks`. Every certificate failure in the sequence run, facts,
//! internalization or proof is `NotProved` and so `Unknown`, never a kill. A certificate bug
//! can lose a kill but never add one.

use std::collections::BTreeSet;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kore::{
    ast::{Pattern, Sort},
    parser::parse_definition,
    walk,
};
use kink_native::bridge::{
    BridgeContext, BridgeFailure, BridgedPaths, paths_from_execution, paths_from_steps,
};
use kink_native::execution::{
    ExecutionAdapter, ExecutionAdapterFailure, ExecutionBudget, SolverProfile, StepRunFailure,
    SteppedExecution,
};
use kink_native::execution_difference::{
    DefinitionFacts, DifferenceCertificate, NotProvedReason, StateSequences, certify_difference,
    definition_facts,
};
use kink_native::feasibility::BackendRelations;
use kink_native::step_events::{ObservationDecider, StepEventSpec, StepObservation};
use kink_native::{MutantRejection, NativeValidator, ValidatedDefinition};
use kink_patch::{
    CandidateDisposition, CandidateGeneration, ClaimSupport, Patch, SentenceRef, Withdrawal,
};
use kink_pattern::{
    CollectionStop, Evaluation, EvaluationContext, EvaluationOptions, ExecutionTerminal,
    ExecutionTerminalKind, PathStop, PatternFailure, PatternOutcome, PatternPlan, SearchPolicy,
    SymbolSorts, evaluate_with,
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

/// A compiled module, its observations, terminal classifier, tests and execution budget.
pub struct Campaign<'a> {
    pub validator: &'a NativeValidator,
    pub module: &'a str,
    pub observation: &'a [StepEventSpec],
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
/// Step declarations validate once against the compiled baseline. Their pattern slots
/// use one baseline observation decider on both sides, so a Distinguish observes an
/// execution difference for some ground instance. The EI certificate remains an AND
/// condition until the variable-identity close-out, using the cached stepped runs.
///
/// A mutant is Killed only through a test with (i) a state-slot `Distinguish`, meaning its
/// ground terminal sets differ; (ii) a pattern-slot `Distinguish` on a test that also has a
/// state-slot `Distinguish`; or (iii) a pattern-slot `Distinguish` on a test for which
/// `certify_difference` returned `Proved`. `Proved` means some ground instance of the test's
/// initial state has, as the two definitions run in k-rust, a baseline state sequence that no
/// mutant-side sequence equals, or the reverse. Each pattern slot observes its declared
/// function of execution configurations.
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
    StepObservation::vocabulary_of(campaign.observation).map_err(|failure| {
        CampaignFailure::new(
            CampaignFailureKind::InvalidDeclaration,
            format!("{failure:?}"),
        )
    })?;
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
    let mut runtime = Runtime::prepare(campaign, &baseline)
        .map_err(|_| admission_failure(BaselineAdmission::Error))?;
    let observation = StepObservation::new(&mut runtime.backend, campaign.observation.to_vec())
        .map_err(|failure| {
            CampaignFailure::new(
                CampaignFailureKind::InvalidDeclaration,
                format!("{failure:?}"),
            )
        })?;
    let baseline_runs = campaign
        .tests
        .iter()
        .map(|test| runtime.run(campaign, test))
        .collect::<Vec<_>>();
    let mut baseline_evidence = baseline_runs
        .iter()
        .map(|(evidence, _)| evidence.clone())
        .collect::<Vec<_>>();
    {
        let facts = runtime.facts();
        for ((test, evidence), (_, cache)) in campaign
            .tests
            .iter()
            .zip(&mut baseline_evidence)
            .zip(&baseline_runs)
        {
            let patterns = facts.as_ref().ok().map(|facts| {
                runtime.step_sides(
                    campaign,
                    test,
                    &observation,
                    facts.existentials,
                    cache.stepped.as_ref(),
                )
            });
            replace_patterns(test, evidence, patterns.as_deref());
        }
    }
    validate_baseline(admit(campaign.tests, &baseline_evidence))?;
    let mut certifier = Certifier {
        runtime: &mut runtime,
        caches: baseline_runs.into_iter().map(|(_, cache)| cache).collect(),
        observation,
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
    caches: Vec<RunCache>,
    observation: StepObservation,
    sequences: Vec<Option<Result<StateSequences, NotProvedReason>>>,
}

impl Certifier<'_> {
    fn sequences(&mut self, index: usize) -> Result<StateSequences, NotProvedReason> {
        if self.sequences[index].is_none() {
            self.sequences[index] = Some(
                self.caches[index]
                    .stepped
                    .as_ref()
                    .ok_or(NotProvedReason::Backend)
                    .and_then(SteppedExecution::certificate_sequences),
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
    // A preparation failure here is the mutant side's.
    let patched =
        Runtime::prepare(campaign, &side).map_err(|_| MutantScopeFailure::Infrastructure)?;
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
                Runtime::prepare(campaign, &side)
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
    ) -> (TestEvidence, RunCache) {
        match (&mut self.symbolic, symbolic) {
            (SymbolicSide::Withdrawn(runtime), true) => runtime.run(campaign, test),
            (SymbolicSide::Unsupported, true) => (
                TestEvidence {
                    test_id: test.id.clone(),
                    run: SideRun::Failed(ExecutionFailureKind::UnsupportedClaims),
                },
                RunCache::default(),
            ),
            _ => self.patched.run(campaign, test),
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
        let (mut mutant, cache) = sides.run(campaign, test, *symbolic);
        let mut paired_baseline = baseline.clone();
        {
            let observation = &certifier.observation;
            let pair_facts = certifier.runtime.facts().and_then(|baseline_facts| {
                sides
                    .facts(*symbolic)
                    .map(|mutant_facts| (baseline_facts, mutant_facts))
            });
            let patterns = pair_facts
                .ok()
                .filter(|(b, m)| b.signature == m.signature)
                .map(|(b, m)| {
                    certifier.runtime.step_pair(
                        campaign,
                        test,
                        observation,
                        b.existentials || m.existentials,
                        (
                            certifier.caches[index].stepped.as_ref(),
                            cache.stepped.as_ref(),
                        ),
                    )
                });
            if let Some((baseline_patterns, mutant_patterns)) = patterns {
                replace_patterns(test, &mut paired_baseline, Some(&baseline_patterns));
                replace_patterns(test, &mut mutant, Some(&mutant_patterns));
            } else {
                replace_patterns(test, &mut paired_baseline, None);
                replace_patterns(test, &mut mutant, None);
            }
        }
        let mut run = match (&paired_baseline.run, &mutant.run) {
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
                        if matches!(declaration.projection(), Projection::Pattern { .. })
                            && !matches!(baseline, OracleSide::Normal(_))
                        {
                            OracleOutcome::Unknown
                        } else {
                            slot_outcome(declaration, baseline, mutant)
                        }
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
                    let baseline_sequences = certifier.sequences(index)?;
                    let mutant_sequences = cache
                        .stepped
                        .as_ref()
                        .ok_or(NotProvedReason::Backend)?
                        .certificate_sequences()?;
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

/// Stepped evidence retained from the primary run.
#[derive(Default)]
struct RunCache {
    stepped: Option<SteppedExecution>,
}

fn step_failure_side(failure: &StepRunFailure) -> OracleSide {
    match failure {
        StepRunFailure::AmbiguousRule(_)
        | StepRunFailure::Unobservable
        | StepRunFailure::Decode(_) => OracleSide::Unknown,
    }
}

fn replace_patterns(test: &TestCase, evidence: &mut TestEvidence, patterns: Option<&[OracleSide]>) {
    if let SideRun::Sides { sides } = &mut evidence.run {
        for (index, (declaration, side)) in test.oracles.iter().zip(sides).enumerate() {
            if matches!(declaration.projection(), Projection::Pattern { .. }) {
                *side = patterns.map_or(OracleSide::Unknown, |patterns| patterns[index].clone());
            }
        }
    }
}

/// Why a compiled side cannot run.
enum Preparation {
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
    /// Parses the side's KORE once for its symbol sorts and event-free backend adapter.
    fn prepare(campaign: &Campaign<'_>, side: &ValidatedDefinition) -> Result<Self, Preparation> {
        let adapter = ExecutionAdapter::without_manifest(SolverProfile::BUILD);
        let parsed = parse_definition(&side.artifacts().definition_kore)
            .map_err(|_| Preparation::Infrastructure)?;
        let symbol_sorts = SymbolSorts::from_definition(&parsed);
        let backend = Backend::from_definition(parsed, campaign.module, BackendOptions::default())
            .map_err(|_| Preparation::Infrastructure)?;
        let context = EvaluationContext {
            test_id: String::new(),
            bounds: campaign.budget.bounds(),
            vocabulary: StepObservation::vocabulary_of(campaign.observation)
                .map_err(|_| Preparation::Infrastructure)?,
            symbol_sorts,
        };
        // Pin the build's profile so the adapter can detect an unexpected backend profile.
        Ok(Self {
            backend,
            adapter,
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

    fn run(&mut self, campaign: &Campaign<'_>, test: &TestCase) -> (TestEvidence, RunCache) {
        let mut cache = RunCache::default();
        let has_pattern = test
            .oracles
            .iter()
            .any(|declaration| matches!(declaration.projection(), Projection::Pattern { .. }));
        let mut pattern_failure = OracleSide::Unknown;
        let execution = if has_pattern {
            match self.adapter.execute_steps(
                &mut self.backend,
                &test.initial_state,
                campaign.budget,
            ) {
                Ok(Ok(stepped)) => {
                    let adapted = stepped.adapted.clone();
                    cache.stepped = Some(stepped);
                    Ok(adapted)
                }
                Ok(Err(failure)) => {
                    pattern_failure = step_failure_side(&failure);
                    self.adapter
                        .execute(&mut self.backend, &test.initial_state, campaign.budget)
                }
                Err(failure) => Err(failure),
            }
        } else {
            self.adapter
                .execute(&mut self.backend, &test.initial_state, campaign.budget)
        };
        let run = match execution {
            Err(failure) => SideRun::Failed((&failure).into()),
            Ok(execution) if execution.timed_out() => {
                SideRun::Failed(ExecutionFailureKind::TimeLimit)
            }
            Ok(execution) => match paths_from_execution(
                &execution,
                &BridgeContext {
                    test_id: &test.id,
                    classify: campaign.classify,
                    sorts: &self.context.symbol_sorts,
                },
            ) {
                Err(failure) => SideRun::Failed((&failure).into()),
                Ok(bridged) => SideRun::Sides {
                    sides: test
                        .oracles
                        .iter()
                        .map(|declaration| match declaration.projection() {
                            Projection::State(projection) => state_side(projection, &bridged),
                            Projection::Pattern { .. } => pattern_failure.clone(),
                        })
                        .collect(),
                },
            },
        };
        (
            TestEvidence {
                test_id: test.id.clone(),
                run,
            },
            cache,
        )
    }

    fn step_sides(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        observation: &StepObservation,
        existentials: bool,
        execution: Option<&SteppedExecution>,
    ) -> Vec<OracleSide> {
        self.step_pair(campaign, test, observation, existentials, (execution, None))
            .0
    }

    fn step_pair(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        observation: &StepObservation,
        existentials: bool,
        executions: (Option<&SteppedExecution>, Option<&SteppedExecution>),
    ) -> (Vec<OracleSide>, Vec<OracleSide>) {
        let mut context = self.context.clone();
        context.test_id.clone_from(&test.id);
        self.backend
            .with_solver(None, |definition, solver| {
                let decider =
                    ObservationDecider::new(definition, solver, &test.initial_state, existentials);
                let relations =
                    BackendRelations::shared(definition, solver, &test.initial_state, existentials);
                let evaluate = |execution: Option<&SteppedExecution>| {
                    let bridged = execution.and_then(|execution| {
                        paths_from_steps(
                            &BridgeContext {
                                test_id: &test.id,
                                classify: campaign.classify,
                                sorts: &context.symbol_sorts,
                            },
                            execution,
                            observation,
                            &decider,
                        )
                        .ok()
                    });
                    test.oracles
                        .iter()
                        .map(|declaration| {
                            let Projection::Pattern {
                                plan,
                                with_bindings,
                            } = declaration.projection()
                            else {
                                return OracleSide::Unknown;
                            };
                            let Some(bridged) = &bridged else {
                                return OracleSide::Unknown;
                            };
                            let evaluation = evaluate_with(
                                &context,
                                plan,
                                &bridged.paths,
                                &bridged.collection,
                                None,
                                EvaluationOptions {
                                    stable_path_keys: true,
                                    search_policy: SearchPolicy::Exhaustive,
                                    input_error: false,
                                },
                                &relations,
                            );
                            if *with_bindings
                                && evaluation.as_ref().is_ok_and(|evaluation| {
                                    evaluation.witnesses.iter().any(|witness| {
                                        witness.bindings.iter().any(|binding| {
                                            !decider.definition_independent(&binding.term)
                                        })
                                    })
                                })
                            {
                                OracleSide::Unknown
                            } else {
                                pattern_side(&evaluation, *with_bindings)
                            }
                        })
                        .collect()
                };
                Ok::<_, k_rust::backend::BackendError>((
                    evaluate(executions.0),
                    evaluate(executions.1),
                ))
            })
            .unwrap_or_else(|_| {
                (
                    vec![OracleSide::Unknown; test.oracles.len()],
                    vec![OracleSide::Unknown; test.oracles.len()],
                )
            })
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stepped_run_failures_make_only_pattern_slots_unknown() {
        let state = OracleDeclaration::new(
            CrashPolicy::Reject,
            Projection::State(StateProjection::WholeTerm),
        )
        .unwrap();
        let vocabulary = kink_pattern::EventVocabulary::new(vec![kink_pattern::Constructor {
            name: "tick".into(),
            payload_sorts: vec![],
        }])
        .unwrap();
        let plan = PatternPlan::new(
            &vocabulary,
            vec![],
            vec![kink_pattern::PatternArm {
                atoms: vec![kink_pattern::Atom {
                    constructor: "tick".into(),
                    payload: vec![],
                }],
                relations: vec![],
            }],
            None,
        )
        .unwrap();
        let pattern = OracleDeclaration::new(
            CrashPolicy::Reject,
            Projection::Pattern {
                plan,
                with_bindings: false,
            },
        )
        .unwrap();
        for failure in [
            StepRunFailure::AmbiguousRule("duplicate".into()),
            StepRunFailure::Unobservable,
            StepRunFailure::Decode("state".into()),
        ] {
            assert_eq!(step_failure_side(&failure), OracleSide::Unknown);
            let test = TestCase {
                id: "failure".into(),
                initial_state: Pattern::Top {
                    sort: Sort::Application {
                        name: "SortGeneratedTopCell".into(),
                        arguments: vec![],
                    },
                },
                oracles: vec![state.clone(), pattern.clone()],
            };
            let mut evidence = TestEvidence {
                test_id: test.id.clone(),
                run: SideRun::Sides {
                    sides: vec![
                        OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(
                            BTreeSet::new(),
                        ))),
                        OracleSide::Normal(OracleValue::Pattern(PatternValue::NoMatch)),
                    ],
                },
            };
            let before = evidence.clone();
            replace_patterns(&test, &mut evidence, None);
            let SideRun::Sides { sides: after } = evidence.run else {
                panic!("sides");
            };
            let SideRun::Sides { sides: before } = before.run else {
                panic!("sides");
            };
            assert_eq!(after[0], before[0]);
            assert_eq!(after[1], OracleSide::Unknown);
        }
    }
}
