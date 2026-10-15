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
//!   Both sides use the baseline signature, evaluation context and solver, and link only the
//!   test's initial variables. A witness and complete contrary coverage prove an observation
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
//! A mutant is Killed only through a `Distinguish`: a state slot compares ground terminal
//! sets, and a pattern slot compares declared functions of execution configurations.
//! A pattern witness and complete contrary coverage prove that some ground instance has
//! different observations. Both sides share the baseline signature and decider. Under
//! k-rust variable identity v3, received names are read verbatim, printing is injective
//! (VI-1..VI-5), and FreshCounter mints apart from received names within each request. Relation and
//! leaf Unsat decisions rely on the definedness premise pinned by TB-01 and the TV-01
//! initial-state admission guard. Undecided evidence stays Unknown.

use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kore::{
    ast::{Pattern, Sort},
    parser::parse_definition,
    walk,
};
use kink_native::bridge::{
    BridgeContext, BridgeFailure, BridgedPaths, paths_from_execution_values, tree_from_steps,
    validate_test_initial_state,
};
use kink_native::coverage::{RuleAuthors, TestCoverage};
use kink_native::execution::{
    AdaptedExecution, ExecutionAdapter, ExecutionAdapterFailure, ExecutionBudget, HaltClass,
    SolverProfile, StepRunFailure, SteppedExecution,
};
use kink_native::feasibility::{BackendRelations, TestInitialState};
use kink_native::representation::validate_representation;
use kink_native::signature::{DefinitionFacts, definition_facts};
use kink_native::step_events::{ObservationDecider, StepEventSpec, StepObservation};
use kink_native::{MutantRejection, NativeValidator, ValidatedDefinition};
use kink_patch::{
    Baseline, CandidateDisposition, CandidateGeneration, ClaimSupport, Patch, SentenceRef,
    Sha256Digest, Withdrawal, apply, structure_sha256,
};
use kink_pattern::{
    CollectionEvidence, CollectionStop, Evaluation, EvaluationContext, EvaluationOptions,
    EventVocabulary, ExecutionTerminal, ExecutionTerminalKind, MonitorOptions, PathStop, PathTree,
    PatternFailure, PatternOutcome, PatternPlan, RelationDecider, SearchPolicy, SymbolSorts,
    TreeOptions, evaluate_tree_with_stats, evaluate_with,
};

use crate::campaign::check_manifest;
use crate::oracle::OracleFailure;
use crate::selection::{CompiledEdit, coverage_selected};
use crate::{
    BaselineAdmission, CampaignFailure, CampaignFailureKind, CrashPolicy, ExecutionFailureKind,
    ExitStop, FinalResult, ManifestTest, MutantId, MutantPlan, MutantReport, MutantScopeFailure,
    MutantStatus, OracleFailureKind, OracleKind, OracleOutcome, OracleSide, OracleValue,
    PatternValue, ScheduleMode, Score, TerminalClass, TestPlan, TestRun, compare_supplied,
    derive_mutant_report, score, validate_baseline,
};
use crate::{MutantSelection, SelectionPolicy};

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
    /// T-CLASSIFY: must be a pure function of its term argument, independent of call
    /// history or mutable state. Every campaign verdict, FirstKill, coverage scheduling
    /// and evidence sharing rely on this premise.
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

/// One mutant's operator, written baseline sentences, plan, report and runs. A coupled
/// mutant is one `MutantRun` regardless of its edit count. Runs follow the recorded order:
/// none for a test planned as `SkippedAfterKill`, and none at all when a mutant-scope
/// failure stopped it before execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MutantRun {
    /// Earlier mutant with the same structure and claim withdrawal; counted once globally.
    pub same_as: Option<MutantId>,
    pub operator: String,
    pub written_sentences: Vec<SentenceRef>,
    pub plan: MutantPlan,
    pub report: MutantReport,
    pub evidence: Vec<TestEvidence>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CampaignOptions {
    pub schedule: ScheduleMode,
    pub selection: SelectionPolicy,
    /// Reuse evidence of identical compiled sides within this campaign.
    pub share_evidence: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CampaignRun {
    /// The declaration whose regenerated order the run used.
    pub selection: SelectionPolicy,
    pub baseline: Vec<TestEvidence>,
    /// The rule coverage of each baseline run, in manifest order: a scheduling input only, read
    /// by no oracle, fold, status or score.
    pub baseline_coverage: Vec<TestCoverage>,
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
/// Mutant counts are per distinct structure/withdrawal group: a candidate with `same_as`
/// adds no global mutant. Per-operator reports retain that operator's candidate counts.
/// An origin folded onto a candidate adds no mutant.
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
        if mutant.same_as.is_some() {
            continue;
        }
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
/// execution difference for some ground instance. Variable identity v3 reads names verbatim,
/// prints injectively and mints apart within each request (VI-1..VI-5), justifying the shared
/// decider's identity and relation decisions. A pattern witness and complete contrary
/// coverage establish the declared observation difference directly.
pub fn run_campaign(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    schedule: ScheduleMode,
) -> Result<CampaignRun, CampaignFailure> {
    run_campaign_with(
        campaign,
        generation,
        &CampaignOptions {
            schedule,
            selection: SelectionPolicy::None,
            share_evidence: true,
        },
    )
}

/// Runs every test, with coverage scheduling when requested.
pub fn run_campaign_with(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    options: &CampaignOptions,
) -> Result<CampaignRun, CampaignFailure> {
    run_campaign_multi(campaign, std::slice::from_ref(generation), options)
}

/// Admits and runs the baseline once, then executes candidates in generation order.
/// Every generation must derive from the validator's own baseline. The global score
/// is available only when every generation is scored; candidate ids are global.
///
/// This is [`run_campaign_multi_with`] through a fresh [`BaselineSession`]: the tests of one
/// campaign have distinct ids, so every baseline request misses and runs live.
pub fn run_campaign_multi(
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
    options: &CampaignOptions,
) -> Result<CampaignRun, CampaignFailure> {
    run_campaign_multi_with(
        campaign,
        generations,
        options,
        &mut BaselineSession::new(campaign.validator, campaign.classify),
    )
}

/// The terminal classifier of a campaign ([`Campaign::classify`]).
type Classify<'a> = dyn Fn(&Pattern) -> ExecutionTerminalKind + 'a;

/// Every input of one baseline run ([`Runtime::run`] and [`Runtime::prepare`]), besides the
/// session's validator and classifier: where each is read is listed on its field.
#[derive(Clone, Debug, PartialEq)]
struct BaselineKey {
    /// The evidence's and the bridge context's test id (`Runtime::run`).
    test_id: String,
    /// The state the adapter executes and the decider's `TestInitialState` (`Runtime::run`).
    initial_state: Pattern,
    /// One side per declaration, each by its projection (`Runtime::run`, `state_side`).
    oracles: Vec<OracleDeclaration>,
    /// The backend's module (`Runtime::prepare`, `Backend::from_definition`).
    module: String,
    /// The execution request's bounds and the watchdog's time (`Runtime::run`).
    budget: ExecutionBudget,
    /// The adapter's expected solver profile (`Runtime::prepare`); one per build.
    profile: SolverProfile,
}

/// A stored live baseline run: the runner's evidence and run cache (stepped evidence and rule
/// coverage), exactly as [`Runtime::run`] returned them.
#[derive(Clone)]
struct StoredBaseline {
    key: BaselineKey,
    evidence: TestEvidence,
    cache: RunCache,
}

/// How a run ended, as a [`BaselineSession`] records it (flow F-13). A recording never enters
/// an evidence row, a report encoding, a digest or a key.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RunStop {
    /// The execution ended without the watchdog: every path ended or stopped at a bound of the
    /// request (depth, simplification).
    Finished,
    /// The watchdog cancelled the execution at the budget's time.
    Time,
    /// The execution adapter returned no execution (an adapter or backend failure).
    Failed,
}

/// The leaves one execution returned, read from its `AdaptedExecution`: leaves per halt class,
/// the deepest leaf's depth, the rule ids their branches and traces name, and how the run
/// ended. After a cancellation k-rust may return some leaves (the paths that had ended, and
/// cancelled ones) or none. Unlike rule coverage (kink-native `TestCoverage`, which lists
/// nothing for a timed-out run because where the watchdog stopped it depends on the host), the
/// census keeps what a stopped run returned: it is a hint for a reader, never a key.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeafCensus {
    pub stop: RunStop,
    pub leaves: BTreeMap<HaltClass, usize>,
    /// The depth of the deepest leaf; `None` without leaves.
    pub deepest: Option<u64>,
    /// The compiled rule ids (`UNIQUE_ID`s) the leaves' branch transitions and `rewrite` or
    /// `remainder` trace entries name, as rule coverage reads them.
    pub rule_ids: BTreeSet<String>,
}

impl LeafCensus {
    fn of(execution: Result<&AdaptedExecution, &ExecutionAdapterFailure>) -> Self {
        let Ok(execution) = execution else {
            return Self {
                stop: RunStop::Failed,
                leaves: BTreeMap::new(),
                deepest: None,
                rule_ids: BTreeSet::new(),
            };
        };
        let mut leaves = BTreeMap::new();
        let mut rule_ids = BTreeSet::new();
        let mut insert = |entry: &str| {
            let entry = entry.strip_prefix("remainder:").unwrap_or(entry);
            rule_ids.extend(
                entry
                    .split(',')
                    .filter(|id| !id.is_empty())
                    .map(str::to_owned),
            );
        };
        for leaf in execution.leaves() {
            *leaves.entry(leaf.halt).or_insert(0) += 1;
            for transition in &leaf.branch.identity {
                insert(&transition.rule);
            }
            for entry in &leaf.branch.trace {
                if matches!(entry.kind.as_str(), "rewrite" | "remainder") {
                    insert(&entry.unique_id);
                }
            }
        }
        Self {
            stop: if execution.timed_out() {
                RunStop::Time
            } else {
                RunStop::Finished
            },
            leaves,
            deepest: execution
                .leaves()
                .iter()
                .map(|leaf| leaf.branch.depth)
                .max(),
            rule_ids,
        }
    }

    /// The number of leaves.
    #[must_use]
    pub fn total(&self) -> usize {
        self.leaves.values().sum()
    }
}

/// One execution of one test on one compiled side, as the session records it: its wall time
/// (the whole of the runner's run of the test: execution, bridge and oracle sides) and its
/// leaf census. Outside every evidence row, digest and key.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunRecording {
    pub test_id: String,
    pub wall: Duration,
    pub census: LeafCensus,
}

/// One baseline request of a campaign call: the recording of the live run that answered it
/// (for a reused run, the run it reuses), whether it was reused, and that run's rule coverage.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BaselineRecording {
    pub run: RunRecording,
    pub reused: bool,
    pub coverage: Option<TestCoverage>,
}

/// What one campaign call through a session ran: every baseline request, in test order, and
/// every live mutant run, per mutant in run order (a test skipped after a kill, a test of a
/// mutant stopped before execution, a shared piece of evidence and an unsupported symbolic
/// side have none).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CallRecording {
    pub baseline: Vec<BaselineRecording>,
    pub mutants: Vec<(MutantId, Vec<RunRecording>)>,
}

impl CallRecording {
    /// The baseline request of the test `test_id`, if the call made one.
    #[must_use]
    pub fn baseline_of(&self, test_id: &str) -> Option<&BaselineRecording> {
        self.baseline
            .iter()
            .find(|recording| recording.run.test_id == test_id)
    }

    /// The live run of the mutant `mutant` on the test `test_id`, if there was one.
    #[must_use]
    pub fn mutant_run(&self, mutant: MutantId, test_id: &str) -> Option<&RunRecording> {
        self.mutants
            .iter()
            .find(|(id, _)| *id == mutant)
            .and_then(|(_, runs)| runs.iter().find(|run| run.test_id == test_id))
    }
}

/// The live baseline runs of one command, each reused by later campaign calls of the same
/// command (flow F-12, README 6.3).
///
/// A session is created for one validator and one classifier, and lives in memory only: it is
/// never written to disk, so every verdict compares a mutant with a baseline run live in this
/// process. [`run_campaign_multi_with`] takes each test's baseline run through it: the first
/// request with a key runs live and stores the runner's own evidence and run cache; a later
/// request with an equal key returns them, inserted exactly where the runner produces baseline
/// evidence, so admission, scheduling, the fold and the comparisons are unchanged. The key is
/// every input of the run ([`BaselineKey`]: test id, initial state, oracle declarations,
/// module, budget, solver profile), and the validator and the classifier are fixed per session;
/// a campaign over another validator is refused, and a campaign with another classifier is not
/// memoised. The session borrows its validator, so that validator cannot change or move while
/// the session lives; a validator's baseline and compile options are fixed at bind and its
/// compiled baseline is memoised, so the session's validator always has the compiled baseline
/// and options [`BaselineSession::compiled_baseline`] records.
///
/// The session is used only when the baseline run is a function of that key: the campaign has
/// no step observation, no oracle is a pattern projection, every test is concrete, and its
/// classifier is the session's. Any other campaign runs every baseline live and leaves the
/// session untouched. A baseline stopped by a bound (for example `Failed(TimeLimit)`) is stored
/// and reused like any other run, and admission refuses it again.
///
/// Reuse rests on k-rust execution determinism, the premise replay already rests on: the same
/// compiled definition, module, budget and state give the same run. For such campaigns no state
/// a baseline run leaves in its `Runtime` is read later in the call except through what the
/// session stores (README 6.3, flow F-12 handoff): the backend's definition cache and its
/// memoised definition facts are functions of the compiled definition; k-rust's per-request
/// thread-local scopes (the `apart` counter, the instance-normal scan memo) restart for every
/// request; with Z3 the solver's result cache holds only `Sat`/`Unsat` answers keyed by the
/// exact query, so a later query reads what re-solving the same query gives (a solver timeout
/// aside, which is host-dependent between any two live runs); after the baseline runs, the call
/// reads the baseline `Runtime` only for definition facts and pattern sides, which feed pattern
/// slots only.
///
/// The session also records (flow F-13) what each call through it ran: the wall time and the
/// leaf census of every baseline request and every live mutant run of the last call
/// ([`BaselineSession::last_call`]). Recording is not memoisation: every call records, a
/// campaign that is not memoised included, and nothing recorded is read by the runner. No
/// recording enters an evidence row, a report encoding, a digest or a key.
pub struct BaselineSession<'v> {
    validator: &'v NativeValidator,
    classify: &'v Classify<'v>,
    /// The validator's compiled baseline (`kore_sha256`) and compile options, when it compiles;
    /// recorded on first request, so a fresh session per call ([`run_campaign_multi`]) costs no
    /// hash of the compiled definition.
    compiled: std::cell::OnceCell<Option<(Sha256Digest, k_rust::kompile::CompileOptions)>>,
    runs: Vec<StoredBaseline>,
    live: usize,
    reused: usize,
    /// The recording of the last call; reset when a call starts.
    last_call: CallRecording,
}

impl<'v> BaselineSession<'v> {
    /// An empty session for `validator`'s compiled baseline and `classify`.
    #[must_use]
    pub fn new(validator: &'v NativeValidator, classify: &'v Classify<'v>) -> Self {
        Self {
            validator,
            classify,
            compiled: std::cell::OnceCell::new(),
            runs: Vec::new(),
            live: 0,
            reused: 0,
            last_call: CallRecording::default(),
        }
    }

    /// What the last call through this session ran (empty before the first call, and for a
    /// call refused before its baseline runs): wall times, leaf censuses and baseline coverage,
    /// outside every evidence row, digest and key.
    #[must_use]
    pub const fn last_call(&self) -> &CallRecording {
        &self.last_call
    }

    /// Baseline runs this session made live (and stored).
    #[must_use]
    pub const fn live_runs(&self) -> usize {
        self.live
    }

    /// Baseline requests this session answered from a stored live run.
    #[must_use]
    pub const fn reused_runs(&self) -> usize {
        self.reused
    }

    /// Stored live runs, one per distinct key.
    #[must_use]
    pub const fn stored_runs(&self) -> usize {
        self.runs.len()
    }

    /// The classifier the session was created with: a campaign memoises only when its
    /// [`Campaign::classify`] is this very reference (the same function through another
    /// reference may have another vtable copy, which only misses).
    #[must_use]
    pub const fn classify(&self) -> &'v Classify<'v> {
        self.classify
    }

    /// The session's validator's compiled baseline (`kore_sha256`) and compile options; `None`
    /// when its baseline does not compile.
    pub fn compiled_baseline(&self) -> Option<(Sha256Digest, &k_rust::kompile::CompileOptions)> {
        self.compiled
            .get_or_init(|| compiled_identity(self.validator))
            .as_ref()
            .map(|(digest, options)| (*digest, options))
    }

    /// Refuses a campaign over another validator than the session's, even an equal clone: the
    /// session's validator is the one it borrows, by reference.
    fn admit(&self, campaign: &Campaign<'_>) -> Result<(), CampaignFailure> {
        if std::ptr::eq(campaign.validator, self.validator) {
            Ok(())
        } else {
            Err(CampaignFailure::new(
                CampaignFailureKind::InvalidDeclaration,
                "the baseline session belongs to another validator than the campaign's",
            ))
        }
    }

    /// Whether the campaign's baseline runs are functions of their keys: no step observation,
    /// no pattern oracle, concrete tests, and the session's classifier.
    fn memoises(&self, campaign: &Campaign<'_>) -> bool {
        let session: &Classify<'_> = self.classify;
        let campaign_classify: &Classify<'_> = campaign.classify;
        campaign.observation.is_empty()
            && std::ptr::eq(session, campaign_classify)
            && campaign.tests.iter().all(|test| {
                test.initial_state.variable_occurrences().is_empty()
                    && test
                        .oracles
                        .iter()
                        .all(|declaration| matches!(declaration.projection(), Projection::State(_)))
            })
    }

    /// The baseline run of `test` on the call's baseline `runtime`: stored, or live and then
    /// stored. With `memoise` false it is live and the session is untouched.
    fn baseline_run(
        &mut self,
        runtime: &mut Runtime,
        campaign: &Campaign<'_>,
        test: &TestCase,
        memoise: bool,
    ) -> (TestEvidence, RunCache) {
        if !memoise {
            let (evidence, cache) = runtime.run(campaign, test);
            self.record_baseline(&cache, false);
            return (evidence, cache);
        }
        let key = BaselineKey {
            test_id: test.id.clone(),
            initial_state: test.initial_state.clone(),
            oracles: test.oracles.clone(),
            module: campaign.module.to_owned(),
            budget: campaign.budget,
            profile: SolverProfile::BUILD,
        };
        if let Some(stored) = self.runs.iter().find(|stored| stored.key == key) {
            self.reused += 1;
            let (evidence, cache) = (stored.evidence.clone(), stored.cache.clone());
            self.record_baseline(&cache, true);
            return (evidence, cache);
        }
        let (evidence, cache) = runtime.run(campaign, test);
        self.record_baseline(&cache, false);
        self.live += 1;
        self.runs.push(StoredBaseline {
            key,
            evidence: evidence.clone(),
            cache: cache.clone(),
        });
        (evidence, cache)
    }

    /// Records one baseline request of the current call (recording only).
    fn record_baseline(&mut self, cache: &RunCache, reused: bool) {
        if let Some(run) = &cache.recording {
            self.last_call.baseline.push(BaselineRecording {
                run: run.clone(),
                reused,
                coverage: cache.coverage.clone(),
            });
        }
    }
}

/// A validator's compiled baseline identity and compile options, when it compiles.
fn compiled_identity(
    validator: &NativeValidator,
) -> Option<(Sha256Digest, k_rust::kompile::CompileOptions)> {
    validator
        .compile_baseline()
        .ok()
        .map(|compiled| (compiled.kore_sha256(), compiled.compile_options().clone()))
}

/// [`run_campaign_multi`] with each test's baseline run taken through `session` (see
/// [`BaselineSession`]). A campaign over another validator than the session's is refused
/// before anything runs. Everything after the baseline runs is [`run_campaign_multi`]'s.
pub fn run_campaign_multi_with(
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
    options: &CampaignOptions,
    session: &mut BaselineSession<'_>,
) -> Result<CampaignRun, CampaignFailure> {
    session.last_call = CallRecording::default();
    session.admit(campaign)?;
    let memoise = session.memoises(campaign);
    if generations.is_empty() {
        return Err(CampaignFailure::new(
            CampaignFailureKind::InvalidDeclaration,
            "a campaign needs at least one generation",
        ));
    }
    let schedule = options.schedule;
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
    if generations
        .iter()
        .any(|generation| !generation.derived_from(campaign.validator.baseline()))
    {
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
    runtime.coverage = Some(RuleAuthors::of(&baseline));
    // Test-written predicates do not inherit the definedness premise of backend-built
    // predicates. Refuse unsafe input through the existing declaration admission gate,
    // before any baseline or mutant execution (TV-01, R2-F1).
    for test in campaign.tests {
        validate_test_initial_state(&mut runtime.backend, &test.initial_state).map_err(
            |failure| {
                CampaignFailure::new(
                    CampaignFailureKind::BaselineOracleFailed,
                    format!("{failure:?}"),
                )
            },
        )?;
    }
    validate_representation(&baseline).map_err(|failure| {
        CampaignFailure::new(
            CampaignFailureKind::BaselineOracleFailed,
            failure.to_string(),
        )
    })?;
    let observation = StepObservation::new(&mut runtime.backend, campaign.observation.to_vec())
        .map_err(|failure| {
            CampaignFailure::new(
                CampaignFailureKind::InvalidDeclaration,
                format!("{failure:?}"),
            )
        })?;
    let (baseline_evidence, baseline_coverage) = {
        let baseline_runs = campaign
            .tests
            .iter()
            .map(|test| session.baseline_run(&mut runtime, campaign, test, memoise))
            .collect::<Vec<_>>();
        let baseline_coverage = baseline_runs
            .iter()
            .map(|(evidence, cache)| {
                cache
                    .coverage
                    .clone()
                    .unwrap_or_else(|| TestCoverage::failed(&evidence.test_id))
            })
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
                let patterns = facts.as_ref().ok().map(|_| {
                    runtime.step_sides(campaign, test, &observation, cache.stepped.as_ref())
                });
                replace_patterns(test, evidence, patterns.as_deref());
            }
        }
        validate_baseline(admit(campaign.tests, &baseline_evidence))?;
        (baseline_evidence, baseline_coverage)
    };
    let paired = campaign
        .tests
        .iter()
        .map(|test| {
            let baseline = baseline_evidence
                .iter()
                .find(|e| e.test_id == test.id)
                .expect("baseline test id");
            let coverage = baseline_coverage
                .iter()
                .find(|e| e.test_id == test.id)
                .expect("coverage test id");
            (
                test.id.as_str(),
                PairedTest {
                    test,
                    baseline,
                    coverage,
                    symbolic: !test.initial_state.variable_occurrences().is_empty(),
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut observations = BaselineObservations {
        runtime: &mut runtime,
        observation,
        evidence: options.share_evidence.then(BTreeMap::new),
    };

    let candidates = generations
        .iter()
        .flat_map(|generation| generation.candidates())
        .collect::<Vec<_>>();
    let mut runs: Vec<MutantRun> = Vec::with_capacity(candidates.len());
    let mut identities: Vec<Option<(Sha256Digest, Withdrawal)>> =
        Vec::with_capacity(candidates.len());
    for (index, candidate) in candidates.into_iter().enumerate() {
        let identity = mutant_identity(
            campaign.validator.baseline(),
            &candidate.patch,
            support.as_ref(),
        );
        let same_as = identity.as_ref().and_then(|identity| {
            identities
                .iter()
                .position(|earlier| earlier.as_ref() == Some(identity))
                .map(MutantId)
        });
        identities.push(identity);
        let execution = run_mutant(
            campaign,
            &candidate.patch,
            &baseline,
            &paired,
            options,
            support.as_ref(),
            &mut observations,
        );
        session
            .last_call
            .mutants
            .push((MutantId(index), execution.recordings));
        let plan = MutantPlan {
            mutant_id: MutantId(index),
            tests: execution.tests,
            mutant_failure: execution.failure,
            claims: execution.claims,
            selection: execution.selection,
        };
        let report = derive_mutant_report(&plan, &manifest, schedule)?;
        if let Some(earlier) = same_as {
            assert_eq!(
                report.status, runs[earlier.0].report.status,
                "STOP: same_as statuses differ"
            );
        }
        runs.push(MutantRun {
            same_as,
            operator: candidate.operator.clone(),
            written_sentences: candidate.patch.written_sentences(),
            plan,
            report,
            evidence: execution.evidence,
        });
    }
    let statuses = runs
        .iter()
        .filter(|run| run.same_as.is_none())
        .map(|run| run.report.status)
        .collect::<Vec<_>>();
    Ok(CampaignRun {
        selection: options.selection,
        baseline: baseline_evidence,
        baseline_coverage,
        mutants: runs,
        score: generations
            .iter()
            .all(CandidateGeneration::scored)
            .then(|| score(&statuses)),
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

/// The baseline backend and validated declarations shared by both observation sides.
struct BaselineObservations<'a> {
    runtime: &'a mut Runtime,
    observation: StepObservation,
    evidence: Option<BTreeMap<(EvidenceKey, String), CachedEvidence>>,
}

/// E2 compares the applied structure and the complete withdrawal value, including its patch.
/// An unavailable identity never removes a mutant from counting.
pub(crate) fn mutant_identity(
    baseline: &Baseline,
    patch: &Patch,
    support: Option<&ClaimSupport>,
) -> Option<(Sha256Digest, Withdrawal)> {
    let applied = apply(baseline, patch).ok()?;
    let structure = structure_sha256(applied.definition()).ok()?;
    let claims = match support {
        Some(support) => support.withdraw(baseline, patch).ok()?,
        None => Withdrawal::default(),
    };
    Some((structure, claims))
}

/// E3 includes the symbolic-side choice even for a ground test.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct EvidenceKey {
    patched: Sha256Digest,
    symbolic: SymbolicEvidenceKey,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum SymbolicEvidenceKey {
    Patched,
    Unsupported,
    Withdrawn(Sha256Digest),
}

#[derive(Clone)]
struct CachedEvidence {
    evidence: TestEvidence,
    signatures_match: bool,
    // Replaying baseline observation queries preserves its solver/prelude mutations on hits.
    stepped: Option<SteppedExecution>,
}

struct PairedTest<'a> {
    test: &'a TestCase,
    baseline: &'a TestEvidence,
    coverage: &'a TestCoverage,
    symbolic: bool,
}

struct MutantExecution {
    tests: Vec<TestPlan>,
    failure: Option<MutantScopeFailure>,
    evidence: Vec<TestEvidence>,
    claims: Withdrawal,
    selection: Option<MutantSelection>,
    /// The session's recordings of the live mutant runs (recording only).
    recordings: Vec<RunRecording>,
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
    paired: &BTreeMap<&str, PairedTest<'_>>,
    options: &CampaignOptions,
    support: Option<&ClaimSupport>,
    observations: &mut BaselineObservations<'_>,
) -> MutantExecution {
    match prepare_mutant(campaign, patch, compiled_baseline, support) {
        Err(failure) => MutantExecution {
            tests: Vec::new(),
            failure: Some(failure),
            evidence: Vec::new(),
            claims: Withdrawal::default(),
            selection: None,
            recordings: Vec::new(),
        },
        Ok((mut sides, claims)) => {
            let selection = mutant_selection(
                campaign,
                paired,
                &sides,
                patch,
                options.selection,
                observations,
            );
            let order = selection.as_ref().map_or_else(
                || campaign.tests.iter().map(|test| test.id.clone()).collect(),
                |selection| selection.order.clone(),
            );
            let (tests, evidence, recordings) = run_tests(
                campaign,
                &mut sides,
                paired,
                &order,
                options.schedule,
                observations,
            );
            MutantExecution {
                tests,
                failure: None,
                evidence,
                claims,
                selection,
                recordings,
            }
        }
    }
}

fn mutant_selection(
    campaign: &Campaign<'_>,
    paired: &BTreeMap<&str, PairedTest<'_>>,
    sides: &MutantSides,
    patch: &Patch,
    policy: SelectionPolicy,
    observations: &BaselineObservations<'_>,
) -> Option<MutantSelection> {
    let SelectionPolicy::Prioritize(selection) = policy else {
        return None;
    };
    let authors = observations
        .runtime
        .coverage
        .as_ref()
        .expect("baseline coverage authors");
    let site_ids = patch
        .written_sentences()
        .iter()
        .map(|sentence| {
            authors
                .ids_of(sentence)
                .map(str::to_owned)
                .collect::<BTreeSet<_>>()
        })
        .collect::<Vec<_>>();
    let mut selected = BTreeSet::new();
    let mut removed_rule_ids = BTreeSet::new();
    let mut global = false;
    for test in campaign.tests {
        let pair = &paired[test.id.as_str()];
        let edit = sides.edit(pair.symbolic);
        let groups = site_ids
            .iter()
            .map(|ids| ids.intersection(&edit.removed_rule_ids).cloned().collect())
            .collect::<Vec<_>>();
        if coverage_selected(pair.coverage, edit, selection.coupled, &groups) {
            selected.insert(test.id.as_str());
        }
        global |= edit.global;
        removed_rule_ids.extend(edit.removed_rule_ids.iter().cloned());
    }
    if global || selected.is_empty() {
        selected.extend(campaign.tests.iter().map(|test| test.id.as_str()));
    }
    let mut order = Vec::with_capacity(campaign.tests.len());
    for first in [true, false] {
        order.extend(
            campaign
                .tests
                .iter()
                .filter(|test| selected.contains(test.id.as_str()) == first)
                .map(|test| test.id.clone()),
        );
    }
    Some(MutantSelection {
        policy,
        order,
        deselected: Vec::new(),
        global,
        removed_rule_ids,
    })
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
    validate_representation(&side).map_err(|_| MutantScopeFailure::RepresentationRefused)?;
    match kink_native::equivalent_compilation(compiled_baseline, &side) {
        Ok(true) => return Err(MutantScopeFailure::EquivalentCompilation),
        Ok(false) => {}
        Err(_) => return Err(MutantScopeFailure::Infrastructure),
    }
    // A preparation failure here is the mutant side's.
    let patched_edit = CompiledEdit::between(compiled_baseline, &side);
    let patched =
        Runtime::prepare(campaign, &side).map_err(|_| MutantScopeFailure::Infrastructure)?;
    let Some(support) = support else {
        return Ok((
            MutantSides {
                patched,
                patched_edit,
                symbolic_edit: None,
                symbolic: SymbolicSide::Patched,
            },
            Withdrawal::default(),
        ));
    };
    // The patch applied during validation, so it applies here too.
    let claims = support
        .withdraw(campaign.validator.baseline(), patch)
        .map_err(|_| MutantScopeFailure::Infrastructure)?;
    let mut symbolic_edit = None;
    let symbolic = if !claims.trusted() {
        SymbolicSide::Unsupported
    } else if let Some(withdrawing) = claims.patch() {
        match campaign.validator.validate(withdrawing) {
            Ok(side) => {
                validate_representation(&side)
                    .map_err(|_| MutantScopeFailure::RepresentationRefused)?;
                symbolic_edit = Some(CompiledEdit::between(compiled_baseline, &side));
                SymbolicSide::Withdrawn(Box::new(
                    Runtime::prepare(campaign, &side)
                        .map_err(|_| MutantScopeFailure::Infrastructure)?,
                ))
            }
            Err(_) => SymbolicSide::Unsupported,
        }
    } else {
        SymbolicSide::Patched
    };
    Ok((
        MutantSides {
            patched,
            symbolic,
            patched_edit,
            symbolic_edit,
        },
        claims,
    ))
}

/// A prepared mutant: the patched definition, and what its symbolic tests run on.
struct MutantSides {
    patched: Runtime,
    symbolic: SymbolicSide,
    patched_edit: CompiledEdit,
    symbolic_edit: Option<CompiledEdit>,
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
    fn evidence_key(&self) -> EvidenceKey {
        EvidenceKey {
            patched: self.patched.digest,
            symbolic: match &self.symbolic {
                SymbolicSide::Patched => SymbolicEvidenceKey::Patched,
                SymbolicSide::Unsupported => SymbolicEvidenceKey::Unsupported,
                SymbolicSide::Withdrawn(runtime) => SymbolicEvidenceKey::Withdrawn(runtime.digest),
            },
        }
    }

    fn edit(&self, symbolic: bool) -> &CompiledEdit {
        if symbolic {
            self.symbolic_edit.as_ref().unwrap_or(&self.patched_edit)
        } else {
            &self.patched_edit
        }
    }

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

    fn facts(&mut self, symbolic: bool) -> Result<DefinitionFacts, String> {
        match (&mut self.symbolic, symbolic) {
            (SymbolicSide::Withdrawn(runtime), true) => runtime.facts(),
            // An unsupported symbolic side has already produced Failed(UnsupportedClaims).
            (SymbolicSide::Unsupported, true) => Err("unsupported symbolic side".into()),
            _ => self.patched.facts(),
        }
    }
}

/// A prepared mutant's test plans and runs, in manifest order, and the session's recordings of
/// its live runs (recording only: nothing here reads them).
fn run_tests(
    campaign: &Campaign<'_>,
    sides: &mut MutantSides,
    paired: &BTreeMap<&str, PairedTest<'_>>,
    order: &[String],
    schedule: ScheduleMode,
    observations: &mut BaselineObservations<'_>,
) -> (Vec<TestPlan>, Vec<TestEvidence>, Vec<RunRecording>) {
    let mut tests = Vec::with_capacity(campaign.tests.len());
    let mut evidence = Vec::with_capacity(campaign.tests.len());
    let mut recordings = Vec::new();
    let mut killed = false;
    for id in order {
        let pair = &paired[id.as_str()];
        let (test, baseline, symbolic) = (pair.test, pair.baseline, pair.symbolic);
        if killed {
            tests.push(TestPlan {
                test_id: test.id.clone(),
                run: TestRun::SkippedAfterKill,
            });
            continue;
        }
        let key = (sides.evidence_key(), test.id.clone());
        let cached = observations
            .evidence
            .as_ref()
            .and_then(|entries| entries.get(&key))
            .cloned();
        let (mut mutant, cache) = match &cached {
            Some(cached) => (
                cached.evidence.clone(),
                RunCache {
                    stepped: cached.stepped.clone(),
                    coverage: None,
                    recording: None,
                },
            ),
            None => sides.run(campaign, test, symbolic),
        };
        if let Some(recording) = &cache.recording {
            recordings.push(recording.clone());
        }
        // Initialize facts on both paths, including each newly prepared mutant backend.
        let signatures_match = observations
            .runtime
            .facts()
            .and_then(|baseline_facts| {
                sides
                    .facts(symbolic)
                    .map(|mutant_facts| baseline_facts.signature == mutant_facts.signature)
            })
            .unwrap_or(false);
        let signatures_match = cached.as_ref().map_or(signatures_match, |cached| {
            assert_eq!(
                signatures_match, cached.signatures_match,
                "STOP: cached signature comparison differs"
            );
            cached.signatures_match
        });
        let mut paired_baseline = baseline.clone();
        if signatures_match {
            // Always use the baseline backend, and repeat its observation queries on hits.
            // Besides preserving its mutable solver state, this keeps later uncached bytes exact.
            let mutant_patterns = observations.runtime.step_sides(
                campaign,
                test,
                &observations.observation,
                cache.stepped.as_ref(),
            );
            if cached.is_none() {
                replace_patterns(test, &mut mutant, Some(&mutant_patterns));
            }
        } else {
            replace_patterns(test, &mut paired_baseline, None);
            replace_patterns(test, &mut mutant, None);
        }
        if cached.is_none()
            && let Some(entries) = &mut observations.evidence
        {
            entries.insert(
                key,
                CachedEvidence {
                    evidence: mutant.clone(),
                    signatures_match,
                    stepped: cache.stepped,
                },
            );
        }
        let run = match (&paired_baseline.run, &mutant.run) {
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
        killed = schedule == ScheduleMode::FirstKill && run.kills();
        tests.push(TestPlan {
            test_id: test.id.clone(),
            run,
        });
        evidence.push(mutant);
    }
    (tests, evidence, recordings)
}

/// Stepped evidence retained from the primary run, its rule coverage when the side records
/// it, and the session's recording of the run (wall time and leaf census; recording only).
#[derive(Clone, Default)]
struct RunCache {
    stepped: Option<SteppedExecution>,
    coverage: Option<TestCoverage>,
    recording: Option<RunRecording>,
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
    digest: Sha256Digest,
    backend: Backend,
    adapter: ExecutionAdapter,
    context: EvaluationContext,
    facts: Option<Result<DefinitionFacts, String>>,
    /// The side's rule authors when its runs record coverage (the baseline only).
    coverage: Option<RuleAuthors>,
}

impl Runtime {
    /// Parses the side's KORE once for its symbol sorts and event-free backend adapter.
    fn prepare(campaign: &Campaign<'_>, side: &ValidatedDefinition) -> Result<Self, Preparation> {
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
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
            digest: side.kore_sha256(),
            backend,
            adapter,
            context,
            facts: None,
            coverage: None,
        })
    }

    fn facts(&mut self) -> Result<DefinitionFacts, String> {
        if self.facts.is_none() {
            self.facts = Some(definition_facts(&mut self.backend).map_err(|error| error.0));
        }
        self.facts.clone().expect("filled above")
    }

    fn run(&mut self, campaign: &Campaign<'_>, test: &TestCase) -> (TestEvidence, RunCache) {
        let started = Instant::now();
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
        cache.coverage = self.coverage.as_ref().map(|authors| match &execution {
            Ok(execution) => TestCoverage::of_execution(&test.id, execution, authors),
            Err(_) => TestCoverage::failed(&test.id),
        });
        // Recording only (flow F-13): read from the execution the run already has.
        let census = LeafCensus::of(execution.as_ref());
        let run = match execution {
            Err(failure) => SideRun::Failed((&failure).into()),
            Ok(execution) if execution.timed_out() => {
                SideRun::Failed(ExecutionFailureKind::TimeLimit)
            }
            Ok(execution) => match self.backend.with_solver(None, |definition, solver| {
                let decider = ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&test.initial_state),
                );
                Ok::<_, k_rust::backend::BackendError>(paths_from_execution_values(
                    &execution,
                    &BridgeContext {
                        test_id: &test.id,
                        classify: campaign.classify,
                        sorts: &self.context.symbol_sorts,
                    },
                    &|term| decider.terminal_value(term),
                ))
            }) {
                Err(_) => SideRun::Sides {
                    sides: vec![OracleSide::Unknown; test.oracles.len()],
                },
                Ok(Err(failure)) => SideRun::Failed((&failure).into()),
                Ok(Ok(bridged)) => SideRun::Sides {
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
        cache.recording = Some(RunRecording {
            test_id: test.id.clone(),
            wall: started.elapsed(),
            census,
        });
        (
            TestEvidence {
                test_id: test.id.clone(),
                run,
            },
            cache,
        )
    }

    /// The pattern-slot sides of one side's stepped run, evaluated with this (the baseline's)
    /// definition, solver and evaluation context.
    fn step_sides(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        observation: &StepObservation,
        execution: Option<&SteppedExecution>,
    ) -> Vec<OracleSide> {
        let mut context = self.context.clone();
        context.test_id.clone_from(&test.id);
        self.backend
            .with_solver(None, |definition, solver| {
                let decider = ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&test.initial_state),
                );
                let relations = BackendRelations::shared(
                    definition,
                    solver,
                    TestInitialState::of_test(&test.initial_state),
                );
                let evaluate = |execution: Option<&SteppedExecution>| {
                    let bridged = execution.and_then(|execution| {
                        tree_from_steps(
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
                            let evaluation = slot_evaluation(
                                &context,
                                plan,
                                &bridged.tree,
                                &bridged.collection,
                                observation.vocabulary(),
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
                Ok::<_, k_rust::backend::BackendError>(evaluate(execution))
            })
            .unwrap_or_else(|_| vec![OracleSide::Unknown; test.oracles.len()])
    }
}

/// `PatternPlan::new` accepts exactly this plan over `vocabulary`. A plan's fields are public,
/// so a plan edited after validation reaches the campaign unchecked; the shared-prefix monitor
/// equals `evaluate_with` only on validated plans (CS-04), and an arm without atoms is one
/// input where they differ (CS-06 review 1).
fn monitor_admits(plan: &PatternPlan, vocabulary: &EventVocabulary) -> bool {
    PatternPlan::new(
        vocabulary,
        plan.variables.clone(),
        plan.arms.clone(),
        plan.side_condition.clone(),
    )
    .is_ok_and(|validated| validated == *plan)
}

/// The exhaustive pattern evaluation of one slot on one side's path tree, equal to
/// `evaluate_with` over the tree's leaves (T1, corpus-scale README 4.6). The shared-prefix
/// monitor computes it when `monitor_admits` the plan and no monitor's live partials overflow
/// [`MonitorOptions::default`]'s cap; otherwise `evaluate_with` computes it from the same leaves.
/// So neither an unvalidated plan nor the cap can change a side, and the monitor's memory stays
/// bounded by the cap per (slot, path) (an overflow costs a second evaluation, not a side).
fn slot_evaluation(
    context: &EvaluationContext,
    plan: &PatternPlan,
    tree: &PathTree,
    collection: &CollectionEvidence,
    vocabulary: &EventVocabulary,
    decider: &dyn RelationDecider,
) -> Result<Evaluation, PatternFailure> {
    let evaluation = EvaluationOptions {
        stable_path_keys: true,
        search_policy: SearchPolicy::Exhaustive,
        input_error: false,
    };
    if monitor_admits(plan, vocabulary) {
        let monitored = evaluate_tree_with_stats(
            context,
            plan,
            tree,
            collection,
            None,
            TreeOptions {
                evaluation,
                monitor: MonitorOptions::default(),
            },
            decider,
        );
        if !monitored.as_ref().is_ok_and(|(_, stats)| stats.overflowed) {
            return monitored.map(|(evaluation, _)| evaluation);
        }
    }
    evaluate_with(
        context,
        plan,
        tree.paths(),
        collection,
        None,
        evaluation,
        decider,
    )
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
/// Complete terminals must come from the bridge guarded by definition independence
/// against that run's own definition (TV-01).
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
            | ExecutionAdapterFailure::UninhabitedVariable(_) => Self::Infrastructure,
        }
    }
}

impl From<&BridgeFailure> for ExecutionFailureKind {
    fn from(failure: &BridgeFailure) -> Self {
        match failure {
            BridgeFailure::NoLeaves
            | BridgeFailure::ContractViolation(_)
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
            MutantRejection::Patch(_)
            | MutantRejection::Compilation(_)
            | MutantRejection::Relink(_) => Self::Rejected,
        }
    }
}

#[cfg(test)]
#[path = "../../../testdata/k/support.rs"]
mod input_test_support;

#[cfg(test)]
mod tests {
    use super::*;

    /// The module is a key component of a stored baseline run (flow F-12): on the same baseline
    /// `Runtime`, a request under another module misses and runs live; the same request again is
    /// a hit. (No fixture has a second executable module, so the integration tests in
    /// tests/session.rs cannot vary it through a campaign.)
    #[test]
    fn a_session_key_holds_the_module() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let validator = NativeValidator::bind(
                    input_test_support::load_path(
                        &std::path::Path::new(input_test_support::DIR).join("counter.k"),
                        "COUNTER",
                    ),
                    k_rust::kompile::CompileOptions::default(),
                );
                let compiled = validator.compile_baseline().unwrap();
                let classify: &Classify<'_> = &|_| ExecutionTerminalKind::Normal;
                let z = || input_test_support::app("Lblz", vec![]);
                let test = TestCase {
                    id: "t".into(),
                    initial_state: input_test_support::initial_state(
                        input_test_support::app(
                            "Lblcounter",
                            vec![z(), input_test_support::app("Lbls", vec![z()])],
                        ),
                        "SortCounter",
                    ),
                    oracles: vec![
                        OracleDeclaration::new(
                            CrashPolicy::Reject,
                            Projection::State(StateProjection::WholeTerm),
                        )
                        .unwrap(),
                    ],
                };
                let tests = [test];
                let campaign = |module| Campaign {
                    validator: &validator,
                    module,
                    observation: &[],
                    classify,
                    tests: &tests,
                    budget: ExecutionBudget {
                        time: std::time::Duration::from_secs(30),
                        max_depth: None,
                        max_simplification_iterations: 1000,
                        max_breadth: None,
                    },
                };
                let counter = campaign("COUNTER");
                let other = campaign("COUNTER-OTHER");
                let mut runtime = Runtime::prepare(&counter, &compiled)
                    .unwrap_or_else(|_| panic!("baseline runtime"));
                let mut session = BaselineSession::new(&validator, classify);
                assert!(session.memoises(&counter) && session.memoises(&other));
                let first = session.baseline_run(&mut runtime, &counter, &tests[0], true);
                assert_eq!((session.live_runs(), session.reused_runs()), (1, 0));
                let moved = session.baseline_run(&mut runtime, &other, &tests[0], true);
                assert_eq!((session.live_runs(), session.reused_runs()), (2, 0));
                assert_eq!(moved.0, first.0, "the same runtime gives the same evidence");
                session.baseline_run(&mut runtime, &other, &tests[0], true);
                session.baseline_run(&mut runtime, &counter, &tests[0], true);
                assert_eq!(
                    (
                        session.live_runs(),
                        session.reused_runs(),
                        session.stored_runs()
                    ),
                    (2, 2, 2)
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Equal patched KORE does not identify the symbolic side: an equation metadata edit
    /// still withdraws claims whose support it touched, while the transition-only twin does not.
    #[test]
    fn evidence_cache_separates_symbolic_sides_and_test_ids() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                use k_rust::kast::{Sort, Term};
                use kink_patch::{Edit, TermRef};
                let validator = NativeValidator::bind(
                    input_test_support::load_path(
                        &std::path::Path::new(input_test_support::DIR)
                            .join("symbolic-claim-survivor.k"),
                        "SYMPARTIAL",
                    ),
                    k_rust::kompile::CompileOptions::default(),
                );
                let baseline = validator.baseline();
                let condition =
                    TermRef::new(input_test_support::rule(baseline, "SYMPARTIAL.half"), [1]);
                let main = Edit::ReplaceTerm {
                    expected: baseline.term(&condition).unwrap().clone(),
                    at: condition,
                    replacement: Term::Token {
                        token: "false".into(),
                        sort: Sort::new("Bool"),
                    },
                };
                let metadata = Edit::AddAttribute {
                    at: input_test_support::rule(baseline, "SYMPARTIAL.d"),
                    key: "group".into(),
                    value: serde_json::json!("cs10"),
                };
                let a = Patch::new(vec![main.clone()])
                    .unwrap()
                    .pinned(baseline)
                    .unwrap();
                let b = Patch::new(vec![main, metadata])
                    .unwrap()
                    .pinned(baseline)
                    .unwrap();
                let compiled = validator.compile_baseline().unwrap();
                assert_eq!(
                    validator.validate(&a).unwrap().kore_sha256(),
                    validator.validate(&b).unwrap().kore_sha256()
                );
                let support = ClaimSupport::new(baseline);
                let input = input_test_support::initial_state(
                    input_test_support::app(
                        "Lblseq",
                        vec![
                            input_test_support::app(
                                "Lblhalf",
                                vec![input_test_support::var("X", "SortNat")],
                            ),
                            input_test_support::app("Lblhalt", vec![]),
                        ],
                    ),
                    "SortProg",
                );
                let tests = ["one", "two"].map(|id| TestCase {
                    id: id.into(),
                    initial_state: input.clone(),
                    oracles: vec![
                        OracleDeclaration::new(
                            CrashPolicy::CompareIdentity,
                            Projection::State(StateProjection::WholeTerm),
                        )
                        .unwrap(),
                    ],
                });
                let campaign = Campaign {
                    validator: &validator,
                    module: "SYMPARTIAL",
                    observation: &[],
                    classify: &|_| ExecutionTerminalKind::Normal,
                    tests: &tests,
                    budget: ExecutionBudget {
                        time: std::time::Duration::from_secs(30),
                        max_depth: Some(32),
                        max_simplification_iterations: 1000,
                        max_breadth: None,
                    },
                };
                for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                    let mut runtime = Runtime::prepare(&campaign, &compiled)
                        .unwrap_or_else(|_| panic!("baseline runtime"));
                    let observation = StepObservation::new(&mut runtime.backend, vec![]).unwrap();
                    let evidence = tests
                        .iter()
                        .map(|test| runtime.run(&campaign, test).0)
                        .collect::<Vec<_>>();
                    let coverage = tests
                        .iter()
                        .map(|test| TestCoverage::failed(&test.id))
                        .collect::<Vec<_>>();
                    let paired = tests
                        .iter()
                        .zip(&evidence)
                        .zip(&coverage)
                        .map(|((test, baseline), coverage)| {
                            (
                                test.id.as_str(),
                                PairedTest {
                                    test,
                                    baseline,
                                    coverage,
                                    symbolic: true,
                                },
                            )
                        })
                        .collect();
                    let mut observations = BaselineObservations {
                        runtime: &mut runtime,
                        observation,
                        evidence: Some(BTreeMap::new()),
                    };
                    let (mut sides_a, claims_a) =
                        prepare_mutant(&campaign, &a, &compiled, Some(&support)).unwrap();
                    let (mut sides_b, claims_b) =
                        prepare_mutant(&campaign, &b, &compiled, Some(&support)).unwrap();
                    assert!(claims_a.withdrawn.is_empty());
                    assert_eq!(claims_b.withdrawn.len(), 2);
                    assert_eq!(sides_a.patched.digest, sides_b.patched.digest);
                    assert_ne!(sides_a.evidence_key(), sides_b.evidence_key());
                    assert!(matches!(sides_a.symbolic, SymbolicSide::Patched));
                    assert!(matches!(sides_b.symbolic, SymbolicSide::Withdrawn(_)));
                    let order = tests.iter().map(|test| test.id.clone()).collect::<Vec<_>>();
                    let (_, first, _) = run_tests(
                        &campaign,
                        &mut sides_a,
                        &paired,
                        &order,
                        schedule,
                        &mut observations,
                    );
                    assert_eq!(first.len(), 2);
                    assert_eq!(observations.evidence.as_ref().unwrap().len(), 2);
                    run_tests(
                        &campaign,
                        &mut sides_b,
                        &paired,
                        &order,
                        schedule,
                        &mut observations,
                    );
                    assert_eq!(
                        observations.evidence.as_ref().unwrap().len(),
                        4,
                        "different symbolic side must miss"
                    );
                    let key = (sides_a.evidence_key(), "one".into());
                    let cached = observations
                        .evidence
                        .as_mut()
                        .unwrap()
                        .get_mut(&key)
                        .unwrap();
                    cached.evidence.run = SideRun::Failed(ExecutionFailureKind::Infrastructure);
                    let (mut repeated, _) =
                        prepare_mutant(&campaign, &a, &compiled, Some(&support)).unwrap();
                    let (_, hit, _) = run_tests(
                        &campaign,
                        &mut repeated,
                        &paired,
                        &order,
                        schedule,
                        &mut observations,
                    );
                    assert_eq!(
                        hit[0].run,
                        SideRun::Failed(ExecutionFailureKind::Infrastructure),
                        "hit must reuse post-replacement evidence"
                    );
                    assert_eq!(
                        hit[1], first[1],
                        "test-id pairing must not reuse another test's evidence"
                    );
                    assert_eq!(observations.evidence.as_ref().unwrap().len(), 4);
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// TV-01 input refusals use the existing BaselineOracleFailed admission path in both
    /// schedules, before classification or mutant execution; the native test pins the
    /// shared boundary itself. These are the only deliverable-5 rows allowed to move.
    #[test]
    fn test_written_partial_negations_refuse_campaign_admission() {
        use kink_patch::{Edit, SelectionPolicy, SiteSelector, TermRef, derive_sites, select};
        let validator = NativeValidator::bind(
            input_test_support::load_path(
                &std::path::Path::new(input_test_support::DIR).join("partialreq.k"),
                "TV01UNSAT",
            ),
            k_rust::kompile::CompileOptions::default(),
        );
        let baseline = validator.baseline();
        let at = TermRef::new(input_test_support::rule(baseline, "TV01UNSAT.part"), [0, 1]);
        let patch = Patch::new(vec![Edit::ReplaceTerm {
            expected: baseline.term(&at).expect("rhs").clone(),
            replacement: k_rust::kast::Term::Token {
                token: "8".into(),
                sort: k_rust::kast::Sort::new("Int"),
            },
            at,
        }])
        .expect("patch");
        let discovery = derive_sites(
            baseline,
            "input-guard",
            &[
                SiteSelector::RuleLabel("TV01UNSAT.part".into()),
                SiteSelector::Path(vec![0, 1]),
            ],
        )
        .expect("site");
        let generation = select(&discovery, SelectionPolicy::Each, 1)
            .expect("selection")
            .fold("input-guard", |_| patch.clone())
            .expect("generation");
        const DIV: &str = r"Lbl'UndsSlsh'Int'Unds'{}(X:SortInt{},Y:SortInt{})";
        let not_equals = |atom: &str, value: &str| {
            format!(
                r#"\not{{SortGeneratedTopCell{{}}}}(\equals{{SortBool{{}},SortGeneratedTopCell{{}}}}({atom},\dv{{SortBool{{}}}}("{value}")))"#
            )
        };
        let positive = format!(r#"Lbl'Unds-GT-'Int'Unds'{{}}({DIV},\dv{{SortInt{{}}}}("0"))"#);
        let reflexive = format!("Lbl'UndsEqlsEqls'Int'Unds'{{}}({DIV},{DIV})");
        let part = "Lblpart{}(X:SortInt{})";
        let reflexive_part = format!("Lbl'UndsEqlsEqls'Int'Unds'{{}}({part},{part})");
        let negation_equivalent_pair = |connective: &str| {
            let negate = |value: &str| {
                format!(
                    r#"\{connective}(\equals{{SortBool{{}},SortGeneratedTopCell{{}}}}({positive},\dv{{SortBool{{}}}}("{value}")),\bottom{{SortGeneratedTopCell{{}}}}())"#
                )
            };
            format!(
                r"\and{{SortGeneratedTopCell{{}}}}({},{})",
                negate("true"),
                negate("false")
            )
        };
        for (label, condition) in [
            (
                "neither",
                format!(
                    r"\and{{SortGeneratedTopCell{{}}}}({},{})",
                    not_equals(&positive, "true"),
                    not_equals(&positive, "false")
                ),
            ),
            ("reflexive", not_equals(&reflexive, "true")),
            ("reflexive-part", not_equals(&reflexive_part, "true")),
            (
                "implies",
                negation_equivalent_pair("implies{SortGeneratedTopCell{}}"),
            ),
            (
                "iff",
                negation_equivalent_pair("iff{SortGeneratedTopCell{}}"),
            ),
            (
                "pred-equals",
                negation_equivalent_pair("equals{SortGeneratedTopCell{},SortGeneratedTopCell{}}"),
            ),
        ] {
            let tests = [TestCase {
                id: label.into(),
                initial_state: Pattern::And {
                    sort: k_rust::kompile::initial_configuration::kore_sort("SortGeneratedTopCell"),
                    arguments: vec![
                        input_test_support::initial_state(
                            input_test_support::app(
                                "Lblpair",
                                vec![
                                    input_test_support::var("X", "SortInt"),
                                    input_test_support::var("Y", "SortInt"),
                                ],
                            ),
                            "SortProg",
                        ),
                        k_rust::kore::parser::parse_pattern(&condition).expect("condition"),
                    ],
                },
                oracles: vec![
                    OracleDeclaration::new(
                        CrashPolicy::Reject,
                        Projection::State(StateProjection::WholeTerm),
                    )
                    .expect("oracle"),
                ],
            }];
            let campaign = Campaign {
                validator: &validator,
                module: "TV01UNSAT",
                observation: &[],
                classify: &|_| panic!("refused input must not be classified"),
                tests: &tests,
                budget: ExecutionBudget {
                    time: std::time::Duration::from_secs(30),
                    max_simplification_iterations: 1000,
                    max_depth: None,
                    max_breadth: None,
                },
            };
            for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let failure =
                    run_campaign(&campaign, &generation, mode).expect_err("unsafe input refused");
                assert_eq!(
                    failure.kind(),
                    CampaignFailureKind::BaselineOracleFailed,
                    "{label} {mode:?}"
                );
            }
        }
    }

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
