//! Runs a campaign through kink-native and maps each run to typed oracle sides.
//!
//! The baseline and every mutant execute every test with one primary time-bounded
//! [`ExecutionAdapter`] run (under `FirstKill`, a mutant only through its first killing
//! test), read through the kink-native bridge. Each declared oracle
//! turns the bridged paths into one [`OracleSide`]; each mapping is an exhaustive
//! `match` that never turns incomplete evidence into a value:
//!
//! - A state oracle (exit stop or final result) needs every path complete and a
//!   collection that stopped for lack of work. A test without a pattern oracle runs as a
//!   state-set result run (re-pin L1-1, [`RunOptions`]): k-rust merges equal final
//!   configurations, and a complete state set has exactly the distinct final configurations of
//!   the path set of the same request, diagnostics included (re-pin decision 3; kink-flow
//!   `tests/modality.rs` checks it on the corpus). A state set with an undefined step, a vacuous
//!   leaf or a contradicted claim is replaced by its path set, whose leaves name their own rules
//!   for the exclusions. A test with a pattern oracle runs as a stepped path set on both sides.
//!   A run the time bound cancelled is `Failed(TimeLimit)` (k-rust answers a cancellation with an
//!   error and publishes no leaf), a mutant's run its work budget stopped ([`WorkBudget`]) ends in
//!   a `work-bound` leaf, and every other incomplete run is `Unknown`, including a backend
//!   diagnostic. A work-bound mutant side is `Unknown` too, but its slot can still distinguish
//!   one-sidedly from a clean, ground, stuck leaf outside the baseline's complete set (re-pin
//!   L1-2, decision 6; [`OneSided`], off by default).
//! - A single crash terminal is a `SemanticCrash` side carrying its terminal term; a
//!   crash among several terminals is `Unknown`. This counts terminal leaves, not distinct
//!   configurations: a path set with two paths to one crash configuration is `Unknown`, and the
//!   state set of the same request, which merges them into one leaf, is a crash side (re-pin
//!   L1-1-fix-1; a kill through it rests on decision 3, `tests/state_set_routes.rs` route 1).
//! - A terminal term with a free variable is `Unknown`. A symbolic run's complete stuck leaf
//!   stands for all of its instances, so its term is not one value: comparing such terms
//!   structurally, or classifying them, is not a comparison of the values the programs compute.
//! - An undefined step (a feasible `Trivial` leaf, `PathStop::UndefinedStep`) is a complete
//!   terminal. Its exit stop is the class `UndefinedStep` without a code, and its final result
//!   is its last configuration, the pre-step term, as for a stuck terminal.
//! - A pattern oracle evaluates declared predicates of consecutive configurations.
//!   Both sides use the baseline signature, evaluation context, definition-independence checks
//!   and event walk, and link only the test's initial variables; every feasibility and relation
//!   query about a side's leaves is decided on that side's own definition and solver (re-pin
//!   finding A-12). A witness and complete contrary coverage prove an observation
//!   difference for some ground instance; an undecided presence, relation or discard is
//!   Unknown. Bindings require complete coverage, ground terms and definition independence.
//! - A run that is no evidence (kink-native `exclusion`: a counted stack stop, a load stack stop
//!   of its side's definition, an undefined step that contradicts a trusted claim, an
//!   implementation-chosen hook in its side's definition or initial state, a value or step that
//!   depends on the short-circuit reading, an allowance refusal, and since re-pin adoption A-1 any
//!   entry of k-rust's run-level lists: a contradicted-claim record, an open value read, an
//!   allowance refusal, an unsupported hook) is `SideRun::Failed` with that
//!   exclusion, so no slot of its test is compared: a mutant's is `Unknown`, and a baseline's
//!   makes admission refuse the campaign (`BaselineOracleFailed`), except a leaf's contradicted
//!   claim, which makes only that test `Failed(ContradictedClaim)` for every mutant (re-pin
//!   decision 2 is per test: Sebastien, 2026-10-17; a record on the list alone refuses, [`admit`]). The check runs whenever a run is judged, a baseline
//!   run a session reuses included, which is judged under the facts of the load that produced it
//!   as well as the current call's ([`BaselineSession`]). A test compares its slots only when
//!   both runs gave sides, so a run whose leaves contradict a claim never gives a
//!   `Distinguish`, whatever else it is (timed out, stack-stopped, failed to bridge).
//!
//! Every mutant is built without the claims its edit leaves unbacked (re-pin R0c-fix-2,
//! Sebastien 2026-10-17): a claim (`total`, `functional`, `preserves-definedness`, a lemma, ...)
//! is its author's assertion about the definition they wrote, and an edit of the part it rests on
//! leaves nobody backing it. The baseline keeps its claims, a trusted premise, and every baseline
//! test runs on the baseline as written. Every test of a mutant, ground or symbolic, runs on its
//! withdrawn definition ([`kink_patch::ClaimSupport::withdraw`]): the patch plus the removal of
//! every claim whose support the patch touched, so the mutant is a consistent theory k-rust
//! executes without trusting them. Equivalence is decided on the mutant as written, before the
//! removal. A mutant whose patch writes a claim itself, edits a lemma, or touches the support of
//! a claim no removal can take away has no such definition and is `UnsupportedClaims`; one whose
//! withdrawn definition does not compile is `StrippedClaimCompileFailure`. Both are unknown.
//! The claim-free mutant must then be a theory with models where its edit can change one (re-pin
//! R0c-fix-3): a function has at most one value per input, so two of its equations that apply
//! to one input with different values leave the mutant with no model, and k-rust's verdict would
//! be its listing order. k-rust's critical-pair check decides it over every pair of equations of
//! a symbol the edit can change ([`kink_native::consistency`]); a pair not shown to join refuses
//! the mutant as `InconsistentMutant`, invalid and outside the score. What the edit changes is read
//! from the compiled definitions (re-pin R0c-fix-4): the symbols whose compiled equations differ
//! from the baseline's, and those whose equations reach one, with kink-patch's source reading;
//! the source reading is a fail-closed cross-check, and a compiled equation of a touched sentence
//! it does not explain refuses the mutant as `UnsupportedClaims` (key `unread-equation`).

//! A run the watchdog cancelled is `TestRun::Failed(TimeLimit)`; an adapter or bridge
//! failure is `TestRun::Failed(Infrastructure)`. A rejected mutant runs nothing. The
//! mutants are the candidates of one folded generation derived from the campaign's own
//! baseline, and only a complete, nonempty generation is scored.
//!
//! A mutant is Killed only through a `Distinguish`: a state slot compares ground terminal
//! sets (or, one-sidedly, finds a final configuration of a work-bound mutant run outside the
//! baseline's complete set, [`OneSided`]), and a pattern slot compares declared functions of
//! execution configurations.
//! A pattern witness and complete contrary coverage prove that some ground instance has
//! different observations. Both sides share the baseline signature and definition-independence
//! decider; each side's leaves are admitted under its own definition. Under
//! k-rust variable identity v3, received names are read verbatim, printing is injective
//! (VI-1..VI-5), and FreshCounter mints apart from received names within each request. Relation and
//! leaf Unsat decisions rely on the definedness premise pinned by TB-01 and the TV-01
//! initial-state admission guard. Undecided evidence stays Unknown.
//!
//! Only relinking and compiling run on several threads (re-pin L1-3 and L1-3-fix-1,
//! [`CampaignOptions::compile_workers`]). The candidates are taken in chunks; each chunk's
//! mutants (each candidate's patch and its withdrawing patch, [`mutant_compiles`]) are compiled
//! ahead ([`NativeValidator::compile_ahead`]: each patch applied on the calling thread, then
//! relinked and compiled on worker threads), every worker is joined, and then the chunk runs
//! exactly as with one worker: one candidate at a time, in candidate order, on the calling
//! thread. k-rust documents relinking and compiling, and nothing else kink runs, as independent
//! of the thread and of what other threads do (its `docs/compatibility.md`, "Concurrency");
//! applying a patch types its edited rules through a recursion with no stack guard, so it stays
//! on the calling thread (review L1-3-1 D1). The consistency check, every backend
//! build ([`Backend::from_definition`]: the load's critical-pair check and definedness discharge)
//! and every execution run the simplifier, whose stack stops depend on the running thread's
//! stack and on the stack other threads hold of its process-wide budget ("Execute"); a stop there
//! refuses a mutant or excludes a run, so on several threads a status, or a mutant's place in the
//! score, would depend on the schedule. They stay sequential, outside any compile, and every
//! backend is built before and outside the watchdog. With one worker nothing is compiled ahead:
//! today's path.

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
    validate_test_initial_state, work_bound_stuck_terminals,
};
use kink_native::consistency::{CompiledEquations, MutantFailure, UnjoinedEquations};
use kink_native::coverage::{RuleAuthors, TestCoverage};
use kink_native::data::{DataEnds, DataFacts, data_ends};
use kink_native::exclusion::{DefinitionExclusions, Exclusion};
use kink_native::execution::{
    AdaptedExecution, ExecutionAdapter, ExecutionAdapterFailure, ExecutionBudget, HaltClass,
    ResultModality, ResultRun, SolverProfile, StepRunFailure, SteppedExecution,
};
use kink_native::feasibility::TestInitialState;
use kink_native::representation::validate_representation;
use kink_native::signature::{DefinitionFacts, definition_facts};
use kink_native::step_events::{ObservationDecider, StepEventSpec, StepObservation};
use kink_native::{MutantRejection, NativeValidator, ValidatedDefinition};
use kink_patch::{
    Baseline, CandidateDisposition, CandidateGeneration, Claim, ClaimSupport, Patch,
    SentenceOrigin, SentenceRef, Sha256Digest, UNREAD_EQUATION_CLAIM, Withdrawal, apply,
    structure_sha256,
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
use serde_json::{Value, json};

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
    /// What the run reports besides its sides (re-pin adoption A-1). Read by no comparison, fold,
    /// status or score, and not encoded in the campaign report.
    pub notes: RunNotes,
}

/// What one run reports besides its sides (re-pin adoption A-1): its contradicted-claim records
/// as specification diagnostics, its count of undecided solver answers, and whether a leaf of it
/// contradicts a claim. Empty for a run that failed or timed out, and for a run reused from a
/// baseline session on a load with a definition-level exclusion.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RunNotes {
    /// k-rust's `contradictedClaims` list of the run, the records of its definition's load
    /// included (`observedIn: load`): each says that a claim of the specification is false at an
    /// application (when `ground`), which the author can act on. Any record excludes the run
    /// (`contradicted-claim`, kink-native `exclusion`); a reader reports them.
    pub contradicted_claims: Vec<k_rust::backend::ContradictedClaimOutput>,
    /// k-rust's count of the undecided solver answers the run's decisions took (`smtUnknowns`;
    /// always 0 without Z3). Reported only (decision D-7 (a1)): never an exclusion.
    pub smt_unknowns: usize,
    /// Whether a leaf of the run contradicts a claim by decision 2's leaf rule (kink-native
    /// `DefinitionExclusions::contradiction_on_a_leaf`): the one contradiction for which
    /// admission keeps a baseline and makes only its test unknown ([`admit`]). A record on the
    /// run's list alone refuses the baseline, as any other exclusion does.
    pub leaf_contradiction: bool,
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
    /// How the runs are requested besides the campaign's budget (re-pin lane 1, L1-1).
    pub run: RunOptions,
    /// How many threads relink and compile mutants ahead of their turn (re-pin L1-3; at most
    /// [`NativeValidator::compile_workers`] of it). 1 (or 0) compiles each mutant when its turn
    /// comes, on the calling thread: the sequential path. More compiles each chunk of
    /// [`AHEAD_PER_WORKER`] times as many candidates ahead (their patches applied on the calling
    /// thread), then runs the chunk as with 1. The run and its report are the same for every
    /// value; only wall time and peak memory differ.
    pub compile_workers: usize,
}

/// How many candidates per compile worker one chunk compiles ahead
/// ([`CampaignOptions::compile_workers`]; kink-native's constant).
pub use kink_native::AHEAD_PER_WORKER;

/// How a campaign requests its runs besides the campaign's [`ExecutionBudget`] (re-pin lane 1,
/// L1-1). The default is a state set for every result run and no work budget, which is what
/// [`run_campaign`] and [`run_campaign_multi`]'s callers in kink use unless they choose otherwise.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RunOptions {
    /// The modality requested for every result run: the run of a test with no pattern oracle,
    /// on the baseline and on every mutant (k-rust's state set by default). A test with a pattern
    /// oracle runs as a stepped path set on both sides, and its fallback run when stepping fails
    /// is a path set too. A state set whose leaves include an undefined step, a vacuous leaf or a
    /// contradicted claim is replaced by the path set of the same request (kink-native
    /// `ExecutionAdapter::execute_result`). That replacement is decided per side, from that
    /// side's own leaves, so the two sides of one test can differ: a baseline state set without
    /// an undefined step is compared with a mutant path set that has one (re-pin L1-1-fix-1,
    /// kink-campaign `tests/state_set_routes.rs` route 2). Sides are compared as sets of
    /// projected final configurations, which decision 3 makes the same in both modalities; the
    /// single-crash rule of [`state_side`] reads the number of terminal leaves, though, so a
    /// state-set side can be a crash side where the path set of the same request is `Unknown`
    /// (route 1). `PathSet` is the reading at 1ee9955, kept for the modality differential.
    pub result_modality: ResultModality,
    /// The work budget of every mutant result run ([`WorkBudget`]).
    pub work: WorkBudget,
    /// Whether a work-bound mutant run can kill one-sidedly ([`OneSided`]; re-pin L1-2).
    pub one_sided: OneSided,
}

impl RunOptions {
    /// Every option as a JSON object, `{result_modality, work, one_sided}`: `work` is null
    /// without a work budget, else `{factor, floor}`; `one_sided` is [`OneSided::name`]. A store
    /// that records the options its runs were made with (kink-corpus index entries, `run_options`)
    /// records this value (re-pin L1-2-land; CACHE-ID review 2 minor 1). Every field is
    /// destructured, without `..`, and every nested option is matched exhaustively, so a new
    /// option does not compile until it is recorded here: no option can be left out of the
    /// record and silently default when the record is read back.
    #[must_use]
    pub fn value(&self) -> Value {
        let Self {
            result_modality,
            work,
            one_sided,
        } = *self;
        let work = match work {
            WorkBudget::Unbounded => Value::Null,
            WorkBudget::Calibrated { factor, floor } => json!({"factor": factor, "floor": floor}),
        };
        json!({
            "result_modality": result_modality.name(),
            "work": work,
            "one_sided": one_sided.name(),
        })
    }
}

/// The version of the one-sided kill rule ([`OneSided`]): which work-bound mutant runs give
/// one-sided evidence (kink-native `bridge::work_bound_stuck_terminals`, read by the mutant
/// runtime's judging) and when a state slot distinguishes from it (`one_sided_distinguishes`).
/// A component of kink's semantics identity ([`crate::identity::KINK_IDENTITY`], key
/// `one_sided`), so every store that honours a verdict made without the rule, or under another
/// version of it, misses or is refused, naming it (re-pin L1-2-land). Bump it whenever either
/// function changes which slots distinguish. v1 (re-pin L1-2, L1-2-fix-1): decision 6 and
/// finding A-15, a clean ground stuck leaf of a work-bound mutant run whose projection the
/// baseline's complete set lacks, with contradicted claims read per path.
pub const ONE_SIDED_VERSION: &str = "kink-campaign/one-sided/v1";

/// The one-sided early kill (re-pin L1-2: decision 6, finding A-15). Off by default: a state slot
/// distinguishes only two complete sides.
///
/// With [`OneSided::NoCrashClassifier`], a state slot whose mutant run ended at its work budget
/// ([`WorkBudget`]) distinguishes when the run's explored part holds a final configuration whose
/// projection the baseline's complete set lacks. Every completion of the mutant run has that
/// configuration among its finals, so the mutant's projected set differs from the baseline's
/// whatever the unexplored part holds. Exactly when (every condition required):
/// - the baseline side of the slot is a value (`OracleSide::Normal`): a complete run, free of
///   every exclusion, all of whose terminals are ground values;
/// - the test is ground (its initial state has no free variable);
/// - the mutant run was judged into sides (it is not an error, not timed out, and no exclusion
///   applies to it), and its only incompleteness is its last, `work-bound` leaf
///   ([`kink_native::bridge::work_bound_stuck_terminals`]: no stack stop, no diagnostic on any
///   leaf, every other leaf stuck, trivial or vacuous, every other path complete, no crash);
/// - a leaf of it is `Stuck`, clean, with a decided ground value (one term, no path predicate, no
///   free variable, definition-independent on the mutant's definition), and the slot's
///   projection of it is not in the baseline's projected set;
/// - the slot projects the whole term or the exit stop without an exit-code cell, which are
///   defined on every final configuration (a failed projection makes a two-sided slot `Error`,
///   and the unexplored part cannot be read).
///
/// Never from a cancelled or timed-out run, never on a pattern slot (stepped runs carry no work
/// budget), never from a complete mutant run (its two-sided comparison already distinguishes when
/// such a leaf exists). The mutant's side stays `Unknown`: only the slot's outcome becomes
/// `Distinguish`.
///
/// Contradicted claims are read per path (Sebastien, 2026-10-17; re-pin L1-2-fix-1; root README,
/// "What a kill trusts"): correcting a false kept claim to "true except where it fails" leaves
/// the baseline's complete set and the leaf's path unchanged unless that path used the claim
/// where it fails, so a contradiction on another path of the mutant run, explored or not, does
/// not void the leaf, and one on its own path does (the leaf is `Stuck`, carries no
/// contradicted claim and is a decided value). An explored contradicted leaf still makes the run
/// no evidence (decision 2's per-test rule, applied first), which is stricter than the principle
/// needs. The rule adds no execution premise; the two-sided per-test rule is a conservative
/// over-approximation of the per-path one, so a work budget can kill where the unbounded run is
/// `Unknown` (`testdata/k/l1/l12ct.k`, `l12cs.k`).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum OneSided {
    /// No one-sided kill.
    #[default]
    Off,
    /// One-sided kills, for a campaign whose classifier never answers
    /// `ExecutionTerminalKind::SemanticCrash` (as kink-flow's and kink-corpus's `all_normal`). The
    /// state slot does not model a mutant set that mixes crash and normal terminals, and a crash
    /// against a normal baseline is no set difference under any crash policy, so a crash terminal
    /// in the part of the mutant run its work budget left unexplored could change the two-sided
    /// verdict away from `Distinguish`. The runner cannot read a classifier's range, so the caller
    /// states it; the explored terminals are checked anyway.
    NoCrashClassifier,
}

impl OneSided {
    /// The record name: `"off"` or `"no-crash-classifier"`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::NoCrashClassifier => "no-crash-classifier",
        }
    }
}

/// The work budget (k-rust `max_work`: the most states a run may visit across all its paths) of
/// a mutant's result runs, calibrated per test from the baseline's run of that test, which used
/// the same request shape (re-pin lane 1, L1-1; k-rust answers section 4.6). A budget only stops a
/// run: a run it does not stop is the unbounded run (k-rust KINK-16 criterion 2), and a run it
/// stops ends in a `work-bound` leaf, which makes the side incomplete, so every slot of that test
/// is `Unknown`, unless it distinguishes one-sidedly ([`OneSided`], re-pin L1-2). It never
/// applies to a baseline run, and never to a stepped run (a pattern test's observed path set): a
/// bounded stepped run would expose the paths it finished where the unbounded run timed out, and
/// a pattern slot can take a witness from them, which would move a `Timeout` toward `Killed`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum WorkBudget {
    /// No work budget: runs are bounded by the campaign's budget only.
    #[default]
    Unbounded,
    /// `max_work = factor * W + floor`, where `W` is the work of the baseline's run of the test.
    Calibrated { factor: u64, floor: u64 },
}

impl WorkBudget {
    /// The `max_work` of a mutant's result run of a test whose baseline run visited
    /// `baseline_work` states; `None` without a budget.
    #[must_use]
    pub const fn limit(self, baseline_work: u64) -> Option<u64> {
        match self {
            Self::Unbounded => None,
            Self::Calibrated { factor, floor } => {
                Some(baseline_work.saturating_mul(factor).saturating_add(floor))
            }
        }
    }
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
            run: RunOptions::default(),
            compile_workers: 1,
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
        &mut BaselineSession::new(campaign.validator),
    )
}

/// Every input of one baseline run ([`Runtime::run`] and [`Runtime::prepare`]), besides the
/// session's validator and the campaign's classifier, which a hit re-applies (flow F-16): where
/// each is read is listed on its field.
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
    /// The modality of the result run (`Runtime::execute`; re-pin L1-1).
    modality: ResultModality,
}

/// A stored live baseline run, under its key.
struct StoredBaseline {
    key: BaselineKey,
    run: StoredRun,
}

/// What a session keeps of one live baseline run (re-pin R0c, R0b review 1 major 1). A run is
/// judged with the exclusions of the load it executed on, and every call prepares its own
/// baseline `Runtime`, so its own load: a hit must not judge a stored run against the requesting
/// call's load alone.
enum StoredRun {
    /// A run whose producing load had no definition-level exclusion: its classifier-independent
    /// part, exactly as [`Runtime::execute`] returned it (the adapter's execution and the run
    /// cache with its rule coverage and recording), and the exclusion facts of the load that
    /// produced it. Its evidence is not stored: a hit judges the stored execution again with the
    /// requesting campaign's classifier (flow F-16), under the producing load's facts combined
    /// with the requesting call's ([`DefinitionExclusions::combined`]).
    Executed {
        executed: Box<Executed>,
        load: DefinitionExclusions,
    },
    /// A run whose producing load was excluded ([`DefinitionExclusions::definition_exclusion`]:
    /// a load stack stop, an implementation-chosen hook): the execution is not kept, so it can
    /// never be judged again on another load. A hit is that exclusion, as the live run was; the
    /// run cache (coverage and recording, never evidence) is kept for the call's recording.
    Excluded {
        exclusion: Exclusion,
        cache: Box<RunCache>,
    },
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
/// the deepest leaf's depth, the rewrite rules the run applied, the states it visited, and how
/// the run ended. Every request answers a cancellation with an error (re-pin L1-1), so a stopped
/// run returns no leaves and no coverage, and its census says so. The census is a hint for a
/// reader, never a key.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeafCensus {
    pub stop: RunStop,
    pub leaves: BTreeMap<HaltClass, usize>,
    /// The depth of the deepest leaf; `None` without leaves.
    pub deepest: Option<u64>,
    /// The compiled ids (`UNIQUE_ID`s) of the rules and equations the run applied: k-rust's run
    /// coverage's `applied` (every run collects it, re-pin L1-1; equations included since L2-1,
    /// as kink-native `TestCoverage::applied_ids`); empty for an execution without coverage.
    pub rule_ids: BTreeSet<String>,
    /// The states the run visited (k-rust `work`); `None` for a failed or timed-out run.
    pub work: Option<u64>,
}

impl LeafCensus {
    fn of(execution: Result<&AdaptedExecution, &ExecutionAdapterFailure>) -> Self {
        let Ok(execution) = execution else {
            return Self {
                stop: RunStop::Failed,
                leaves: BTreeMap::new(),
                deepest: None,
                rule_ids: BTreeSet::new(),
                work: None,
            };
        };
        let mut leaves = BTreeMap::new();
        for leaf in execution.leaves() {
            *leaves.entry(leaf.halt).or_insert(0) += 1;
        }
        let rule_ids = execution
            .coverage()
            .map(|coverage| coverage.applied.clone())
            .unwrap_or_default();
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
            work: (!execution.timed_out()).then(|| execution.work()),
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
/// mutant stopped before execution and a shared piece of evidence have none).
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
/// A session is created for one validator, and lives in memory only: it is never written to
/// disk, so every verdict compares a mutant with a baseline run live in this process.
/// [`run_campaign_multi_with`] takes each test's baseline run through it: the first request
/// with a key executes live and stores the execution (the adapter's leaves, before any
/// classification) with its run cache; a later request with an equal key takes that execution
/// and judges it again exactly as the live run did, with the requesting campaign's classifier,
/// on this call's baseline side, so the evidence is inserted exactly where the runner produces
/// baseline evidence and admission, scheduling, the fold and the comparisons are unchanged.
/// The key is every input of the execution ([`BaselineKey`]: test id, initial state, oracle
/// declarations, module, budget, solver profile), and the validator is fixed per session; a
/// campaign over another validator is refused. The session borrows its validator, so that
/// validator cannot change or move while the session lives; a validator's baseline and compile
/// options are fixed at bind and its compiled baseline is memoised, so the session's validator
/// always has the compiled baseline and options [`BaselineSession::compiled_baseline`] records.
///
/// The classifier is not part of the session's identity (flow F-16, F-12 review 1): a
/// `dyn Fn` may hold state, so no reference stands for a behaviour. A hit therefore calls the
/// campaign's classifier on the stored execution's terminals, as the live run of a fresh call
/// does, and the evidence of a hit is the evidence a fresh call gives for any classifier,
/// stateful or panicking ones included. No premise about the classifier is made.
///
/// The session is used only when the baseline execution is a function of that key: the
/// campaign has no step observation, no oracle is a pattern projection, and every test is
/// concrete. Any other campaign runs every baseline live and leaves the session untouched. A
/// baseline stopped by a bound (for example `Failed(TimeLimit)`) is stored and reused like any
/// other run, and admission refuses it again.
///
/// Every call prepares its own baseline `Runtime`, so its own load of the definition, and a load
/// can count a stack stop on one call and none on the next (finding A-08). A run is therefore
/// stored with the exclusion facts of the load that produced it ([`StoredRun`]) and a hit is
/// judged under those facts combined with the requesting call's (re-pin R0c, R0b review 1 major
/// 1): load stack stops, the implementation-chosen census, the role-rooted axioms and the
/// `preserves-definedness` ids, everything [`Runtime::judge`] reads from a load. A run whose own
/// load had a definition-level exclusion is not stored at all: only that exclusion is, and a hit
/// is the exclusion again, on every later call of the session.
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
/// slots only. A hit judges the stored execution on this call's baseline `Runtime` (bridge,
/// terminal values and state sides read the compiled definition and, with Z3, that same exact
/// query cache), as a fresh call judges its own execution.
///
/// The session also records (flow F-13) what each call through it ran: the wall time and the
/// leaf census of every baseline request and every live mutant run of the last call
/// ([`BaselineSession::last_call`]). Recording is not memoisation: every call records, a
/// campaign that is not memoised included, and nothing recorded is read by the runner. No
/// recording enters an evidence row, a report encoding, a digest or a key.
pub struct BaselineSession<'v> {
    validator: &'v NativeValidator,
    /// The validator's compiled baseline (`kore_sha256`) and compile options, when it compiles;
    /// recorded on first request, so a fresh session per call ([`run_campaign_multi`]) costs no
    /// hash of the compiled definition.
    compiled: std::cell::OnceCell<Option<(Sha256Digest, k_rust::kompile::CompileOptions)>>,
    runs: Vec<StoredBaseline>,
    live: usize,
    reused: usize,
    /// The recording of the last call; reset when a call starts.
    last_call: CallRecording,
    /// The findings of the full critical-pair check every call reads as assumed (kink-flow's
    /// `[spec] assume_joined`; fz26 KINK-BASELINE-FINDINGS), by name.
    assume_joined: Vec<String>,
    /// The baseline's data facts under [`Self::assume_joined`], with the compiled baseline's
    /// `kore_sha256` they were computed for: given by the caller ([`Self::with_baseline_data`]) or
    /// computed by the first call that has a mutant, on its baseline load, and reused by every
    /// later call.
    baseline_data: Option<(Sha256Digest, DataFacts)>,
}

impl<'v> BaselineSession<'v> {
    /// An empty session for `validator`'s compiled baseline, assuming no finding.
    #[must_use]
    pub fn new(validator: &'v NativeValidator) -> Self {
        Self {
            validator,
            compiled: std::cell::OnceCell::new(),
            runs: Vec::new(),
            live: 0,
            reused: 0,
            last_call: CallRecording::default(),
            assume_joined: Vec::new(),
            baseline_data: None,
        }
    }

    /// The session, its calls reading the findings `names` names as assumed (fz26
    /// KINK-BASELINE-FINDINGS): on the baseline, so that a finding the author names does not
    /// make every mutant `baseline-findings`, and on each claim-free mutant alike. A name that
    /// matches no finding of the baseline, more than one, or a decided one refuses every call
    /// with a mutant ([`DataFacts::refused_names`]).
    #[must_use]
    pub fn assuming(mut self, names: Vec<String>) -> Self {
        self.assume_joined = names;
        self.baseline_data = None;
        self
    }

    /// The session with the baseline's data facts already computed by the caller (`facts`, on the
    /// validator's compiled baseline loaded on kink's route, under [`Self::assume_joined`]), so no
    /// call computes them again. Facts computed for another compiled definition or other names
    /// are not used.
    #[must_use]
    pub fn with_baseline_data(mut self, facts: DataFacts) -> Self {
        if facts.assume_joined() == self.assume_joined.as_slice()
            && let Some((digest, _)) = self.compiled_baseline()
        {
            self.baseline_data = Some((digest, facts));
        }
        self
    }

    /// The names the session's calls read as assumed.
    #[must_use]
    pub fn assume_joined(&self) -> &[String] {
        &self.assume_joined
    }

    /// The baseline's data facts, when a call has computed them or the caller gave them.
    #[must_use]
    pub fn baseline_data(&self) -> Option<&DataFacts> {
        self.baseline_data.as_ref().map(|(_, facts)| facts)
    }

    /// The baseline's data facts for `compiled` (the call's baseline compile) loaded as
    /// `runtime`: the session's, or computed on `runtime`'s selected definition and kept.
    fn data_of(
        &mut self,
        compiled: &ValidatedDefinition,
        runtime: &mut Runtime,
    ) -> Result<DataFacts, String> {
        let digest = compiled.kore_sha256();
        if let Some((stored, facts)) = &self.baseline_data
            && *stored == digest
        {
            return Ok(facts.clone());
        }
        let definition = runtime
            .backend
            .select_definition(None)
            .map_err(|error| error.to_string())?;
        let facts = DataFacts::of(&definition, &self.assume_joined);
        self.baseline_data = Some((digest, facts.clone()));
        Ok(facts)
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

    /// Whether the campaign's baseline executions are functions of their keys: no step
    /// observation, no pattern oracle and concrete tests. The classifier is not consulted: a hit
    /// re-applies the campaign's own.
    fn memoises(campaign: &Campaign<'_>) -> bool {
        campaign.observation.is_empty()
            && campaign.tests.iter().all(|test| {
                test.initial_state.variable_occurrences().is_empty()
                    && test
                        .oracles
                        .iter()
                        .all(|declaration| matches!(declaration.projection(), Projection::State(_)))
            })
    }

    /// The baseline run of `test` on the call's baseline `runtime`: a stored execution judged
    /// again with the campaign's classifier, or live and then stored. With `memoise` false it
    /// is live and the session is untouched.
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
            modality: runtime.modality,
        };
        if let Some(stored) = self.runs.iter().find(|stored| stored.key == key) {
            let (evidence, cache) = match &stored.run {
                // The classifier-dependent part of the run, again (flow F-16), under the facts of
                // the load that produced it and of this call's load (re-pin R0c).
                StoredRun::Executed { executed, load } => (
                    runtime.judge_on(campaign, test, executed, Some(load)),
                    executed.cache.clone(),
                ),
                StoredRun::Excluded { exclusion, cache } => (
                    TestEvidence {
                        test_id: test.id.clone(),
                        run: SideRun::Failed((*exclusion).into()),
                        notes: RunNotes::default(),
                    },
                    (**cache).clone(),
                ),
            };
            self.reused += 1;
            self.record_baseline(&cache, true);
            return (evidence, cache);
        }
        let (evidence, executed) = runtime.run_keeping(campaign, test, None);
        let cache = executed.cache.clone();
        self.record_baseline(&cache, false);
        self.live += 1;
        // A run of an excluded load is never stored for reuse: only its exclusion is.
        let run = match runtime.exclusions.definition_exclusion() {
            Some(exclusion) => StoredRun::Excluded {
                exclusion,
                cache: Box::new(executed.cache),
            },
            None => StoredRun::Executed {
                executed: Box::new(executed),
                load: runtime.exclusions.clone(),
            },
        };
        self.runs.push(StoredBaseline { key, run });
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
    let memoise = BaselineSession::memoises(campaign);
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
    // Every mutant is built claim-free (re-pin R0c-fix-2): the support relation is needed for
    // every campaign, ground or symbolic.
    let support = ClaimSupport::new(campaign.validator.baseline());

    let Ok(baseline) = campaign.validator.compile_baseline() else {
        return Err(admission_failure(BaselineAdmission::Invalid));
    };
    let mut runtime = Runtime::prepare(campaign, &baseline)
        .map_err(|_| admission_failure(BaselineAdmission::Error))?;
    runtime.coverage = Some(RuleAuthors::of(&baseline));
    runtime.modality = options.run.result_modality;
    // The baseline's full critical-pair check, once per session (fz26 KINK-BASELINE-FINDINGS):
    // only a call with a mutant reads it, and a name the author gives that the baseline refuses
    // refuses the call.
    let data = if generations
        .iter()
        .any(|generation| !generation.candidates().is_empty())
    {
        let facts = session
            .data_of(&baseline, &mut runtime)
            .map_err(|_| admission_failure(BaselineAdmission::Error))?;
        let refused = facts.refused_names();
        if !refused.is_empty() {
            return Err(CampaignFailure::new(
                CampaignFailureKind::InvalidDeclaration,
                refused
                    .iter()
                    .map(|refusal| format!("assume_joined `{}`: {}", refusal.name, refusal.reason))
                    .collect::<Vec<_>>()
                    .join("; "),
            ));
        }
        Ok(facts)
    } else {
        Err("a call with no mutant reads no baseline data facts".to_owned())
    };
    // The baseline's compiled equations, which every mutant's are read against (re-pin
    // R0c-fix-4). A baseline that does not internalize again leaves every mutant unchecked.
    let admission = MutantAdmission {
        equations: CompiledEquations::of(&baseline),
        support,
        module: campaign.module.to_owned(),
        assume_joined: session.assume_joined.clone(),
        data,
    };
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
    let (baseline_evidence, baseline_coverage, baseline_work) = {
        let baseline_runs = campaign
            .tests
            .iter()
            .map(|test| session.baseline_run(&mut runtime, campaign, test, memoise))
            .collect::<Vec<_>>();
        // The work of each baseline run, which calibrates the mutants' work budget of its test.
        let baseline_work = baseline_runs
            .iter()
            .map(|(_, cache)| cache.work)
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
                    runtime.step_sides(campaign, test, &observation, cache.stepped.as_ref(), None)
                });
                replace_patterns(test, evidence, patterns.as_deref());
            }
        }
        let admission = admit(campaign.tests, &baseline_evidence);
        if admission == BaselineAdmission::OracleFailed
            && let Some((test_id, exclusion)) = baseline_exclusion(&baseline_evidence)
        {
            return Err(CampaignFailure::excluded(
                CampaignFailureKind::BaselineOracleFailed,
                exclusion,
                format!(
                    "the baseline run of test {test_id} is no evidence: {}",
                    exclusion.name()
                ),
            ));
        }
        validate_baseline(admission)?;
        (baseline_evidence, baseline_coverage, baseline_work)
    };
    let paired = campaign
        .tests
        .iter()
        .zip(&baseline_work)
        .map(|(test, work)| {
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
                    mutant_max_work: work.and_then(|work| options.run.work.limit(work)),
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
    let mut identities: Vec<Option<MutantIdentity>> = Vec::with_capacity(candidates.len());
    let chunk = options.compile_workers.max(1) * AHEAD_PER_WORKER;
    let mut ahead = None;
    for (index, candidate) in candidates.iter().copied().enumerate() {
        if options.compile_workers > 1 && index % chunk == 0 {
            // Drop what the last chunk left of its own, then compile this chunk ahead; every
            // worker is joined before the chunk's first candidate runs below.
            drop(ahead.take());
            let patches = candidates[index..candidates.len().min(index + chunk)]
                .iter()
                .flat_map(|candidate| {
                    mutant_compiles(
                        campaign.validator.baseline(),
                        &admission.support,
                        &candidate.patch,
                    )
                })
                .collect::<Vec<_>>();
            ahead = Some(
                campaign
                    .validator
                    .compile_ahead(&patches, options.compile_workers),
            );
        }
        stage_log::note(campaign, stage_log::Stage::Mutant(index));
        let identity = mutant_identity(
            campaign.validator.baseline(),
            &candidate.patch,
            &admission.support,
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
            &admission,
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
            inconsistent_pairs: execution.inconsistent_pairs,
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
    drop(ahead);
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

/// The patches the runner's mutant preparation compiles for `patch`: the patch itself and, when
/// [`ClaimSupport::withdraw`] gives a trusted withdrawal that removes claims, its withdrawing
/// patch (re-pin L1-3: what a caller compiles ahead, [`NativeValidator::compile_ahead`]). A patch
/// that does not apply gives only itself.
pub fn mutant_compiles(baseline: &Baseline, support: &ClaimSupport, patch: &Patch) -> Vec<Patch> {
    let withdrawing = support
        .withdraw(baseline, patch)
        .ok()
        .filter(Withdrawal::trusted)
        .and_then(|claims| claims.patch().cloned());
    std::iter::once(patch.clone()).chain(withdrawing).collect()
}

/// Where the steps after compile run (re-pin L1-3), recorded in unit tests only: each candidate's
/// turn, each consistency check, backend build and execution, with the campaign and the thread.
mod stage_log {
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Stage {
        Mutant(usize),
        Consistency,
        Backend,
        Execute,
    }

    /// `(campaign address, stage, thread)`, in the order the steps ran.
    #[cfg(test)]
    pub static LOG: std::sync::Mutex<Vec<(usize, Stage, std::thread::ThreadId)>> =
        std::sync::Mutex::new(Vec::new());

    #[cfg(test)]
    pub fn note(campaign: &super::Campaign<'_>, stage: Stage) {
        LOG.lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push((
                std::ptr::from_ref(campaign).addr(),
                stage,
                std::thread::current().id(),
            ));
    }

    #[cfg(not(test))]
    #[inline(always)]
    pub const fn note(_: &super::Campaign<'_>, _: Stage) {}
}

fn admission_failure(admission: BaselineAdmission) -> CampaignFailure {
    validate_baseline(admission).expect_err("a rejected admission")
}

/// The first baseline test whose run is excluded ([`kink_native::exclusion`]) in a way that
/// refuses the campaign, with its exclusion: every exclusion but a contradicted claim ([`admit`]).
fn baseline_exclusion(evidence: &[TestEvidence]) -> Option<(&str, Exclusion)> {
    evidence.iter().find_map(|evidence| match evidence.run {
        SideRun::Failed(ExecutionFailureKind::ContradictedClaim)
            if evidence.notes.leaf_contradiction =>
        {
            None
        }
        SideRun::Sides { .. } => None,
        SideRun::Failed(kind) => kind
            .exclusion()
            .map(|exclusion| (evidence.test_id.as_str(), exclusion)),
    })
}

/// A baseline side that failed is `Error`; one that is bounded, unknown or a crash its
/// declaration rejects is `OracleFailed`, and so is a baseline run that is excluded
/// ([`kink_native::exclusion`]): it completed but is no evidence, as an unknown side.
///
/// The exception is a baseline run a leaf of which contradicts a trusted claim (re-pin decision
/// 2, per test since Sebastien's 2026-10-17 decision): it makes that test
/// `Failed(ContradictedClaim)` for every mutant ([`run_tests`]) and refuses nothing else. The
/// baseline is inconsistent only at inputs that test reaches; weakening the claim there gives a
/// definition with models in which every other test, whose runs show no contradiction, behaves
/// the same. A baseline run excluded only by a record on k-rust's `contradictedClaims` list (re-pin
/// adoption A-1; [`RunNotes::leaf_contradiction`] false) is refused as any other exclusion is:
/// before A-1 such a run was either compared or, when a leaf carried the record, unknown and
/// refused, so reading the list relaxes no refusal. Keeping such a baseline per test would
/// relax the refusal of the second case, which needs its own decision.
fn admit(tests: &[TestCase], evidence: &[TestEvidence]) -> BaselineAdmission {
    let mut admission = BaselineAdmission::Accepted;
    for (test, evidence) in tests.iter().zip(evidence) {
        let sides = match &evidence.run {
            SideRun::Sides { sides, .. } => sides,
            SideRun::Failed(ExecutionFailureKind::ContradictedClaim)
                if evidence.notes.leaf_contradiction =>
            {
                continue;
            }
            SideRun::Failed(kind) if kind.exclusion().is_some() => {
                admission = BaselineAdmission::OracleFailed;
                continue;
            }
            SideRun::Failed(_) => return BaselineAdmission::Error,
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

/// E2: two mutants with this identity behave alike. It is the applied structure (equivalence is
/// decided on the mutant as written) and the claim-free mutant every test runs on: its applied
/// structure when claims are removed, or that no definition without unbacked claims exists.
/// An unavailable identity never removes a mutant from counting.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MutantIdentity {
    structure: Sha256Digest,
    claim_free: ClaimFree,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ClaimFree {
    /// The patch leaves no claim unbacked: the mutant as written.
    AsWritten,
    /// The applied structure of the withdrawn definition.
    Withdrawn(Sha256Digest),
    /// Some unbacked claim cannot be removed: the mutant is refused.
    Unsupported,
}

pub(crate) fn mutant_identity(
    baseline: &Baseline,
    patch: &Patch,
    support: &ClaimSupport,
) -> Option<MutantIdentity> {
    let applied = apply(baseline, patch).ok()?;
    let structure = structure_sha256(applied.definition()).ok()?;
    let claims = support.withdraw(baseline, patch).ok()?;
    let claim_free = if !claims.trusted() {
        ClaimFree::Unsupported
    } else if let Some(withdrawing) = claims.patch() {
        ClaimFree::Withdrawn(
            structure_sha256(apply(baseline, withdrawing).ok()?.definition()).ok()?,
        )
    } else {
        ClaimFree::AsWritten
    };
    Some(MutantIdentity {
        structure,
        claim_free,
    })
}

/// E3: the compiled definition a mutant's tests run on (the claim-free mutant).
type EvidenceKey = Sha256Digest;

#[derive(Clone)]
struct CachedEvidence {
    evidence: TestEvidence,
    signatures_match: bool,
    // Replaying baseline observation queries preserves its solver/prelude mutations on hits.
    stepped: Option<SteppedExecution>,
    /// The run's one-sided evidence ([`RunCache::one_sided`]), so a hit judges as the live run.
    one_sided: Vec<ExecutionTerminal>,
}

struct PairedTest<'a> {
    test: &'a TestCase,
    baseline: &'a TestEvidence,
    coverage: &'a TestCoverage,
    /// The work budget of every mutant's result run of this test ([`WorkBudget::limit`] of the
    /// baseline run's work; `None` without a budget or without a baseline count).
    mutant_max_work: Option<u64>,
}

struct MutantExecution {
    tests: Vec<TestPlan>,
    failure: Option<MutantScopeFailure>,
    evidence: Vec<TestEvidence>,
    claims: Withdrawal,
    inconsistent_pairs: Vec<UnjoinedEquations>,
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
/// or make `FirstKill` run every test. No test outcome overrides a kill: a contradicted claim
/// (re-pin decision 2) makes only its own test unknown ([`derive_mutant_report`]).
fn run_mutant(
    campaign: &Campaign<'_>,
    patch: &Patch,
    compiled_baseline: &ValidatedDefinition,
    paired: &BTreeMap<&str, PairedTest<'_>>,
    options: &CampaignOptions,
    admission: &MutantAdmission,
    observations: &mut BaselineObservations<'_>,
) -> MutantExecution {
    // fz26 KINK-BASELINE-FINDINGS: no end of a baseline with a finding left is data, so no
    // comparison on it can kill, and the mutant is unknown before it compiles.
    let gated = match &admission.data {
        Ok(facts) if data_ends(facts) == DataEnds::None => Err(MutantRefusal::new(
            MutantScopeFailure::BaselineFindings,
            Withdrawal::default(),
        )),
        _ => prepare_mutant(campaign, patch, compiled_baseline, admission),
    };
    match gated {
        Err(refusal) => {
            let MutantRefusal {
                failure,
                claims,
                inconsistent_pairs,
            } = *refusal;
            MutantExecution {
                tests: Vec::new(),
                failure: Some(failure),
                evidence: Vec::new(),
                claims,
                inconsistent_pairs,
                selection: None,
                recordings: Vec::new(),
            }
        }
        Ok((mut sides, claims)) => {
            sides.runtime.modality = options.run.result_modality;
            sides.runtime.one_sided = options.run.one_sided;
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
                inconsistent_pairs: Vec::new(),
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
        let edit = &sides.edit;
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

/// Builds the mutant every test runs on ([`claim_free_mutant`]) and its runtime, or its
/// mutant-scope failure with the claims its patch leaves unbacked. A preparation failure after
/// the claim-free mutant is built is the mutant side's (`Infrastructure`).
fn prepare_mutant(
    campaign: &Campaign<'_>,
    patch: &Patch,
    compiled_baseline: &ValidatedDefinition,
    admission: &MutantAdmission,
) -> Result<(MutantSides, Withdrawal), Box<MutantRefusal>> {
    let ClaimFreeMutant {
        side,
        claims,
        loaded,
        ..
    } = claim_free_mutant(
        campaign.validator,
        compiled_baseline,
        patch,
        admission,
        &mut |stage| match stage {
            MutantStage::Backend => stage_log::note(campaign, stage_log::Stage::Backend),
            MutantStage::Consistency => stage_log::note(campaign, stage_log::Stage::Consistency),
        },
    )?;
    let fail = |failure| MutantRefusal::new(failure, claims.clone());
    let edit = CompiledEdit::between(compiled_baseline, &side);
    // The claim-free mutant's backend was loaded once, for its facts, and runs its tests.
    let runtime = Runtime::from_loaded(campaign, &side, loaded)
        .map_err(|_| fail(MutantScopeFailure::Infrastructure))?;
    Ok((MutantSides { runtime, edit }, claims))
}

/// A step of [`claim_free_mutant`] that it reports to its caller's stage hook before running it
/// (the runner's unit tests record where each step runs, re-pin L1-3).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum MutantStage {
    /// The load of the claim-free mutant on kink's route (`Backend::from_definition`), whose
    /// selected definition its full critical-pair check and its runs read.
    Backend,
    /// The consistency check of the claim-free mutant
    /// ([`kink_native::consistency::admit_mutant_with`]) and the comparison of its findings with
    /// the baseline's.
    Consistency,
}

/// The claim-free mutant of a patch: the compiled definition every test of the mutant runs on,
/// the claims the patch leaves unbacked, which its compile has withdrawn, and its full
/// critical-pair check under the admission's names ([`claim_free_mutant`]).
pub struct ClaimFreeMutant {
    pub side: ValidatedDefinition,
    pub claims: Withdrawal,
    /// The claim-free mutant's data facts, on the definition its runs execute on.
    pub data: DataFacts,
    /// The claim-free mutant's load, which the runner's runtime takes over.
    loaded: LoadedSide,
}

impl std::fmt::Debug for ClaimFreeMutant {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ClaimFreeMutant")
            .field("side", &self.side.kore_sha256())
            .field("claims", &self.claims)
            .field("data", &self.data)
            .finish_non_exhaustive()
    }
}

/// The claim-free mutant of `patch`, exactly as the runner builds it for every test of the
/// mutant, or its mutant-scope failure with the claims its patch leaves unbacked (re-pin
/// R0c-fix-2, Sebastien 2026-10-17: a mutant drops the claims its edit leaves unbacked).
/// `validator` is the campaign's (bound to the baseline the patch was derived from),
/// `compiled_baseline` its baseline compile, `admission` what every mutant of that baseline is
/// admitted against ([`MutantAdmission::new`]), and `on_stage` is told each [`MutantStage`]
/// before it runs.
///
/// The mutant as written is validated, admitted and checked for an equivalent compilation first,
/// with the baseline's claims, so a semantically null edit stays `EquivalentCompilation` and
/// removing claims never makes a mutant equivalent. Then [`ClaimSupport::withdraw`] removes every
/// claim the edit leaves unbacked, and the claim-free mutant is compiled: every test, ground or
/// symbolic, runs on it. A mutant with an unbacked claim no removal takes away is
/// `UnsupportedClaims`; one whose claim-free definition k-rust refuses to compile is
/// `StrippedClaimCompileFailure`. Both are unknown, never killed.
///
/// Last, the claim-free mutant must be a theory with models where its edit can change one (re-pin
/// R0c-fix-3, decisions log 2026-10-17 "inconsistent mutants"): every pair of equations of a
/// symbol whose compiled equations differ from the baseline's or reach one, or that the patch
/// redefines or reaches by kink-patch's source reading ([`ClaimSupport::effect`]), must join by
/// k-rust's critical-pair check ([`kink_native::consistency::admit_mutant_with`], re-pin
/// R0c-fix-4). A pair not shown to join, or a check that cannot run, refuses the mutant as
/// `InconsistentMutant`, invalid and outside the score, with the pairs named. A compiled equation
/// of a sentence the patch touches whose head the source reading does not redefine leaves the
/// claims the edit unbacks unknown, so the mutant is `UnsupportedClaims`, each such equation
/// recorded as an unsupported claim with key [`UNREAD_EQUATION_CLAIM`]. The check reads the
/// claim-free mutant's full critical-pair check ([`DataFacts`]), computed once on the backend its
/// runs execute on (fz26 KINK-BASELINE-FINDINGS); a mutant that does not load there is
/// `Infrastructure`. Every finding outside the heads the edit can change must then be the
/// baseline's (by name and by the unique ids of its equations): such a pair is normalized with the
/// baseline's equations alone, and kink checks it rather than arguing it, refusing a difference
/// as `MutantFindings` (unknown). Whether the baseline's own findings leave any end data is the
/// runner's question, not this function's (`BaselineFindings`).
///
/// # Errors
///
/// The mutant-scope failure that refuses the mutant, with the claims and pairs it names.
pub fn claim_free_mutant(
    validator: &NativeValidator,
    compiled_baseline: &ValidatedDefinition,
    patch: &Patch,
    admission: &MutantAdmission,
    on_stage: &mut dyn FnMut(MutantStage),
) -> Result<ClaimFreeMutant, Box<MutantRefusal>> {
    let support = &admission.support;
    let unclaimed = |failure| MutantRefusal::new(failure, Withdrawal::default());
    let side = validator
        .validate(patch)
        .map_err(|rejection| unclaimed(MutantScopeFailure::from(&rejection)))?;
    validate_representation(&side)
        .map_err(|_| unclaimed(MutantScopeFailure::RepresentationRefused))?;
    match kink_native::equivalent_compilation(compiled_baseline, &side) {
        Ok(true) => return Err(unclaimed(MutantScopeFailure::EquivalentCompilation)),
        Ok(false) => {}
        Err(_) => return Err(unclaimed(MutantScopeFailure::Infrastructure)),
    }
    // The patch applied during validation, so it applies here too.
    let baseline = validator.baseline();
    let (mut claims, effect) = support
        .withdraw(baseline, patch)
        .and_then(|claims| Ok((claims, support.effect(baseline, patch)?)))
        .map_err(|_| unclaimed(MutantScopeFailure::Infrastructure))?;
    if !claims.trusted() {
        return Err(MutantRefusal::new(
            MutantScopeFailure::UnsupportedClaims,
            claims,
        ));
    }
    let side = match claims.patch() {
        None => side,
        Some(withdrawing) => match validator.validate(withdrawing) {
            Ok(side) => side,
            Err(_) => {
                return Err(MutantRefusal::new(
                    MutantScopeFailure::StrippedClaimCompileFailure,
                    claims,
                ));
            }
        },
    };
    validate_representation(&side).map_err(|_| {
        MutantRefusal::new(MutantScopeFailure::RepresentationRefused, claims.clone())
    })?;
    on_stage(MutantStage::Backend);
    let infrastructure = |claims: &Withdrawal| {
        MutantRefusal::new(MutantScopeFailure::Infrastructure, claims.clone())
    };
    let loaded = LoadedSide::load(&side, &admission.module).map_err(|_| infrastructure(&claims))?;
    let baseline_data = admission
        .data
        .as_ref()
        .map_err(|_| infrastructure(&claims))?;
    let data = DataFacts::of(&loaded.selected, &admission.assume_joined);
    on_stage(MutantStage::Consistency);
    let admitted = match &admission.equations {
        Ok(equations) => kink_native::consistency::admit_mutant_with(
            equations,
            &side,
            &effect,
            &loaded.selected,
            &data,
        ),
        Err(why) => Err(MutantFailure::Inconsistent(
            kink_native::consistency::Inconsistency::Unchecked(format!(
                "the baseline's equations did not internalize: {why}"
            )),
        )),
    };
    let effect = match admitted {
        Ok(effect) => effect,
        Err(MutantFailure::UnreadEquations(unread)) => {
            // The patch's effect on the claims is not known: no claim-free definition is known
            // either, so the mutant is refused as unsupported, naming each unread equation.
            let fallback = effect
                .touched
                .iter()
                .next()
                .map_or(SentenceOrigin::Inserted { edit: 0 }, |at| {
                    SentenceOrigin::Baseline(at.clone())
                });
            claims
                .unsupported
                .extend(unread.into_iter().map(|equation| Claim {
                origin: equation.origin.unwrap_or_else(|| fallback.clone()),
                key: UNREAD_EQUATION_CLAIM.to_owned(),
                value: serde_json::json!({"head": equation.head, "equation": equation.equation}),
            }));
            return Err(MutantRefusal::new(
                MutantScopeFailure::UnsupportedClaims,
                claims,
            ));
        }
        Err(MutantFailure::Uninternalizable(_)) => {
            return Err(MutantRefusal::new(
                MutantScopeFailure::Infrastructure,
                claims,
            ));
        }
        Err(MutantFailure::Inconsistent(inconsistency)) => {
            return Err(Box::new(MutantRefusal {
                failure: MutantScopeFailure::InconsistentMutant,
                claims,
                inconsistent_pairs: inconsistency.pairs(),
            }));
        }
    };
    if data.differs_outside(baseline_data, effect.checked.as_ref()) {
        return Err(MutantRefusal::new(
            MutantScopeFailure::MutantFindings,
            claims,
        ));
    }
    Ok(ClaimFreeMutant {
        side,
        claims,
        data,
        loaded,
    })
}

/// What every mutant of a campaign is admitted against: the baseline's claim support and its
/// compiled equations (re-pin R0c-fix-4), the module the mutants load, the names of the findings
/// read as assumed, and the baseline's data facts under them (fz26 KINK-BASELINE-FINDINGS).
pub struct MutantAdmission {
    support: ClaimSupport,
    equations: Result<CompiledEquations, String>,
    /// The backend's module of every mutant load (the campaign's).
    module: String,
    assume_joined: Vec<String>,
    data: Result<DataFacts, String>,
}

impl MutantAdmission {
    /// The admission of every mutant of `baseline` (a validator's baseline), whose compile is
    /// `compiled`, each loaded for `module` (KORE-encoded, the campaign's), reading the findings
    /// `assume_joined` names as assumed: its claim support, its compiled equations, which every
    /// mutant's are read against, and its data facts, which every mutant's are compared with
    /// (computed here on `compiled` loaded on kink's route). A baseline whose equations do not
    /// internalize again leaves every mutant unchecked (`InconsistentMutant`); one that does not
    /// load leaves every mutant `Infrastructure`.
    #[must_use]
    pub fn new(
        baseline: &kink_patch::Baseline,
        compiled: &ValidatedDefinition,
        module: &str,
        assume_joined: &[String],
    ) -> Self {
        let data = LoadedSide::load(compiled, module)
            .map(|loaded| DataFacts::of(&loaded.selected, assume_joined))
            .map_err(|_| format!("the baseline does not load for {module}"));
        Self {
            support: ClaimSupport::new(baseline),
            equations: CompiledEquations::of(compiled),
            module: module.to_owned(),
            assume_joined: assume_joined.to_vec(),
            data,
        }
    }

    /// The baseline's data facts, unless the baseline did not load.
    #[must_use]
    pub fn baseline_data(&self) -> Option<&DataFacts> {
        self.data.as_ref().ok()
    }

    /// The baseline's claim support.
    #[must_use]
    pub const fn support(&self) -> &ClaimSupport {
        &self.support
    }
}

/// Why a mutant runs no test: its mutant-scope failure, the claims its patch leaves unbacked (as
/// far as the preparation got), and the pairs of equations that refuse an inconsistent mutant.
#[derive(Debug)]
pub struct MutantRefusal {
    pub failure: MutantScopeFailure,
    pub claims: Withdrawal,
    pub inconsistent_pairs: Vec<UnjoinedEquations>,
}

impl MutantRefusal {
    fn new(failure: MutantScopeFailure, claims: Withdrawal) -> Box<Self> {
        Box::new(Self {
            failure,
            claims,
            inconsistent_pairs: Vec::new(),
        })
    }
}

/// A prepared mutant: the claim-free definition every test runs on, and its compiled edit.
struct MutantSides {
    runtime: Runtime,
    edit: CompiledEdit,
}

impl MutantSides {
    fn evidence_key(&self) -> EvidenceKey {
        self.runtime.digest
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
        let (test, baseline) = (pair.test, pair.baseline);
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
                    work: None,
                    one_sided: cached.one_sided.clone(),
                },
            ),
            None => sides
                .runtime
                .run_bounded(campaign, test, pair.mutant_max_work),
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
                    .runtime
                    .facts()
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
            // The baseline backend decides what both sides share (definition independence,
            // terminal values, the event walk); the mutant's own backend decides every
            // feasibility and relation query about the mutant's leaves (re-pin finding A-12).
            // Repeat the queries on hits too, so both backends' solver state evolves as in a
            // fresh call.
            let mutant_patterns = observations.runtime.step_sides(
                campaign,
                test,
                &observations.observation,
                cache.stepped.as_ref(),
                Some(&mut sides.runtime),
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
                    one_sided: cache.one_sided.clone(),
                },
            );
        }
        let run = match (&paired_baseline.run, &mutant.run) {
            // Admission keeps a baseline run that contradicts a claim: the test is unknown.
            (SideRun::Failed(ExecutionFailureKind::ContradictedClaim), _) => {
                TestRun::Failed(ExecutionFailureKind::ContradictedClaim)
            }
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
                            match slot_outcome(declaration, baseline, mutant) {
                                // Re-pin L1-2 (decision 6): a work-bound mutant run's clean ground
                                // stuck leaf outside the baseline's complete set.
                                OracleOutcome::Unknown
                                    if one_sided_distinguishes(
                                        declaration,
                                        baseline,
                                        mutant,
                                        &cache.one_sided,
                                    ) =>
                                {
                                    OracleOutcome::Distinguish
                                }
                                outcome => outcome,
                            }
                        }
                    })
                    .collect(),
            ),
            // Admission refused every other failed baseline run.
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

/// The classifier-independent part of one run ([`Runtime::execute`]): the adapter's execution,
/// the side a pattern slot gets when stepping failed, and the run cache.
struct Executed {
    execution: Result<AdaptedExecution, ExecutionAdapterFailure>,
    pattern_failure: OracleSide,
    cache: RunCache,
}

/// Stepped evidence retained from the primary run, its rule coverage when the side records
/// it, and the session's recording of the run (wall time and leaf census; recording only).
#[derive(Clone, Default)]
struct RunCache {
    stepped: Option<SteppedExecution>,
    coverage: Option<TestCoverage>,
    recording: Option<RunRecording>,
    /// The states the run visited (k-rust `work`) when it returned a result in time; on the
    /// baseline it calibrates the mutants' work budget of the test ([`WorkBudget`]).
    work: Option<u64>,
    /// The one-sided evidence of a mutant run (re-pin L1-2, [`OneSided`]): the clean, ground,
    /// stuck terminals of a work-bound run judged into sides, of a ground test, read with the
    /// campaign's classifier and the mutant's own definition
    /// ([`kink_native::bridge::work_bound_stuck_terminals`]). Empty for every other run, and for
    /// every run of a side whose option is off (a baseline's always). Classifier-dependent, unlike
    /// the rest of the cache: a baseline session never reads it.
    one_sided: Vec<ExecutionTerminal>,
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
    /// The modality of the side's result runs ([`RunOptions::result_modality`]).
    modality: ResultModality,
    /// Whether the side's runs collect one-sided evidence ([`RunOptions::one_sided`]; a mutant's
    /// only).
    one_sided: OneSided,
    /// What the side's definition contributes to the exclusions of each of its runs, read from
    /// its compiled KORE and from the definition its backend selected for the default module
    /// (the only module a request names), on the thread that runs it (re-pin R0b).
    exclusions: DefinitionExclusions,
}

/// One load of a compiled side on kink's route: its parsed KORE, the backend built from it for a
/// module, and the definition that backend selected for it (loaded, its load counts and value
/// claims final; findings A-08, C-10).
struct LoadedSide {
    parsed: k_rust::kore::ast::Definition,
    backend: Backend,
    selected: std::sync::Arc<k_rust::k_rust_backend::definition::BackendDefinition>,
}

impl LoadedSide {
    fn load(side: &ValidatedDefinition, module: &str) -> Result<Self, Preparation> {
        let parsed = parse_definition(&side.artifacts().definition_kore)
            .map_err(|_| Preparation::Infrastructure)?;
        let mut backend =
            Backend::from_definition(parsed.clone(), module, BackendOptions::default())
                .map_err(|_| Preparation::Infrastructure)?;
        // Selecting the default module loads it if the backend has not yet.
        let selected = backend
            .select_definition(None)
            .map_err(|_| Preparation::Infrastructure)?;
        Ok(Self {
            parsed,
            backend,
            selected,
        })
    }
}

impl Runtime {
    /// Parses the side's KORE once for its symbol sorts and event-free backend adapter.
    fn prepare(campaign: &Campaign<'_>, side: &ValidatedDefinition) -> Result<Self, Preparation> {
        stage_log::note(campaign, stage_log::Stage::Backend);
        let loaded = LoadedSide::load(side, campaign.module)?;
        Self::from_loaded(campaign, side, loaded)
    }

    /// The runtime of `side` on its load `loaded` ([`LoadedSide::load`] for the campaign's
    /// module).
    fn from_loaded(
        campaign: &Campaign<'_>,
        side: &ValidatedDefinition,
        loaded: LoadedSide,
    ) -> Result<Self, Preparation> {
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
        let LoadedSide {
            parsed,
            backend,
            selected,
        } = loaded;
        let symbol_sorts = SymbolSorts::from_definition(&parsed);
        let exclusions = DefinitionExclusions::of(
            &parsed,
            &selected,
            &side.compile_options().builtin_source_prefixes,
        );
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
            modality: ResultModality::default(),
            one_sided: OneSided::Off,
            exclusions,
        })
    }

    fn facts(&mut self) -> Result<DefinitionFacts, String> {
        if self.facts.is_none() {
            self.facts = Some(
                definition_facts(&mut self.backend).map_err(|error| error.message().to_owned()),
            );
        }
        self.facts.clone().expect("filled above")
    }

    fn run(&mut self, campaign: &Campaign<'_>, test: &TestCase) -> (TestEvidence, RunCache) {
        self.run_bounded(campaign, test, None)
    }

    /// [`Runtime::run`] with a work budget for a result run (`max_work`; a mutant's,
    /// [`WorkBudget`]).
    fn run_bounded(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        max_work: Option<u64>,
    ) -> (TestEvidence, RunCache) {
        let (evidence, executed) = self.run_keeping(campaign, test, max_work);
        (evidence, executed.cache)
    }

    /// [`Runtime::run_bounded`], also returning the classifier-independent part of the run (the
    /// execution and its run cache), which a [`BaselineSession`] stores.
    fn run_keeping(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        max_work: Option<u64>,
    ) -> (TestEvidence, Executed) {
        let started = Instant::now();
        let mut executed = self.execute(campaign, test, max_work);
        let (evidence, one_sided) = self.judge_with(campaign, test, &executed, None);
        executed.cache.one_sided = one_sided;
        // Recording only (flow F-13): read from the execution the run already has.
        executed.cache.recording = Some(RunRecording {
            test_id: test.id.clone(),
            wall: started.elapsed(),
            census: LeafCensus::of(executed.execution.as_ref()),
        });
        (evidence, executed)
    }

    /// The execution of one test and what is read from it alone: the stepped evidence when a
    /// pattern oracle needs it, the rule coverage and the work count. Nothing here reads the
    /// campaign's classifier or its oracle declarations other than whether one is a pattern
    /// oracle.
    ///
    /// The request is a function of the test (re-pin L1-1): a test with a pattern oracle runs as
    /// a stepped path set, and when stepping fails its run is a path-set result run, so both
    /// sides of such a test are path sets; any other test runs as a result run in this side's
    /// modality, which is the campaign's. The leaves need not be in that modality: a state set
    /// with an undefined step, a vacuous leaf or a contradicted claim is replaced by its path set
    /// on this side alone ([`RunOptions::result_modality`]). `max_work` bounds result runs only,
    /// never a stepped run ([`WorkBudget`]).
    fn execute(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        max_work: Option<u64>,
    ) -> Executed {
        stage_log::note(campaign, stage_log::Stage::Execute);
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
                    self.adapter.execute_result(
                        &mut self.backend,
                        &test.initial_state,
                        campaign.budget,
                        ResultRun {
                            modality: ResultModality::PathSet,
                            max_work,
                        },
                    )
                }
                Err(failure) => Err(failure),
            }
        } else {
            self.adapter.execute_result(
                &mut self.backend,
                &test.initial_state,
                campaign.budget,
                ResultRun {
                    modality: self.modality,
                    max_work,
                },
            )
        };
        cache.coverage = self.coverage.as_ref().map(|authors| match &execution {
            Ok(execution) => TestCoverage::of_execution(&test.id, execution, authors),
            Err(_) => TestCoverage::failed(&test.id),
        });
        cache.work = execution
            .as_ref()
            .ok()
            .filter(|execution| !execution.timed_out())
            .map(AdaptedExecution::work);
        Executed {
            execution,
            pattern_failure,
            cache,
        }
    }

    /// The evidence of one executed test: its execution bridged with the campaign's classifier
    /// and decided with this side's definition and solver, one side per oracle declaration.
    #[cfg(test)]
    fn judge(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        executed: &Executed,
    ) -> TestEvidence {
        self.judge_on(campaign, test, executed, None)
    }

    /// [`Runtime::judge`] of an execution that ran on another load of this side's definition,
    /// whose exclusion facts are `producing` (a run a [`BaselineSession`] stored in an earlier
    /// call; `None` for this runtime's own run). Everything the judgement reads from a load is
    /// read under both loads' facts at once ([`DefinitionExclusions::combined`]): the load stack
    /// stops, the implementation-chosen census, the role-rooted axioms (collection terminals)
    /// and the `preserves-definedness` ids. The decider's definition is this runtime's: a
    /// session stores only runs of loads without a definition-level exclusion, and a load
    /// without stack stops is a function of the compiled definition (finding A-08), so the two
    /// loads give the same definition whenever neither is excluded, and the combined facts
    /// exclude the run otherwise.
    fn judge_on(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        executed: &Executed,
        producing: Option<&DefinitionExclusions>,
    ) -> TestEvidence {
        self.judge_with(campaign, test, executed, producing).0
    }

    /// [`Runtime::judge_on`], and the run's one-sided evidence ([`RunCache::one_sided`]): read
    /// only when this side's option is on, the test is ground, and the run is judged into sides
    /// (no failure, no timeout, no exclusion), with the same classifier and decider as its sides.
    fn judge_with(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        executed: &Executed,
        producing: Option<&DefinitionExclusions>,
    ) -> (TestEvidence, Vec<ExecutionTerminal>) {
        let one_sided =
            self.one_sided != OneSided::Off && test.initial_state.free_variables().is_empty();
        let mut terminals = Vec::new();
        let combined;
        let exclusions = match producing {
            Some(producing) => {
                combined = self.exclusions.combined(producing);
                &combined
            }
            None => &self.exclusions,
        };
        let collections_trusted = exclusions.collections_trusted();
        let notes = match &executed.execution {
            Ok(execution) if !execution.timed_out() => RunNotes {
                contradicted_claims: execution.facts().contradicted_claims.clone(),
                smt_unknowns: execution.facts().smt_unknowns,
                leaf_contradiction: exclusions.contradiction_on_a_leaf(execution),
            },
            _ => RunNotes::default(),
        };
        let run = match &executed.execution {
            Err(failure) => SideRun::Failed(failure.into()),
            Ok(execution) if execution.timed_out() => {
                SideRun::Failed(ExecutionFailureKind::TimeLimit)
            }
            Ok(execution) => match self.backend.with_solver(None, |definition, solver| {
                let decider = ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&test.initial_state),
                )
                .trusting_collections(collections_trusted);
                let context = BridgeContext {
                    test_id: &test.id,
                    classify: campaign.classify,
                    sorts: &self.context.symbol_sorts,
                };
                let value = |term: &Pattern| decider.terminal_value(term);
                let bridged = paths_from_execution_values(execution, &context, &value);
                let state_exclusion = exclusions.state_exclusion(definition, &test.initial_state);
                // Re-pin L1-2: kept below only when the run is judged into sides.
                let one_sided = if one_sided {
                    work_bound_stuck_terminals(execution, &context, &value)
                } else {
                    Vec::new()
                };
                Ok::<_, k_rust::backend::BackendError>((bridged, state_exclusion, one_sided))
            }) {
                // No decider: every slot is unknown, unless the run is excluded, which is read
                // from its leaves and from the test's initial state on the selected definition
                // (re-pin R0c-fix-2, R0c-fix-1 review minor), or no definition can be selected to
                // read the state on, which gives no side either. An excluded run gives no side, so
                // no slot, a pattern slot `run_tests` fills from the stepped run included, can
                // take one from it.
                Err(_) => match exclusions.run_exclusion(execution) {
                    Some(exclusion) => SideRun::Failed(exclusion.into()),
                    None => match self.backend.select_definition(None) {
                        Err(_) => SideRun::Failed(ExecutionFailureKind::Infrastructure),
                        Ok(definition) => {
                            match exclusions.state_exclusion(&definition, &test.initial_state) {
                                Some(exclusion) => SideRun::Failed(exclusion.into()),
                                None => SideRun::Sides {
                                    sides: vec![OracleSide::Unknown; test.oracles.len()],
                                },
                            }
                        }
                    },
                },
                Ok((Err(failure), ..)) => SideRun::Failed((&failure).into()),
                // A run that bridged is checked for its exclusions before any side is formed
                // (re-pin R0b): an excluded run gives no side to any slot, on the baseline as on
                // a mutant, live or reused from a baseline session.
                Ok((Ok(bridged), state_exclusion, one_sided)) => {
                    match exclusions.run_exclusion(execution).or(state_exclusion) {
                        Some(exclusion) => SideRun::Failed(exclusion.into()),
                        None => {
                            terminals = one_sided;
                            SideRun::Sides {
                                sides: test
                                    .oracles
                                    .iter()
                                    .map(|declaration| match declaration.projection() {
                                        Projection::State(projection) => {
                                            state_side(projection, &bridged)
                                        }
                                        Projection::Pattern { .. } => {
                                            executed.pattern_failure.clone()
                                        }
                                    })
                                    .collect(),
                            }
                        }
                    }
                }
            },
        };
        (
            TestEvidence {
                test_id: test.id.clone(),
                run,
                notes,
            },
            terminals,
        )
    }

    /// The pattern-slot sides of one side's stepped run. This (the baseline's) definition and
    /// evaluation context decide what both sides share: definition independence, terminal
    /// values and the event walk. The definition that produced the leaves decides every
    /// feasibility and relation query about them (re-pin finding A-12): this runtime's own for
    /// its own run (`leaves` `None`), the mutant's `leaves` runtime for a mutant run.
    fn step_sides(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        observation: &StepObservation,
        execution: Option<&SteppedExecution>,
        leaves: Option<&mut Runtime>,
    ) -> Vec<OracleSide> {
        let mut context = self.context.clone();
        context.test_id.clone_from(&test.id);
        let trusted = self.exclusions.collections_trusted()
            && leaves
                .as_ref()
                .is_none_or(|leaves| leaves.exclusions.collections_trusted());
        let evaluate = |decider: &ObservationDecider<'_>| {
            let bridged = execution.and_then(|execution| {
                tree_from_steps(
                    &BridgeContext {
                        test_id: &test.id,
                        classify: campaign.classify,
                        sorts: &context.symbol_sorts,
                    },
                    execution,
                    observation,
                    decider,
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
                        decider.relations(),
                    );
                    if *with_bindings
                        && evaluation.as_ref().is_ok_and(|evaluation| {
                            evaluation.witnesses.iter().any(|witness| {
                                witness
                                    .bindings
                                    .iter()
                                    .any(|binding| !decider.definition_independent(&binding.term))
                            })
                        })
                    {
                        OracleSide::Unknown
                    } else {
                        pattern_side(&evaluation, *with_bindings)
                    }
                })
                .collect::<Vec<_>>()
        };
        let initial = || TestInitialState::of_test(&test.initial_state);
        let sides = match leaves {
            None => self.backend.with_solver(None, |definition, solver| {
                let decider = ObservationDecider::new(definition, solver, initial())
                    .trusting_collections(trusted);
                Ok::<_, k_rust::backend::BackendError>(evaluate(&decider))
            }),
            Some(leaves) => self.backend.with_solver(None, |definition, _| {
                leaves
                    .backend
                    .with_solver(None, |leaf_definition, leaf_solver| {
                        let decider = ObservationDecider::for_leaves_of(
                            definition,
                            leaf_definition,
                            leaf_solver,
                            initial(),
                        )
                        .trusting_collections(trusted);
                        Ok::<_, k_rust::backend::BackendError>(evaluate(&decider))
                    })
            }),
        };
        sides.unwrap_or_else(|_| vec![OracleSide::Unknown; test.oracles.len()])
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

/// Whether a state slot that compared `Unknown` distinguishes one-sidedly (re-pin L1-2,
/// [`OneSided`]): the baseline side is a value, the mutant side is `Unknown`, the slot projects
/// the whole term or the exit stop without an exit-code cell, and the projection of one of the
/// mutant run's one-sided `terminals` ([`RunCache::one_sided`], empty unless the run qualifies) is
/// not in the baseline's projected set. The projection is the slot's own ([`project`]) applied
/// to that one terminal, and a projected set is the set of its terminals' projections, so the
/// mutant's projected set, which holds it in every completion of the run, differs from the
/// baseline's.
fn one_sided_distinguishes(
    declaration: &OracleDeclaration,
    baseline: &OracleSide,
    mutant: &OracleSide,
    terminals: &[ExecutionTerminal],
) -> bool {
    let (Projection::State(projection), OracleSide::Normal(baseline), OracleSide::Unknown) =
        (declaration.projection(), baseline, mutant)
    else {
        return false;
    };
    if !matches!(
        projection,
        StateProjection::WholeTerm
            | StateProjection::ExitStop {
                exit_code_cell: None
            }
    ) {
        return false;
    }
    terminals.iter().any(
        |terminal| match (project(projection, &[terminal]), baseline) {
            (Some(OracleValue::ExitStop(leaf)), OracleValue::ExitStop(set)) => !leaf.is_subset(set),
            (
                Some(OracleValue::FinalResult(FinalResult::WholeTerm(leaf))),
                OracleValue::FinalResult(FinalResult::WholeTerm(set)),
            ) => !leaf.is_subset(set),
            _ => false,
        },
    )
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

    /// Re-pin R0b deliverables 1, 2, 7 and 9: `judge` gives an excluded run no side for any
    /// slot (`SideRun::Failed` with the exclusion), on a live run and on a run a baseline session
    /// reuses alike, before any evidence leaves the runner: a run that counted a stack stop, a
    /// run whose leaf reports an allowance refusal, and every run on a side whose load counted a
    /// stack stop or whose definition references an implementation-chosen hook. The same
    /// execution without the exclusion is judged a value. An excluded baseline run is admitted as
    /// `OracleFailed`, never as evidence.
    ///
    /// Re-pin adoption A-1: so is a run whose leaves are clean but one of k-rust's run-level lists
    /// holds an entry (a contradicted-claim record, an open value read, an allowance refusal, an
    /// unsupported hook), live and reused alike; a record on the list alone refuses the baseline
    /// (`leaf_contradiction` false), and the record is carried as a note. A nonzero count of
    /// undecided solver answers excludes nothing (decision D-7 (a1)) and is carried as a note.
    #[test]
    fn an_excluded_run_gives_no_side_live_or_reused() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                use k_rust::backend::BackendDiagnosticOutput;
                use kink_native::exclusion::HookReference;
                use kink_native::feasibility::LeafFeasibility;
                let validator = NativeValidator::bind(
                    input_test_support::load_path(
                        &std::path::Path::new(input_test_support::DIR).join("counter.k"),
                        "COUNTER",
                    ),
                    k_rust::kompile::CompileOptions::default(),
                );
                let compiled = validator.compile_baseline().unwrap();
                let classify: &dyn Fn(&Pattern) -> ExecutionTerminalKind =
                    &|_| ExecutionTerminalKind::Normal;
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
                let campaign = Campaign {
                    validator: &validator,
                    module: "COUNTER",
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
                let test = &tests[0];
                let mut runtime = Runtime::prepare(&campaign, &compiled)
                    .unwrap_or_else(|_| panic!("baseline runtime"));
                assert_eq!(runtime.exclusions.definition_exclusion(), None);
                let clean = runtime.execute(&campaign, test, None);
                assert!(matches!(
                    runtime.judge(&campaign, test, &clean).run,
                    SideRun::Sides { ref sides } if matches!(sides.as_slice(), [OracleSide::Normal(_)])
                ));
                // The clean run's result as k-rust returns it, then with a counted stack stop or
                // with an allowance refusal on its leaf.
                let Ok(clean_execution) = &clean.execution else {
                    panic!("the counter runs")
                };
                let raw = || k_rust::backend::ExecutionResult {
                    modality: k_rust::backend::ResultModalityOutput::PathSet,
                    leaves: clean_execution
                        .leaves()
                        .iter()
                        .map(|leaf| {
                            assert_eq!(leaf.halt, HaltClass::Stuck);
                            k_rust::backend::ExecutionLeaf {
                                state: leaf.branch.state.clone(),
                                diagnostics: Vec::new(),
                                candidates: None,
                                remainder: None,
                                depth: leaf.branch.depth,
                                reason: k_rust::backend::HaltReasonOutput::Stuck,
                                rule_id: None,
                                rule_label: None,
                                contradicted_total: None,
                                cause: None,
                                detail: None,
                                trace: leaf.branch.trace.clone(),
                                branch: leaf.branch.identity.clone(),
                                effects: Vec::new(),
                                observations: Vec::new(),
                            }
                        })
                        .collect(),
                    effects: Vec::new(),
                    discarded: Vec::new(),
                    coverage: None,
                    work: 0,
                    expanded: 0,
                    stack_stops: 0,
                    smt_unknowns: 0,
                    implementation_chosen_values: Vec::new(),
                    contradicted_claims: Vec::new(),
                    allowance_refusals: Vec::new(),
                    unsupported_hooks: Vec::new(),
                };
                let executed = |result: k_rust::backend::ExecutionResult| {
                    let feasibility = vec![LeafFeasibility::Syntactic; result.leaves.len()];
                    Executed {
                        execution: Ok(ExecutionAdapter::adapt_result(
                            result,
                            false,
                            &campaign.budget,
                            feasibility,
                        )
                        .unwrap()),
                        pattern_failure: OracleSide::Unknown,
                        cache: RunCache::default(),
                    }
                };
                let mut stopped = raw();
                stopped.stack_stops = 1;
                let mut refused = raw();
                refused.leaves[0]
                    .diagnostics
                    .push(BackendDiagnosticOutput::UnsupportedHookUnevaluated {
                        hook: "BYTES.padRight".into(),
                        reason: "the result exceeds the allowance".into(),
                    });
                assert!(matches!(
                    runtime.judge(&campaign, test, &executed(raw())).run,
                    SideRun::Sides { .. }
                ));
                // Re-pin adoption A-1: each run-level list, with every leaf clean.
                let record = k_rust::backend::ContradictedClaimOutput {
                    claim: k_rust::backend::ContradictedClaimKind::Total,
                    symbol: Some("Lbltd".into()),
                    k_label: Some("td".into()),
                    rule_id: "tdeq".into(),
                    rule_label: Some("COUNTER.tdeq".into()),
                    origin: None,
                    application: serde_json::Value::Null,
                    undefined: serde_json::Value::Null,
                    rewrite_rule_id: None,
                    rewrite_rule_label: None,
                    rewrite_rule_origin: None,
                    ground: true,
                    observed_in: k_rust::backend::ObservedInOutput::Load,
                };
                let hook = |hook: &str| k_rust::backend::UnevaluatedHookOutput {
                    hook: hook.into(),
                    reason: "listed only".into(),
                    observed_in: k_rust::backend::ObservedInOutput::Run,
                };
                let mut recorded = raw();
                recorded.contradicted_claims.push(record.clone());
                let mut marked = raw();
                marked
                    .implementation_chosen_values
                    .push(k_rust::backend::ChosenValueOutput {
                        hook: "MAP.keys_list".into(),
                        class: "order".into(),
                    });
                let mut listed_refusal = raw();
                listed_refusal
                    .allowance_refusals
                    .push(hook("BYTES.padRight"));
                let mut unsupported = raw();
                unsupported
                    .unsupported_hooks
                    .push(hook("STRING.countAllOccurrences"));
                let mut undecided = raw();
                undecided.smt_unknowns = 3;
                let judged = runtime.judge(&campaign, test, &executed(undecided));
                assert!(matches!(judged.run, SideRun::Sides { .. }));
                assert_eq!(judged.notes.smt_unknowns, 3);
                assert_eq!(
                    admit(&tests, std::slice::from_ref(&judged)),
                    BaselineAdmission::Accepted
                );
                let judged = runtime.judge(&campaign, test, &executed(recorded.clone()));
                assert_eq!(judged.notes.contradicted_claims, std::slice::from_ref(&record));
                assert!(!judged.notes.leaf_contradiction);
                for (result, kind) in [
                    (stopped, ExecutionFailureKind::StackStop),
                    (refused, ExecutionFailureKind::AllowanceRefusal),
                    (recorded, ExecutionFailureKind::ContradictedClaim),
                    (marked, ExecutionFailureKind::ImplementationChosenValue),
                    (listed_refusal, ExecutionFailureKind::AllowanceRefusal),
                    (unsupported, ExecutionFailureKind::UnsupportedHook),
                ] {
                    let executed = executed(result);
                    assert_eq!(
                        runtime.judge(&campaign, test, &executed).run,
                        SideRun::Failed(kind)
                    );
                    // A stored baseline run is judged again on the call's runtime.
                    let mut session = BaselineSession::new(&validator);
                    session.runs.push(StoredBaseline {
                        key: BaselineKey {
                            test_id: test.id.clone(),
                            initial_state: test.initial_state.clone(),
                            oracles: test.oracles.clone(),
                            module: "COUNTER".into(),
                            budget: campaign.budget,
                            profile: SolverProfile::BUILD,
                            modality: ResultModality::default(),
                        },
                        run: StoredRun::Executed {
                            executed: Box::new(executed),
                            load: DefinitionExclusions::default(),
                        },
                    });
                    let (evidence, _) = session.baseline_run(&mut runtime, &campaign, test, true);
                    assert_eq!(session.reused_runs(), 1);
                    assert_eq!(evidence.run, SideRun::Failed(kind));
                    assert_eq!(
                        admit(&tests, std::slice::from_ref(&evidence)),
                        BaselineAdmission::OracleFailed
                    );
                    assert_eq!(
                        baseline_exclusion(std::slice::from_ref(&evidence))
                            .map(|(id, exclusion)| (id.to_owned(), exclusion)),
                        Some(("t".to_owned(), kind.exclusion().unwrap()))
                    );
                }
                // Definition-level exclusions apply to every run on the side, a clean one too.
                runtime.exclusions.load_stack_stops = 1;
                assert_eq!(
                    runtime.judge(&campaign, test, &clean).run,
                    SideRun::Failed(ExecutionFailureKind::LoadStackStop)
                );
                runtime.exclusions.load_stack_stops = 0;
                runtime.exclusions.implementation_chosen = vec![HookReference {
                    module: "COUNTER".into(),
                    sentence: "r".into(),
                    symbol: "Lblchoice".into(),
                    hook: "MAP.choice".into(),
                }];
                assert_eq!(
                    runtime.judge(&campaign, test, &clean).run,
                    SideRun::Failed(ExecutionFailureKind::ImplementationChosenHook)
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Re-pin L1-2-land (CACHE-ID review 2 minor 1): the run options' record names every option,
    /// the one-sided rule included, and tells each value apart.
    #[test]
    fn the_run_options_record_names_every_option() {
        assert_eq!(
            RunOptions::default().value(),
            json!({"result_modality": "state-set", "work": null, "one_sided": "off"})
        );
        let options = RunOptions {
            result_modality: ResultModality::PathSet,
            work: WorkBudget::Calibrated {
                factor: 4,
                floor: 10_000,
            },
            one_sided: OneSided::NoCrashClassifier,
        };
        assert_eq!(
            options.value(),
            json!({
                "result_modality": "path-set",
                "work": {"factor": 4, "floor": 10_000},
                "one_sided": "no-crash-classifier",
            })
        );
        for changed in [
            RunOptions {
                result_modality: ResultModality::StateSet,
                ..options
            },
            RunOptions {
                work: WorkBudget::Unbounded,
                ..options
            },
            RunOptions {
                one_sided: OneSided::Off,
                ..options
            },
        ] {
            assert_ne!(changed.value(), options.value(), "{changed:?}");
        }
    }

    /// Re-pin L1-2 (decision 6, finding A-15): a run's one-sided evidence is read only on a side
    /// whose option is on, of a ground test, from a run judged into sides: a counted stack stop
    /// makes the run no evidence at all, and a diagnostic on its stuck leaf, a symbolic test or
    /// the option off leaves it without one-sided evidence.
    #[test]
    fn one_sided_evidence_needs_the_option_a_ground_test_and_a_clean_unstopped_run() {
        with_one_test(
            "l1/onesided.k",
            "ONESIDED",
            input_test_support::app("Lblstart", vec![input_test_support::int(10)]),
            "SortProg",
            |_, compiled, campaign| {
                use k_rust::backend::{
                    BackendDiagnosticOutput, ExecutionLeaf, ExecutionResult, HaltReasonOutput,
                };
                let test = &campaign.tests[0];
                let mut runtime =
                    Runtime::prepare(campaign, compiled).unwrap_or_else(|_| panic!("the runtime"));
                runtime.one_sided = OneSided::NoCrashClassifier;
                // start(10), done(17), then three states of the loop: the fourth is work-bound.
                let max_work = Some(5);
                let bounded = runtime.execute(campaign, test, max_work);
                let unknown = SideRun::Sides {
                    sides: vec![OracleSide::Unknown],
                };
                let (evidence, terminals) = runtime.judge_with(campaign, test, &bounded, None);
                assert_eq!(evidence.run, unknown);
                let [terminal] = terminals.as_slice() else {
                    panic!("one terminal: {terminals:?}")
                };
                assert_eq!(terminal.kind, ExecutionTerminalKind::Normal);
                assert!(
                    terminal
                        .state
                        .to_string()
                        .contains(r#"Lbldone{}(\dv{SortInt{}}("17"))"#),
                    "{}",
                    terminal.state
                );
                runtime.one_sided = OneSided::Off;
                assert_eq!(
                    runtime.judge_with(campaign, test, &bounded, None),
                    (evidence.clone(), Vec::new())
                );
                runtime.one_sided = OneSided::NoCrashClassifier;

                // The run's result as k-rust returns it, then with a counted stack stop or with a
                // diagnostic on its stuck leaf.
                let Ok(execution) = &bounded.execution else {
                    panic!("the run returns")
                };
                let raw = || ExecutionResult {
                    modality: k_rust::backend::ResultModalityOutput::StateSet,
                    leaves: execution
                        .leaves()
                        .iter()
                        .map(|leaf| ExecutionLeaf {
                            state: leaf.branch.state.clone(),
                            diagnostics: Vec::new(),
                            candidates: None,
                            remainder: None,
                            depth: leaf.branch.depth,
                            reason: match leaf.halt {
                                HaltClass::Stuck => HaltReasonOutput::Stuck,
                                HaltClass::WorkBound => HaltReasonOutput::WorkBound,
                                halt => panic!("{halt:?}"),
                            },
                            rule_id: None,
                            rule_label: None,
                            contradicted_total: None,
                            cause: None,
                            detail: None,
                            trace: leaf.branch.trace.clone(),
                            branch: leaf.branch.identity.clone(),
                            effects: Vec::new(),
                            observations: Vec::new(),
                        })
                        .collect(),
                    effects: Vec::new(),
                    discarded: Vec::new(),
                    coverage: None,
                    work: execution.work(),
                    expanded: 0,
                    stack_stops: 0,
                    smt_unknowns: 0,
                    implementation_chosen_values: Vec::new(),
                    contradicted_claims: Vec::new(),
                    allowance_refusals: Vec::new(),
                    unsupported_hooks: Vec::new(),
                };
                let feasibility = execution
                    .leaves()
                    .iter()
                    .map(|leaf| leaf.feasibility)
                    .collect::<Vec<_>>();
                let executed = |result: ExecutionResult| Executed {
                    execution: Ok(ExecutionAdapter::adapt_bounded_result(
                        result,
                        false,
                        &campaign.budget,
                        max_work,
                        feasibility.clone(),
                    )
                    .unwrap()),
                    pattern_failure: OracleSide::Unknown,
                    cache: RunCache::default(),
                };
                assert_eq!(
                    runtime.judge_with(campaign, test, &executed(raw()), None),
                    (evidence, terminals.clone())
                );
                let mut stopped = raw();
                stopped.stack_stops = 1;
                assert_eq!(
                    runtime.judge_with(campaign, test, &executed(stopped), None),
                    (
                        TestEvidence {
                            test_id: "t".into(),
                            run: SideRun::Failed(ExecutionFailureKind::StackStop),
                            notes: RunNotes::default(),
                        },
                        Vec::new()
                    )
                );
                let mut diagnosed = raw();
                assert_eq!(diagnosed.leaves[0].reason, HaltReasonOutput::Stuck);
                diagnosed.leaves[0].diagnostics.push(
                    BackendDiagnosticOutput::UnsupportedHookUnevaluated {
                        hook: "TEST.hook".into(),
                        reason: "unavailable".into(),
                    },
                );
                let (evidence, terminals) =
                    runtime.judge_with(campaign, test, &executed(diagnosed), None);
                assert_eq!((evidence.run, terminals), (unknown.clone(), Vec::new()));

                // A symbolic test: start(N) for every Int N.
                let symbolic = TestCase {
                    id: "t".into(),
                    initial_state: input_test_support::initial_state(
                        input_test_support::app(
                            "Lblstart",
                            vec![input_test_support::var("N", "SortInt")],
                        ),
                        "SortProg",
                    ),
                    oracles: test.oracles.clone(),
                };
                let bounded = runtime.execute(campaign, &symbolic, max_work);
                let (_, terminals) = runtime.judge_with(campaign, &symbolic, &bounded, None);
                assert_eq!(terminals, Vec::new());
            },
        );
    }

    /// One state-oracle test `t` of `program` (sort `SortProg` unless `sort` says otherwise) on
    /// the fixture `file`, module `module`, run through `body` with its validator, compiled side
    /// and campaign.
    fn with_one_test(
        file: &'static str,
        module: &'static str,
        program: Pattern,
        sort: &'static str,
        body: impl FnOnce(&NativeValidator, &ValidatedDefinition, &Campaign<'_>) + Send + 'static,
    ) {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(move || {
                let validator = NativeValidator::bind(
                    input_test_support::load_path(
                        &std::path::Path::new(input_test_support::DIR).join(file),
                        module,
                    ),
                    k_rust::kompile::CompileOptions::default(),
                );
                let compiled = validator.compile_baseline().unwrap();
                let classify: &dyn Fn(&Pattern) -> ExecutionTerminalKind =
                    &|_| ExecutionTerminalKind::Normal;
                let tests = [TestCase {
                    id: "t".into(),
                    initial_state: input_test_support::initial_state(program, sort),
                    oracles: vec![
                        OracleDeclaration::new(
                            CrashPolicy::Reject,
                            Projection::State(StateProjection::WholeTerm),
                        )
                        .unwrap(),
                    ],
                }];
                let campaign = Campaign {
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
                body(&validator, &compiled, &campaign);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Re-pin R0c deliverable 4 (R0b review 1 minor; finding A-12): `run_tests` passes the
    /// mutant's own runtime to `step_sides`, so the mutant's leaves are admitted, and their
    /// feasibility and relations decided, on the mutant's definition. `r0c/a12partial.k` and
    /// `r0c/a12total.k` differ only in `mydiv`'s `total` (a hooked division, so definedness is
    /// `Y =/= 0` where it is partial). The symbolic test `seq(go(X), halt)` leaves on the total
    /// side `done(X) /\ mydiv(X, 0) = 1`. Admitted under the partial (baseline) definition, it
    /// gains `\ceil(mydiv(X, 0))`, which Z3 refutes: the leaf would be discarded and the `went`
    /// pattern side would be Unknown. Admitted under its own definition it is feasible, the step
    /// is witnessed, and the mutant's side is `Match`. Without a solver neither is decided. The
    /// baseline's own side is Unknown (its remainder's feasibility is not exactly decided), so
    /// the slot is Unknown either way: the wiring shows in the mutant's evidence.
    #[test]
    fn run_tests_decides_mutant_leaves_on_the_mutant_definition() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                use input_test_support as support;
                let dir = std::path::Path::new(support::DIR).join("r0c");
                let compile = |file: &str| {
                    NativeValidator::bind(
                        support::load_path(&dir.join(file), "A12"),
                        k_rust::kompile::CompileOptions::default(),
                    )
                };
                let base = compile("a12partial.k");
                let base_side = base.compile_baseline().unwrap();
                let total_side = compile("a12total.k").compile_baseline().unwrap();
                let specs = vec![StepEventSpec {
                    constructor: "went".into(),
                    pre: support::k_config(
                        support::app(
                            "Lblseq",
                            vec![
                                support::app("Lblgo", vec![support::var("A", "SortInt")]),
                                support::var("P", "SortProg"),
                            ],
                        ),
                        "SortProg",
                        "R",
                        "C",
                    ),
                    post: None,
                    payload: vec!["A".into()],
                }];
                let vocabulary = StepObservation::vocabulary_of(&specs).unwrap();
                let plan = kink_pattern::PatternPlan::new(
                    &vocabulary,
                    Vec::new(),
                    vec![kink_pattern::PatternArm {
                        atoms: vec![kink_pattern::Atom {
                            constructor: "went".into(),
                            payload: Vec::new(),
                        }],
                        relations: Vec::new(),
                    }],
                    None,
                )
                .unwrap();
                let tests = [TestCase {
                    id: "t".into(),
                    initial_state: support::initial_state(
                        support::app(
                            "Lblseq",
                            vec![
                                support::app("Lblgo", vec![support::var("X", "SortInt")]),
                                support::app("Lblhalt", vec![]),
                            ],
                        ),
                        "SortProg",
                    ),
                    oracles: vec![
                        OracleDeclaration::new(
                            CrashPolicy::CompareIdentity,
                            Projection::Pattern {
                                plan,
                                with_bindings: false,
                            },
                        )
                        .unwrap(),
                    ],
                }];
                let classify: &dyn Fn(&Pattern) -> ExecutionTerminalKind =
                    &|_| ExecutionTerminalKind::Normal;
                let campaign = Campaign {
                    validator: &base,
                    module: "A12",
                    observation: &specs,
                    classify,
                    tests: &tests,
                    budget: ExecutionBudget {
                        time: std::time::Duration::from_secs(30),
                        max_depth: None,
                        max_simplification_iterations: 1000,
                        max_breadth: None,
                    },
                };
                let test = &tests[0];
                let mut runtime =
                    Runtime::prepare(&campaign, &base_side).unwrap_or_else(|_| panic!());
                let observation =
                    StepObservation::new(&mut runtime.backend, specs.clone()).unwrap();
                // The baseline side, as `run_campaign_multi_with` forms it.
                let (mut baseline, cache) = runtime.run(&campaign, test);
                let patterns =
                    runtime.step_sides(&campaign, test, &observation, cache.stepped.as_ref(), None);
                replace_patterns(test, &mut baseline, Some(&patterns));
                let unknown = SideRun::Sides {
                    sides: vec![OracleSide::Unknown],
                };
                assert_eq!(baseline.run, unknown);
                let coverage = TestCoverage::failed("t");
                let paired = BTreeMap::from([(
                    "t",
                    PairedTest {
                        test,
                        baseline: &baseline,
                        coverage: &coverage,
                        mutant_max_work: None,
                    },
                )]);
                // The total definition as the mutant side.
                let mut sides = MutantSides {
                    runtime: Runtime::prepare(&campaign, &total_side).unwrap_or_else(|_| panic!()),
                    edit: CompiledEdit::between(&base_side, &total_side),
                };
                let mut observations = BaselineObservations {
                    runtime: &mut runtime,
                    observation,
                    evidence: None,
                };
                let (plans, evidence, _) = run_tests(
                    &campaign,
                    &mut sides,
                    &paired,
                    &["t".to_owned()],
                    ScheduleMode::Full,
                    &mut observations,
                );
                assert_eq!(
                    plans[0].run,
                    TestRun::Compared(vec![OracleOutcome::Unknown])
                );
                let decided = SideRun::Sides {
                    sides: vec![OracleSide::Normal(OracleValue::Pattern(
                        PatternValue::Match { bindings: None },
                    ))],
                };
                if SolverProfile::BUILD == SolverProfile::Z3 {
                    assert_eq!(evidence[0].run, decided);
                    // The same mutant run decided on the baseline's definition: its leaf is
                    // refuted and the side is Unknown.
                    let (_, mutant_cache) = sides.runtime.run(&campaign, test);
                    assert_eq!(
                        observations.runtime.step_sides(
                            &campaign,
                            test,
                            &observations.observation,
                            mutant_cache.stepped.as_ref(),
                            None,
                        ),
                        [OracleSide::Unknown]
                    );
                } else {
                    assert_eq!(evidence[0].run, unknown);
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
                notes: RunNotes::default(),
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

    /// fz26 KINK-BASELINE-FINDINGS (review R2-S2): a claim-free mutant whose findings outside the
    /// heads its edit can change differ from the baseline's is `MutantFindings`, checked rather
    /// than argued. The mutant is hand-built against a forged admission: `counter.k`'s edit of a
    /// rewrite rule's condition changes no equation (no head is checked), so every finding is
    /// outside, and the admission's baseline facts are r3-plainq's, whose genuine pair the
    /// mutant lacks. With the baseline's own facts the same mutant is admitted (the runner's own
    /// `BaselineFindings` gate is kink-flow's `tests/findings.rs`).
    #[test]
    fn a_mutant_whose_findings_differ_from_the_baselines_is_unknown() {
        use k_rust::kast::{Sort, Term};
        use kink_patch::{Edit, TermRef};
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let validator = NativeValidator::bind(
                    input_test_support::load("counter.k"),
                    k_rust::kompile::CompileOptions::default(),
                );
                let baseline = validator.baseline();
                let compiled = validator.compile_baseline().unwrap();
                let at = TermRef::new(input_test_support::rule(baseline, "COUNTER.branch"), [1]);
                let patch = Patch::new(vec![Edit::ReplaceTerm {
                    expected: baseline.term(&at).unwrap().clone(),
                    at,
                    replacement: Term::Token {
                        token: "false".into(),
                        sort: Sort::new("Bool"),
                    },
                }])
                .unwrap();
                let mut admission = MutantAdmission::new(baseline, &compiled, "COUNTER", &[]);
                assert!(admission.baseline_data().unwrap().has_data());
                let mutant =
                    claim_free_mutant(&validator, &compiled, &patch, &admission, &mut |_| {})
                        .expect("the baseline's own facts admit the mutant");
                assert!(mutant.data.has_data());

                let plainq = NativeValidator::bind(
                    input_test_support::load_path(
                        &std::path::Path::new(input_test_support::DIR)
                            .join("../flow/findings/r3-plainq/spec.k"),
                        "PQ",
                    ),
                    k_rust::kompile::CompileOptions::default(),
                );
                let forged = kink_native::consistency::loaded_definition(
                    &plainq.compile_baseline().unwrap(),
                )
                .unwrap();
                let facts = DataFacts::of(&forged, &[]);
                assert_eq!(data_ends(&facts), DataEnds::None);
                admission.data = Ok(facts);
                let refusal =
                    claim_free_mutant(&validator, &compiled, &patch, &admission, &mut |_| {})
                        .expect_err("the findings differ");
                assert_eq!(refusal.failure, MutantScopeFailure::MutantFindings);
                assert_eq!(refusal.failure.status(), MutantStatus::Unknown);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    mod kink_tier {
        use super::*;

        /// Equal patched KORE does not identify the mutant's claim-free side: an equation metadata
        /// edit still withdraws claims whose support it touched, while the transition-only twin does
        /// not, so the two run on different definitions (re-pin R0c-fix-2: every test runs on the
        /// claim-free mutant).
        #[test]
        #[ignore = "kink"]
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
                    let support = MutantAdmission::new(baseline, &compiled, "SYMPARTIAL", &[]);
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
                        let observation =
                            StepObservation::new(&mut runtime.backend, vec![]).unwrap();
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
                                        mutant_max_work: None,
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
                            prepare_mutant(&campaign, &a, &compiled, &support).unwrap();
                        let (mut sides_b, claims_b) =
                            prepare_mutant(&campaign, &b, &compiled, &support).unwrap();
                        assert!(claims_a.withdrawn.is_empty());
                        assert_eq!(claims_b.withdrawn.len(), 2);
                        assert!(claims_b.patch().is_some());
                        assert_ne!(sides_a.evidence_key(), sides_b.evidence_key());
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
                            "a different claim-free side must miss"
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
                            prepare_mutant(&campaign, &a, &compiled, &support).unwrap();
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

        /// Re-pin L1-3 deliverable 3: with compile workers, every consistency check, backend build
        /// and execution of a campaign runs on the calling thread, each candidate's after its turn
        /// begins and before the next one's, in candidate order, and the steps are the sequential
        /// run's, in the same order, with the same run. Two generations of the same pair of patches
        /// (structurally equal, so every candidate after the first is `same_as` an earlier one).
        #[test]
        #[ignore = "kink"]
        fn only_compiling_leaves_the_calling_thread_and_candidates_keep_their_order() {
            use k_rust::{
                definition::Sentence,
                kast::{Sort, Term},
            };
            use kink_patch::{Discovery, Edit, SiteSelector, TermRef, derive_sites, select};
            use stage_log::Stage;
            std::thread::Builder::new()
                .stack_size(16 * 1024 * 1024)
                .spawn(|| {
                    let validator = NativeValidator::bind(
                        input_test_support::load("counter.k"),
                        k_rust::kompile::CompileOptions::default(),
                    );
                    let baseline = validator.baseline();
                    let at = input_test_support::rule(baseline, "COUNTER.branch");
                    let term_at = TermRef::new(at.clone(), [1]);
                    let false_term = Term::Token {
                        token: "false".into(),
                        sort: Sort::new("Bool"),
                    };
                    let mut replacement = baseline.sentence(&at).unwrap().clone();
                    let Sentence::Rule { requires, .. } = &mut replacement else {
                        panic!("rule");
                    };
                    *requires = false_term.clone();
                    let mut discovery = Discovery::empty(baseline, false, false);
                    for path in [vec![0], vec![1]] {
                        discovery = discovery
                            .union(
                                &derive_sites(
                                    baseline,
                                    "site",
                                    &[
                                        SiteSelector::RuleLabel("COUNTER.branch".into()),
                                        SiteSelector::Path(path),
                                    ],
                                )
                                .unwrap(),
                            )
                            .unwrap();
                    }
                    let generation = || {
                        select(&discovery, kink_patch::SelectionPolicy::Each, 2)
                            .unwrap()
                            .fold("duplicates", |origin| {
                                Patch::new(vec![if origin.site_tuple[0].path.0 == [0] {
                                    Edit::ReplaceSentence {
                                        at: at.clone(),
                                        replacement: replacement.clone(),
                                    }
                                } else {
                                    Edit::ReplaceTerm {
                                        at: term_at.clone(),
                                        expected: baseline.term(&term_at).unwrap().clone(),
                                        replacement: false_term.clone(),
                                    }
                                }])
                                .unwrap()
                            })
                            .unwrap()
                    };
                    let generations = [generation(), generation()];
                    let z = |b: &str| Pattern::DomainValue {
                        sort: k_rust::kompile::initial_configuration::kore_sort("SortBool"),
                        value: b.into(),
                    };
                    let tests = ["true", "false"].map(|b| TestCase {
                        id: format!("choose-{b}"),
                        initial_state: input_test_support::initial_state(
                            input_test_support::app("Lblchoose", vec![z(b)]),
                            "SortControl",
                        ),
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
                        module: "COUNTER",
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
                    if validator.compile_workers(4) < 2 {
                        // Review L1-3-1 D3: one CPU, or a memory allowance too small for two.
                        eprintln!(
                            "skipped: this host allows one compile worker, so 4 would run the \
                             sequential path"
                        );
                        return;
                    }
                    let address = std::ptr::from_ref(&campaign).addr();
                    let thread = std::thread::current().id();
                    let steps = |workers| {
                        let start = stage_log::LOG.lock().unwrap().len();
                        let run = run_campaign_multi(
                            &campaign,
                            &generations,
                            &CampaignOptions {
                                schedule: ScheduleMode::Full,
                                selection: SelectionPolicy::None,
                                share_evidence: false,
                                run: RunOptions::default(),
                                compile_workers: workers,
                            },
                        )
                        .unwrap();
                        let log = stage_log::LOG.lock().unwrap()[start..]
                            .iter()
                            .filter(|(at, _, _)| *at == address)
                            .copied()
                            .collect::<Vec<_>>();
                        assert!(
                            log.iter().all(|(_, _, on)| *on == thread),
                            "{workers} workers: a step left the calling thread: {log:?}"
                        );
                        (
                            run,
                            log.into_iter()
                                .map(|(_, stage, _)| stage)
                                .collect::<Vec<_>>(),
                        )
                    };
                    let (sequential, sequential_steps) = steps(1);
                    let (ahead, ahead_steps) = steps(4);
                    assert_eq!(ahead, sequential);
                    assert_eq!(ahead_steps, sequential_steps);
                    assert_eq!(
                        ahead.mutants.iter().map(|m| m.same_as).collect::<Vec<_>>(),
                        [
                            None,
                            Some(MutantId(0)),
                            Some(MutantId(0)),
                            Some(MutantId(0))
                        ]
                    );
                    // The baseline's steps, then each candidate's turn in candidate order, each
                    // with its own backend build (whose loaded definition its full check reads,
                    // fz26 KINK-BASELINE-FINDINGS), consistency check and executions.
                    let turns = ahead_steps
                        .iter()
                        .enumerate()
                        .filter_map(|(at, stage)| match stage {
                            Stage::Mutant(index) => Some((at, *index)),
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(
                        turns.iter().map(|(_, index)| *index).collect::<Vec<_>>(),
                        [0, 1, 2, 3]
                    );
                    assert!(
                        ahead_steps[..turns[0].0].contains(&Stage::Backend)
                            && ahead_steps[..turns[0].0].contains(&Stage::Execute),
                        "the baseline is built and run first"
                    );
                    for (n, (at, _)) in turns.iter().enumerate() {
                        let end = turns
                            .get(n + 1)
                            .map_or(ahead_steps.len(), |(next, _)| *next);
                        let own = &ahead_steps[at + 1..end];
                        assert_eq!(
                            own,
                            [
                                Stage::Backend,
                                Stage::Consistency,
                                Stage::Execute,
                                Stage::Execute
                            ],
                            "candidate {n}"
                        );
                    }
                })
                .unwrap()
                .join()
                .unwrap();
        }

        /// The module is a key component of a stored baseline run (flow F-12): on the same baseline
        /// `Runtime`, a request under another module misses and runs live; the same request again is
        /// a hit. (No fixture has a second executable module, so the integration tests in
        /// tests/session.rs cannot vary it through a campaign.)
        #[test]
        #[ignore = "kink"]
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
                    let classify: &dyn Fn(&Pattern) -> ExecutionTerminalKind =
                        &|_| ExecutionTerminalKind::Normal;
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
                    let mut session = BaselineSession::new(&validator);
                    assert!(
                        BaselineSession::memoises(&counter) && BaselineSession::memoises(&other)
                    );
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

        /// Re-pin R0c deliverable 1 (R0b review 1 major 1, the reviewer's probe): every call prepares
        /// its own baseline `Runtime`, and so its own load. A baseline run whose load counted a stack
        /// stop is excluded in its call; a later call whose own load is clean must not admit it.
        /// Before R0c the session stored the run and judged it again on call 2's clean load alone,
        /// which admitted it (`SideRun::Sides`, `Accepted`). Now only its exclusion is stored, and
        /// call 2's request is answered with it.
        #[test]
        #[ignore = "kink"]
        fn a_reused_baseline_of_a_stopped_load_is_refused() {
            let z = || input_test_support::app("Lblz", vec![]);
            let program = input_test_support::app(
                "Lblcounter",
                vec![z(), input_test_support::app("Lbls", vec![z()])],
            );
            with_one_test(
                "counter.k",
                "COUNTER",
                program,
                "SortCounter",
                |validator, compiled, campaign| {
                    let test = &campaign.tests[0];
                    let mut session = BaselineSession::new(validator);
                    // Call 1: its load counted a stack stop.
                    let mut first =
                        Runtime::prepare(campaign, compiled).unwrap_or_else(|_| panic!());
                    first.exclusions.load_stack_stops = 1;
                    let (e1, _) = session.baseline_run(&mut first, campaign, test, true);
                    assert_eq!(e1.run, SideRun::Failed(ExecutionFailureKind::LoadStackStop));
                    // Call 2: a clean load; the request is answered from the session, with call 1's
                    // exclusion, and admission refuses it.
                    let mut second =
                        Runtime::prepare(campaign, compiled).unwrap_or_else(|_| panic!());
                    assert_eq!(second.exclusions.definition_exclusion(), None);
                    let (e2, _) = session.baseline_run(&mut second, campaign, test, true);
                    assert_eq!(
                        (
                            session.live_runs(),
                            session.reused_runs(),
                            session.stored_runs()
                        ),
                        (1, 1, 1)
                    );
                    assert_eq!(e2.run, SideRun::Failed(ExecutionFailureKind::LoadStackStop));
                    assert_eq!(
                        admit(campaign.tests, std::slice::from_ref(&e2)),
                        BaselineAdmission::OracleFailed
                    );
                    // The same request on a fresh session and call 2's clean load is evidence.
                    let (fresh, _) = BaselineSession::new(validator).baseline_run(
                        &mut second,
                        campaign,
                        test,
                        true,
                    );
                    assert!(
                        matches!(fresh.run, SideRun::Sides { .. }),
                        "{:?}",
                        fresh.run
                    );
                },
            );
        }

        /// Re-pin R0c deliverable 1: a stored baseline run is judged under the load facts of the
        /// load that produced it combined with the requesting call's. Call 1's load holds an axiom
        /// rooted at a collection role symbol (finding C-10, set here as the load would report it),
        /// so the run's List terminal `keys(ListItem(3))` has no value; call 2's load is clean, and
        /// the reused run still has none. The same execution judged on call 2's load alone is a value.
        #[test]
        #[ignore = "kink"]
        fn a_reused_baseline_is_judged_under_its_producing_load() {
            let program = input_test_support::app("Lblstart", vec![input_test_support::int(3)]);
            with_one_test(
                "r0b/keysfree.k",
                "KEYSFREE",
                program,
                "SortProg",
                |validator, compiled, campaign| {
                    let test = &campaign.tests[0];
                    let mut session = BaselineSession::new(validator);
                    let mut first =
                        Runtime::prepare(campaign, compiled).unwrap_or_else(|_| panic!());
                    first.exclusions.role_rooted_axioms = vec!["a role-rooted equation".into()];
                    let unknown = SideRun::Sides {
                        sides: vec![OracleSide::Unknown],
                    };
                    let (e1, _) = session.baseline_run(&mut first, campaign, test, true);
                    assert_eq!(e1.run, unknown);
                    let mut second =
                        Runtime::prepare(campaign, compiled).unwrap_or_else(|_| panic!());
                    assert!(second.exclusions.collections_trusted());
                    let (e2, _) = session.baseline_run(&mut second, campaign, test, true);
                    assert_eq!((session.live_runs(), session.reused_runs()), (1, 1));
                    assert_eq!(e2.run, unknown);
                    let StoredRun::Executed { executed, .. } = &session.runs[0].run else {
                        panic!("a clean-census load's run is stored")
                    };
                    assert!(matches!(
                        second.judge(campaign, test, executed).run,
                        SideRun::Sides { ref sides } if matches!(sides.as_slice(), [OracleSide::Normal(_)])
                    ));
                },
            );
        }
    }
}
