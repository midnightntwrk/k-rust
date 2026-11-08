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
//!   `tests/modality.rs` checks it on the corpus). That holds whatever the leaves (fz26
//!   KINK-PATHSET-FALLBACK): a state set's undefined steps and vacuous leaves are leaves of the
//!   path set, and its `contradictedClaims` list holds absorbed arrivals' records, which the
//!   exclusions read. A test with a pattern oracle runs as a stepped path set on both sides.
//!   A run the time bound cancelled is `Failed(TimeLimit)` (k-rust answers a cancellation with an
//!   error and publishes no leaf), a mutant's run its work budget stopped ([`WorkBudget`]), and a
//!   baseline's result run [`RunOptions::baseline_max_work`] stopped, end in a `work-bound` leaf,
//!   and every other incomplete run is `Unknown`, including a backend diagnostic. A baseline's
//!   `work-bound` side is `Unknown`, so admission refuses the campaign (`BaselineOracleFailed`). A
//!   work-bound mutant side is `Unknown` too, but its slot can still distinguish one-sidedly from a
//!   clean, ground, stuck leaf outside the baseline's complete set (re-pin L1-2, decision 6;
//!   [`OneSided`], off by default).
//! - A single crash terminal is a `SemanticCrash` side carrying its terminal term; a
//!   crash among several terminals is `Unknown`. This counts terminal leaves, not distinct
//!   configurations: a path set with two paths to one crash configuration is `Unknown`, and the
//!   state set of the same request, which merges them into one leaf, is a crash side (re-pin
//!   L1-1-fix-1; a kill through it rests on decision 3, `tests/state_set_routes.rs` route 1).
//! - A terminal term with a free variable is `Unknown`. A symbolic run's complete stuck leaf
//!   stands for all of its instances, so its term is not one value: comparing such terms
//!   structurally, or classifying them, is not a comparison of the values the programs compute.
//! - A whole-term slot, and a crash side, compares terminal configurations without the content
//!   of their `<generatedCounter>` cell (fz26 FZ-FRESH; [`StateProjection::WholeTerm`]): the
//!   counter is compilation's encoding of the values already minted, undeclared by the
//!   definition and constraining nothing at a terminal. Which of a rule's two or more `!`
//!   variables gets which counter offset the definition leaves open, so a run through a step that
//!   built a candidate of such a rule is no evidence: k-rust notes it on the run's
//!   `implementationChosenValues` list (class `fresh-association`), which excludes the run as any
//!   other entry there does (kink-native [`Exclusion::ImplementationChosenValue`]).
//!   A cell projection ([`StateProjection::Cells`]) compares the same erasure with the content of
//!   each uncompared cell replaced by `\top` of its sort, and so does its crash side.
//! - An undefined step (a feasible `Trivial` leaf, `PathStop::UndefinedStep`) is a complete
//!   terminal, but no end (kink27 R1-UNDEF; the reading is stated once in kink's `trust.md`, "What
//!   a kill trusts"). Every state slot projects the run's ends only ([`project`]), and the
//!   single-crash rule and the free-variable rule above read the ends only: a side whose every
//!   path takes an undefined step has the empty set in every state slot, a value, so a baseline
//!   end the mutant lacks distinguishes (a removed end), and an undefined path beside the same
//!   ends distinguishes nothing. Its pre-step term is not one of the run's ends
//!   ([`TestEvidence::ends`]), so it is not judged as data under the other side's definition
//!   either. A pattern slot still observes the step's prefix, whose configurations are reached
//!   ([`pattern_side`]). kink-native's bridge still completes the leaf on the terms of a stuck
//!   leaf, its term a terminal value (TV-01): no state slot reads that term, so the check costs
//!   completeness (a side `Unknown`) where the term is no value, never a kill.
//! - Every compared end is data under both definitions (fz26 KINK-OVERLOAD-VALUE; kink-native
//!   [`data_ends`]): a run's terminals are judged under its own definition and facts when the
//!   run is judged, and each side's terminals ([`TestEvidence::ends`]), pattern bindings and
//!   one-sided terminals are judged under the other side's before a pair's slots are compared
//!   ([`judge_across`]); an end that is not data there makes that side's slot `Unknown` for that
//!   pair only (a one-sided terminal is dropped). Each definition reads the ends with its own
//!   theory, and a mutant can change a symbol's role (an `anywhere` rule on a baseline
//!   constructor, an overload member that lowers a baseline normal form).
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
//! leaf Unsat decisions rely on k-rust's solver reading each atom with its operands' definedness
//! (T-UNSAT, pinned by TB-01 and kink-native `tests/trust_base.rs`); the TV-01 initial-state
//! admission guard is kept as a fail-closed narrowing. Undecided evidence stays Unknown.
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
//!
//! A campaign may stop its result runs at named rewrite rules ([`Stop`], [`RunOptions::stop`]):
//! for a definition that never terminates, the observer chooses the end. A stop of rules `R` and
//! count `N` defines the truncated system, in which a path ends at its `N`th stop event: a step
//! by a rule of `R` that is its state's one successor (before the step for a rule to stop
//! before, after it for a rule to stop after), or where the definition's own run ends. Its ends
//! are what every slot compares, so a kill is relative to the stop. k-rust stops a path at a
//! selected rule only where its step is the state's one successor, and lists the rules it went
//! on past where the step had another; kink-native excludes such a run (`passed-stop`), so every
//! verdict is a fact of the system in which any step of a rule of `R` is a stop event. The count
//! is k-rust's ([`Runtime::execute`]): a run to the `N`th stop event is one request, whose paths
//! count their stop events, take each before the `N`th as any other step and end at the `N`th,
//! so its stop leaves and its own ends are the truncated system's ends from the test's initial
//! state, and its state set merges a state only into one whose path passed as many stop events.
//! Each side resolves the stop's names on its own definition: a name must label a
//! rewrite rule there, or the baseline's campaign is refused and a mutant is not admitted
//! (`StopUnresolved`), never run without its stop, which would compare ends of two different
//! observations.
//!
//! A campaign may also declare observation channels ([`RunOptions::observe`],
//! [`crate::observation`]). Every result run then carries a probe within its one request: the
//! baseline's records its channels, and each mutant's compares its elements with that record as
//! they come and ends the request at the first difference. Each test gets one slot more, after its
//! end slots, which distinguishes at the first decided difference of the two runs' channels, never
//! past either side's open point. A baseline run that a deterministic bound cut and that is
//! otherwise complete is a prefix program: it has no end, so admission does not read its end
//! sides (a complete path of it that crashed still meets each slot's crash policy) and its end
//! slots agree within its horizon, and its channels decide the test. A baseline run whose log did
//! not only grow by appending refuses the campaign (`log-not-appended`). A name of
//! a point class must label a rewrite rule on each side, or the baseline's campaign is refused
//! and a mutant is not admitted (`PointUnresolved`); a mutant whose declarations of the read
//! cells' values differ from the baseline's is not admitted either (`ObservationIncompatible`).
//! A campaign without a declaration makes every request, judges every run and admits every mutant
//! as before observations existed.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::time::{Duration, Instant};

use k_rust::k_rust_backend::definition::BackendDefinition;

use k_rust::backend::{Backend, BackendOptions, counter_erased};
use k_rust::k_rust_backend::nesting::SegmentRefused;
use k_rust::kore::{
    ast::{Pattern, Sort},
    parser::parse_definition,
    walk,
};
use kink_native::bridge::{
    BridgeContext, BridgeFailure, BridgedPaths, OpenApplication, leaf_keys, open_applications,
    open_symbols, paths_from_execution_existing, tree_from_steps, validate_test_initial_state,
    work_bound_stuck_terminals,
};
use kink_native::consistency::{CompiledEquations, MutantFailure, UnjoinedEquations};
use kink_native::coverage::{RuleAuthors, TestCoverage};
use kink_native::data::{DataEnds, DataFacts, data_ends};
use kink_native::exclusion::{DefinitionExclusions, Exclusion};
use kink_native::execution::{
    AdaptedExecution, DefinitionTables, ExecutionAdapter, ExecutionAdapterFailure, ExecutionBudget,
    HaltClass, RequestProbe, ResultModality, ResultRun, SolverProfile, StepRunFailure,
    SteppedExecution, StopRules,
};

use crate::condition::{KoreSignature, StopWhen};
use crate::observation::{
    BaselineRecord, Comparison, Element, LeafFacts, Observation, ObservationProbe, Observe,
    Resolved, Trace,
};
use kink_native::feasibility::TestInitialState;
use kink_native::representation::validate_representation;
use kink_native::signature::{DefinitionFacts, definition_facts};
use kink_native::step_events::{NonValue, ObservationDecider, StepEventSpec, StepObservation};
use kink_native::{MutantRejection, NativeValidator, ValidatedDefinition};
use kink_patch::{
    Baseline, CandidateDisposition, CandidateGeneration, Claim, ClaimSupport, Patch,
    SentenceOrigin, SentenceRef, Sha256Digest, UNREAD_EQUATION_CLAIM, Withdrawal, apply,
    structure_sha256,
};
use kink_pattern::{
    CollectionEvidence, CollectionStop, Evaluation, EvaluationContext, EvaluationOptions,
    EventVocabulary, ExecutionTerminal, ExecutionTerminalKind, Feasibility, MonitorOptions,
    PathInput, PathStop, PathTree, PatternFailure, PatternOutcome, PatternPlan, RelationDecider,
    RelationDecision, SearchPolicy, SymbolSorts, TermRelation, TreeOptions,
    evaluate_tree_with_stats, evaluate_with,
};

use crate::campaign::check_manifest;
use crate::cells::CellProjection;
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
    ExitStop { exit_code_cell: Option<String> },
    /// Every terminal's whole configuration, with the content of its `<generatedCounter>` cell
    /// erased ([`counter_erased`]). The counter is compilation's record of the values a run has
    /// minted for `!` variables: the definition does not declare it, and at a terminal, where no
    /// further step mints a value, it constrains nothing. How many values a run minted shows only
    /// where the minted values went, in the declared cells, which stay. A slot that names the
    /// counter cell among its [`Self::TermPaths`] still reads it.
    WholeTerm,
    /// The subterms at these child-index paths (`kore::walk::children`). The paths must be
    /// nonempty, sorted and prefix-free, and there must be at least one.
    TermPaths(Vec<Vec<u32>>),
    /// Every terminal's whole configuration, with its `<generatedCounter>` content erased as in
    /// [`Self::WholeTerm`] and the content of each uncompared cell replaced by `\top` of its sort
    /// ([`CellProjection::project`]). Defined on every configuration, as the whole term is. Its
    /// value is a [`FinalResult::WholeTerm`] set of projected configurations: which cells a value
    /// leaves out is its slot's declaration, and two slots' values are never compared with each
    /// other. [`crate::CellLayout::unobservable_projection`] builds the projection that leaves out the
    /// cells a definition declares `unobservable`.
    Cells(CellProjection),
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
            Projection::State(
                StateProjection::WholeTerm
                | StateProjection::TermPaths(_)
                | StateProjection::Cells(_),
            ) => OracleKind::FinalResult,
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
    /// The terminal values of the run's complete paths, which its state sides are projected from
    /// (canonical under its own definition, TV-01), as a set: a path set and the state set of the
    /// same request give the same one; empty when the run gave no sides. An undefined step's
    /// pre-step term is no end and is not here (kink27 R1-UNDEF, module documentation). A pair
    /// judges them under the other side's definition before it compares the state slots (fz26
    /// KINK-OVERLOAD-VALUE, [`judge_across`]). Not encoded in the campaign report.
    pub ends: BTreeSet<Pattern>,
    /// Whether a complete path of the run is an undefined step (kink27 R1-UNDEF): a state value
    /// with no [`Self::ends`] is then the value of a run whose every path takes one, not a value
    /// whose ends were omitted ([`judge_across`], review N2).
    pub undefined_steps: bool,
    /// The states of the run's one-sided terminals (re-pin L1-2, [`OneSided`]) that its pair kept
    /// ([`RunCache::one_sided`] after [`judge_across`]: the clean, ground, stuck terminals of a
    /// work-bound mutant run that are data under the baseline's definition): the ends a state
    /// slot of the pair distinguishes one-sidedly from, when its projection of one of them is
    /// outside the baseline's projected set. Set only on a mutant's evidence, by the pairing;
    /// empty on every other evidence. Read by no comparison, fold, status or score (the slot
    /// reads the terminals themselves), and not encoded in the campaign report.
    pub one_sided_ends: BTreeSet<Pattern>,
    /// The ends of [`Self::ends`] that some path of the run reached at its last stop ([`Stop`]):
    /// a stop leaf of the run, a `cut-point` or `terminal` leaf at its path's `N`th stop event,
    /// rather than a leaf where the definition's own run ends. Evidence for a reader of where
    /// each end came from: both kinds are ends of the truncated system and compared alike, and
    /// two paths can reach one end each way. Empty for a run without a stop. Read by no
    /// comparison, fold, status or score, and not encoded in the campaign report.
    pub stop_ends: BTreeSet<Pattern>,
    /// For each pattern slot (by its index in the test's oracles), the terms its relation
    /// decisions read ([`ReadTerms`]): the payloads, bound values and assumptions of every
    /// relation the side's own decider decided other than by syntactic identity, and of every
    /// feasibility it decided. The slot's `Match` or `NoMatch` rests on them, decided in this
    /// side's theory, so a pair judges them under the other side's definition (fz26
    /// KINK-OVERLOAD-VALUE review S1, [`judge_across`]). Not encoded in the campaign report.
    pub payloads: BTreeMap<usize, BTreeSet<Pattern>>,
}

/// What one run reports besides its sides (re-pin adoption A-1): its contradicted-claim records
/// as specification diagnostics, the entries of its short-circuit readings that count against it
/// (the steps that exclude it as `short-circuit-reading`), its count of undecided solver answers,
/// and whether a leaf of it contradicts a claim. Empty for a run that failed or timed out, and
/// for a run reused from a baseline session on a load with a definition-level exclusion.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RunNotes {
    /// k-rust's `contradictedClaims` list of the run, the records of its definition's load
    /// included (`observedIn: load`): each says that a claim of the specification is false at an
    /// application (when `ground`), which the author can act on. Any record excludes the run
    /// (`contradicted-claim`, kink-native `exclusion`); a reader reports them.
    pub contradicted_claims: Vec<k_rust::backend::ContradictedClaimOutput<Pattern>>,
    /// The entries of k-rust's `shortCircuitReadings` list of the run that count against it on
    /// the judging definition (kink-native
    /// `DefinitionExclusions::counting_short_circuit_readings`): each names the rewrite rule whose
    /// work read the definedness of an operand a short-circuiting backend may skip, the operator,
    /// whether k-rust found the operand undefined or left it undecided, and the operand. Any entry
    /// excludes the run (`short-circuit-reading`); a reader reports them as the step that did.
    pub short_circuit_readings: Vec<k_rust::backend::ShortCircuitReadingOutput<Pattern>>,
    /// k-rust's count of the undecided solver answers the run's decisions took (`smtUnknowns`;
    /// always 0 without Z3). Reported only (decision D-7 (a1)): never an exclusion.
    pub smt_unknowns: usize,
    /// kink's count beside it: the undecided solver answers of the questions kink asked outside
    /// the run to judge it (kink-native `feasibility`, "Undecided answers"): the adapter's leaf
    /// feasibility (`RunFacts::decider_smt_unknowns`), the observation decider's leaf feasibility
    /// and relation queries for its state and pattern slots, and, on the mutant's evidence of a
    /// pair, the judgements of [`judge_across`] under both definitions. Always 0 without Z3.
    /// Reported only, never an exclusion, as `smt_unknowns` is.
    pub decider_smt_unknowns: usize,
    /// Whether a leaf of the run contradicts a claim by decision 2's leaf rule (kink-native
    /// `DefinitionExclusions::contradiction_on_a_leaf`): the one contradiction for which
    /// admission keeps a baseline and makes only its test unknown ([`admit`]). A record on the
    /// run's list alone refuses the baseline, as any other exclusion does.
    pub leaf_contradiction: bool,
    /// On the mutant's evidence of a pair only: the slots [`judge_across`] made unknown for the
    /// pair, and why (fz26 KINK-CAUSE-SUBTERM). Empty on every run's own evidence, and on a
    /// baseline's.
    pub across: Vec<CrossRefusal>,
    /// Whether a judgement kink makes of the run outside it could not be made for a reason that
    /// need not be a fact of the run (it can be the host's): the backend refused the operation
    /// (`Backend::with_solver` failed: a stack segment or the solver's initialization refused,
    /// or a failed solver prelude) for the observation decider over its leaves, for the
    /// judgement of its pattern slots, for the definition's facts a test with a pattern slot
    /// compares signatures by ([`Runtime::facts`]), or, on the mutant's evidence of a pair, for
    /// the judgement of either side's ends under the other side's definition ([`judge_across`]);
    /// or that judgement admitted no end as data because the definition's full critical-pair
    /// check ran out of native stack (kink-native `DataFacts::stack_stopped`); or one of those
    /// judgements met a stop for lack of native stack while it ran, a stop a site that only
    /// refines its answer dismissed included (k-rust's `stop::OperationRecord::stack_stops`
    /// around the judgement, [`judgement`]): the decider's existence judgement of a leaf
    /// (kink-native `ObservationDecider::configuration_exists`, k-rust's `ground_defined`) then
    /// answers "not shown to exist" where more stack would show it, and whether such a stop
    /// happens depends on the thread's stack and on the stack other threads hold. The slots that
    /// judgement decides are then `Unknown`, or the ends it judges are not data, so such an
    /// unknown is no function of the run's inputs and kink-flow's outcome cache never stores it
    /// (CF-33d). It decides no status here.
    pub unjudged: bool,
    /// The leaves, by their ordinal in the run's response order (kink-native `leaf_keys`), whose
    /// paths the bridge left incomplete when it read the run's own leaves for its state slots:
    /// each such path makes every state slot `Unknown`, `Timeout` or `Error` by its stop, before
    /// any end is read ([`state_side`]). Empty when no path is incomplete, and for a run that
    /// failed, timed out, was excluded or was not judged. A reader ties an undecided state slot
    /// to the leaves it is undecided by with it (kink-flow names an open application of an
    /// edited function only when every such leaf holds one, [`LeafCensus::leaf_open`]). It decides
    /// no status here.
    pub incomplete_leaves: BTreeSet<usize>,
    /// Why the run's stop condition ([`Stop::with_when`]) left it no evidence
    /// ([`ExecutionFailureKind::StopCondition`]): the last arrival the condition was left
    /// undecided at, with its reason, or the condition's refusal. `None` for every other run.
    pub stop_condition: Option<String>,
    /// What the run observed of its channels, under an observation declaration
    /// ([`RunOptions::observe`], [`crate::observation`]): a baseline's record, which every
    /// mutant's run of the test is compared with, or a mutant's comparison with it and, on the
    /// mutant's evidence of a pair, the observation slot's verdict (its position on `Distinguish`,
    /// its horizon on an `Agree` that rests on the baseline's prefix). The record decides the
    /// observation slot and whether the baseline is a prefix program: it is the one member of the
    /// notes a comparison reads. `None` for a run without a declaration.
    pub observation: Option<Observation>,
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
/// L1-1). The default is a state set for every result run, no work budget and kink's solver
/// budget, which is what [`run_campaign`] and [`run_campaign_multi`]'s callers in kink use unless
/// they choose otherwise.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunOptions {
    /// The modality requested for every result run: the run of a test with no pattern oracle,
    /// on the baseline and on every mutant (k-rust's state set by default). A test with a pattern
    /// oracle runs as a stepped path set on both sides, and its fallback run when stepping fails
    /// is a path set too. Both sides of a test run in this modality, whatever their leaves (fz26
    /// KINK-PATHSET-FALLBACK removed the per-side replacement of a state set with an undefined,
    /// vacuous or contradicted leaf by its path set). Sides are compared as sets of projected
    /// final configurations, which decision 3 makes the same in both modalities; the
    /// single-crash rule of [`state_side`] reads the number of ends (leaves that are not undefined
    /// steps), though, so a state-set side can be a crash side where the path set of the same
    /// request is `Unknown` (`tests/state_set_routes.rs` routes 1 and 2). `PathSet` is the reading
    /// at 1ee9955, kept for the modality differential.
    pub result_modality: ResultModality,
    /// The work budget of every mutant result run ([`WorkBudget`]).
    pub work: WorkBudget,
    /// Whether a work-bound mutant run can kill one-sidedly ([`OneSided`]; re-pin L1-2).
    pub one_sided: OneSided,
    /// The `max_work` of every baseline result run of the call (k-rust: the most states a run may
    /// visit across all its paths), never of a stepped run, for [`WorkBudget`]'s reason. A bound
    /// only stops a run: a baseline run it does not stop is the run without it, and one it stops
    /// ends in a `work-bound` leaf, whose side is `Unknown`. `None` (the default): baselines are
    /// bounded by the campaign's [`ExecutionBudget`] only.
    pub baseline_max_work: Option<u64>,
    /// The first attempt's Z3 resource units of every backend the call's runs execute on, the
    /// baseline's and each mutant's ([`Self::backend_options`]): with the fixed retries, the
    /// bound of every Z3 attempt of a run, so whether a query is decided is a function of the
    /// query, this budget and the Z3 build. The default is [`kink_native::SMT_RESOURCE_LIMIT`].
    pub smt_resource_limit: std::num::NonZeroU32,
    /// Where every result run ends besides its own end ([`Stop`]), on the baseline and on every
    /// mutant; [`Stop::NONE`] by default, under which every run is the run before stops existed.
    pub stop: Stop,
    /// The observation channels every result run is compared by besides its end slots
    /// ([`Observe`], [`crate::observation`]); [`Observe::NONE`] by default, under which every
    /// run, key and verdict is the one before observations existed.
    pub observe: Observe,
}

impl Default for RunOptions {
    fn default() -> Self {
        Self {
            result_modality: ResultModality::default(),
            work: WorkBudget::default(),
            one_sided: OneSided::default(),
            baseline_max_work: None,
            smt_resource_limit: kink_native::SMT_RESOURCE_LIMIT,
            stop: Stop::NONE,
            observe: Observe::NONE,
        }
    }
}

impl RunOptions {
    /// The solver options of every backend the call's runs execute on: kink's
    /// ([`kink_native::BACKEND_OPTIONS`]) with [`Self::smt_resource_limit`].
    #[must_use]
    pub const fn backend_options(&self) -> BackendOptions {
        kink_native::backend_options(self.smt_resource_limit)
    }

    /// Every option as a JSON object, `{result_modality, work, one_sided}`: `work` is null
    /// without a work budget, else `{factor, floor}`; `one_sided` is [`OneSided::name`]; and
    /// `baseline_max_work` only when it is set, so the value of every option set without it, a
    /// kink-corpus index entry's included, is the value it had before the option existed, and
    /// absence means exactly `None`; `stop` likewise only with a stop ([`Stop::value`]), and
    /// `observe` only with an observation declaration ([`Observe::value`]).
    /// `smt_resource_limit` is a member under the Z3 profile only: under the no-Z3 profile no
    /// backend reads it, so it decides nothing a store keeps, and the value is the one the options
    /// had before it existed. A store that records the options its runs were made with
    /// (kink-corpus index entries, `run_options`) records this value (re-pin L1-2-land; CACHE-ID
    /// review 2 minor 1). Every field is destructured, without `..`, and every nested option is
    /// matched exhaustively, so a new option does not compile until it is recorded here: no
    /// option can be left out of the record and silently default when the record is read back.
    #[must_use]
    pub fn value(&self) -> Value {
        let Self {
            result_modality,
            work,
            one_sided,
            baseline_max_work,
            smt_resource_limit,
            stop,
            observe,
        } = *self;
        let work = match work {
            WorkBudget::Unbounded => Value::Null,
            WorkBudget::Calibrated { factor, floor } => json!({"factor": factor, "floor": floor}),
        };
        let mut value = json!({
            "result_modality": result_modality.name(),
            "work": work,
            "one_sided": one_sided.name(),
        });
        if let Some(max_work) = baseline_max_work {
            value["baseline_max_work"] = json!(max_work);
        }
        if SolverProfile::BUILD == SolverProfile::Z3 {
            value["smt_resource_limit"] = json!(smt_resource_limit.get());
        }
        if let Some(stop) = stop.value() {
            value["stop"] = stop;
        }
        if let Some(observe) = observe.value() {
            value["observe"] = observe;
        }
        value
    }
}

/// The version of kink's counted stop ([`Stop`]): how a result run with a stop is made of
/// requests ([`Runtime::execute`]), how each side resolves the stop's names (by exact label of a
/// rewrite rule; the baseline refused and a mutant not admitted otherwise), and that a stop leaf
/// is compared as an end of the truncated system. A component of kink's semantics identity
/// ([`crate::identity::KINK_IDENTITY`], key `stop`), so a store that honours a verdict made under
/// another version misses or is refused. Bump it whenever any of these changes what a run with a
/// stop returns; a run without a stop is outside all of it. v1: the run to the `N`th stop event
/// was staged, one request per stage start, each ending its paths at their first stop event,
/// with `max_depth` bounding each request, the work budget spent across the requests in the order
/// of their starts' patterns, and each resumed cut point's step credited to coverage. v2: the run
/// is one request from the test's initial state, which k-rust ends at each path's `N`th stop
/// event (kink-native `ExecutionAdapter::execute_result_counted`). Its ends, coverage and
/// exclusions are those of the same truncated system and its work is the same count of expanded
/// states, but `max_depth` now bounds each path from the initial state, as in a run without a
/// stop, a work budget reaches the states of k-rust's one exploration of the run (depth first)
/// rather than the stages' starts in the order of their patterns, and a leaf's depth is its
/// path's from the initial state; so a run that a bound stops, and the depths a census reports,
/// can differ from v1's. v3: a stop may carry a stop condition ([`Stop::with_when`],
/// [`crate::condition`]), asked at each arrival within the one request: the count counts the
/// arrivals where it holds, every other arrival is taken as a step; a run with an arrival where it
/// was left undecided, or a refusal, is no evidence on either side (`stop-condition`); and a
/// mutant whose declarations of the read cells' sorts are not the baseline's is not admitted
/// (`stop-condition-incompatible`). A stop without a condition makes every request, judges every
/// run and admits every mutant as v2 does.
pub const STOP_VERSION: &str = "kink-campaign/stop/v3";

/// Where a campaign's result runs end besides their own end (the observer's choice for a
/// definition that never terminates): rewrite rules named by exact K label, to stop before
/// ([`StopRules::before`], k-rust `cut_point_rules`) or after ([`StopRules::after`],
/// `terminal_rules`), and a count `N`: a path ends at its `N`th stop event, a step by a named
/// rule that is its state's one successor (see the module documentation), or where the
/// definition's own run ends, whichever comes first. A test may have its own count
/// ([`Self::with_test_count`]): the count is a property of the observation of one program, while
/// the rules are the campaign's.
///
/// A stop may carry a condition ([`Self::with_when`], [`crate::condition`]): a function of named
/// cells of each arrival's stop state, evaluated in one fixed observer, so that the count counts
/// the arrivals where it holds.
///
/// [`RunOptions`] is `Copy`, so a stop is held interned: equal stops are one value, which lives
/// as long as the process. [`Stop::NONE`] names no rule.
///
/// A stop applies to result runs only. A pattern oracle's stepped run has none, so a campaign
/// with a stop and a pattern oracle is refused, and so is a campaign manifest for runs with a
/// stop: a manifest does not record one, so it could not say what its report's verdicts are
/// relative to.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Stop(Option<&'static CountedStop>);

/// No stop rule, the rules of a run without a stop ([`Stop::execute_result`]).
static NO_STOP: StopRules = StopRules::NONE;

/// The rules and counts of a [`Stop`] that names a rule.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct CountedStop {
    rules: StopRules,
    count: std::num::NonZeroU64,
    counts: BTreeMap<String, std::num::NonZeroU64>,
    when: Option<StopWhen>,
}

impl Stop {
    /// No stop: every run ends where its paths end.
    pub const NONE: Self = Self(None);

    /// The stop at the rules `rules`, at the `count`th stop event of a path; `None` when `rules`
    /// names no rule, for which a count means nothing.
    #[must_use]
    pub fn new(rules: StopRules, count: std::num::NonZeroU64) -> Option<Self> {
        (!rules.is_none()).then(|| {
            Self::interned(CountedStop {
                rules,
                count,
                counts: BTreeMap::new(),
                when: None,
            })
        })
    }

    /// This stop with the count `count` for the test `test_id` (its id in the campaign's tests);
    /// [`Self::NONE`] stays as it is.
    #[must_use]
    pub fn with_test_count(self, test_id: &str, count: std::num::NonZeroU64) -> Self {
        match self.0 {
            None => self,
            Some(counted) => {
                let mut counted = counted.clone();
                counted.counts.insert(test_id.to_owned(), count);
                Self::interned(counted)
            }
        }
    }

    /// This stop with the condition `when` ([`crate::condition`]): every test's run counts only
    /// the arrivals where it holds. [`Self::NONE`] stays as it is, since a condition is asked only
    /// at arrivals at a stop's rules.
    #[must_use]
    pub fn with_when(self, when: StopWhen) -> Self {
        match self.0 {
            None => self,
            Some(counted) => {
                let mut counted = counted.clone();
                counted.when = Some(when);
                Self::interned(counted)
            }
        }
    }

    /// The condition; `None` for a stop without one and for [`Self::NONE`].
    #[must_use]
    pub fn when(self) -> Option<&'static StopWhen> {
        self.0.and_then(|counted| counted.when.as_ref())
    }

    fn interned(counted: CountedStop) -> Self {
        static INTERNED: std::sync::Mutex<BTreeSet<&'static CountedStop>> =
            std::sync::Mutex::new(BTreeSet::new());
        let mut interned = INTERNED
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(existing) = interned.get(&counted) {
            return Self(Some(existing));
        }
        let leaked: &'static CountedStop = Box::leak(Box::new(counted));
        interned.insert(leaked);
        Self(Some(leaked))
    }

    /// Whether this names no rule.
    #[must_use]
    pub const fn is_none(self) -> bool {
        self.0.is_none()
    }

    /// The rules; `None` for [`Self::NONE`].
    #[must_use]
    pub fn rules(self) -> Option<&'static StopRules> {
        self.0.map(|counted| &counted.rules)
    }

    /// The count of every test without its own; `None` for [`Self::NONE`].
    #[must_use]
    pub fn count(self) -> Option<std::num::NonZeroU64> {
        self.0.map(|counted| counted.count)
    }

    /// The rules and the count of the run of the test `test_id`; `None` for [`Self::NONE`].
    #[must_use]
    pub fn of_test(self, test_id: &str) -> Option<(&'static StopRules, std::num::NonZeroU64)> {
        self.0.map(|counted| {
            (
                &counted.rules,
                counted
                    .counts
                    .get(test_id)
                    .copied()
                    .unwrap_or(counted.count),
            )
        })
    }

    /// The result run of the test `test_id` from `initial`, as a campaign makes it
    /// ([`RunOptions::stop`]): `adapter`'s one request, which with a stop ends each path at its
    /// `N`th stop event, `N` the test's count ([`Self::of_test`]; see the module documentation).
    /// For a caller that runs a test again outside a campaign, such as a diagnostic run, so that
    /// it runs the request the campaign ran.
    ///
    /// # Errors
    ///
    /// The adapter's failure of the request.
    pub fn execute_result(
        self,
        adapter: &ExecutionAdapter,
        backend: &mut Backend,
        test_id: &str,
        initial: &Pattern,
        budget: ExecutionBudget,
        run: ResultRun,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        self.execute_result_with(
            adapter,
            backend,
            &mut DefinitionTables::new(),
            test_id,
            initial,
            budget,
            run,
        )
    }

    /// [`Self::execute_result`] reading `backend`'s definition tables from `tables`, which the
    /// caller keeps beside `backend` for all its runs ([`DefinitionTables`]).
    #[expect(
        clippy::too_many_arguments,
        reason = "Self::execute_result's inputs and the backend's tables, which belong beside the \
                  backend and not in any of the others"
    )]
    fn execute_result_with(
        self,
        adapter: &ExecutionAdapter,
        backend: &mut Backend,
        tables: &mut DefinitionTables,
        test_id: &str,
        initial: &Pattern,
        budget: ExecutionBudget,
        run: ResultRun,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        self.execute_asking(
            adapter, backend, tables, test_id, initial, budget, run, None,
        )
        .0
    }

    /// [`Self::execute_result_with`], and the reason of the last arrival the stop's condition
    /// was left undecided at, when it was. With a condition the request asks it at each arrival
    /// (kink-native `ExecutionAdapter::execute_result_counted`); a condition its oracle cannot
    /// give fails the run as the condition's refusal does
    /// ([`ExecutionAdapterFailure::StopCondition`]). With `probe` the request carries it
    /// (kink-native `ExecutionAdapter::execute_result_probed`), composed with the stop and its
    /// condition within the one request.
    #[expect(
        clippy::too_many_arguments,
        reason = "Self::execute_result_with's inputs and the run's probe"
    )]
    fn execute_asking(
        self,
        adapter: &ExecutionAdapter,
        backend: &mut Backend,
        tables: &mut DefinitionTables,
        test_id: &str,
        initial: &Pattern,
        budget: ExecutionBudget,
        run: ResultRun,
        probe: Option<RequestProbe<'_>>,
    ) -> (
        Result<AdaptedExecution, ExecutionAdapterFailure>,
        Option<String>,
    ) {
        let (rules, count) = self
            .of_test(test_id)
            .unwrap_or((&NO_STOP, std::num::NonZeroU64::MIN));
        let Some(when) = self.when() else {
            return (
                adapter.execute_result_probed(
                    backend, tables, initial, budget, run, rules, count, None, probe,
                ),
                None,
            );
        };
        match when.asking(|condition| {
            adapter.execute_result_probed(
                backend,
                tables,
                initial,
                budget,
                run,
                rules,
                count,
                Some(condition),
                probe,
            )
        }) {
            Ok((execution, undecided)) => (execution, undecided),
            Err(reason) => (
                Err(ExecutionAdapterFailure::StopCondition(format!(
                    "no stop condition could be asked: {reason}"
                ))),
                None,
            ),
        }
    }

    /// The stop as a JSON object, `{before, after, count}`, with `counts` (`{test_id: count}`)
    /// when a test has its own count, and `when`, the condition's identity
    /// ([`StopWhen::identity`]), when it has one; `None` for [`Self::NONE`]. A stop without a
    /// condition has the value it had before conditions existed. Every field is destructured, so
    /// a new one does not compile until it is recorded here.
    #[must_use]
    pub fn value(self) -> Option<Value> {
        let CountedStop {
            rules: StopRules { before, after },
            count,
            counts,
            when,
        } = self.0?;
        let mut value = json!({"before": before, "after": after, "count": count.get()});
        if !counts.is_empty() {
            value["counts"] = counts
                .iter()
                .map(|(test, count)| (test.clone(), json!(count.get())))
                .collect::<serde_json::Map<_, _>>()
                .into();
        }
        if let Some(when) = when {
            value["when"] = when.identity().clone();
        }
        Some(value)
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
/// baseline's complete set lacks, with contradicted claims read per path. v2 (kink27
/// R3-UNDEF-BRIDGE): an undefined step's leaf of the mutant run completes when its pre-step
/// configuration is shown to exist, not only by a terminal value, so `work_bound_stuck_terminals`
/// admits runs with such a leaf that v1 refused. v3: a slot projecting the configuration without
/// its uncompared cells ([`StateProjection::Cells`]), which is defined on every configuration,
/// distinguishes one-sidedly as the whole term does. v4: a run with a stop ([`Stop`]) gives
/// one-sided evidence. A clean ground stop leaf is final in the truncated system by a fact of its
/// own path (its last step is its `N`th stop event, or its one successor is by a rule it stops
/// before at its `N`th, decided without a diagnostic; the earlier stop events are steps of that
/// path), so it is a final configuration of every completion of the run, as a clean ground stuck
/// leaf is. (Under [`STOP_VERSION`] v1 the run was staged, and the rule read the joined run of
/// every stage, whose path to such a leaf passed only through stage starts that were stop leaves
/// of finished earlier requests; under v2 it is one request, and the rule reads it as any run.)
/// v5: the cell projection leaves out cells inside `?` and `*` cells, in each instance, and
/// compares a Map's or a Set's instances as a multiset ([`crate::CellLayout::position`]); it is
/// still defined on every configuration, so the rule reads it as before, over projections that
/// v4 never made (a slot leaving out such a cell was refused). v6: a run with a stop condition
/// ([`Stop::with_when`]) gives one-sided evidence: its clean ground stop leaf ends its path at
/// an arrival where the condition was decided to hold, every earlier arrival of that path was
/// decided to fail or was an earlier event, and each decision is a fact of the observer and that
/// state, so the leaf is final in the truncated system by a fact of its own path, as under v5. A
/// run with a `stop-undecided` leaf (a path that ended at an arrival the condition left
/// undecided) gives none: it is no evidence (`stop-condition`) before it is judged into sides.
pub const ONE_SIDED_VERSION: &str = "kink-campaign/one-sided/v6";

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
/// - the slot projects the whole term, the configuration without its uncompared cells
///   ([`StateProjection::Cells`]) or the exit stop without an exit-code cell, which are defined
///   on every final configuration (a failed projection makes a two-sided slot `Error`, and the
///   unexplored part cannot be read).
///
/// Never from a cancelled or timed-out run, never on a pattern slot (stepped runs carry no work
/// budget), never from a complete mutant run (its two-sided comparison already distinguishes when
/// such a leaf exists). The mutant's side stays `Unknown`: only the slot's outcome becomes
/// `Distinguish`.
///
/// Contradicted claims are read per path (Sebastien, 2026-10-17; re-pin L1-2-fix-1; kink's `trust.md`,
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
/// is `Unknown`, unless it distinguishes one-sidedly ([`OneSided`], re-pin L1-2). A baseline's
/// result runs take [`RunOptions::baseline_max_work`] instead, and no work budget ever applies to
/// a stepped run (a pattern test's observed path set): a
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
    /// Candidate mutants kink did not admit.
    pub not_admitted: u64,
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
            MutantStatus::NotAdmitted => tally.not_admitted += 1,
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
    /// The solver options of the backend the run executes on (`LoadedSide::load`;
    /// [`RunOptions::smt_resource_limit`]).
    solver: BackendOptions,
    /// The modality of the result run (`Runtime::execute`; re-pin L1-1).
    modality: ResultModality,
    /// The result run's work bound (`Runtime::execute`; [`RunOptions::baseline_max_work`]), so a
    /// session never answers a request with a run made under another bound.
    max_work: Option<u64>,
    /// The result run's stop (`Runtime::execute`; [`RunOptions::stop`]).
    stop: Stop,
    /// The result run's observation declaration (`Runtime::execute_against`;
    /// [`RunOptions::observe`]), whose probe records the run's channels.
    observe: Observe,
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
        load: Box<DefinitionExclusions>,
    },
    /// A run whose producing load was excluded ([`DefinitionExclusions::definition_exclusion`]:
    /// a load stack stop, an implementation-chosen hook, a condition equating two terms): the
    /// execution is not kept, so it can never be judged again on another load. A load the
    /// short-circuit analysis flags is not excluded (CF-03): its runs are kept and each reuse
    /// judges the stored run's own `shortCircuitReadings` list under the combined facts, as the
    /// live run was judged. A hit is that exclusion, as the live run was; the
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
    /// The functions applied unreduced in the states of the final leaves k-rust normalised,
    /// stuck, undefined steps, indeterminate or a stop's (kink-native [`open_applications`]), each
    /// once, with its first application in the first such leaf in run order: the definition
    /// leaves the application's value open there (kink27 R5-WEAKENING).
    pub open: Vec<OpenApplication>,
    /// For each leaf in the run's response order, the functions applied unreduced in its state
    /// or its path predicates when it is such a leaf (kink-native [`open_symbols`]), by KORE
    /// symbol; empty for every other leaf. With
    /// [`RunNotes::incomplete_leaves`] it says whether every leaf that keeps a state slot
    /// undecided holds such an application.
    pub leaf_open: Vec<BTreeSet<String>>,
}

impl LeafCensus {
    /// `functions`: the side's function symbols defined by equations ([`Runtime`]'s).
    fn of(
        execution: Result<&AdaptedExecution, &ExecutionAdapterFailure>,
        functions: &BTreeSet<String>,
    ) -> Self {
        let Ok(execution) = execution else {
            return Self {
                stop: RunStop::Failed,
                leaves: BTreeMap::new(),
                deepest: None,
                rule_ids: BTreeSet::new(),
                work: None,
                open: Vec::new(),
                leaf_open: Vec::new(),
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
            leaf_open: execution
                .leaves()
                .iter()
                .map(|leaf| open_symbols(leaf, functions))
                .collect(),
            open: execution
                .leaves()
                .iter()
                .flat_map(|leaf| open_applications(leaf, functions))
                .fold(Vec::new(), |mut open, application| {
                    if !open
                        .iter()
                        .any(|seen: &OpenApplication| seen.symbol == application.symbol)
                    {
                        open.push(application);
                    }
                    open
                }),
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
    /// The binding collection every baseline result run of the session's calls asks with
    /// ([`Self::with_bindings`]); `None`: the runs collect no bindings.
    bindings: Option<kink_native::execution::BindingCollection>,
    /// The length up to which every baseline result run of the session's calls collects rule
    /// windows ([`Self::with_windows`]); 1 collects none.
    windows: std::num::NonZeroUsize,
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
            bindings: None,
            windows: std::num::NonZeroUsize::MIN,
        }
    }

    /// The session, every baseline result run of its calls collecting the bindings of its fired
    /// instances under `bindings` (kink-native `ResultRun::bindings`: the front end's authored
    /// symbols and template binders), which the run's coverage carries
    /// (`TestCoverage::bindings`). k-rust states that asking changes no other field of the
    /// result, so a stored run is reused as before; a mutant's runs never ask.
    #[must_use]
    pub fn with_bindings(mut self, bindings: kink_native::execution::BindingCollection) -> Self {
        self.bindings = Some(bindings);
        self
    }

    /// The session, every baseline result run of its calls that collects bindings also
    /// collecting the rule windows of length up to `depth` (kink-native
    /// `DefinitionTables::with_windows`), which the run's coverage carries
    /// (`TestCoverage::windows`); a depth of 1 collects none. k-rust states that asking changes
    /// no other field of the result; a mutant's runs never ask.
    #[must_use]
    pub const fn with_windows(mut self, depth: std::num::NonZeroUsize) -> Self {
        self.windows = depth;
        self
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

    /// The session with the baseline's data facts already computed by the caller, so no call
    /// computes them again. The caller vouches that `facts` are those of the session validator's
    /// compiled baseline, loaded on kink's route (`Backend::from_definition` of its KORE) for the
    /// module its campaigns name: they are stamped with that compile's `kore_sha256`, and the
    /// session cannot tell them from facts of another definition. Facts computed with other
    /// names than [`Self::assume_joined`] are not used (the session computes its own on its
    /// first call with a mutant).
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
            let (evidence, cache) = runtime.run_bounded(campaign, test, runtime.baseline_max_work);
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
            solver: runtime.solver,
            modality: runtime.modality,
            max_work: runtime.baseline_max_work,
            stop: runtime.stop,
            observe: runtime
                .observe
                .as_ref()
                .map_or(Observe::NONE, |observing| observing.declared),
        };
        if let Some(stored) = self.runs.iter().find(|stored| stored.key == key) {
            let (evidence, cache) = match &stored.run {
                // The classifier-dependent part of the run, again (flow F-16), under the facts of
                // the load that produced it and of this call's load (re-pin R0c).
                StoredRun::Executed { executed, load } => (
                    runtime.judge_on(campaign, test, executed, Some(&**load)),
                    executed.cache.clone(),
                ),
                StoredRun::Excluded { exclusion, cache } => (
                    TestEvidence {
                        test_id: test.id.clone(),
                        run: SideRun::Failed((*exclusion).into()),
                        notes: RunNotes::default(),
                        ends: BTreeSet::new(),
                        undefined_steps: false,
                        one_sided_ends: BTreeSet::new(),
                        stop_ends: BTreeSet::new(),
                        payloads: BTreeMap::new(),
                    },
                    (**cache).clone(),
                ),
            };
            self.reused += 1;
            self.record_baseline(&cache, true);
            return (evidence, cache);
        }
        let (evidence, executed) =
            runtime.run_keeping(campaign, test, runtime.baseline_max_work, None);
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
                load: Box::new(runtime.exclusions.clone()),
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
    run_campaign_session(campaign, generations, options, session, None)
}

/// A caller's order of a mutant's tests, chosen once the mutant's claim-free side, the definition
/// every test of the mutant runs on, has compiled ([`run_campaign_multi_ordered`]): given the
/// mutant's [`CompiledEdit`] as a ground test witnesses it ([`CompiledEdit::for_ground_tests`]:
/// the claim-free side's against the compiled baseline, or the mutant as written's when only
/// definedness claims were withdrawn), the ids of the tests that run first. A caller whose tests
/// are not ground reads the edit as a ground test would, which changes only the order.
pub type FirstTests<'f> = dyn FnMut(&CompiledEdit) -> BTreeSet<String> + 'f;

/// [`run_campaign_multi_with`] with each mutant's tests ordered by the caller once the mutant
/// compiles: the tests `first` names run first, then the rest, each group in the campaign's test
/// order (kink-flow's kill search, which keeps its programs' coverage by baseline sentence and
/// reads the edit through [`CompiledEdit::witness`]). A mutant refused before its claim-free side
/// compiles runs no test and is never given to `first`. Each mutant's plan lists its tests in the
/// order they ran, and its report is derived against the manifest in that order; the plan records
/// no [`MutantSelection`], since no policy chose the order. The order changes no status in the
/// no-Z3 profile while no wall-clock bound fires, as for [`SelectionPolicy::Prioritize`] (module
/// [`crate::selection`]). A campaign that also asks for a selection policy is refused before
/// anything runs: the two would be two orders of one mutant's tests.
pub fn run_campaign_multi_ordered(
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
    options: &CampaignOptions,
    session: &mut BaselineSession<'_>,
    first: &mut FirstTests<'_>,
) -> Result<CampaignRun, CampaignFailure> {
    if options.selection != SelectionPolicy::None {
        return Err(CampaignFailure::new(
            CampaignFailureKind::InvalidDeclaration,
            "a caller's test order and a selection policy would be two orders of a mutant's tests",
        ));
    }
    run_campaign_session(campaign, generations, options, session, Some(first))
}

fn run_campaign_session(
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
    options: &CampaignOptions,
    session: &mut BaselineSession<'_>,
    mut first: Option<&mut FirstTests<'_>>,
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
            // The observation slot comes after the end slots.
            slot_count: test.oracles.len() + usize::from(!options.run.observe.is_none()),
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
    let mut runtime = Runtime::prepare_with(
        campaign,
        &baseline,
        options.run.backend_options(),
        options.run.stop.when().is_some() || !options.run.observe.is_none(),
    )
    .map_err(|_| admission_failure(BaselineAdmission::Error))?;
    runtime.coverage = Some(RuleAuthors::of(&baseline));
    if let Some(bindings) = &session.bindings {
        runtime.tables = DefinitionTables::new()
            .with_bindings(bindings.clone())
            .with_windows(session.windows);
    }
    runtime.modality = options.run.result_modality;
    runtime.baseline_max_work = options.run.baseline_max_work;
    runtime.stop = options.run.stop;
    if !options.run.stop.is_none() {
        // A stop ends result runs; a pattern oracle's stepped run has none, so its sides would be
        // of another observation than the stop states.
        if let Some(test) = campaign.tests.iter().find(|test| {
            test.oracles
                .iter()
                .any(|declaration| matches!(declaration.projection(), Projection::Pattern { .. }))
        }) {
            return Err(CampaignFailure::new(
                CampaignFailureKind::InvalidDeclaration,
                format!(
                    "test {} has a pattern oracle, whose stepped run takes no stop",
                    test.id
                ),
            ));
        }
        let unresolved = resolve_stop(options.run.stop, &mut runtime.backend)
            .map_err(|_| admission_failure(BaselineAdmission::Error))?;
        if !unresolved.is_empty() {
            return Err(CampaignFailure::stop_unresolved(unresolved));
        }
        // The condition's cells are read on the baseline with its declarations; cells it has no
        // leaf cell symbol for state no observation of it.
        if let Some(when) = options.run.stop.when()
            && let Some(Err(reason)) = runtime
                .signature
                .as_ref()
                .map(|signature| signature.reads(when.cells()))
        {
            return Err(CampaignFailure::new(
                CampaignFailureKind::InvalidDeclaration,
                format!("stop-condition: {reason} on the baseline"),
            ));
        }
    }
    if !options.run.observe.is_none() {
        runtime.observe = Some(Arc::new(observing(
            campaign,
            &baseline,
            options.run.observe,
            &mut runtime,
        )?));
    }
    // The baseline's full critical-pair check, once per session (fz26 KINK-BASELINE-FINDINGS):
    // a name the author gives that the baseline refuses refuses a call with a mutant. Every call
    // reads it for the ends of the baseline's runs (KINK-OVERLOAD-VALUE: an overload application
    // is data only under the definition's facts), so a program's class does not depend on whether
    // the call has a mutant; a call without one that cannot compute them admits no overload end.
    let baseline_data = session.data_of(&baseline, &mut runtime);
    runtime.data = baseline_data.as_ref().ok().cloned();
    let data = if generations
        .iter()
        .any(|generation| !generation.candidates().is_empty())
    {
        let facts = baseline_data.map_err(|_| admission_failure(BaselineAdmission::Error))?;
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
        solver: options.run.backend_options(),
        assume_joined: session.assume_joined.clone(),
        data,
        signature: runtime.signature.clone(),
    };
    // Refuse unsafe input through the existing declaration admission gate, before any baseline
    // or mutant execution (TV-01, R2-F1). Its definedness refusals of test-written predicates
    // date from before k-rust's solver read each atom with its operands' definedness (GAP K15)
    // and are kept as a fail-closed narrowing (`validate_test_initial_state`).
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
                // The backend refused the definition's facts: the pattern slots are unknown for a
                // reason that need not be a fact of the run ([`RunNotes::unjudged`]).
                if patterns.is_none() && has_pattern_slot(test) {
                    evidence.notes.unjudged = true;
                }
                replace_patterns(test, evidence, patterns.as_ref());
            }
        }
        let admission = admit(campaign.tests, &baseline_evidence);
        if admission == BaselineAdmission::OracleFailed
            && let Some(evidence) = baseline_evidence.iter().find(|evidence| {
                evidence.run == SideRun::Failed(ExecutionFailureKind::StopCondition)
            })
        {
            return Err(CampaignFailure::stop_condition_refused(
                &evidence.test_id,
                evidence
                    .notes
                    .stop_condition
                    .as_deref()
                    .unwrap_or("no answer"),
            ));
        }
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
        if admission == BaselineAdmission::OracleFailed
            && let Some((test_id, refusal)) = baseline_evidence.iter().find_map(|evidence| {
                // A run that gave no sides is refused for that first ([`admit`]).
                matches!(evidence.run, SideRun::Sides { .. }).then_some(())?;
                baseline_record(evidence)?
                    .refusal
                    .as_deref()
                    .map(|refusal| (&evidence.test_id, refusal))
            })
        {
            return Err(CampaignFailure::new(
                CampaignFailureKind::BaselineOracleFailed,
                format!("observe: the baseline run of test {test_id} refuses it: {refusal}"),
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
            first.as_deref_mut(),
        );
        session
            .last_call
            .mutants
            .push((MutantId(index), execution.recordings));
        // A caller's order (`run_campaign_multi_ordered`): the manifest lists the tests in the
        // order they ran, which the plan records no selection for.
        let ordered;
        let manifest = match &execution.caller_order {
            None => &manifest,
            Some(order) => {
                ordered = order
                    .iter()
                    .map(|id| {
                        manifest
                            .iter()
                            .find(|test| test.test_id == *id)
                            .expect("a caller's order lists the campaign's tests")
                            .clone()
                    })
                    .collect::<Vec<_>>();
                &ordered
            }
        };
        let plan = MutantPlan {
            mutant_id: MutantId(index),
            tests: execution.tests,
            mutant_failure: execution.failure,
            claims: execution.claims,
            inconsistent_pairs: execution.inconsistent_pairs,
            selection: execution.selection,
        };
        let report = derive_mutant_report(&plan, manifest, schedule)?;
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

/// The campaign's observation declaration `observe` as every side's runs observe it, on the
/// baseline `baseline` and its runtime `runtime` ([`Observing`]).
///
/// # Errors
///
/// The campaign is refused (`InvalidDeclaration`) when a test has a pattern oracle (its stepped
/// run carries no probe, so its sides would be of another run than the channels), when a name of
/// a point class labels no rewrite rule of the baseline (`point-unresolved`), and when a cell
/// states no observation of the baseline's configuration ([`Observe::resolve`]).
fn observing(
    campaign: &Campaign<'_>,
    baseline: &ValidatedDefinition,
    observe: Observe,
    runtime: &mut Runtime,
) -> Result<Observing, CampaignFailure> {
    let invalid = |detail: String| {
        CampaignFailure::new(
            CampaignFailureKind::InvalidDeclaration,
            format!("observe: {detail}"),
        )
    };
    if let Some(test) = campaign.tests.iter().find(|test| has_pattern_slot(test)) {
        return Err(invalid(format!(
            "test {} has a pattern oracle, whose stepped run carries no observation probe",
            test.id
        )));
    }
    let unresolved = observe
        .rules()
        .unresolved(&mut runtime.backend)
        .map_err(|_| admission_failure(BaselineAdmission::Error))?;
    if !unresolved.is_empty() {
        return Err(invalid(format!(
            "point-unresolved: {} label no rewrite rule of the baseline",
            unresolved.join(", ")
        )));
    }
    let kore = parse_definition(&baseline.artifacts().definition_kore)
        .map_err(|_| admission_failure(BaselineAdmission::Error))?;
    let layout = crate::CellLayout::of_parsed(baseline, &kore)
        .map_err(|refusal| invalid(format!("{refusal:?}")))?;
    let resolved = observe.resolve(&layout, &kore).map_err(invalid)?;
    let shared = runtime
        .backend
        .select_definition(None)
        .map_err(|_| admission_failure(BaselineAdmission::Error))?;
    Ok(Observing {
        declared: observe,
        resolved,
        shared,
        trusted: runtime.exclusions.collections_trusted(),
    })
}

/// A difference the observation slot reported, re-derived from both sides' values
/// ([`observed_difference`]): the position, and each side's element there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObservedDifference {
    pub position: crate::observation::Position,
    /// The baseline's element at the position: the element a capture run of the baseline read,
    /// a content or, under `count`, an undecided element where the record holds one; or END or
    /// UNDEF where its record closes the channel there.
    pub baseline: Element,
    /// The mutant's element at the position, as its probe read it
    /// ([`crate::ObservationVerdict::element`]).
    pub mutant: Element,
}

/// The two elements of the difference `verdict` reports for the test `test` of `campaign` run
/// under `options` (the options of the call that judged it), whose baseline's run recorded
/// `record` ([`crate::observation`], "The slot").
///
/// The record keeps no values, only 8 bytes of each element's digest. The baseline's element is
/// re-derived by a capture run: the baseline's request for the test again, on a fresh load of
/// the baseline, with a probe that records its channels as the baseline's probe does and ends
/// the path at the reported element. The element's digest bytes must be the recorded ones: the
/// run is then the recorded run up to that element (the record is a function of the request),
/// and the value read is the one whose digest was compared, a content. Where the record holds an
/// undecided element (a class under `count`), the capture run must read an undecided element
/// there, with no digest: the event exists and its content is not decided. Where the baseline's
/// channel is closed at the position, its element is END or UNDEF, from the record. The mutant's
/// element is its probe's ([`crate::ObservationVerdict::element`]). The two must differ in every
/// model: two contents differ as values, and an undecided element differs only from a closure
/// (END, UNDEF or a cycle's silence), since it is a content whose value is not known.
///
/// # Errors
///
/// Why the difference is not re-derived: the verdict reports none, the record has no such
/// channel or is open there, the capture run failed or did not reach the element, its element is
/// not the recorded one (another digest, or decided where the record's is undecided or the
/// reverse), or the two elements do not differ in every model. Each is an error of the run that
/// reported the difference, never a verdict.
pub fn observed_difference(
    campaign: &Campaign<'_>,
    options: &RunOptions,
    test: &TestCase,
    record: &BaselineRecord,
    verdict: &crate::ObservationVerdict,
) -> Result<ObservedDifference, String> {
    let position = verdict
        .position
        .clone()
        .ok_or("the slot reports no difference")?;
    let mutant = verdict
        .element
        .clone()
        .ok_or("the slot reports no element of the mutant")?;
    let channel = record
        .channels
        .iter()
        .position(|channel| channel.name == position.channel)
        .ok_or_else(|| format!("the record has no channel `{}`", position.channel))?;
    let recorded = &record.channels[channel];
    let baseline = match (recorded.elements.get(position.index), &recorded.end) {
        (Some(recorded), _) => {
            let (element, captured) =
                capture_element(campaign, options, test, channel, position.index)?;
            if captured != *recorded {
                return Err(format!(
                    "the capture run's element {} of `{}` does not have the recorded digest: the \
                     capture run is not the recorded run",
                    position.index, position.channel
                ));
            }
            // The digest is a content's: the capture run read a value there, or read none where
            // the record holds an undecided element.
            let content = matches!(element, Element::Content(_) | Element::Evaluated(_));
            if content != recorded.is_some() {
                return Err(format!(
                    "the capture run's element {} of `{}` is {} where the record's is {}",
                    position.index,
                    position.channel,
                    decidedness(&element),
                    if recorded.is_some() {
                        "a content"
                    } else {
                        "undecided"
                    }
                ));
            }
            element
        }
        (None, crate::ChannelEnd::Closed(closure)) => match closure {
            crate::Closure::End => Element::End,
            crate::Closure::Undefined => Element::Undefined,
            crate::Closure::Cycle => Element::Cycle,
        },
        (None, crate::ChannelEnd::Open(_)) => {
            return Err(format!(
                "the record's channel `{}` is open before {}",
                position.channel, position.index
            ));
        }
    };
    if baseline == mutant {
        return Err(format!(
            "both sides' elements {} of `{}` are equal: the difference is not re-derived",
            position.index, position.channel
        ));
    }
    let closure =
        |element: &Element| matches!(element, Element::End | Element::Undefined | Element::Cycle);
    if !closure(&baseline)
        && !closure(&mutant)
        && (baseline == Element::Undecided || mutant == Element::Undecided)
    {
        return Err(format!(
            "the elements {} of `{}` are {} on the baseline and {} on the mutant: an undecided \
             content differs in every model only from a closure (END, UNDEF or a cycle)",
            position.index,
            position.channel,
            decidedness(&baseline),
            decidedness(&mutant)
        ));
    }
    Ok(ObservedDifference {
        position,
        baseline,
        mutant,
    })
}

/// How an element is decided, for an error of [`observed_difference`].
fn decidedness(element: &Element) -> &'static str {
    match element {
        Element::Content(_) | Element::Evaluated(_) => "a content",
        Element::Undecided => "undecided",
        Element::End => "END",
        Element::Undefined => "UNDEF",
        Element::Cycle => "a cycle's silence",
    }
}

/// The element `index` of the channel `channel` of a capture run of the baseline for `test`
/// ([`observed_difference`]), with its digest bytes as the run recorded them.
fn capture_element(
    campaign: &Campaign<'_>,
    options: &RunOptions,
    test: &TestCase,
    channel: usize,
    index: usize,
) -> Result<(Element, Option<[u8; 8]>), String> {
    let baseline = campaign
        .validator
        .compile_baseline()
        .map_err(|_| "the baseline does not compile".to_owned())?;
    let mut runtime = Runtime::prepare_with(campaign, &baseline, options.backend_options(), true)
        .map_err(|_| "the baseline does not load".to_owned())?;
    runtime.modality = options.result_modality;
    runtime.stop = options.stop;
    let observing = observing(campaign, &baseline, options.observe, &mut runtime)
        .map_err(|failure| failure.to_string())?;
    let trusted = observing.trusted && runtime.exclusions.collections_trusted();
    // The baseline's request (`Runtime::execute_against` on the runtime that reads coverage):
    // its modality, work bound and stop; the guard outcomes and bindings it records do not move
    // the run.
    let run = ResultRun {
        modality: runtime.modality,
        max_work: options.baseline_max_work,
        guards: true,
        bindings: false,
    };
    let (execution, captured) = crate::observation::evaluating(options.observe, |evaluation| {
        let mut probe = ObservationProbe::capturing(
            &observing.resolved,
            &observing.shared,
            trusted,
            &test.initial_state,
            evaluation.within(),
            channel,
            index,
        );
        let request = RequestProbe {
            rules: probe.rules(),
            probe: &mut probe,
        };
        let (execution, _) = runtime.stop.execute_asking(
            &runtime.adapter,
            &mut runtime.backend,
            &mut runtime.tables,
            &test.id,
            &test.initial_state,
            campaign.budget,
            run,
            Some(request),
        );
        (execution, probe.captured())
    });
    execution.map_err(|failure| format!("the capture run failed: {failure:?}"))?;
    captured
        .ok_or_else(|| format!("the capture run did not reach the element {index} of its channel"))
}

/// Why the mutant whose runtime is `mutant` is not admitted under the observation `observing`,
/// read on the baseline whose declarations `admission` holds; `None` when it is admitted (module
/// [`crate::observation`]).
/// - `PointUnresolved`: a name of a point class labels no rewrite rule of the claim-free mutant
///   (the edit deleted the rule, made it an equation or dropped its label). Positions are named
///   by label, which is metadata, so no kill may rest on an edit of a label.
/// - `ObservationIncompatible`: the cells the declaration reads could hold a term that denotes
///   another value on the mutant than on the baseline: a sort or symbol those cells reach on
///   either side is declared by both otherwise ([`KoreSignature::incompatibility`]), a symbol they
///   reach that both declare is a free constructor on one side only (an `anywhere` rule or an
///   overload axiom heads it on the other), or the mutant does not trust its collection terms
///   where the baseline does. Every element is read as a value under the baseline's definition,
///   so where neither holds, a term that is a value there denotes the same value in both.
fn observation_refusal(
    observing: &Observing,
    admission: &MutantAdmission,
    mutant: &mut Runtime,
) -> Option<MutantScopeFailure> {
    match observing.declared.rules().unresolved(&mut mutant.backend) {
        Ok(unresolved) if unresolved.is_empty() => {}
        Ok(_) => return Some(MutantScopeFailure::PointUnresolved),
        Err(_) => return Some(MutantScopeFailure::Infrastructure),
    }
    let cells = observing.resolved.cells();
    let incompatible = || MutantScopeFailure::ObservationIncompatible;
    let (Some(baseline), Some(own)) = (&admission.signature, &mutant.signature) else {
        return Some(incompatible());
    };
    if !own
        .incompatibility(baseline, cells)
        .is_ok_and(|incompatibility| incompatibility.is_none())
    {
        return Some(incompatible());
    }
    if observing.trusted && !mutant.exclusions.collections_trusted() {
        return Some(incompatible());
    }
    let Ok(definition) = mutant.backend.select_definition(None) else {
        return Some(MutantScopeFailure::Infrastructure);
    };
    let (Ok(theirs), Ok(mine)) = (baseline.read_symbols(cells), own.read_symbols(cells)) else {
        return Some(incompatible());
    };
    let differs = theirs.union(&mine).any(|symbol| {
        let on = |side: &BackendDefinition| side.symbols().contains_key(symbol.as_str());
        on(&observing.shared)
            && on(&definition)
            && kink_native::feasibility::is_free_constructor(&observing.shared, symbol)
                != kink_native::feasibility::is_free_constructor(&definition, symbol)
    });
    differs.then(incompatible)
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
/// ([`kink_native::exclusion`]): it completed but is no evidence, as an unknown side. Under an
/// observation declaration, a run whose log did not only grow by appending is `OracleFailed`
/// (`log-not-appended`, [`crate::observation::BaselineRecord::refusal`]), and a prefix
/// program's sides are not read: it has no end, and its channels are compared up to their
/// horizons ([`crate::observation::BaselineRecord::prefix`]). A complete path of it that crashed
/// still meets each slot's crash policy, as a crashing side does
/// ([`crate::observation::BaselineRecord::crashed`]).
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
            SideRun::Failed(kind)
                if kind.exclusion().is_some() || *kind == ExecutionFailureKind::StopCondition =>
            {
                admission = BaselineAdmission::OracleFailed;
                continue;
            }
            SideRun::Failed(_) => return BaselineAdmission::Error,
        };
        let record = baseline_record(evidence);
        if record.is_some_and(|record| record.refusal.is_some()) {
            admission = BaselineAdmission::OracleFailed;
            continue;
        }
        // A prefix program has no end: its end slots compare nothing, and it is admitted for its
        // observation channels ([`crate::observation`]), under each slot's crash policy.
        if let Some(record) = record.filter(|record| record.prefix) {
            if record.crashed
                && test
                    .oracles
                    .iter()
                    .any(|declaration| declaration.crash_policy() == CrashPolicy::Reject)
            {
                admission = BaselineAdmission::OracleFailed;
            }
            continue;
        }
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
    /// The order the tests ran in when the caller chose it ([`run_campaign_multi_ordered`]).
    caller_order: Option<Vec<String>>,
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
#[allow(clippy::too_many_arguments)]
fn run_mutant(
    campaign: &Campaign<'_>,
    patch: &Patch,
    compiled_baseline: &ValidatedDefinition,
    paired: &BTreeMap<&str, PairedTest<'_>>,
    options: &CampaignOptions,
    admission: &MutantAdmission,
    observations: &mut BaselineObservations<'_>,
    first: Option<&mut FirstTests<'_>>,
) -> MutantExecution {
    // fz26 KINK-BASELINE-FINDINGS: no end of a baseline with a finding left is data, so no
    // comparison on it can kill, and the mutant is unknown before it compiles.
    let gated = match &admission.data {
        Ok(facts) if data_ends(facts) == DataEnds::None => Err(MutantRefusal::new(
            MutantScopeFailure::BaselineFindings,
            Withdrawal::default(),
        )),
        _ => prepare_mutant(
            campaign,
            patch,
            compiled_baseline,
            admission,
            options.run.stop.when().is_some() || !options.run.observe.is_none(),
        ),
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
                caller_order: None,
                recordings: Vec::new(),
            }
        }
        Ok((mut sides, claims)) => {
            sides.runtime.modality = options.run.result_modality;
            sides.runtime.one_sided = options.run.one_sided;
            sides.runtime.stop = options.run.stop;
            // The stop names the observation on this side too: a name that labels no rewrite
            // rule of the claim-free mutant leaves it undefined there, and the mutant is not run
            // without it.
            let failure = match resolve_stop(options.run.stop, &mut sides.runtime.backend) {
                Ok(unresolved) if unresolved.is_empty() => {
                    condition_incompatible(options.run.stop, admission, &sides.runtime)
                        .then_some(MutantScopeFailure::StopConditionIncompatible)
                }
                Ok(_) => Some(MutantScopeFailure::StopUnresolved),
                Err(_) => Some(MutantScopeFailure::Infrastructure),
            };
            // The observation names its positions on this side too, and reads its cells with the
            // baseline's declarations: a mutant on which either fails is not run under it.
            let failure = failure.or_else(|| {
                let observing = observations.runtime.observe.clone()?;
                let refusal = observation_refusal(&observing, admission, &mut sides.runtime);
                sides.runtime.observe = Some(observing);
                refusal
            });
            if let Some(failure) = failure {
                return MutantExecution {
                    tests: Vec::new(),
                    failure: Some(failure),
                    evidence: Vec::new(),
                    claims,
                    inconsistent_pairs: Vec::new(),
                    selection: None,
                    caller_order: None,
                    recordings: Vec::new(),
                };
            }
            let selection = mutant_selection(
                campaign,
                paired,
                &sides,
                patch,
                options.selection,
                observations,
            );
            let caller_order = first.map(|first| {
                let first = first(&sides.ground_witness);
                let mut order = Vec::with_capacity(campaign.tests.len());
                for runs_first in [true, false] {
                    order.extend(
                        campaign
                            .tests
                            .iter()
                            .filter(|test| first.contains(&test.id) == runs_first)
                            .map(|test| test.id.clone()),
                    );
                }
                order
            });
            let order = match (&selection, &caller_order) {
                (Some(selection), _) => selection.order.clone(),
                (None, Some(order)) => order.clone(),
                (None, None) => campaign.tests.iter().map(|test| test.id.clone()).collect(),
            };
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
                caller_order,
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
/// the claim-free mutant is built is the mutant side's (`Infrastructure`). The runtime holds the
/// mutant's declarations only when `declarations` (a stop condition's admission or an observation
/// declaration's reads them).
fn prepare_mutant(
    campaign: &Campaign<'_>,
    patch: &Patch,
    compiled_baseline: &ValidatedDefinition,
    admission: &MutantAdmission,
    declarations: bool,
) -> Result<(MutantSides, Withdrawal), Box<MutantRefusal>> {
    let ClaimFreeMutant {
        side,
        claims,
        data,
        ground_witness,
        loaded,
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
    let ground_witness = ground_witness.unwrap_or_else(|| edit.clone());
    // The claim-free mutant's backend was loaded once, for its facts, and runs its tests; its
    // facts judge its ends and, in each pair, the baseline's (KINK-OVERLOAD-VALUE).
    let mut runtime = Runtime::from_loaded(campaign, &side, loaded, declarations)
        .map_err(|_| fail(MutantScopeFailure::Infrastructure))?;
    runtime.data = Some(data);
    Ok((
        MutantSides {
            runtime,
            edit,
            ground_witness,
        },
        claims,
    ))
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
    /// The mutant's edit as a ground test witnesses it, when that is not the claim-free side's
    /// ([`CompiledEdit::for_ground_tests`]): the mutant as written against the baseline, when
    /// only definedness claims were withdrawn from it.
    pub ground_witness: Option<CompiledEdit>,
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
/// as `MutantFindings` (unknown); when the check read no head, every finding is compared. A
/// mutant whose ends are not data while the baseline's are (kink-native `data::data_ends`) is
/// `MutantFindings` too. Whether the baseline's own findings leave any end data is the runner's
/// question, not this function's (`BaselineFindings`).
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
    // The mutant as written is read once more before the claim-free side replaces it: for the
    // edit a ground test witnesses ([`CompiledEdit::for_ground_tests`]).
    let (side, ground_witness) = match claims.patch() {
        None => (side, None),
        Some(withdrawing) => match validator.validate(withdrawing) {
            Ok(withdrawn) => {
                let witness = CompiledEdit::for_ground_tests(compiled_baseline, &side, &claims);
                (withdrawn, witness)
            }
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
    let loaded = LoadedSide::load(&side, &admission.module, admission.solver)
        .map_err(|_| infrastructure(&claims))?;
    let baseline_data = admission
        .data
        .as_ref()
        .map_err(|_| infrastructure(&claims))?;
    let data = DataFacts::of(&loaded.selected, &admission.assume_joined);
    on_stage(MutantStage::Consistency);
    let admitted = match &admission.equations {
        Ok(equations) => kink_native::consistency::admit_mutant_with(
            equations,
            baseline_data,
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
    // fz26 KINK-BASELINE-FINDINGS review S1: when the gate read nothing (no checked head), every
    // finding is compared, not only those the gate would read for no head; and wherever the
    // baseline has data the mutant must have it too (part 3: both sides' ends are data).
    let read_nothing = effect.checked.as_ref().is_some_and(BTreeSet::is_empty);
    let differs = if read_nothing {
        data.differs(baseline_data)
    } else {
        data.differs_outside(baseline_data, effect.checked.as_ref())
    };
    let lost = data_ends(baseline_data) != DataEnds::None && data_ends(&data) == DataEnds::None;
    if differs || lost {
        return Err(MutantRefusal::new(
            MutantScopeFailure::MutantFindings,
            claims,
        ));
    }
    Ok(ClaimFreeMutant {
        side,
        claims,
        data,
        ground_witness,
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
    /// The solver options of every mutant load's backend, which the mutant's runs execute on
    /// (the campaign's, [`RunOptions::backend_options`]).
    solver: BackendOptions,
    assume_joined: Vec<String>,
    data: Result<DataFacts, String>,
    /// The baseline's declarations, which a mutant's read signature is compared with under a
    /// stop condition ([`crate::condition`]); `None` when the campaign has none, and on an
    /// admission [`Self::new`] builds, which checks claim-free mutants and runs none, so that a
    /// mutant run under a condition against it is never admitted.
    signature: Option<KoreSignature>,
}

impl MutantAdmission {
    /// The admission of every mutant of `baseline` (a validator's baseline), whose compile is
    /// `compiled`, each loaded for `module` (KORE-encoded, the campaign's), reading the findings
    /// `assume_joined` names as assumed: its claim support, its compiled equations, which every
    /// mutant's are read against, and its data facts, which every mutant's are compared with
    /// (computed here on `compiled` loaded on kink's route). A baseline whose equations do not
    /// internalize again leaves every mutant unchecked (`InconsistentMutant`); one that does not
    /// load leaves every mutant `Infrastructure`. Every mutant loads with kink's solver options
    /// ([`kink_native::BACKEND_OPTIONS`]) unless [`Self::with_solver`] gives others; the data
    /// facts read the loaded definition only, which no solver option changes (a load runs no
    /// solver operation).
    #[must_use]
    pub fn new(
        baseline: &kink_patch::Baseline,
        compiled: &ValidatedDefinition,
        module: &str,
        assume_joined: &[String],
    ) -> Self {
        let loaded = LoadedSide::load(compiled, module, kink_native::BACKEND_OPTIONS);
        let data = loaded
            .map(|loaded| DataFacts::of(&loaded.selected, assume_joined))
            .map_err(|_| format!("the baseline does not load for {module}"));
        Self {
            support: ClaimSupport::new(baseline),
            equations: CompiledEquations::of(compiled),
            module: module.to_owned(),
            solver: kink_native::BACKEND_OPTIONS,
            assume_joined: assume_joined.to_vec(),
            data,
            signature: None,
        }
    }

    /// This admission with `solver` as the solver options of every mutant load.
    #[must_use]
    pub const fn with_solver(mut self, solver: BackendOptions) -> Self {
        self.solver = solver;
        self
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

/// A prepared mutant: the claim-free definition every test runs on, its compiled edit, and that
/// edit as a ground test witnesses it ([`CompiledEdit::for_ground_tests`]), which a caller's
/// order reads ([`FirstTests`]).
struct MutantSides {
    runtime: Runtime,
    edit: CompiledEdit,
    ground_witness: CompiledEdit,
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
            None => sides.runtime.run_compared(
                campaign,
                test,
                pair.mutant_max_work,
                baseline_record(baseline),
            ),
        };
        if let Some(recording) = &cache.recording {
            recordings.push(recording.clone());
        }
        // Initialize facts on both paths, including each newly prepared mutant backend. Facts
        // the backend refused are not kept ([`Runtime::facts`]): the pair's pattern slots are then
        // unknown for a reason that need not be a fact of the run ([`RunNotes::unjudged`]), and
        // its evidence is not kept for reuse, so a later call compares the signatures again.
        let compared_signatures = observations.runtime.facts().and_then(|baseline_facts| {
            sides
                .runtime
                .facts()
                .map(|mutant_facts| baseline_facts.signature == mutant_facts.signature)
        });
        let facts_refused = compared_signatures.is_err();
        if facts_refused && has_pattern_slot(test) {
            mutant.notes.unjudged = true;
        }
        let signatures_match = compared_signatures.unwrap_or(false);
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
            && !facts_refused
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
        // fz26 KINK-OVERLOAD-VALUE: every end compared below is data under both definitions.
        let mut one_sided = cache.one_sided;
        judge_across(
            test,
            &mut paired_baseline,
            &mut mutant,
            &mut one_sided,
            observations.runtime,
            &mut sides.runtime,
        );
        // CF-16: the kept one-sided terminals, for a reader of the kill (kink-flow `evidence`).
        mutant.one_sided_ends = one_sided
            .iter()
            .map(|terminal| terminal.state.clone())
            .collect();
        // The observation slot, after the end slots ([`crate::observation::judge`]), on the
        // mutant's sides as the pair judged them.
        let observed = sides.runtime.observe.is_some().then(|| {
            let record = baseline_record(&paired_baseline);
            let mutant_sides = match &mutant.run {
                SideRun::Sides { sides } => Some(sides.clone()),
                SideRun::Failed(_) => None,
            };
            let undefined = mutant.undefined_steps && mutant.ends.is_empty();
            let verdict = match (record, &mut mutant.notes.observation) {
                (Some(record), Some(Observation::Compared(comparison))) => {
                    let verdict = crate::observation::judge(
                        record,
                        comparison,
                        mutant_sides.as_deref(),
                        undefined,
                    );
                    comparison.verdict = Some(verdict.clone());
                    verdict.outcome
                }
                _ => OracleOutcome::Unknown,
            };
            (verdict, record.is_some_and(|record| record.prefix))
        });
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
                        // A prefix program has no end: within its horizon its end slots have
                        // nothing to compare, and its channels decide the test.
                        if observed.is_some_and(|(_, prefix)| prefix) {
                            OracleOutcome::Agree
                        } else if matches!(declaration.projection(), Projection::Pattern { .. })
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
                                        &one_sided,
                                    ) =>
                                {
                                    OracleOutcome::Distinguish
                                }
                                outcome => outcome,
                            }
                        }
                    })
                    .chain(observed.map(|(outcome, _)| outcome))
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

/// The baseline's record of its channels in its run's evidence `evidence`, when it has one.
fn baseline_record(evidence: &TestEvidence) -> Option<&BaselineRecord> {
    match &evidence.notes.observation {
        Some(Observation::Recorded(record)) => Some(record),
        _ => None,
    }
}

/// The classifier-independent part of one run ([`Runtime::execute`]): the adapter's execution,
/// the side a pattern slot gets when stepping failed, and the run cache.
struct Executed {
    execution: Result<AdaptedExecution, ExecutionAdapterFailure>,
    pattern_failure: OracleSide,
    cache: RunCache,
    /// The last arrival the stop's condition was left undecided at, with its reason, when the
    /// run asked a condition and it was ([`Stop::with_when`]).
    undecided: Option<String>,
    /// What the run's observation probe built of its channels ([`RunOptions::observe`]), and
    /// whether it compared them with a baseline's record (a mutant's run); `None` for a run
    /// without a declaration.
    observed: Option<(Trace, bool)>,
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
        StepRunFailure::AmbiguousRule(_) | StepRunFailure::Unobservable => OracleSide::Unknown,
    }
}

/// Judges the compared ends of one pair under the other side's definition (fz26
/// KINK-OVERLOAD-VALUE; the own side's judgement is the run's, [`Runtime::judge_with`] and
/// [`Runtime::step_sides`]). Each definition reads the ends with its own theory, and the two may
/// differ on any symbol: a mutant can make a baseline constructor an `anywhere` head (`c(1) => d
/// [anywhere]`, under which the baseline's end `c(1)` and the mutant's `d` are one value), or
/// add an overload member that lowers a baseline normal form. Two different ends differ in each
/// definition's initial model only when both are data in both (k-rust-backend `data_term`, "Two
/// definitions"), so before the slots of `test` are compared:
/// - the baseline's terminals ([`TestEvidence::ends`]) must be data under the mutant's definition
///   and the mutant's under the baseline's: each must be its own terminal value there
///   ([`ObservationDecider::terminal_value`] with that definition's collection trust and
///   [`data_ends`] of its facts: a free-constructor, injection and domain-value check, and k-rust's
///   `is_data` on each outermost overload application). A failure makes every state slot of that
///   side `Unknown`, for this pair only;
/// - every binding of a pattern side must be definition-independent under the mutant's definition
///   (the baseline's own bindings and the mutant's were judged under the baseline's by
///   [`Runtime::step_sides`], whose shared definition is the baseline's); a failure makes that
///   slot `Unknown`;
/// - a one-sided terminal of the mutant run must be data under the baseline's definition, or it
///   is dropped (it can then not distinguish);
/// - every term a pattern slot's relation decisions read ([`TestEvidence::payloads`], recorded by
///   [`ReadTerms`]) must be definition-independent under the other side's definition: a slot's
///   `Match` or `NoMatch` is decided from relations between that side's payloads in that side's
///   theory alone, so a failure makes that slot `Unknown` (review S1).
///
/// A value-holding state slot whose side has no ends is `Unknown` (review N2): the ends are the
/// terminals it was projected from, and a producer that omits them cannot be judged. A side whose
/// every complete path is an undefined step has no ends and is judged: each of its state slots is
/// the empty set ([`TestEvidence::undefined_steps`], kink27 R1-UNDEF).
///
/// A side with no data facts (`None`), or with a finding left ([`DataEnds::None`]), makes every
/// end judged under it not data. A failure to reach a definition does too. A host's refusal of a
/// stack one of these judgements needed fails the mutant run as infrastructure instead.
///
/// Each slot made unknown is recorded in the mutant's evidence ([`RunNotes::across`]), with whose
/// end it is and why (fz26 KINK-CAUSE-SUBTERM), for the reader's cause; nothing compares it.
fn judge_across(
    test: &TestCase,
    baseline: &mut TestEvidence,
    mutant: &mut TestEvidence,
    one_sided: &mut Vec<ExecutionTerminal>,
    baseline_runtime: &mut Runtime,
    mutant_runtime: &mut Runtime,
) {
    // The terminals a side's state slots compare: none unless some state slot has a value.
    let compared = |evidence: &TestEvidence| match &evidence.run {
        SideRun::Sides { sides }
            if test.oracles.iter().zip(sides).any(|(declaration, side)| {
                matches!(declaration.projection(), Projection::State(_))
                    && matches!(side, OracleSide::Normal(_) | OracleSide::SemanticCrash(_))
            }) =>
        {
            evidence.ends.iter().cloned().collect()
        }
        _ => Vec::new(),
    };
    let bindings = |evidence: &TestEvidence| match &evidence.run {
        SideRun::Sides { sides } => sides
            .iter()
            .filter_map(|side| match side {
                OracleSide::Normal(OracleValue::Pattern(PatternValue::Match {
                    bindings: Some(witnesses),
                })) => Some(witnesses),
                _ => None,
            })
            .flatten()
            .flatten()
            .map(|binding| binding.term.clone())
            .collect::<Vec<_>>(),
        SideRun::Failed(_) => Vec::new(),
    };
    // The terms the relation decisions of a side's value-holding pattern slots read.
    let payloads = |evidence: &TestEvidence| match &evidence.run {
        SideRun::Sides { sides } => test
            .oracles
            .iter()
            .zip(sides)
            .enumerate()
            .filter(|(_, (declaration, side))| {
                matches!(declaration.projection(), Projection::Pattern { .. })
                    && matches!(side, OracleSide::Normal(_))
            })
            .flat_map(|(index, _)| evidence.payloads.get(&index).into_iter().flatten().cloned())
            .collect::<Vec<_>>(),
        SideRun::Failed(_) => Vec::new(),
    };
    // Under the mutant's definition: the baseline's terminals and payloads, and both sides'
    // bindings.
    let (under_mutant, undecided_under_mutant, unjudged_under_mutant) = mutant_runtime.judge_ends(
        test,
        &compared(baseline),
        &[bindings(baseline), bindings(mutant), payloads(baseline)].concat(),
    );
    // Under the baseline's definition: the mutant's terminals, then its one-sided terminals.
    let mutant_ends = compared(mutant);
    let terminals = mutant_ends.len();
    let (under_baseline, undecided_under_baseline, unjudged_under_baseline) = baseline_runtime
        .judge_ends(
            test,
            &mutant_ends
                .into_iter()
                .chain(one_sided.iter().map(|terminal| terminal.state.clone()))
                .collect::<Vec<_>>(),
            &payloads(mutant),
        );
    // A host's refusal of a stack a judgement under either definition needed is no answer about
    // the ends: the pair's mutant run fails as infrastructure, which kink-flow's outcome cache
    // never stores. Both judgements run first, so that both backends' solver state evolves as
    // without the refusal.
    // Both judgements are kink's questions about the mutant's run.
    mutant.notes.decider_smt_unknowns = mutant
        .notes
        .decider_smt_unknowns
        .saturating_add(undecided_under_mutant)
        .saturating_add(undecided_under_baseline);
    // A judgement the backend refused leaves the ends it judges not data, for a reason that need
    // not be a fact of the run ([`RunNotes::unjudged`]).
    mutant.notes.unjudged |= unjudged_under_mutant || unjudged_under_baseline;
    let (Ok(under_mutant), Ok(under_baseline)) = (under_mutant, under_baseline) else {
        mutant.run = SideRun::Failed(ExecutionFailureKind::Infrastructure);
        mutant.payloads.clear();
        mutant.notes.across = Vec::new();
        one_sided.clear();
        return;
    };
    let (mutant_data, one_sided_data) = under_baseline.terminals.split_at(terminals);
    let mut one_sided_data = one_sided_data.iter().copied();
    one_sided.retain(|_| one_sided_data.next().unwrap_or(false));
    let mut across = Vec::new();
    for (evidence, data, causes, other, baseline_end) in [
        (
            &mut *baseline,
            under_mutant.terminals.as_slice(),
            under_mutant.terminal_causes.as_slice(),
            &under_mutant,
            true,
        ),
        (
            &mut *mutant,
            mutant_data,
            &under_baseline.terminal_causes[..terminals],
            &under_baseline,
            false,
        ),
    ] {
        let SideRun::Sides { sides } = &mut evidence.run else {
            continue;
        };
        // A value-holding state slot with no ends to judge fails closed (review N2), unless every
        // complete path of its run is an undefined step, which is no end (kink27 R1-UNDEF).
        let states_data = (!evidence.ends.is_empty() || evidence.undefined_steps)
            && data.iter().all(|data| *data);
        for (index, (declaration, side)) in test.oracles.iter().zip(sides).enumerate() {
            // A pattern value whose relation decisions read a term that is not data under the
            // other side's definition (review S1).
            let payload_refused = (matches!(declaration.projection(), Projection::Pattern { .. })
                && matches!(side, OracleSide::Normal(_)))
            .then(|| evidence.payloads.get(&index))
            .flatten()
            .and_then(|read| read.iter().find(|term| !other.independent.contains(term)));
            // Why the slot is refused, for the reader's cause (fz26 KINK-CAUSE-SUBTERM).
            let refused = match payload_refused {
                Some(term) => Some((CrossEnd::Payload, other.cause_of(term))),
                None => match (declaration.projection(), &*side) {
                    (
                        Projection::State(_),
                        OracleSide::Normal(_) | OracleSide::SemanticCrash(_),
                    ) if !states_data => Some((
                        CrossEnd::Terminal,
                        if evidence.ends.is_empty() {
                            CrossCause::NoEnds
                        } else {
                            causes
                                .iter()
                                .flatten()
                                .next()
                                .cloned()
                                .unwrap_or(CrossCause::NotData(None))
                        },
                    )),
                    (
                        Projection::Pattern { .. },
                        OracleSide::Normal(OracleValue::Pattern(PatternValue::Match {
                            bindings: Some(witnesses),
                        })),
                    ) => witnesses
                        .iter()
                        .flatten()
                        .find(|binding| !under_mutant.independent.contains(&binding.term))
                        .map(|binding| (CrossEnd::Binding, under_mutant.cause_of(&binding.term))),
                    _ => None,
                },
            };
            if let Some((end, cause)) = refused {
                *side = OracleSide::Unknown;
                across.push(CrossRefusal {
                    slot: index,
                    baseline_end,
                    end,
                    cause,
                });
            }
        }
    }
    mutant.notes.across = across;
}

/// What one definition says of the ends of the other side of a pair ([`Runtime::judge_ends`]).
struct EndJudgement {
    /// For each terminal judged, in order, whether it is data there.
    terminals: Vec<bool>,
    /// The binding terms judged definition-independent there.
    independent: Vec<Pattern>,
    /// For each terminal judged, in order, why it is not data there (`None` when it is).
    terminal_causes: Vec<Option<CrossCause>>,
    /// Each binding (or payload) term judged not definition-independent there, and why.
    binding_causes: Vec<(Pattern, CrossCause)>,
}

impl EndJudgement {
    /// Why `term`, a binding or payload judged here, is not definition-independent here.
    fn cause_of(&self, term: &Pattern) -> CrossCause {
        self.binding_causes
            .iter()
            .find(|(judged, _)| judged == term)
            .map_or(CrossCause::NotData(None), |(_, cause)| cause.clone())
    }
}

/// A slot of one pair that [`judge_across`] made unknown, because an end, binding or payload of
/// one side is not data under the other side's definition, or a state value has no ends to judge
/// (fz26 KINK-CAUSE-SUBTERM, KINK-OVERLOAD-VALUE review N4): the side's run did end in a value of
/// its own definition. Kept in the mutant's evidence of the pair ([`RunNotes::across`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CrossRefusal {
    /// The slot's index in the test's oracles.
    pub slot: usize,
    /// Whose end it is: the baseline's or the mutant's.
    pub baseline_end: bool,
    /// What of the side was judged.
    pub end: CrossEnd,
    /// Why the first such end of the slot is not data there.
    pub cause: CrossCause,
}

/// What of a side [`judge_across`] refused ([`CrossRefusal`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CrossEnd {
    /// A terminal a state slot is projected from ([`TestEvidence::ends`]), judged under the
    /// other side's definition.
    Terminal,
    /// A binding of a pattern slot's match, judged under the mutant's definition (both sides'
    /// bindings are).
    Binding,
    /// A term a pattern slot's relation decisions read ([`TestEvidence::payloads`]), judged under
    /// the other side's definition.
    Payload,
}

/// Why an end is not data under the other side's definition ([`CrossRefusal`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CrossCause {
    /// A value-holding state slot whose side has no ends to judge (review N2): refused closed.
    NoEnds,
    /// That definition admits no end as data: it has no data facts, or a finding of its full
    /// check is left, or it could not be reached ([`data_ends`] gives [`DataEnds::None`]).
    NoData,
    /// The end is not its own terminal value there (a binding: not definition-independent there):
    /// the first node, in pre-order, that fails its own test there
    /// ([`ObservationDecider::first_non_value`], [`ObservationDecider::first_dependent`]), or
    /// `None` when every node passes and the end's canonical form there differs from it.
    NotData(Option<Box<NonValue>>),
}

/// The side of one pattern slot ([`Runtime::step_sides`]) and the terms its relation decisions
/// read ([`TestEvidence::payloads`]).
type PatternSide = (OracleSide, BTreeSet<Pattern>);

/// The pattern-slot sides of one run ([`Runtime::step_sides`]), or the host's refusal of a stack
/// that judging them needed, and the undecided solver answers the judgement took.
struct StepSides {
    sides: Result<Vec<PatternSide>, SegmentRefused>,
    /// The decider's [`ObservationDecider::smt_unknowns`] ([`RunNotes::decider_smt_unknowns`]).
    smt_unknowns: usize,
    /// Whether the backend refused the judgement, so every pattern side is `Unknown`, or the
    /// judgement met a stack stop ([`judgement`]): either for a reason that need not be a fact of
    /// the run ([`RunNotes::unjudged`]).
    unjudged: bool,
}

/// `backend.with_solver(None, operation)`: the solver operation of a judgement kink makes of a
/// run outside it (the run's decider, its pattern slots, a pair's judgement of ends), whose
/// refusal marks the run unjudged ([`RunNotes::unjudged`]). A unit test can make it refuse
/// (`tests::REFUSE_JUDGEMENTS`), as a refused stack segment or solver would.
///
/// `stack_stopped` is set when the operation met a stop for lack of native stack, one a site
/// dismissed included, read from the operation's record (`stop::with_operation_record`, which
/// counts every such stop inside, also in an operation on another backend that `operation`
/// runs); that too marks the run unjudged. A unit test can make it report one
/// (`tests::STACK_STOP_JUDGEMENTS`).
fn judgement<T>(
    backend: &mut Backend,
    stack_stopped: &mut bool,
    operation: impl FnOnce(
        &k_rust::k_rust_backend::definition::BackendDefinition,
        &dyn k_rust::k_rust_backend::smt::SmtSolver,
    ) -> Result<T, k_rust::backend::BackendError>,
) -> Result<T, k_rust::backend::BackendError> {
    #[cfg(test)]
    if tests::REFUSE_JUDGEMENTS.with(std::cell::Cell::get) {
        return Err(k_rust::backend::BackendError::new(
            "the backend refused the operation (a unit test's refusal)",
        ));
    }
    let (result, record) = k_rust::k_rust_backend::stop::with_operation_record(|| {
        backend.with_solver(None, operation)
    });
    *stack_stopped |= record.stack_stops > 0;
    #[cfg(test)]
    {
        *stack_stopped |= tests::STACK_STOP_JUDGEMENTS.with(std::cell::Cell::get);
    }
    result
}

/// Whether `test` has a pattern slot, whose side the pattern judgement gives
/// ([`replace_patterns`]).
fn has_pattern_slot(test: &TestCase) -> bool {
    test.oracles
        .iter()
        .any(|declaration| matches!(declaration.projection(), Projection::Pattern { .. }))
}

/// `evidence` with its pattern slots replaced by `patterns`, or each made `Unknown` without them
/// (`None`). A host's refusal of a stack the judgement of the pattern slots needed is a fact about
/// the host, not about the run, so it fails the run as infrastructure instead of becoming a side.
fn replace_patterns(test: &TestCase, evidence: &mut TestEvidence, patterns: Option<&StepSides>) {
    if let Some(patterns) = patterns {
        evidence.notes.decider_smt_unknowns = evidence
            .notes
            .decider_smt_unknowns
            .saturating_add(patterns.smt_unknowns);
        evidence.notes.unjudged |= patterns.unjudged;
    }
    let patterns = match patterns.map(|patterns| &patterns.sides) {
        Some(Err(_)) => {
            if matches!(evidence.run, SideRun::Sides { .. }) {
                evidence.run = SideRun::Failed(ExecutionFailureKind::Infrastructure);
                evidence.payloads.clear();
            }
            return;
        }
        Some(Ok(patterns)) => Some(patterns.as_slice()),
        None => None,
    };
    if let SideRun::Sides { sides } = &mut evidence.run {
        for (index, (declaration, side)) in test.oracles.iter().zip(sides).enumerate() {
            if matches!(declaration.projection(), Projection::Pattern { .. }) {
                match patterns {
                    Some(patterns) => {
                        side.clone_from(&patterns[index].0);
                        evidence.payloads.insert(index, patterns[index].1.clone());
                    }
                    None => {
                        *side = OracleSide::Unknown;
                        evidence.payloads.remove(&index);
                    }
                }
            }
        }
    }
}

/// The relation decider of one pattern slot's evaluation, recording the terms its decisions read
/// (fz26 KINK-OVERLOAD-VALUE review S1). A pattern slot's `Match` or `NoMatch` rests on the
/// relations the side's own decider decides between its event payloads and bound values, in that
/// side's theory (re-pin A-12): with `c(1) => d` made `[anywhere]` in a mutant, the baseline's
/// payloads `c(1)` and `d` are unequal under the baseline and one value under the mutant. So every
/// term such a decision reads must be data under the other side's definition too
/// ([`judge_across`]), as bindings and ends are. Recorded: the two terms and the assumed relations
/// of every relation decided other than `Indeterminate` and other than `Equal` by syntactic
/// identity (identical terms are equal in every theory), with the relations an `EqualIf` adds; and
/// the assumptions of every feasibility decided `Sat` or `Unsat`.
struct ReadTerms<'d> {
    inner: &'d dyn RelationDecider,
    read: std::cell::RefCell<BTreeSet<Pattern>>,
}

impl<'d> ReadTerms<'d> {
    fn new(inner: &'d dyn RelationDecider) -> Self {
        Self {
            inner,
            read: std::cell::RefCell::new(BTreeSet::new()),
        }
    }

    fn record<'t>(&self, terms: impl IntoIterator<Item = &'t Pattern>) {
        self.read.borrow_mut().extend(terms.into_iter().cloned());
    }

    fn read(self) -> BTreeSet<Pattern> {
        self.read.into_inner()
    }
}

fn relation_terms(relations: &[TermRelation]) -> impl Iterator<Item = &Pattern> {
    relations
        .iter()
        .flat_map(|relation| [&relation.left, &relation.right])
}

impl RelationDecider for ReadTerms<'_> {
    fn relate(
        &self,
        path: &PathInput,
        assumed: &[TermRelation],
        left: &Pattern,
        right: &Pattern,
    ) -> RelationDecision {
        let decision = self.inner.relate(path, assumed, left, right);
        match &decision {
            RelationDecision::Indeterminate => {}
            RelationDecision::Equal if left == right => {}
            RelationDecision::EqualIf(added) => {
                self.record([left, right]);
                self.record(relation_terms(assumed));
                self.record(relation_terms(added));
            }
            RelationDecision::Equal | RelationDecision::Unequal => {
                self.record([left, right]);
                self.record(relation_terms(assumed));
            }
        }
        decision
    }

    fn feasible(&self, path: &PathInput, assumptions: &[TermRelation]) -> Feasibility {
        let feasibility = self.inner.feasible(path, assumptions);
        if feasibility != Feasibility::Unknown {
            self.record(relation_terms(assumptions));
        }
        feasibility
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
    /// The tables `backend`'s result runs read from its definition, built on the first
    /// ([`DefinitionTables`]): a function of the definition, so one per backend.
    tables: DefinitionTables,
    context: EvaluationContext,
    /// The definition's facts once computed ([`Runtime::facts`]; a refusal is not kept).
    facts: Option<DefinitionFacts>,
    /// The side's rule authors when its runs record coverage (the baseline only).
    coverage: Option<RuleAuthors>,
    /// The modality of the side's result runs ([`RunOptions::result_modality`]).
    modality: ResultModality,
    /// Whether the side's runs collect one-sided evidence ([`RunOptions::one_sided`]; a mutant's
    /// only).
    one_sided: OneSided,
    /// Where the side's result runs end besides their own end ([`RunOptions::stop`]), resolved on
    /// the side's definition before it runs anything ([`resolve_stop`]).
    stop: Stop,
    /// The `max_work` of the side's result runs a [`BaselineSession`] makes
    /// ([`RunOptions::baseline_max_work`]; the baseline's only, a mutant's runs take
    /// [`WorkBudget`]).
    baseline_max_work: Option<u64>,
    /// What the side's definition contributes to the exclusions of each of its runs, read from
    /// its compiled KORE and from the definition its backend selected for the default module
    /// (the only module a request names), on the thread that runs it (re-pin R0b).
    exclusions: DefinitionExclusions,
    /// The side's data facts (its full critical-pair check, [`DataFacts`]) on the definition its
    /// backend selected: the baseline's (the session's), or the claim-free mutant's. They say
    /// which ends are data under this side's definition ([`data_ends`]), for its own runs and for
    /// the other side's ends of a pair ([`judge_across`]); `None` when they are not known, which
    /// admits no overload application and makes every end of the other side not data here.
    data: Option<DataFacts>,
    /// The KORE symbols declared `function` without a hook: the symbols equations define, whose
    /// application left in a leaf's state is one no equation reduces (a run's [`LeafCensus`]).
    functions: BTreeSet<String>,
    /// The solver options of `backend` ([`LoadedSide::solver`]).
    solver: BackendOptions,
    /// The declarations a stop condition's read signature is read from
    /// ([`crate::condition`], "Reading a mutant's cells"); `None` on a side loaded for a
    /// campaign without a stop condition or an observation declaration.
    signature: Option<KoreSignature>,
    /// The campaign's observation declaration as the side's result runs observe it
    /// ([`RunOptions::observe`]); `None` without one.
    observe: Option<Arc<Observing>>,
}

/// An observation declaration as every side's runs observe it: resolved on the baseline
/// ([`Observe::resolve`]), with the baseline's definition, under which every element's value is
/// read on every side, and whether that definition trusts its collection terms.
struct Observing {
    declared: Observe,
    resolved: Resolved,
    shared: Arc<BackendDefinition>,
    trusted: bool,
}

/// One load of a compiled side on kink's route: its parsed KORE, the backend built from it for a
/// module, and the definition that backend selected for it (loaded, its load counts and value
/// claims final; findings A-08, C-10).
struct LoadedSide {
    parsed: k_rust::kore::ast::Definition,
    backend: Backend,
    selected: std::sync::Arc<k_rust::k_rust_backend::definition::BackendDefinition>,
    /// The solver options `backend` was built with.
    solver: BackendOptions,
}

impl LoadedSide {
    fn load(
        side: &ValidatedDefinition,
        module: &str,
        solver: BackendOptions,
    ) -> Result<Self, Preparation> {
        let parsed = parse_definition(&side.artifacts().definition_kore)
            .map_err(|_| Preparation::Infrastructure)?;
        let mut backend = Backend::from_definition(parsed.clone(), module, solver)
            .map_err(|_| Preparation::Infrastructure)?;
        // Selecting the default module loads it if the backend has not yet.
        let selected = backend
            .select_definition(None)
            .map_err(|_| Preparation::Infrastructure)?;
        Ok(Self {
            parsed,
            backend,
            selected,
            solver,
        })
    }
}

impl Runtime {
    /// Parses the side's KORE once for its symbol sorts and event-free backend adapter.
    /// [`Self::prepare_with`] with kink's solver options (tests only: every campaign call names
    /// its options).
    #[cfg(test)]
    fn prepare(campaign: &Campaign<'_>, side: &ValidatedDefinition) -> Result<Self, Preparation> {
        Self::prepare_with(campaign, side, kink_native::BACKEND_OPTIONS, false)
    }

    /// The runtime of `side`, loaded for the campaign's module on a backend with the solver
    /// options `solver`, with its declarations when `signature` ([`Self::from_loaded`]).
    fn prepare_with(
        campaign: &Campaign<'_>,
        side: &ValidatedDefinition,
        solver: BackendOptions,
        signature: bool,
    ) -> Result<Self, Preparation> {
        stage_log::note(campaign, stage_log::Stage::Backend);
        let loaded = LoadedSide::load(side, campaign.module, solver)?;
        Self::from_loaded(campaign, side, loaded, signature)
    }

    /// The runtime of `side` on its load `loaded` ([`LoadedSide::load`] for the campaign's
    /// module). Its declarations, which only a stop condition reads (its `signature`),
    /// are read from the load when `signature`, and not otherwise.
    fn from_loaded(
        campaign: &Campaign<'_>,
        side: &ValidatedDefinition,
        loaded: LoadedSide,
        signature: bool,
    ) -> Result<Self, Preparation> {
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
        let LoadedSide {
            parsed,
            backend,
            selected,
            solver,
        } = loaded;
        let symbol_sorts = SymbolSorts::from_definition(&parsed);
        let signature = signature.then(|| KoreSignature::of(&parsed));
        let functions = parsed
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
            .filter_map(|sentence| match sentence {
                k_rust::kore::ast::Sentence::SymbolDeclaration {
                    hooked,
                    symbol,
                    attributes,
                    ..
                } if !hooked
                    && attributes.has(k_rust::names::KoreAttribute::Function)
                    && !attributes.has(k_rust::names::KoreAttribute::Hook) =>
                {
                    Some(symbol.name.clone())
                }
                _ => None,
            })
            .collect();
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
            tables: DefinitionTables::new(),
            context,
            facts: None,
            coverage: None,
            modality: ResultModality::default(),
            one_sided: OneSided::Off,
            stop: Stop::NONE,
            baseline_max_work: None,
            exclusions,
            data: None,
            functions,
            solver,
            signature,
            observe: None,
        })
    }

    /// The definition's facts, computed once and kept. A refusal is not kept: the backend's
    /// refusal of the operation (`Backend::with_solver`) need not be a fact of the definition, so
    /// the next call asks again.
    fn facts(&mut self) -> Result<DefinitionFacts, String> {
        if let Some(facts) = &self.facts {
            return Ok(facts.clone());
        }
        #[cfg(test)]
        if tests::REFUSE_JUDGEMENTS.with(std::cell::Cell::get) {
            return Err("the backend refused the operation (a unit test's refusal)".into());
        }
        let facts =
            definition_facts(&mut self.backend).map_err(|error| error.message().to_owned())?;
        self.facts = Some(facts.clone());
        Ok(facts)
    }

    /// [`Runtime::run_bounded`] without a work budget (tests only: every campaign run names its
    /// bound).
    #[cfg(test)]
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
        let (evidence, executed) = self.run_keeping(campaign, test, max_work, None);
        (evidence, executed.cache)
    }

    /// [`Runtime::run_bounded`] of a mutant's run, whose observation probe compares its channels
    /// with the baseline's record `against` ([`RunOptions::observe`]).
    fn run_compared(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        max_work: Option<u64>,
        against: Option<&BaselineRecord>,
    ) -> (TestEvidence, RunCache) {
        let (evidence, executed) = self.run_keeping(campaign, test, max_work, against);
        (evidence, executed.cache)
    }

    /// [`Runtime::run_bounded`], also returning the classifier-independent part of the run (the
    /// execution and its run cache), which a [`BaselineSession`] stores.
    fn run_keeping(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        max_work: Option<u64>,
        against: Option<&BaselineRecord>,
    ) -> (TestEvidence, Executed) {
        let started = Instant::now();
        let mut executed = self.execute_against(campaign, test, max_work, against);
        let (evidence, one_sided) = self.judge_with(campaign, test, &executed, None);
        executed.cache.one_sided = one_sided;
        // Recording only (flow F-13): read from the execution the run already has.
        executed.cache.recording = Some(RunRecording {
            test_id: test.id.clone(),
            wall: started.elapsed(),
            census: LeafCensus::of(executed.execution.as_ref(), &self.functions),
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
    /// modality, which is the campaign's, whatever its leaves ([`RunOptions::result_modality`]).
    /// `max_work` bounds result runs only, never a stepped run ([`WorkBudget`]). A result run
    /// with a stop ([`RunOptions::stop`]) is one request to the test's count
    /// ([`Stop::execute_result`]); one without is the request it was before stops existed. Every
    /// result run reads the side's definition tables, built on its first.
    #[cfg(test)]
    fn execute(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        max_work: Option<u64>,
    ) -> Executed {
        self.execute_against(campaign, test, max_work, None)
    }

    /// [`Runtime::execute`], with the side's observation probe on a result run under an
    /// observation declaration: recording the run's channels, or comparing them with the
    /// baseline's record `against` on a mutant's run ([`crate::observation`]). A mutant's run
    /// without a record to compare with (its baseline's run gave none) carries no probe.
    fn execute_against(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        max_work: Option<u64>,
        against: Option<&BaselineRecord>,
    ) -> Executed {
        stage_log::note(campaign, stage_log::Stage::Execute);
        let mut cache = RunCache::default();
        let has_pattern = test
            .oracles
            .iter()
            .any(|declaration| matches!(declaration.projection(), Projection::Pattern { .. }));
        let mut pattern_failure = OracleSide::Unknown;
        let mut undecided = None;
        let mut observed = None;
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
                    self.adapter.execute_result_counted(
                        &mut self.backend,
                        &mut self.tables,
                        &test.initial_state,
                        campaign.budget,
                        ResultRun {
                            modality: ResultModality::PathSet,
                            max_work,
                            guards: self.coverage.is_some(),
                            bindings: self.coverage.is_some(),
                        },
                        &NO_STOP,
                        std::num::NonZeroU64::MIN,
                        None,
                    )
                }
                Err(failure) => Err(failure),
            }
        } else {
            // The baseline's runs (the runtime that reads coverage) collect guard outcomes and
            // the bindings of their fired instances, which a program's result records; a mutant's
            // runs never do.
            let run = ResultRun {
                modality: self.modality,
                max_work,
                guards: self.coverage.is_some(),
                bindings: self.coverage.is_some(),
            };
            let compared = self.coverage.is_none();
            let observing = self
                .observe
                .clone()
                .filter(|_| !compared || against.is_some());
            let trusted = self.exclusions.collections_trusted();
            let declared = observing
                .as_ref()
                .map_or(Observe::NONE, |observing| observing.declared);
            let (execution, asked, trace) =
                crate::observation::evaluating(declared, |evaluation| {
                    let mut probe = observing.as_ref().map(|observing| {
                        ObservationProbe::new(
                            &observing.resolved,
                            &observing.shared,
                            observing.trusted && trusted,
                            &test.initial_state,
                            against,
                            evaluation.within(),
                        )
                    });
                    let request = probe.as_mut().map(|probe| RequestProbe {
                        rules: probe.rules(),
                        probe,
                    });
                    let (execution, asked) = self.stop.execute_asking(
                        &self.adapter,
                        &mut self.backend,
                        &mut self.tables,
                        &test.id,
                        &test.initial_state,
                        campaign.budget,
                        run,
                        request,
                    );
                    (execution, asked, probe.map(ObservationProbe::finish))
                });
            observed = trace.map(|trace| (trace, against.is_some()));
            undecided = asked;
            execution
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
            undecided,
            observed,
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
        let own = self.data.as_ref().map_or(DataEnds::None, data_ends);
        let mut notes = match &executed.execution {
            Ok(execution) if !execution.timed_out() => RunNotes {
                contradicted_claims: execution.facts().contradicted_claims.clone(),
                short_circuit_readings: exclusions
                    .counting_short_circuit_readings(execution.facts())
                    .into_iter()
                    .cloned()
                    .collect(),
                smt_unknowns: execution.facts().smt_unknowns,
                decider_smt_unknowns: execution.facts().decider_smt_unknowns,
                leaf_contradiction: exclusions.contradiction_on_a_leaf(execution),
                across: Vec::new(),
                unjudged: false,
                incomplete_leaves: BTreeSet::new(),
                stop_condition: None,
                observation: None,
            },
            _ => RunNotes::default(),
        };
        // Own facts whose check ran out of native stack admit no end of the run as data, for a
        // reason of the thread ([`RunNotes::unjudged`]).
        if own == DataEnds::None && self.data.as_ref().is_some_and(DataFacts::stack_stopped) {
            notes.unjudged = true;
        }
        let mut ends = BTreeSet::new();
        let mut stop_ends = BTreeSet::new();
        let mut undefined_steps = false;
        // Whether a complete path of the run ended in a semantic crash ([`crate::observation`]:
        // a prefix program's admission reads it under its slots' crash policies).
        let mut crashed = false;
        // Whether the bridge kept the run's one path as complete or as a real prefix
        // ([`crate::observation`]): for a probe's leaf, `ResultLimit`, which the bridge gives one
        // whose state has a terminal value or is shown to exist.
        let mut vouched = false;
        // For a run with an observation probe, whether each leaf's state is shown to exist
        // ([`LeafFacts::existence`]), on the definition that produced it, under its collection
        // trust; empty for a run the decider did not judge, which shows no leaf to exist.
        let mut existing = Vec::new();
        // Whether the decider's judgements met a stack stop ([`judgement`]), which marks the run
        // unjudged below.
        let mut stack_stopped = false;
        let run = match &executed.execution {
            Err(failure) => {
                if let ExecutionAdapterFailure::StopCondition(reason) = failure {
                    notes.stop_condition = Some(reason.clone());
                }
                SideRun::Failed(failure.into())
            }
            Ok(execution) if execution.timed_out() => {
                SideRun::Failed(ExecutionFailureKind::TimeLimit)
            }
            // A path that ended at an arrival the stop's condition left undecided: whether that
            // arrival is a stop event is not known, so neither is the path's end, and the run is
            // no evidence on either side, before its leaves are read for anything else.
            Ok(execution)
                if execution
                    .leaves()
                    .iter()
                    .any(|leaf| leaf.halt == HaltClass::StopUndecided) =>
            {
                notes.stop_condition = Some(executed.undecided.clone().unwrap_or_else(|| {
                    "a path ended at an arrival the stop condition left undecided".to_owned()
                }));
                SideRun::Failed(ExecutionFailureKind::StopCondition)
            }
            Ok(execution) => match judgement(
                &mut self.backend,
                &mut stack_stopped,
                |definition, solver| {
                    let decider = ObservationDecider::new(
                        definition,
                        solver,
                        TestInitialState::of_test(&test.initial_state),
                    )
                    .trusting_collections(collections_trusted)
                    .judging_data(own, own);
                    let context = BridgeContext {
                        test_id: &test.id,
                        classify: campaign.classify,
                        sorts: &self.context.symbol_sorts,
                    };
                    let value = |term: &Pattern| decider.terminal_value(term);
                    let exists = |term: &Pattern| decider.configuration_exists(term);
                    // A host's refusal of a stack the decider's judgements needed fails the run as
                    // infrastructure, never as an answer about its leaves.
                    let (bridged, one_sided) = decider
                        .host_refusal_during(|| {
                            let bridged =
                                paths_from_execution_existing(execution, &context, &value, &exists);
                            // Re-pin L1-2: kept below only when the run is judged into sides.
                            let one_sided = if one_sided {
                                work_bound_stuck_terminals(execution, &context, &value, &exists)
                            } else {
                                Vec::new()
                            };
                            if executed.observed.is_some() {
                                existing = execution
                                    .leaves()
                                    .iter()
                                    .map(|leaf| LeafFacts::existence(leaf, exists))
                                    .collect();
                            }
                            (bridged, one_sided)
                        })
                        .unwrap_or_else(|refused| {
                            (Err(BridgeFailure::HostStackRefused(refused)), Vec::new())
                        });
                    let state_exclusion = exclusions.state_exclusion(
                        definition,
                        &test.initial_state,
                        execution.facts(),
                    );
                    notes.decider_smt_unknowns = notes
                        .decider_smt_unknowns
                        .saturating_add(decider.smt_unknowns());
                    Ok::<_, k_rust::backend::BackendError>((bridged, state_exclusion, one_sided))
                },
            ) {
                // No decider: every slot is unknown, unless the run is excluded, which is read
                // from its leaves and from the test's initial state on the selected definition
                // (re-pin R0c-fix-2, R0c-fix-1 review minor), or no definition can be selected to
                // read the state on, which gives no side either. An excluded run gives no side, so
                // no slot, a pattern slot `run_tests` fills from the stepped run included, can
                // take one from it. The backend refused the decider, so the run is unjudged
                // (`RunNotes::unjudged`): its unknown slots need not be facts of the run.
                Err(_) => {
                    notes.unjudged = true;
                    match exclusions.run_exclusion(execution) {
                        Some(exclusion) => SideRun::Failed(exclusion.into()),
                        None => match self.backend.select_definition(None) {
                            Err(_) => SideRun::Failed(ExecutionFailureKind::Infrastructure),
                            Ok(definition) => {
                                match exclusions.state_exclusion(
                                    &definition,
                                    &test.initial_state,
                                    execution.facts(),
                                ) {
                                    Some(exclusion) => SideRun::Failed(exclusion.into()),
                                    None => SideRun::Sides {
                                        sides: vec![OracleSide::Unknown; test.oracles.len()],
                                    },
                                }
                            }
                        },
                    }
                }
                Ok((Err(failure), ..)) => SideRun::Failed((&failure).into()),
                // A run that bridged is checked for its exclusions before any side is formed
                // (re-pin R0b): an excluded run gives no side to any slot, on the baseline as on
                // a mutant, live or reused from a baseline session.
                Ok((Ok(bridged), state_exclusion, one_sided)) => {
                    match exclusions.run_exclusion(execution).or(state_exclusion) {
                        Some(exclusion) => SideRun::Failed(exclusion.into()),
                        None => {
                            terminals = one_sided;
                            vouched = matches!(
                                bridged.paths.as_slice(),
                                [path] if path.complete || path.stop.has_real_prefix()
                            );
                            let sides = test
                                .oracles
                                .iter()
                                .map(|declaration| match declaration.projection() {
                                    Projection::State(projection) => {
                                        state_side(projection, &bridged)
                                    }
                                    Projection::Pattern { .. } => executed.pattern_failure.clone(),
                                })
                                .collect();
                            // An undefined step's pre-step term is no end (kink27 R1-UNDEF). The
                            // sides have read the paths, so their ends move into the evidence.
                            // A path's key names its leaf ([`leaf_keys`]), so the paths of
                            // stop leaves are known by key.
                            let keys = leaf_keys(execution.leaves());
                            notes.incomplete_leaves = bridged
                                .paths
                                .iter()
                                .filter(|path| !path.complete)
                                .filter_map(|path| {
                                    let key = path.path_key.as_ref()?;
                                    keys.iter().position(|other| other == key)
                                })
                                .collect();
                            let stopped = execution
                                .leaves()
                                .iter()
                                .zip(keys)
                                .filter(|(leaf, _)| {
                                    matches!(
                                        leaf.halt,
                                        HaltClass::CutPoint | HaltClass::TerminalRule
                                    )
                                })
                                .map(|(_, key)| key)
                                .collect::<BTreeSet<_>>();
                            for path in bridged.paths {
                                let Some(terminal) = path.execution_terminal else {
                                    continue;
                                };
                                if terminal.kind == ExecutionTerminalKind::UndefinedStep {
                                    undefined_steps = true;
                                } else {
                                    crashed |=
                                        terminal.kind == ExecutionTerminalKind::SemanticCrash;
                                    if path.path_key.is_some_and(|key| stopped.contains(&key)) {
                                        stop_ends.insert(terminal.state.clone());
                                    }
                                    ends.insert(terminal.state);
                                }
                            }
                            SideRun::Sides { sides }
                        }
                    }
                }
            },
        };
        notes.unjudged |= stack_stopped;
        notes.observation = self.observation_note(
            executed,
            &run,
            undefined_steps && ends.is_empty(),
            crashed,
            &notes,
            vouched,
            &existing,
        );
        (
            TestEvidence {
                test_id: test.id.clone(),
                run,
                notes,
                ends,
                undefined_steps,
                one_sided_ends: BTreeSet::new(),
                stop_ends,
                payloads: BTreeMap::new(),
            },
            terminals,
        )
    }

    /// What `executed`'s observation probe built, as the run's notes report it
    /// ([`RunNotes::observation`]): a baseline's record of its channels, ended by its run `run`
    /// (its sides, whether every complete path is an undefined step, whether a complete path
    /// crashed, its leaves' halts and those of its incomplete paths, `notes`'
    /// [`RunNotes::incomplete_leaves`], and the facts of the path its leaves share), or a mutant's
    /// comparison with its one leaf's facts, which the pair's slot reads ([`run_tests`]). The
    /// facts read whether the bridge vouched for the run's one path (`vouched`) and whether each
    /// leaf's state is shown to exist (`existing`, [`LeafFacts::existence`]).
    #[allow(clippy::too_many_arguments)]
    fn observation_note(
        &self,
        executed: &Executed,
        run: &SideRun,
        undefined_steps: bool,
        crashed: bool,
        notes: &RunNotes,
        vouched: bool,
        existing: &[bool],
    ) -> Option<Observation> {
        let (trace, compared) = executed.observed.clone()?;
        let leaves = executed
            .execution
            .as_ref()
            .ok()
            .filter(|execution| !execution.timed_out())
            .map(AdaptedExecution::leaves)
            .unwrap_or_default();
        let every = LeafFacts::every(leaves, vouched, existing);
        if compared {
            let existing = |index: usize| existing.get(index).copied().unwrap_or(false);
            return Some(Observation::Compared(Comparison {
                trace: Box::new(trace),
                leaf: match leaves {
                    [leaf] => Some(LeafFacts::of(leaf, vouched, existing(0))),
                    // A run of several paths: the leaf where its probe found a difference, which
                    // ended the request (`crate::observation`, "Several paths").
                    leaves => leaves
                        .iter()
                        .position(|leaf| leaf.halt == HaltClass::ProbeDifference)
                        .map(|index| LeafFacts::of(&leaves[index], false, existing(index))),
                },
                every,
                verdict: None,
            }));
        }
        let observing = self.observe.as_ref()?;
        let sides = match run {
            SideRun::Sides { sides } => Some(sides.as_slice()),
            SideRun::Failed(_) => None,
        };
        let halts = leaves.iter().map(|leaf| leaf.halt).collect::<Vec<_>>();
        let incomplete = notes
            .incomplete_leaves
            .iter()
            .filter_map(|index| halts.get(*index).copied())
            .collect::<Vec<_>>();
        Some(Observation::Recorded(crate::observation::record(
            &observing.resolved,
            trace,
            sides,
            undefined_steps,
            crashed,
            &halts,
            &incomplete,
            LeafFacts::shared(leaves, vouched, existing),
            every,
        )))
    }

    /// The pattern-slot sides of one side's stepped run. This (the baseline's) definition and
    /// evaluation context decide what both sides share: definition independence, terminal
    /// values and the event walk. The definition that produced the leaves decides every
    /// feasibility and relation query about them (re-pin finding A-12): this runtime's own for
    /// its own run (`leaves` `None`), the mutant's `leaves` runtime for a mutant run.
    ///
    /// The host's refusal of a stack one of those judgements needed is `Err`
    /// ([`ObservationDecider::host_refusal_during`]), never a side.
    fn step_sides(
        &mut self,
        campaign: &Campaign<'_>,
        test: &TestCase,
        observation: &StepObservation,
        execution: Option<&SteppedExecution>,
        leaves: Option<&mut Runtime>,
    ) -> StepSides {
        let mut context = self.context.clone();
        context.test_id.clone_from(&test.id);
        let trusted = self.exclusions.collections_trusted()
            && leaves
                .as_ref()
                .is_none_or(|leaves| leaves.exclusions.collections_trusted());
        // A host refusal anywhere below, the bridge's `BridgeFailure::HostStackRefused` included,
        // is the refusal `host_refusal_during` returns.
        let evaluate = |decider: &ObservationDecider<'_>| {
            let sides = decider.host_refusal_during(|| {
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
                            return (OracleSide::Unknown, BTreeSet::new());
                        };
                        let Some(bridged) = &bridged else {
                            return (OracleSide::Unknown, BTreeSet::new());
                        };
                        let relations = ReadTerms::new(decider.relations());
                        let evaluation = slot_evaluation(
                            &context,
                            plan,
                            &bridged.tree,
                            &bridged.collection,
                            observation.vocabulary(),
                            &relations,
                        );
                        let side = if *with_bindings
                            && evaluation.as_ref().is_ok_and(|evaluation| {
                                evaluation.witnesses.iter().any(|witness| {
                                    witness.bindings.iter().any(|binding| {
                                        !decider.definition_independent(&binding.term)
                                    })
                                })
                            }) {
                            OracleSide::Unknown
                        } else {
                            pattern_side(&evaluation, *with_bindings)
                        };
                        (side, relations.read())
                    })
                    .collect::<Vec<_>>()
            });
            StepSides {
                sides,
                smt_unknowns: decider.smt_unknowns(),
                unjudged: false,
            }
        };
        let initial = || TestInitialState::of_test(&test.initial_state);
        let own = self.data.as_ref().map_or(DataEnds::None, data_ends);
        let mut stack_stopped = false;
        let sides = match leaves {
            None => judgement(
                &mut self.backend,
                &mut stack_stopped,
                |definition, solver| {
                    let decider = ObservationDecider::new(definition, solver, initial())
                        .trusting_collections(trusted)
                        .judging_data(own, own);
                    Ok::<_, k_rust::backend::BackendError>(evaluate(&decider))
                },
            ),
            Some(leaves) => {
                let leaf_data = leaves.data.as_ref().map_or(DataEnds::None, data_ends);
                judgement(&mut self.backend, &mut stack_stopped, |definition, _| {
                    leaves
                        .backend
                        .with_solver(None, |leaf_definition, leaf_solver| {
                            let decider = ObservationDecider::for_leaves_of(
                                definition,
                                leaf_definition,
                                leaf_solver,
                                initial(),
                            )
                            .trusting_collections(trusted)
                            .judging_data(own, leaf_data);
                            Ok::<_, k_rust::backend::BackendError>(evaluate(&decider))
                        })
                })
            }
        };
        let mut sides = sides.unwrap_or_else(|_| StepSides {
            sides: Ok(vec![
                (OracleSide::Unknown, BTreeSet::new());
                test.oracles.len()
            ]),
            smt_unknowns: 0,
            unjudged: true,
        });
        // A stack stop the judgement met ([`judgement`]).
        sides.unjudged |= stack_stopped;
        sides
    }

    /// Whether each of `terminals`, ends of the other side of a pair, is data under this side's
    /// definition (its own terminal value there, read with this side's collection trust and
    /// [`data_ends`] of its facts), and which of `bindings` are definition-independent there
    /// ([`judge_across`]). Without facts, with a finding left, or when no definition can be
    /// reached, nothing is. The host's refusal of a stack one of these judgements needed is `Err`
    /// ([`ObservationDecider::host_refusal_during`]), never an answer about the ends. Beside it:
    /// the undecided solver answers the judgement took, and whether the backend refused the
    /// judgement as a whole (no definition reached) or the judgement met a stack stop
    /// ([`judgement`], [`RunNotes::unjudged`]).
    fn judge_ends(
        &mut self,
        test: &TestCase,
        terminals: &[Pattern],
        bindings: &[Pattern],
    ) -> (Result<EndJudgement, SegmentRefused>, usize, bool) {
        let refused = || EndJudgement {
            terminals: vec![false; terminals.len()],
            independent: Vec::new(),
            terminal_causes: vec![Some(CrossCause::NoData); terminals.len()],
            binding_causes: bindings
                .iter()
                .map(|term| (term.clone(), CrossCause::NoData))
                .collect(),
        };
        if terminals.is_empty() && bindings.is_empty() {
            return (Ok(refused()), 0, false);
        }
        let ends = self.data.as_ref().map_or(DataEnds::None, data_ends);
        if ends == DataEnds::None {
            // Facts whose check ran out of native stack admit no end for a reason of the thread,
            // not of the definition ([`RunNotes::unjudged`]).
            let stack = self.data.as_ref().is_some_and(DataFacts::stack_stopped);
            return (Ok(refused()), 0, stack);
        }
        let trusted = self.exclusions.collections_trusted();
        let mut stack_stopped = false;
        let (judged, smt_unknowns, refused_judgement) = judgement(
            &mut self.backend,
            &mut stack_stopped,
            |definition, solver| {
                let decider = ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&test.initial_state),
                )
                .trusting_collections(trusted)
                .judging_data(ends, ends);
                let judgement = decider.host_refusal_during(|| {
                    let terminals = terminals
                        .iter()
                        .map(|end| decider.terminal_value(end).as_ref() == Some(end))
                        .zip(terminals)
                        .collect::<Vec<_>>();
                    let (independent, dependent): (Vec<_>, Vec<_>) = bindings
                        .iter()
                        .partition(|term| decider.definition_independent(term));
                    // Causes only of what is refused (fz26 KINK-CAUSE-SUBTERM), from the walks above.
                    EndJudgement {
                        terminal_causes: terminals
                            .iter()
                            .map(|(data, end)| {
                                (!data).then(|| {
                                    CrossCause::NotData(decider.first_non_value(end).map(Box::new))
                                })
                            })
                            .collect(),
                        terminals: terminals.iter().map(|(data, _)| *data).collect(),
                        binding_causes: dependent
                            .into_iter()
                            .map(|term| {
                                (
                                    term.clone(),
                                    CrossCause::NotData(
                                        decider.first_dependent(term).map(Box::new),
                                    ),
                                )
                            })
                            .collect(),
                        independent: independent.into_iter().cloned().collect(),
                    }
                });
                Ok::<_, k_rust::backend::BackendError>((judgement, decider.smt_unknowns(), false))
            },
        )
        // The backend refused the judgement: nothing is data, and the judgement is marked
        // refused ([`RunNotes::unjudged`]).
        .unwrap_or_else(|_| (Ok(refused()), 0, true));
        // A stack stop the judgement met ([`judgement`]) marks it unjudged too.
        (judged, smt_unknowns, refused_judgement || stack_stopped)
    }
}

/// Whether a stop condition of `stop` could read the mutant `mutant`'s cells as other terms than
/// they are (a sort or symbol the read cells reach declared otherwise than in the baseline's
/// declarations in `admission`, [`KoreSignature::incompatibility`], or either side's
/// declarations not read or its cells not readable): the condition's front end reads every
/// side's cells with the baseline's declarations, so such a mutant would be asked another
/// question than the baseline. `false` without a condition.
fn condition_incompatible(stop: Stop, admission: &MutantAdmission, mutant: &Runtime) -> bool {
    let Some(when) = stop.when() else {
        return false;
    };
    let (Some(baseline), Some(mutant)) = (&admission.signature, &mutant.signature) else {
        return true;
    };
    mutant
        .incompatibility(baseline, when.cells())
        .map_or(true, |incompatibility| incompatibility.is_some())
}

/// Whether the stop of a campaign is defined on a side whose backend is `backend`: every name
/// labels a rewrite rule of its definition ([`StopRules::unresolved`]). `Ok` with the names that
/// do not, empty when the stop is resolved or there is none.
fn resolve_stop(stop: Stop, backend: &mut Backend) -> Result<Vec<String>, ExecutionAdapterFailure> {
    stop.rules()
        .map_or_else(|| Ok(Vec::new()), |rules| rules.unresolved(backend))
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
/// the whole term, the configuration without its uncompared cells or the exit stop without an
/// exit-code cell (each defined on every configuration), and the projection of one of the
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
            | StateProjection::Cells(_)
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
    // An undefined step is no end (module documentation): every rule below reads the ends only,
    // so a run whose every terminal is one is a value, the empty set in every state slot.
    let ends = terminals
        .into_iter()
        .filter(|terminal| terminal.kind != ExecutionTerminalKind::UndefinedStep)
        .collect::<Vec<_>>();
    if ends
        .iter()
        .any(|terminal| !terminal.state.free_variables().is_empty())
    {
        return OracleSide::Unknown;
    }
    if ends
        .iter()
        .any(|terminal| terminal.kind == ExecutionTerminalKind::SemanticCrash)
    {
        // Mixed crash and normal terminal sets are not modelled. A crash is compared by its
        // terminal term, an end like any other, so without its counter content as in
        // `StateProjection::WholeTerm`, and under a cell projection without the content of its
        // uncompared cells too: such a cell's content must not distinguish there either.
        return match ends.as_slice() {
            [terminal] => OracleSide::SemanticCrash(
                match projection {
                    StateProjection::Cells(cells) => cells.project(&terminal.state),
                    StateProjection::ExitStop { .. }
                    | StateProjection::WholeTerm
                    | StateProjection::TermPaths(_) => counter_erased(&terminal.state),
                }
                .into_owned(),
            ),
            _ => OracleSide::Unknown,
        };
    }
    project(projection, &ends).map_or(OracleSide::Error, OracleSide::Normal)
}

/// Projects a run's ends: its complete terminals that are neither a crash nor an undefined step
/// ([`state_side`] removes both); `None` is a projection failure. A whole term is the end's
/// configuration with its `<generatedCounter>` content erased ([`StateProjection::WholeTerm`]),
/// so two sets of ends that differ only in that cell agree; a cell projection also leaves out its
/// uncompared cells' content ([`StateProjection::Cells`]). Every projection of no ends is the
/// empty set.
fn project(projection: &StateProjection, ends: &[&ExecutionTerminal]) -> Option<OracleValue> {
    Some(match projection {
        StateProjection::ExitStop { exit_code_cell } => OracleValue::ExitStop(
            ends.iter()
                .map(|terminal| {
                    Some(ExitStop {
                        class: match terminal.kind {
                            ExecutionTerminalKind::Normal => TerminalClass::Normal,
                            ExecutionTerminalKind::Stuck => TerminalClass::Stuck,
                            ExecutionTerminalKind::UndefinedStep
                            | ExecutionTerminalKind::SemanticCrash => return None,
                        },
                        code: match exit_code_cell {
                            None => None,
                            Some(cell) => Some(exit_code(&terminal.state, cell)?),
                        },
                    })
                })
                .collect::<Option<BTreeSet<_>>>()?,
        ),
        StateProjection::WholeTerm => OracleValue::FinalResult(FinalResult::WholeTerm(
            ends.iter()
                .map(|terminal| counter_erased(&terminal.state).into_owned())
                .collect(),
        )),
        StateProjection::Cells(cells) => OracleValue::FinalResult(FinalResult::WholeTerm(
            ends.iter()
                .map(|terminal| cells.project(&terminal.state).into_owned())
                .collect(),
        )),
        StateProjection::TermPaths(paths) => OracleValue::FinalResult(FinalResult::TermPaths(
            ends.iter()
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
/// least one witness and every witness on a real prefix; otherwise the side is `Unknown`. A path
/// that ends in an undefined step is a real prefix: its configurations are reached, and only the
/// step's outcome is no configuration (kink's `trust.md`, "What a kill trusts").
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
            ExecutionAdapterFailure::StopCondition(_) => Self::StopCondition,
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
            | BridgeFailure::ClassifiedUndefinedStep
            | BridgeFailure::HostStackRefused(_) => Self::Infrastructure,
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
    use kink_native::execution::RecordedRun;

    thread_local! {
        /// Whether the backend refuses every judgement kink makes of a run on this thread
        /// ([`judgement`], [`Runtime::facts`]), as a refused stack segment or solver would.
        pub(super) static REFUSE_JUDGEMENTS: std::cell::Cell<bool> =
            const { std::cell::Cell::new(false) };
        /// Whether every judgement kink makes of a run on this thread reports a stack stop
        /// ([`judgement`]), as one whose work ran out of native stack does; its answer is the
        /// backend's.
        pub(super) static STACK_STOP_JUDGEMENTS: std::cell::Cell<bool> =
            const { std::cell::Cell::new(false) };
    }

    /// CF-33d: a judgement of a run the backend refuses leaves its slots unknown for a reason
    /// that need not be the run's, and marks the run `unjudged` (kink-flow's outcome cache then
    /// writes no record of it): the run's decider (every slot unknown), the pattern judgement,
    /// a pair's judgement of ends (nothing is data) and the definition's facts, which are not
    /// kept when refused, so the next call computes them. The same judgements the backend makes
    /// leave the run judged.
    #[test]
    fn a_refused_judgement_marks_the_run_unjudged_at_every_site() {
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
            |_, compiled, campaign| {
                let refuse = |on: bool| REFUSE_JUDGEMENTS.with(|refuse| refuse.set(on));
                let test = &campaign.tests[0];
                let mut runtime = Runtime::prepare(campaign, compiled).unwrap_or_else(|_| panic!());
                let definition = runtime.backend.select_definition(None).unwrap();
                runtime.data = Some(DataFacts::of(&definition, &[]));
                let observation = StepObservation::new(&mut runtime.backend, vec![]).unwrap();

                // The run's decider.
                let (judged, _) = runtime.run(campaign, test);
                assert!(!judged.notes.unjudged, "{judged:?}");
                assert!(matches!(judged.run, SideRun::Sides { .. }), "{judged:?}");
                refuse(true);
                let (refused, _) = runtime.run(campaign, test);
                refuse(false);
                assert!(refused.notes.unjudged, "{refused:?}");
                assert_eq!(
                    refused.run,
                    SideRun::Sides {
                        sides: vec![OracleSide::Unknown]
                    }
                );

                // The pattern judgement.
                let sides = runtime.step_sides(campaign, test, &observation, None, None);
                assert!(!sides.unjudged);
                refuse(true);
                let sides = runtime.step_sides(campaign, test, &observation, None, None);
                refuse(false);
                assert!(sides.unjudged);
                let mut evidence = judged.clone();
                replace_patterns(test, &mut evidence, Some(&sides));
                assert!(evidence.notes.unjudged);

                // A pair's judgement of ends.
                let end = judged.ends.iter().next().expect("an end").clone();
                let (judgement, _, unjudged) =
                    runtime.judge_ends(test, std::slice::from_ref(&end), &[]);
                assert!(!unjudged && judgement.is_ok_and(|judgement| judgement.terminals[0]));
                refuse(true);
                let (judgement, _, unjudged) = runtime.judge_ends(test, &[end], &[]);
                refuse(false);
                assert!(unjudged && judgement.is_ok_and(|judgement| !judgement.terminals[0]));

                // The definition's facts: a refusal is not kept.
                refuse(true);
                assert!(runtime.facts().is_err());
                refuse(false);
                assert!(runtime.facts().is_ok());
                refuse(true);
                assert!(runtime.facts().is_ok(), "computed facts are kept");
                refuse(false);
            },
        );
    }

    /// CF-33e: a judgement that met a stop for lack of native stack (here reported by the unit
    /// test's switch, as [`judgement`] reports one from the operation's record) keeps the
    /// backend's answers but marks the run unjudged at every site: the run's decider, the
    /// pattern judgement and a pair's judgement of ends. kink-flow's outcome cache then writes no
    /// unknown record of it (`outcomes::cacheable`).
    #[test]
    fn a_judgement_that_met_a_stack_stop_marks_the_run_unjudged_at_every_site() {
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
            |_, compiled, campaign| {
                let stop = |on: bool| STACK_STOP_JUDGEMENTS.with(|stop| stop.set(on));
                let test = &campaign.tests[0];
                let mut runtime = Runtime::prepare(campaign, compiled).unwrap_or_else(|_| panic!());
                let definition = runtime.backend.select_definition(None).unwrap();
                runtime.data = Some(DataFacts::of(&definition, &[]));
                let observation = StepObservation::new(&mut runtime.backend, vec![]).unwrap();

                let (judged, _) = runtime.run(campaign, test);
                assert!(!judged.notes.unjudged, "{judged:?}");
                stop(true);
                let (stopped, _) = runtime.run(campaign, test);
                stop(false);
                assert!(stopped.notes.unjudged, "{stopped:?}");
                assert_eq!(stopped.run, judged.run);

                let sides = runtime.step_sides(campaign, test, &observation, None, None);
                assert!(!sides.unjudged);
                stop(true);
                let stopped_sides = runtime.step_sides(campaign, test, &observation, None, None);
                stop(false);
                assert!(stopped_sides.unjudged);
                assert_eq!(stopped_sides.sides, sides.sides);

                let end = judged.ends.iter().next().expect("an end").clone();
                stop(true);
                let (judgement, _, unjudged) = runtime.judge_ends(test, &[end], &[]);
                stop(false);
                assert!(unjudged && judgement.is_ok_and(|judgement| judgement.terminals[0]));
            },
        );
    }

    /// CF-33e, the record [`judgement`] reads: an existence judgement of k-rust
    /// (`ground_defined`) whose ceil condition recurses deeper than its thread's stack, with no
    /// stack segment allowed, meets a stop for lack of native stack, which the definedness walk
    /// dismisses (the term is then not shown defined); the judgement reports it. The same
    /// judgement of a shallow term reports none.
    #[test]
    fn a_judgement_whose_ground_defined_call_ran_out_of_stack_reports_the_stop() {
        // `deep(N)` recurses `N` levels; `p` is partial, `\ceil(p(X)) = (X ==Int 1)`.
        const DEFINITION: &str = r#"[] module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.sub"), smt-hook{}("-")]
            hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
            hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
            hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
            symbol deep{}(SortInt{}) : SortInt{} [function{}(), total{}()]
            symbol p{}(SortInt{}) : SortInt{} [function{}()]
            axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, \dv{SortInt{}}("0")), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))) []
            axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(gtInt{}(VarN:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(addInt{}(deep{}(subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortInt{}}("1")), \top{SortInt{}}()))) []
            axiom{R} \implies{R}(\top{R}(), \equals{R, R}(\ceil{SortInt{}, R}(p{}(X:SortInt{})), \equals{SortBool{}, R}(eqInt{}(X:SortInt{}, \dv{SortInt{}}("1")), \dv{SortBool{}}("true")))) []
        endmodule []"#;
        let judged = |depth: u32| {
            std::thread::scope(|scope| {
                std::thread::Builder::new()
                    .stack_size(8 << 20)
                    .spawn_scoped(scope, || {
                        let mut backend = Backend::new(
                            DEFINITION,
                            "MAIN",
                            k_rust::backend::BackendOptions::default(),
                        )
                        .expect("the definition loads");
                        backend.set_simplification_stack_budget(0);
                        let term = k_rust::kore::parser::parse_pattern(&format!(
                            r#"p{{}}(deep{{}}(\dv{{SortInt{{}}}}("{depth}")))"#
                        ))
                        .expect("the term parses");
                        let mut stack_stopped = false;
                        let defined =
                            judgement(&mut backend, &mut stack_stopped, |definition, _| {
                                Ok(definition
                                    .admit_unverified(&term, &[])
                                    .internalize_term()
                                    .is_ok_and(|internal| definition.ground_defined(&internal)))
                            })
                            .expect("the judgement runs");
                        (defined, stack_stopped)
                    })
                    .expect("the thread starts")
                    .join()
                    .expect("the judgement does not panic")
            })
        };
        assert_eq!(judged(100_000), (false, true));
        assert_eq!(judged(1), (true, false));
        assert_eq!(judged(2), (false, false));
    }

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
                                stops: None,
                                arrivals: None,
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
                    short_circuit_readings: Vec::new(),
                    passed_stops: Vec::new(),
                    state_matches: None,
                };
                let executed = |result: k_rust::backend::KoreExecutionResult| {
                    let feasibility = vec![LeafFeasibility::Syntactic; result.leaves.len()];
                    Executed {
                        execution: Ok(ExecutionAdapter::adapt_result(
                            result,
                            false,
                            &campaign.budget,
                            feasibility,
                            RecordedRun {
                                short_circuit_readings: true,
                                ground: true,
                            },
                        )
                        .unwrap()),
                        pattern_failure: OracleSide::Unknown,
                        cache: RunCache::default(),
                        undecided: None,
                        observed: None,
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
                    application: k_rust::kore::parser::parse_pattern(r"\top{SortBool{}}()").unwrap(),
                    undefined: k_rust::kore::parser::parse_pattern(r"\top{SortBool{}}()").unwrap(),
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
                // So does kink's own count about the run: the adapter's undecided answers about
                // the leaves reach the notes (the counter's leaves are ground, so the observation
                // decider adds none of its own).
                let mut counted = executed(raw());
                counted.execution = counted
                    .execution
                    .map(|execution| execution.with_decider_smt_unknowns(2));
                let judged = runtime.judge(&campaign, test, &counted);
                assert!(matches!(judged.run, SideRun::Sides { .. }));
                assert_eq!(judged.notes.decider_smt_unknowns, 2);
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
                            solver: kink_native::BACKEND_OPTIONS,
                            modality: ResultModality::default(),
                            max_work: None,
                            stop: Stop::NONE,
                            observe: Observe::NONE,
                        },
                        run: StoredRun::Executed {
                            executed: Box::new(executed),
                            load: Box::default(),
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

    /// CF-03: on a definition whose short-circuit analysis flags a rule, a run is judged by its
    /// own `shortCircuitReadings` list, live and as a stored baseline reused on the call's
    /// runtime. The counter definition reads no short-circuit operand; its facts are marked as if
    /// the analysis had flagged the rule `flagged`. A run whose list holds no entry is judged; one
    /// whose list holds an entry that counts (the load's, of no rule's work, of a flagged rule's
    /// work, or of any rule's work on a run that is not ground or on a definition whose rules
    /// introduce a variable) is `short-circuit-reading`, its notes naming each counting entry; an
    /// entry of an unflagged rule's work on a ground run counts not; a run its backend recorded
    /// without the capability is excluded, its empty list being no list. On facts the analysis
    /// clears, no list is read.
    #[test]
    fn a_flagged_definition_judges_each_run_by_its_short_circuit_readings() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                use k_rust::backend::{ObservedInOutput, ReadingOutcomeOutput, ShortCircuitReadingOutput};
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
                let tests = [TestCase {
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
                }];
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
                assert!(!runtime.exclusions.short_circuit_flagged());
                let cleared = runtime.exclusions.clone();
                runtime.exclusions.short_circuit_results = vec!["flagged".into()];
                runtime.exclusions.short_circuit_rules = std::iter::once("flagged".into()).collect();
                assert!(runtime.exclusions.short_circuit_flagged());
                assert_eq!(runtime.exclusions.definition_exclusion(), None);
                assert_eq!(
                    runtime.exclusions.static_exclusion(),
                    Some(Exclusion::ShortCircuitReading)
                );
                let judged = |side: &SideRun| matches!(side, SideRun::Sides { sides } if matches!(sides.as_slice(), [OracleSide::Normal(_)]));
                let excluded = SideRun::Failed(ExecutionFailureKind::ShortCircuitReading);
                // The live run lists nothing: it is judged, and its notes name no entry.
                let clean = runtime.execute(&campaign, test, None);
                let Ok(clean_execution) = &clean.execution else {
                    panic!("the counter runs")
                };
                assert_eq!(clean_execution.facts().short_circuit_readings, Some(Vec::new()));
                assert!(clean_execution.facts().ground);
                let live = runtime.judge(&campaign, test, &clean);
                assert!(judged(&live.run), "{:?}", live.run);
                assert!(live.notes.short_circuit_readings.is_empty());
                let raw = || k_rust::backend::ExecutionResult {
                    modality: k_rust::backend::ResultModalityOutput::PathSet,
                    leaves: clean_execution
                        .leaves()
                        .iter()
                        .map(|leaf| k_rust::backend::ExecutionLeaf {
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
                            stops: None,
                            arrivals: None,
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
                    short_circuit_readings: Vec::new(),
                    passed_stops: Vec::new(),
                    state_matches: None,
                };
                let reading = |rule: Option<&str>, observed_in| ShortCircuitReadingOutput {
                    operator: Some("BOOL.andThen".into()),
                    outcome: ReadingOutcomeOutput::Undefined,
                    head: Some("Lbl'Unds'divInt'Unds'".into()),
                    operand: k_rust::kore::parser::parse_pattern(r"\top{SortBool{}}()").unwrap(),
                    rewrite_rule_id: rule.map(str::to_owned),
                    rewrite_rule_label: rule.map(|rule| format!("COUNTER.{rule}")),
                    rewrite_rule_origin: None,
                    observed_in,
                };
                let listing = |readings: Vec<ShortCircuitReadingOutput<Pattern>>| {
                    let mut result = raw();
                    result.short_circuit_readings = readings;
                    result
                };
                let executed = |result: k_rust::backend::KoreExecutionResult, recorded: RecordedRun| {
                    let feasibility = vec![LeafFeasibility::Syntactic; result.leaves.len()];
                    Executed {
                        execution: Ok(ExecutionAdapter::adapt_result(
                            result,
                            false,
                            &campaign.budget,
                            feasibility,
                            recorded,
                        )
                        .unwrap()),
                        pattern_failure: OracleSide::Unknown,
                        cache: RunCache::default(),
                        undecided: None,
                        observed: None,
                    }
                };
                let ground = RecordedRun {
                    short_circuit_readings: true,
                    ground: true,
                };
                let symbolic = RecordedRun {
                    ground: false,
                    ..ground
                };
                let unlisted = RecordedRun {
                    short_circuit_readings: false,
                    ..ground
                };
                let flagged = reading(Some("flagged"), ObservedInOutput::Run);
                let unflagged = reading(Some("other"), ObservedInOutput::Run);
                let of_no_rule = reading(None, ObservedInOutput::Run);
                let at_load = reading(Some("other"), ObservedInOutput::Load);
                // (result, recording, judged, the counting entries).
                let cases = [
                    (raw(), ground, true, Vec::new()),
                    (raw(), unlisted, false, Vec::new()),
                    (listing(vec![flagged.clone()]), ground, false, vec![flagged.clone()]),
                    (listing(vec![unflagged.clone()]), ground, true, Vec::new()),
                    (listing(vec![unflagged.clone()]), symbolic, false, vec![unflagged.clone()]),
                    (listing(vec![of_no_rule.clone()]), ground, false, vec![of_no_rule.clone()]),
                    (listing(vec![at_load.clone()]), ground, false, vec![at_load.clone()]),
                    (
                        listing(vec![unflagged.clone(), flagged.clone()]),
                        ground,
                        false,
                        vec![flagged.clone()],
                    ),
                ];
                for (index, (result, recorded, expected, counting)) in cases.into_iter().enumerate() {
                    let executed = executed(result, recorded);
                    let evidence = runtime.judge(&campaign, test, &executed);
                    if expected {
                        assert!(judged(&evidence.run), "case {index}: {:?}", evidence.run);
                    } else {
                        assert_eq!(evidence.run, excluded, "case {index}");
                    }
                    assert_eq!(evidence.notes.short_circuit_readings, counting, "case {index}");
                    // A stored baseline run is judged again by its own list on the call's
                    // runtime, as the live run was.
                    let mut session = BaselineSession::new(&validator);
                    session.runs.push(StoredBaseline {
                        key: BaselineKey {
                            test_id: test.id.clone(),
                            initial_state: test.initial_state.clone(),
                            oracles: test.oracles.clone(),
                            module: "COUNTER".into(),
                            budget: campaign.budget,
                            profile: SolverProfile::BUILD,
                            solver: kink_native::BACKEND_OPTIONS,
                            modality: ResultModality::default(),
                            max_work: None,
                            stop: Stop::NONE,
                            observe: Observe::NONE,
                        },
                        run: StoredRun::Executed {
                            executed: Box::new(executed),
                            load: Box::default(),
                        },
                    });
                    let (reused, _) = session.baseline_run(&mut runtime, &campaign, test, true);
                    assert_eq!(session.reused_runs(), 1, "case {index}");
                    assert_eq!(reused.run, evidence.run, "case {index}");
                    assert_eq!(reused.notes, evidence.notes, "case {index}");
                }
                // A definition whose rules introduce a variable has no ground run: an entry of an
                // unflagged rule's work counts there.
                runtime.exclusions.existential_rules = std::iter::once("fresh".into()).collect();
                let evidence = runtime.judge(
                    &campaign,
                    test,
                    &executed(listing(vec![unflagged.clone()]), ground),
                );
                assert_eq!(evidence.run, excluded);
                assert_eq!(evidence.notes.short_circuit_readings, std::slice::from_ref(&unflagged));
                // The live run on the flagged facts is stored, not excluded with its load: a
                // reuse judges it again.
                let mut session = BaselineSession::new(&validator);
                let (first, _) = session.baseline_run(&mut runtime, &campaign, test, true);
                let (second, _) = session.baseline_run(&mut runtime, &campaign, test, true);
                assert_eq!(session.reused_runs(), 1);
                assert!(judged(&first.run) && judged(&second.run), "{first:?} {second:?}");
                assert!(matches!(session.runs[0].run, StoredRun::Executed { .. }));
                // Facts the analysis clears read no list: a non-empty one, or none at all, is
                // judged.
                runtime.exclusions = cleared;
                for (result, recorded) in [
                    (listing(vec![of_no_rule.clone(), at_load.clone()]), symbolic),
                    (raw(), unlisted),
                ] {
                    let evidence = runtime.judge(&campaign, test, &executed(result, recorded));
                    assert!(judged(&evidence.run), "{:?}", evidence.run);
                    assert!(evidence.notes.short_circuit_readings.is_empty());
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Re-pin L1-2-land (CACHE-ID review 2 minor 1): the run options' record names every option,
    /// the one-sided rule included, and tells each value apart.
    #[test]
    fn the_run_options_record_names_every_option() {
        // The solver budget is a member under the Z3 profile only, where a backend reads it.
        let z3 = SolverProfile::BUILD == SolverProfile::Z3;
        let solver = |mut value: Value| {
            if z3 {
                value["smt_resource_limit"] = json!(kink_native::SMT_RESOURCE_LIMIT.get());
            }
            value
        };
        assert_eq!(
            RunOptions::default().value(),
            solver(json!({"result_modality": "state-set", "work": null, "one_sided": "off"}))
        );
        let options = RunOptions {
            result_modality: ResultModality::PathSet,
            work: WorkBudget::Calibrated {
                factor: 4,
                floor: 10_000,
            },
            one_sided: OneSided::NoCrashClassifier,
            baseline_max_work: None,
            smt_resource_limit: kink_native::SMT_RESOURCE_LIMIT,
            stop: Stop::NONE,
            observe: Observe::NONE,
        };
        assert_eq!(
            options.value(),
            solver(json!({
                "result_modality": "path-set",
                "work": {"factor": 4, "floor": 10_000},
                "one_sided": "no-crash-classifier",
            }))
        );
        let other_budget = RunOptions {
            smt_resource_limit: std::num::NonZeroU32::new(1).unwrap(),
            ..options
        };
        assert_eq!(other_budget.value() != options.value(), z3);
        // A baseline work bound is a member only when it is set.
        assert_eq!(
            RunOptions {
                baseline_max_work: Some(20_000),
                ..options
            }
            .value(),
            solver(json!({
                "result_modality": "path-set",
                "work": {"factor": 4, "floor": 10_000},
                "one_sided": "no-crash-classifier",
                "baseline_max_work": 20_000,
            }))
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
            RunOptions {
                baseline_max_work: Some(1),
                ..options
            },
            RunOptions {
                stop: Stop::new(
                    StopRules {
                        before: Vec::new(),
                        after: vec!["CLOCK.frame".into()],
                    },
                    std::num::NonZeroU64::MIN,
                )
                .unwrap(),
                ..options
            },
        ] {
            assert_ne!(changed.value(), options.value(), "{changed:?}");
        }
    }

    /// A stop is a member of the run options record only when it names a rule, with its rules
    /// as written, its count and each test's own count; equal stops are one interned value.
    #[test]
    fn the_run_options_record_names_the_stop() {
        let rules = StopRules {
            before: vec!["CLOCK.frame".into()],
            after: Vec::new(),
        };
        let three = std::num::NonZeroU64::new(3).unwrap();
        assert_eq!(
            Stop::new(StopRules::NONE, three),
            None,
            "a count of no rule means nothing"
        );
        let stop = Stop::new(rules.clone(), three).unwrap();
        assert_eq!(stop, Stop::new(rules.clone(), three).unwrap());
        assert_eq!(
            stop.value(),
            Some(json!({"before": ["CLOCK.frame"], "after": [], "count": 3}))
        );
        let counted = stop.with_test_count("t", std::num::NonZeroU64::MIN);
        assert_eq!(
            counted.value(),
            Some(json!({"before": ["CLOCK.frame"], "after": [], "count": 3, "counts": {"t": 1}}))
        );
        assert_eq!(
            counted.of_test("t"),
            Some((&rules, std::num::NonZeroU64::MIN))
        );
        assert_eq!(counted.of_test("u"), Some((&rules, three)));
        assert_eq!(Stop::NONE.with_test_count("t", three), Stop::NONE);
        assert_eq!(Stop::NONE.value(), None);
        let options = RunOptions {
            stop,
            ..RunOptions::default()
        };
        assert_eq!(
            options.value()["stop"],
            json!({"before": ["CLOCK.frame"], "after": [], "count": 3})
        );
        assert!(RunOptions::default().value().get("stop").is_none());
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
                            stops: None,
                            arrivals: None,
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
                    short_circuit_readings: Vec::new(),
                    passed_stops: Vec::new(),
                    state_matches: None,
                };
                let feasibility = execution
                    .leaves()
                    .iter()
                    .map(|leaf| leaf.feasibility)
                    .collect::<Vec<_>>();
                let executed = |result: ExecutionResult<Pattern>| Executed {
                    execution: Ok(ExecutionAdapter::adapt_bounded_result(
                        result,
                        false,
                        &campaign.budget,
                        max_work,
                        feasibility.clone(),
                        RecordedRun {
                            short_circuit_readings: true,
                            ground: true,
                        },
                    )
                    .unwrap()),
                    pattern_failure: OracleSide::Unknown,
                    cache: RunCache::default(),
                    undecided: None,
                    observed: None,
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
                            ends: BTreeSet::new(),
                            undefined_steps: false,
                            one_sided_ends: BTreeSet::new(),
                            stop_ends: BTreeSet::new(),
                            payloads: BTreeMap::new(),
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
                let edit = CompiledEdit::between(&base_side, &total_side);
                let mut sides = MutantSides {
                    runtime: Runtime::prepare(&campaign, &total_side).unwrap_or_else(|_| panic!()),
                    ground_witness: edit.clone(),
                    edit,
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
                        observations
                            .runtime
                            .step_sides(
                                &campaign,
                                test,
                                &observations.observation,
                                mutant_cache.stepped.as_ref(),
                                None,
                            )
                            .sides
                            .expect("the host maps the stacks the leaves need")
                            .into_iter()
                            .map(|(side, _)| side)
                            .collect::<Vec<_>>(),
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
                ends: BTreeSet::new(),
                undefined_steps: false,
                one_sided_ends: BTreeSet::new(),
                stop_ends: BTreeSet::new(),
                payloads: BTreeMap::new(),
            };
            // The undecided answers the judgement of the pattern slots took are kink's questions
            // about this run: they add to its notes, and the slots take the judged sides.
            let mut counted = evidence.clone();
            counted.notes.decider_smt_unknowns = 1;
            let judged = StepSides {
                sides: Ok(vec![
                    (OracleSide::Unknown, BTreeSet::new()),
                    (OracleSide::Unknown, BTreeSet::new()),
                ]),
                smt_unknowns: 2,
                unjudged: false,
            };
            replace_patterns(&test, &mut counted, Some(&judged));
            assert_eq!(counted.notes.decider_smt_unknowns, 3);
            assert!(
                matches!(&counted.run, SideRun::Sides { sides } if sides[1] == OracleSide::Unknown)
            );
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

    /// fz26 KINK-OVERLOAD-VALUE: before a pair's slots are compared, each side's ends are judged
    /// under the other side's definition (`judge_across`). `testdata/k/overload/anyw.k` has the
    /// free constructor `c`; `anyw-anywhere.k` adds `[anywhere]` to its rule `c(1) => d`, so `c`
    /// roots an equation there and `c(1)` is not data. With the plain definition as baseline: the
    /// baseline's state slot holding `c(1)` and its pattern binding `c(1)` become unknown, while the
    /// mutant's `d` (a free constructor of both) stays; and the mutant's own binding `c(1)` is
    /// judged under the mutant's definition too. With the roles reversed, a one-sided terminal of
    /// the mutant holding `c(1)` is dropped and one holding `d` kept. Every other side is untouched.
    #[test]
    fn every_compared_end_is_judged_under_the_other_definition() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let dir = std::path::Path::new(input_test_support::DIR).join("overload");
                let validator = |file: &str| {
                    NativeValidator::bind(
                        input_test_support::load_path(&dir.join(file), "AW"),
                        k_rust::kompile::CompileOptions::default(),
                    )
                };
                let (plain, anywhere) = (validator("anyw.k"), validator("anyw-anywhere.k"));
                let state = OracleDeclaration::new(
                    CrashPolicy::Reject,
                    Projection::State(StateProjection::WholeTerm),
                )
                .unwrap();
                let vocabulary =
                    kink_pattern::EventVocabulary::new(vec![kink_pattern::Constructor {
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
                        with_bindings: true,
                    },
                )
                .unwrap();
                // The KORE names of `c` and `d`: the constructors of sort `Foo` of the baseline.
                let name = |arity: usize| {
                    let compiled = plain.compile_baseline().unwrap();
                    let definition =
                        kink_native::consistency::loaded_definition(&compiled).unwrap();
                    definition
                        .symbols()
                        .values()
                        .find(|symbol| {
                            symbol.result_sort
                                == k_rust::k_rust_backend::term::Sort::simple("SortFoo")
                                && symbol.argument_sorts.len() == arity
                                && symbol.name.starts_with("Lbl")
                        })
                        .expect("a constructor of Foo")
                        .name
                        .to_string()
                };
                let c1 = input_test_support::app(
                    &name(1),
                    vec![Pattern::DomainValue {
                        sort: Sort::Application {
                            name: "SortInt".into(),
                            arguments: vec![],
                        },
                        value: "1".into(),
                    }],
                );
                let d = input_test_support::app(&name(0), vec![]);
                let tests = [TestCase {
                    id: "t".into(),
                    initial_state: input_test_support::initial_state(
                        input_test_support::app(
                            "Lblgo",
                            vec![Pattern::DomainValue {
                                sort: Sort::Application {
                                    name: "SortInt".into(),
                                    arguments: vec![],
                                },
                                value: "1".into(),
                            }],
                        ),
                        "SortPgm",
                    ),
                    oracles: vec![state, pattern],
                }];
                let classify: &dyn Fn(&Pattern) -> ExecutionTerminalKind =
                    &|_| ExecutionTerminalKind::Normal;
                let campaign = Campaign {
                    validator: &plain,
                    module: "AW",
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
                let runtime = |validator: &NativeValidator| {
                    let side = validator.compile_baseline().unwrap();
                    let mut runtime =
                        Runtime::prepare(&campaign, &side).unwrap_or_else(|_| panic!());
                    let definition = runtime.backend.select_definition(None).unwrap();
                    let facts = DataFacts::of(&definition, &[]);
                    assert!(facts.has_data());
                    runtime.data = Some(facts);
                    runtime
                };
                let (mut plain_runtime, mut anywhere_runtime) =
                    (runtime(&plain), runtime(&anywhere));
                let evidence = |end: &Pattern| TestEvidence {
                    test_id: "t".into(),
                    run: SideRun::Sides {
                        sides: vec![
                            OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(
                                BTreeSet::from([end.clone()]),
                            ))),
                            OracleSide::Normal(OracleValue::Pattern(PatternValue::Match {
                                bindings: Some(BTreeSet::from([vec![kink_pattern::Binding {
                                    name: "X".into(),
                                    term: end.clone(),
                                }]])),
                            })),
                        ],
                    },
                    notes: RunNotes::default(),
                    ends: BTreeSet::from([end.clone()]),
                    undefined_steps: false,
                    one_sided_ends: BTreeSet::new(),
                    stop_ends: BTreeSet::new(),
                    payloads: BTreeMap::new(),
                };
                let sides = |evidence: &TestEvidence| match &evidence.run {
                    SideRun::Sides { sides } => sides
                        .iter()
                        .map(|side| matches!(side, OracleSide::Unknown))
                        .collect::<Vec<_>>(),
                    SideRun::Failed(_) => panic!("sides"),
                };
                let terminal = |state: &Pattern| ExecutionTerminal {
                    kind: ExecutionTerminalKind::Stuck,
                    state: state.clone(),
                };
                let test = &tests[0];
                // The plain baseline against the anywhere mutant.
                let (mut baseline, mut mutant) = (evidence(&c1), evidence(&d));
                let mut one_sided = vec![terminal(&c1), terminal(&d)];
                judge_across(
                    test,
                    &mut baseline,
                    &mut mutant,
                    &mut one_sided,
                    &mut plain_runtime,
                    &mut anywhere_runtime,
                );
                assert_eq!(sides(&baseline), [true, true], "{baseline:?}");
                assert_eq!(sides(&mutant), [false, false], "{mutant:?}");
                assert_eq!(one_sided, [terminal(&c1), terminal(&d)]);
                // fz26 KINK-CAUSE-SUBTERM: the mutant's evidence says which slots were refused,
                // whose end, and the first node that fails its own test under the mutant's
                // definition: `c(1)`. Since KRUST-ANYWHERE-HEAD `c` is a data head there (a plain
                // `anywhere` head declared `value-production`), so `c(1)` fails as an application
                // of a data head k-rust does not judge data: the rule `c(1) => d` reduces it.
                let refusals = |evidence: &TestEvidence| {
                    evidence
                        .notes
                        .across
                        .iter()
                        .map(|refusal| {
                            let node = match &refusal.cause {
                                CrossCause::NotData(Some(failure)) => {
                                    assert_eq!(
                                        failure.test,
                                        kink_native::step_events::LocalTest::OverloadData
                                    );
                                    Some(failure.node.clone())
                                }
                                CrossCause::NotData(None) => None,
                                CrossCause::NoData => Some(Pattern::Top {
                                    sort: k_rust::kore::ast::Sort::Variable("no-data".into()),
                                }),
                                CrossCause::NoEnds => Some(Pattern::Top {
                                    sort: k_rust::kore::ast::Sort::Variable("no-ends".into()),
                                }),
                            };
                            (refusal.slot, refusal.baseline_end, refusal.end, node)
                        })
                        .collect::<Vec<_>>()
                };
                assert_eq!(
                    refusals(&mutant),
                    [
                        (0, true, CrossEnd::Terminal, Some(c1.clone())),
                        (1, true, CrossEnd::Binding, Some(c1.clone()))
                    ]
                );
                assert!(baseline.notes.across.is_empty());
                // The mutant's own binding `c(1)` is not data under its own definition.
                let (mut baseline, mut mutant) = (evidence(&d), evidence(&c1));
                let mut none = Vec::new();
                judge_across(
                    test,
                    &mut baseline,
                    &mut mutant,
                    &mut none,
                    &mut plain_runtime,
                    &mut anywhere_runtime,
                );
                assert_eq!(sides(&baseline), [false, false], "{baseline:?}");
                assert_eq!(sides(&mutant), [false, true], "{mutant:?}");
                assert_eq!(
                    refusals(&mutant),
                    [(1, false, CrossEnd::Binding, Some(c1.clone()))]
                );
                // The anywhere baseline against the plain mutant: one-sided terminals.
                let (mut baseline, mut mutant) = (evidence(&d), evidence(&d));
                let mut one_sided = vec![terminal(&c1), terminal(&d)];
                judge_across(
                    test,
                    &mut baseline,
                    &mut mutant,
                    &mut one_sided,
                    &mut anywhere_runtime,
                    &mut plain_runtime,
                );
                assert_eq!(sides(&baseline), [false, false], "{baseline:?}");
                assert_eq!(sides(&mutant), [false, false], "{mutant:?}");
                assert_eq!(one_sided, [terminal(&d)]);
                // A side without facts makes every end judged under it not data.
                plain_runtime.data = None;
                let (mut baseline, mut mutant) = (evidence(&d), evidence(&d));
                judge_across(
                    test,
                    &mut baseline,
                    &mut mutant,
                    &mut Vec::new(),
                    &mut anywhere_runtime,
                    &mut plain_runtime,
                );
                assert_eq!(sides(&baseline), [true, true], "{baseline:?}");
                assert_eq!(sides(&mutant), [false, true], "{mutant:?}");
                let no_data = Some(Pattern::Top {
                    sort: k_rust::kore::ast::Sort::Variable("no-data".into()),
                });
                assert_eq!(
                    refusals(&mutant),
                    [
                        (0, true, CrossEnd::Terminal, no_data.clone()),
                        (1, true, CrossEnd::Binding, no_data.clone()),
                        (1, false, CrossEnd::Binding, no_data)
                    ]
                );
                // Review N2: a value-holding state slot without ends is not compared unjudged.
                let mut plain_runtime = runtime(&plain);
                let (mut baseline, mut mutant) = (evidence(&d), evidence(&d));
                mutant.ends.clear();
                judge_across(
                    test,
                    &mut baseline,
                    &mut mutant,
                    &mut Vec::new(),
                    &mut anywhere_runtime,
                    &mut plain_runtime,
                );
                assert_eq!(sides(&baseline), [false, false], "{baseline:?}");
                assert_eq!(sides(&mutant), [true, false], "{mutant:?}");
                assert_eq!(
                    refusals(&mutant),
                    [(
                        0,
                        false,
                        CrossEnd::Terminal,
                        Some(Pattern::Top {
                            sort: k_rust::kore::ast::Sort::Variable("no-ends".into()),
                        })
                    )]
                );
                // kink27 R1-UNDEF: a side whose every path takes an undefined step has no ends and
                // the empty final result, which is judged and compared, not refused.
                let (mut baseline, mut mutant) = (evidence(&d), evidence(&d));
                mutant.ends.clear();
                mutant.undefined_steps = true;
                if let SideRun::Sides { sides } = &mut mutant.run {
                    sides[0] = OracleSide::Normal(OracleValue::FinalResult(
                        FinalResult::WholeTerm(BTreeSet::new()),
                    ));
                }
                judge_across(
                    test,
                    &mut baseline,
                    &mut mutant,
                    &mut Vec::new(),
                    &mut anywhere_runtime,
                    &mut plain_runtime,
                );
                assert_eq!(sides(&baseline), [false, false], "{baseline:?}");
                assert_eq!(sides(&mutant), [false, false], "{mutant:?}");
                assert!(mutant.notes.across.is_empty(), "{mutant:?}");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// fz26 KINK-OVERLOAD-VALUE review S1: a pattern slot's outcome is decided from relations
    /// between one side's event payloads in that side's theory, so the terms those decisions read
    /// are judged under the other side's definition too. `testdata/k/overload/tick.k` emits one
    /// `tick` event per item of `tick(c(1), tick(d, done))`; `tick-anywhere.k` makes `c(1) => d`
    /// apply anywhere, so the mutant's items are `d` and `d`. The plan `tick(X) ; tick(X)` (a use
    /// of the bound payload) gives the baseline `NoMatch` (`c(1)` and `d` clash under the
    /// baseline) and the mutant `Match`, which compares as a kill. Under the mutant's definition
    /// `c(1)` is not data (`c` roots an equation there), so the baseline's slot is `Unknown` and
    /// the slot does not distinguish; the mutant's `Match` read only identical payloads.
    #[test]
    fn a_pattern_slot_is_judged_on_the_payloads_its_relations_read() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                use input_test_support as support;
                let dir = std::path::Path::new(support::DIR).join("overload");
                let validator = |file: &str| {
                    NativeValidator::bind(
                        support::load_path(&dir.join(file), "TICK"),
                        k_rust::kompile::CompileOptions::default(),
                    )
                };
                let (plain, anywhere) = (validator("tick.k"), validator("tick-anywhere.k"));
                let specs = vec![StepEventSpec {
                    constructor: "tick".into(),
                    pre: support::k_config(
                        support::app(
                            "Lbltick",
                            vec![support::var("X", "SortFoo"), support::var("P", "SortPgm")],
                        ),
                        "SortPgm",
                        "R",
                        "C",
                    ),
                    post: None,
                    payload: vec!["X".into()],
                }];
                let vocabulary = StepObservation::vocabulary_of(&specs).unwrap();
                let clause = |mode| kink_pattern::PayloadClause {
                    position: 0,
                    mode,
                    variable: "X".into(),
                };
                let plan = PatternPlan::new(
                    &vocabulary,
                    vec![(
                        "X".into(),
                        Sort::Application {
                            name: "SortFoo".into(),
                            arguments: vec![],
                        },
                    )],
                    vec![kink_pattern::PatternArm {
                        atoms: vec![
                            kink_pattern::Atom {
                                constructor: "tick".into(),
                                payload: vec![clause(kink_pattern::MatchMode::Bind)],
                            },
                            kink_pattern::Atom {
                                constructor: "tick".into(),
                                payload: vec![clause(kink_pattern::MatchMode::Use)],
                            },
                        ],
                        relations: vec![kink_pattern::Relation::EventuallyAfter],
                    }],
                    None,
                )
                .unwrap();
                let declaration = OracleDeclaration::new(
                    CrashPolicy::CompareIdentity,
                    Projection::Pattern {
                        plan,
                        with_bindings: false,
                    },
                )
                .unwrap();
                let tests = [TestCase {
                    id: "t".into(),
                    initial_state: support::initial_state(
                        support::app(
                            "Lbltick",
                            vec![
                                support::app("Lblc", vec![support::int(1)]),
                                support::app(
                                    "Lbltick",
                                    vec![
                                        support::app("Lbld", vec![]),
                                        support::app("Lbldone", vec![]),
                                    ],
                                ),
                            ],
                        ),
                        "SortPgm",
                    ),
                    oracles: vec![declaration.clone()],
                }];
                let classify: &dyn Fn(&Pattern) -> ExecutionTerminalKind =
                    &|_| ExecutionTerminalKind::Normal;
                let campaign = Campaign {
                    validator: &plain,
                    module: "TICK",
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
                let runtime = |validator: &NativeValidator| {
                    let side = validator.compile_baseline().unwrap();
                    let mut runtime =
                        Runtime::prepare(&campaign, &side).unwrap_or_else(|_| panic!());
                    let definition = runtime.backend.select_definition(None).unwrap();
                    let facts = DataFacts::of(&definition, &[]);
                    assert!(facts.has_data());
                    runtime.data = Some(facts);
                    runtime
                };
                let (mut baseline_runtime, mut mutant_runtime) =
                    (runtime(&plain), runtime(&anywhere));
                let observation =
                    StepObservation::new(&mut baseline_runtime.backend, specs.clone()).unwrap();
                // The baseline side, as `run_campaign_multi_with` forms it.
                let (mut baseline, cache) = baseline_runtime.run(&campaign, test);
                let patterns = baseline_runtime.step_sides(
                    &campaign,
                    test,
                    &observation,
                    cache.stepped.as_ref(),
                    None,
                );
                replace_patterns(test, &mut baseline, Some(&patterns));
                let side = |value| SideRun::Sides {
                    sides: vec![OracleSide::Normal(OracleValue::Pattern(value))],
                };
                assert_eq!(baseline.run, side(PatternValue::NoMatch), "{baseline:?}");
                assert!(
                    baseline.payloads[&0].contains(&support::app("Lblc", vec![support::int(1)])),
                    "{baseline:?}"
                );
                // The mutant side, as `run_tests` forms it.
                let (mut mutant, mutant_cache) = mutant_runtime.run(&campaign, test);
                let patterns = baseline_runtime.step_sides(
                    &campaign,
                    test,
                    &observation,
                    mutant_cache.stepped.as_ref(),
                    Some(&mut mutant_runtime),
                );
                replace_patterns(test, &mut mutant, Some(&patterns));
                assert_eq!(
                    mutant.run,
                    side(PatternValue::Match { bindings: None }),
                    "{mutant:?}"
                );
                let SideRun::Sides { sides: before } = &baseline.run else {
                    panic!()
                };
                let SideRun::Sides {
                    sides: mutant_sides,
                } = &mutant.run
                else {
                    panic!()
                };
                // Before: a kill.
                assert_eq!(
                    slot_outcome(&declaration, &before[0], &mutant_sides[0]),
                    OracleOutcome::Distinguish
                );
                judge_across(
                    test,
                    &mut baseline,
                    &mut mutant,
                    &mut Vec::new(),
                    &mut baseline_runtime,
                    &mut mutant_runtime,
                );
                assert_eq!(
                    baseline.run,
                    SideRun::Sides {
                        sides: vec![OracleSide::Unknown]
                    }
                );
                assert_eq!(mutant.run, side(PatternValue::Match { bindings: None }));
                // fz26 KINK-CAUSE-SUBTERM: the refusal names the baseline's payload.
                assert!(
                    matches!(
                        mutant.notes.across.as_slice(),
                        [CrossRefusal {
                            slot: 0,
                            baseline_end: true,
                            end: CrossEnd::Payload,
                            cause: CrossCause::NotData(Some(_)),
                        }]
                    ),
                    "{:?}",
                    mutant.notes.across
                );
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
                            prepare_mutant(&campaign, &a, &compiled, &support, false).unwrap();
                        let (mut sides_b, claims_b) =
                            prepare_mutant(&campaign, &b, &compiled, &support, false).unwrap();
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
                            prepare_mutant(&campaign, &a, &compiled, &support, false).unwrap();
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

        /// A session never answers a baseline request with a run made under another baseline
        /// work bound ([`RunOptions::baseline_max_work`]): two requests that differ only in the
        /// bound are two live runs, and each is reused only for its own bound. A bound of one
        /// state stops the run in a `work-bound` leaf, whose side is `Unknown`.
        #[test]
        #[ignore = "kink"]
        fn a_baseline_run_is_reused_only_under_its_own_work_bound() {
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
                    let mut runtime =
                        Runtime::prepare(campaign, compiled).unwrap_or_else(|_| panic!());
                    let (unbounded, _) = session.baseline_run(&mut runtime, campaign, test, true);
                    let normal = |run: &SideRun| {
                        matches!(run, SideRun::Sides { sides }
                            if matches!(sides.as_slice(), [OracleSide::Normal(_)]))
                    };
                    assert!(normal(&unbounded.run), "{:?}", unbounded.run);
                    runtime.baseline_max_work = Some(1);
                    let (bounded, cache) = session.baseline_run(&mut runtime, campaign, test, true);
                    assert_eq!((session.live_runs(), session.reused_runs()), (2, 0));
                    assert_eq!(
                        bounded.run,
                        SideRun::Sides {
                            sides: vec![OracleSide::Unknown]
                        }
                    );
                    assert!(
                        cache.recording.as_ref().is_some_and(|run| run
                            .census
                            .leaves
                            .contains_key(&HaltClass::WorkBound)),
                        "{:?}",
                        cache.recording
                    );
                    let (again, _) = session.baseline_run(&mut runtime, campaign, test, true);
                    assert_eq!(again.run, bounded.run);
                    runtime.baseline_max_work = None;
                    let (again, _) = session.baseline_run(&mut runtime, campaign, test, true);
                    assert_eq!(again.run, unbounded.run);
                    assert_eq!(
                        (
                            session.live_runs(),
                            session.reused_runs(),
                            session.stored_runs()
                        ),
                        (2, 2, 2)
                    );
                },
            );
        }
    }
}
