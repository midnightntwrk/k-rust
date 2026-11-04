//! The kill search with its outcome cache (flow README 5.4, 5.6 and 7.5): `kink-flow run`.
//!
//! One command admits the specification once and uses its one `NativeValidator` for the
//! result cache update and for every mutation. Per mutation, in the list's order:
//!
//! 1. Resolve it into one pinned patch (F-04); an `invalid-mutation` ends there. A mutation
//!    whose edit only weakens the specification (kink-patch `ClaimSupport::weakening`: it deletes
//!    equations of functions or lemmas, or narrows an equation's `requires`) is `unkillable`
//!    there too, with reason `weakening`: every model of the specification is a model of the
//!    mutant, so no program can kill it, and nothing runs (kink27 R5-WEAKENING). It is decided
//!    after the `baseline-findings` check (before tier 1, a baseline with a finding no
//!    `[spec] assume_joined` name assumes makes every mutation with a program in O `unknown`),
//!    since the argument reads the baseline's normal forms as a model (fix round 1).
//! 2. Choose the programs O: the comparable programs of the up-to-date result cache, cheapest
//!    first (the record's `wall_ms`, then corpus order; [`ProgramOrder`], README 6.4). Every
//!    live call then runs first the programs of the call whose cached coverage witnesses the
//!    mutant's edit, then the rest, each group in O's order: once the mutant's claim-free side
//!    compiles, the runner gives its compiled edit (kink-campaign `CompiledEdit::between`, the
//!    rule its coverage selection reads; `run_campaign_multi_ordered`), and a program witnesses
//!    it as [`witnesses`] says (matched, k-rust `matched`, for an axiom whose edit changed its
//!    `requires`, alone or with its right-hand side or `ensures`; applied, k-rust `applied`,
//!    otherwise; every program for an edit that is not site-local; re-pin L2-1-tail), and a
//!    program whose cached coverage is not complete witnesses every edit, since it covers only
//!    what its run explored before it stopped. The row's `witnesses` lists the witnessing
//!    programs of O, from a live call's compiled edit or, on a row tier 1 decides with no call,
//!    from the one the mutation's outcome file keeps ([`EditWitness`]); it is empty on the
//!    `no-comparable-program` row of an empty O, and otherwise null when there is neither. What is decided before any compile
//!    (tier 1, the compiles ahead) depends only on the set of programs in O, not on their
//!    order. The order changes which killing program is found first and the cost,
//!    never a status in the no-Z3 profile while no `budget.time_ms` bound fires (under Z3 a
//!    reused backend's cache of solver answers can make it move one between killed, unknown and
//!    survived, never to a false kill; review L2-1-tail-1 D1, D2).
//! 3. Tier 1 (README 7.5.3): the valid outcome records of the programs of O, under a key that
//!    names every input of the outcome (kink's build, the k-rust revision, the solver profile,
//!    the specification's execution digest, the budget, the oracles, the mutation's identity,
//!    the program digest and the program's baseline run digest). A valid `killed` record makes
//!    the status `killed` with no call (its killer the first such program in the order a live
//!    call would run O: first the programs that witness the compiled edit the outcome file
//!    keeps, then the rest, each in O's order; so after `--full` cached every killer, the killer
//!    is the one a cold first-kill call finds first, for the same order of O); otherwise the
//!    programs with a valid `agree` record form A, in that order, and L = O minus A. With L empty the status
//!    is the runner's fold over A's cached outcomes (survived), with no call.
//! 4. Otherwise the mutant runs live on L. Tier 2 (README 7.5.5): when the killer hint names a
//!    comparable program of L, one call runs that program alone; if it kills, that is the
//!    verdict. Otherwise the cold call runs L (the hinted program included), the programs that
//!    witness the compiled edit first, then the rest, each in O's order.
//! 5. Every status is `kink_campaign::derive_mutant_report` (schedule `FirstKill`) over the
//!    assembled plan: A's cached outcomes in step 3's order, then the last live call's tests in
//!    their order, with that call's mutant-scope failure. kink-flow adds no fold and compares
//!    no terms: a mutation is killed only by a proved `Distinguish`, live from
//!    `run_campaign_multi` in this command or cached under an exactly matching key. A cached
//!    agreement is the fold's bottom, so the assembled status is the cold call's status; a
//!    live mutant-scope failure that precedes execution next to a cached agreement is the
//!    corpus error `outcome-conflict`. A live mutant-scope `Infrastructure` failure is not
//!    (flow F-16): the status is the live plan's alone (`error`), as a cold call gives it, and
//!    the cached agreements leave the plan and the row.
//! 6. After every call, each program's baseline row from that call is compared, by run
//!    digest, with its cached record. Any difference is a corpus error: the mutation gets the
//!    status `error` with reason `baseline-mismatch:<program id>` (or
//!    `baseline-count-mismatch`), nothing is written to tier 1 for it, and the run stops.
//! 7. After a verdict, every live test whose outcome is cacheable (killed or agree) gets a
//!    tier-1 record, unless its call's plan carries a mutant-scope failure, and the mutation's
//!    outcome file keeps the call's compiled edit ([`EditWitness`]). A `killed` status
//!    makes its first killing program the mutation's hint; any other status removes it. The
//!    hints file and the report are written after every mutation, corpus errors included.
//!
//! The steps above are the first-kill search ([`ScheduleMode::FirstKill`], the default).
//! `run --full` ([`RunOptions::schedule`] [`ScheduleMode::Full`]) runs every comparable program on
//! every selected mutation, so that each row holds every cell of the kill matrix:
//!
//! - O is every comparable program in corpus order, and a live call keeps that order (step 2;
//!   `witnesses` still names the programs that witness the compiled edit, in that order).
//! - Tier 1 decides with no call only when every program of O has a valid record (step 3): a
//!   `killed` record does not decide a full row, which needs every cell. The valid records,
//!   killed and agreements alike, are the cached cells C, and L = O minus C.
//! - No one-program call is made for the hint (step 4): a hint only orders the first-kill
//!   search, and under `Full` every program of L runs in one call. A hint that names
//!   no comparable program is still reported and removed.
//! - The fold (step 5) is `derive_mutant_report` under `Full` over C's outcomes then the call's
//!   tests, with the same `outcome-conflict` and `Infrastructure` rules.
//! - Records and the hint follow step 7 unchanged. Each row carries `killed_by`, every killing
//!   program in corpus order (null under first-kill, whose killer depends on the order and on what
//!   the cache holds), its `killer` is the first of them, and its `executed` lists every program
//!   of O in corpus order, cached and live; the document carries the per-program `matrix`
//!   ([`crate::report::matrix`]).
//!
//! A tier-1 record is the outcome of one executed test, and the schedule decides only whether a
//! test is executed, never what an executed test's request, sides or slots are; in the no-Z3
//! profile a program's outcome does not depend on which programs ran before it in the call
//! (step 2). So a record does not depend on the schedule, the tier-1 context does not name it,
//! and the records either schedule writes serve both. A full row's status is the first-kill
//! row's: both are kink-campaign's fold over the same per-program outcomes, in which a kill ranks
//! above every inconclusive outcome, and under `FirstKill` the fold only reads fewer outcomes
//! below a kill.
//!
//! Every campaign call goes through the command's one [`BaselineRunner`] and its in-memory
//! baseline session (flow F-12, README 6.3): each program's baseline runs live at most once per
//! command, in the result update or in the first call that needs it, and later calls of the
//! same command reuse that live run where the runner produces baseline evidence. The drift check
//! still compares every call's baseline rows with the cached records. The run document's
//! `baseline_runs` counts the live and reused baseline runs.
//!
//! Flow F-13: every executed entry names its oracle slots (and, for a distinguishing slot, the
//! two sides), carries the session's timings (`wall_ms`, `baseline_ms`, `baseline_reused`) and,
//! for a stopped run, the leaf census in its cause; every row carries `call_wall_ms`; the
//! document lists the rules no resolving mutation of the list targets. None of these enters an
//! evidence row, a digest, a key, an outcome record or a hint.
//!
//! CF-16: every live call computes the kill evidence of each distinguishing test from its own
//! evidence ([`crate::evidence`]: the first differing cell path of the two sides' ends and both
//! values as K text), which the test's executed entry shows and its `killed` tier-1 record keeps
//! (outside the key, inside the record digest), so a kill decided from tier 1 shows it too. It
//! enters no evidence row, run digest, key or hint, and nothing decides a status from it.
//!
//! Threads (re-pin L1-3, L1-3-fix-1): only relinking and compiling run on several threads
//! ([`RunOptions::compile_workers`]). The selected mutations are taken in chunks; each chunk's
//! mutants that would make a live call are compiled ahead (kink-native
//! `NativeValidator::compile_ahead`: each patch applied on the calling thread, then relinked and
//! compiled on a worker) and every worker is joined before the chunk's first mutation runs, so
//! every step above runs as with one worker: one mutation at a time, in list order, every
//! resolution, patch application, load, consistency check and execution on the calling thread
//! (the loads', checks' and executions' stack stops depend on the thread and on the other
//! threads' stack, k-rust `docs/compatibility.md`, "Execute"; applying types edited rules
//! through a recursion with no stack guard, review L1-3-1 D1; relinking and compiling depend on
//! neither, "Concurrency").
//!
//! `run --verify` ([`RunMode::Verify`]) decides nothing from tier 1: it runs the cold call over
//! O for every mutation, then one call per valid record whose program the cold call did not
//! execute, and reports every record (and the cached path's status) that differs from the live
//! runs as `outcome-mismatch:<program id>`. A compiled edit the outcome file keeps that differs
//! from the cold call's is reported in `mismatches` (`{cached: {witness}, live: {witness}}`)
//! and leaves the row's status alone, since it decides none. It writes no record and no hint.
//!
//! Memos (re-pin L1-4, [`crate::memo`]): the declaration census of the admission and the facts
//! of each mutation's resolution are memoised under keys that name every input they depend on,
//! `kink_build` and `kink`. A mutation whose facts the memo holds and that tier 1 decides with no
//! call is not resolved (step 1): [`Search::search_memo`] builds its row from the facts with the
//! code [`Search::search_one`] uses for a live resolution. Every mutation that compiles or runs
//! anything is resolved in this command. `run --verify` resolves every mutation and runs the
//! census live, and reports every stored record that differs (`resolution-mismatch`; in
//! `mismatches` also for a mutation `--only` does not select or a corpus error left unsearched,
//! and for a census also when the live census refuses the specification; re-pin L1-4 fix 1).

use crate::{
    admit::{AdmittedSpec, InputSession, admit_spec_with},
    cli::{CommandSpelling, FrontEnd, Verb},
    digest::{hint_key_of, mutation_identity, outcome_context, spec_digest},
    hints::{HintEntry, Hints},
    manifest::{Budget, FlowManifest},
    memo::{self, Facts, MemoUse},
    mutation::{
        EditedRule, InvalidMutation, Mutation, MutationList, ResolvedMutation, resolve, rule_texts,
    },
    outcomes::{CachedOutcome, OutcomeRecord, OutcomeStore, cacheable, slot_name},
    report::{
        RUN_SCHEMA, RUN_VERSION, action, action_spelled, claims_value, executed_cause, matrix,
        refused_action, rules_value, slots_value, specification_diagnostics_value, survivors,
        typing_diagnostics_value, untargeted_rules, unusable_programs,
    },
    results::{
        BaselineRunner, ProgramRow, RESULT_SCHEMA_VERSION, ResultClass, cache_directory, kebab,
        millis, run_digest, runner_refusal, update_results,
    },
};
use k_rust::definition::AttributeKey;
use kink_campaign::{
    CallRecording, CampaignFailure, CampaignOptions, CampaignReport, CompiledEdit, ManifestTest,
    MutantId, MutantPlan, MutantReport, MutantRun, MutantScopeFailure, MutantStatus, OracleOutcome,
    ScheduleMode, TestCase, TestEvidence, TestPlan, TestRun, Witness, derive_mutant_report,
};
use kink_corpus::{Store, admission::AdmissionRecord};
use kink_native::{
    DeclarationCensus,
    coverage::{Authorship, RuleAuthors},
    data::{DataEnds, NamedFinding, data_ends},
    declaration_census,
    execution::SolverProfile,
};
use kink_patch::{
    CandidateGeneration, ClaimSupport, Patch, SentenceRef, Sha256Digest, Weakening, WeakeningKind,
    Withdrawal,
};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    time::Instant,
};

/// The run document's file in the cache directory, rewritten after every mutation.
pub const REPORT_FILE: &str = "report.json";

/// The status of a mutation that does not resolve to a patch (README 5.5).
pub const INVALID_MUTATION: &str = "invalid-mutation";

/// Why tier 1 is off for a build of `profile`, or `None` when it may be used (re-pin decision 5,
/// finding B-09). Under the Z3 profile a solver query can time out (k-rust's per-query timeout).
/// k-rust counts a run's undecided answers (`smtUnknowns`), but kink's own solver queries outside
/// a run (leaf feasibility, the observation decider) carry no such count, so a Z3 result is not a
/// function of the inputs a key names and the Execute promise does not cover it: tier 1 then
/// neither reads nor writes, and neither do the result cache, the memos and the pattern cache. The
/// profile is the build's (`SolverProfile::BUILD`, kink-native's `z3` feature), so it follows
/// workspace feature unification: a kink-flow linked with a Z3 kink-native has it off.
pub const fn tier1_refusal(profile: SolverProfile) -> Option<&'static str> {
    match profile {
        SolverProfile::NoZ3 => None,
        SolverProfile::Z3 => Some(
            "tier 1 is disabled under the z3 profile: a solver query can time out, and although \
             k-rust counts a run's undecided answers, kink's own solver queries outside a run \
             (leaf feasibility, the observation decider) carry no such count, so no outcome is \
             cached or read; every mutation runs live",
        ),
    }
}

/// The `killer_source` of a status decided by a valid tier-1 `killed` record.
pub const SOURCE_OUTCOME_CACHE: &str = "outcome-cache";
/// The `killer_source` of a kill found by the one-program call over the hinted program.
pub const SOURCE_HINT: &str = "hint";
/// The `killer_source` of a kill found by the cold call.
pub const SOURCE_SEARCH: &str = "search";

/// The status of a mutation whose edit only weakens the specification (kink27 R5-WEAKENING):
/// kink-flow's own, decided at resolution with reason [`WEAKENING_REASON`]; kink-corpus and the
/// campaign runner keep their statuses for it.
pub const UNKILLABLE: &str = "unkillable";
/// The reason of an [`UNKILLABLE`] mutation.
pub const WEAKENING_REASON: &str = "weakening";

/// Every status a mutation can have, in the order the counts list them: the runner's
/// mutant statuses with kink-flow's `unkillable`, then the flow's own `invalid-mutation`.
/// `error` is also the status of a corpus error and of an `outcome-mismatch` (their reasons say
/// which).
pub const STATUSES: [&str; 9] = [
    "killed",
    "survived",
    "equivalent",
    UNKILLABLE,
    "not-admitted",
    "timeout",
    "unknown",
    "error",
    INVALID_MUTATION,
];

/// The runner's mutant status as the run document names it.
pub const fn status_name(status: MutantStatus) -> &'static str {
    match status {
        MutantStatus::Killed => "killed",
        MutantStatus::Survived => "survived",
        MutantStatus::Equivalent => "equivalent",
        MutantStatus::NotAdmitted => "not-admitted",
        MutantStatus::Timeout => "timeout",
        MutantStatus::Unknown => "unknown",
        MutantStatus::Error => "error",
    }
}

/// Options of the `run` command.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunOptions {
    /// Run only the mutations with these ids (all when empty).
    pub only: Vec<String>,
    /// The cache directory; default `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
    /// How the programs are ordered inside each tier of the kill search.
    pub order: ProgramOrder,
    /// How many threads compile mutants ahead of their turn (`--compile-workers`; `None`:
    /// [`DEFAULT_COMPILE_WORKERS`]). 1 compiles each mutant in its own campaign call, on the
    /// calling thread. Every run document, outcome record and hint is the same for every value
    /// (re-pin L1-3; [`run_with`]).
    pub compile_workers: Option<usize>,
    /// Whether the warm path's memos are used (`--no-memo`: [`MemoUse::Off`]; re-pin L1-4,
    /// [`crate::memo`]). Every run document, outcome record and hint is the same either way.
    pub memo: MemoUse,
    /// Which programs each mutation runs on: [`ScheduleMode::FirstKill`] (the default), the kill
    /// search, which stops at the first killing program; [`ScheduleMode::Full`] (`--full`), every
    /// comparable program in corpus order, whatever [`RunOptions::order`] says, so that each row
    /// holds every cell of the kill matrix (module documentation).
    pub schedule: ScheduleMode,
}

// `ScheduleMode` has no default of its own: a campaign schedule is not something kink-campaign's
// other callers should get implicitly.
impl Default for RunOptions {
    fn default() -> Self {
        Self {
            only: Vec::new(),
            cache: None,
            order: ProgramOrder::default(),
            compile_workers: None,
            memo: MemoUse::default(),
            schedule: ScheduleMode::FirstKill,
        }
    }
}

/// The run document's name of a schedule (its `schedule`): `first-kill` or `full`, kink-corpus's
/// spelling of the same schedules.
pub const fn schedule_name(schedule: ScheduleMode) -> &'static str {
    match schedule {
        ScheduleMode::FirstKill => "first-kill",
        ScheduleMode::Full => "full",
    }
}

/// The compile workers of a `run` that names none ([`RunOptions::compile_workers`]). On
/// `examples/imp`'s 21 mutants (re-pin L1-3), 4 workers compile in 1.7 s what 1 compiles in
/// 4.2-4.9 s, and 6 or 8 gain little more while taking more of a shared host. At most the
/// validator's memory cap and the host's parallelism are used
/// ([`kink_native::NativeValidator::compile_workers`]).
pub const DEFAULT_COMPILE_WORKERS: usize = 4;

/// How the kill search orders the programs of O, and so inside each tier of a live call (the
/// programs whose coverage witnesses the mutant's compiled edit, then the rest; README 5.6 step 2
/// and 6.4).
///
/// The order never changes a status in the no-Z3 profile while no wall-clock bound
/// (`budget.time_ms`) fires (README 6.4; a run near the bound can time out in one order and
/// finish in another, review L2-1-tail-1 D2): under FirstKill a Killed
/// status comes from any killing test and ranks above every other status, and a mutant-scope
/// failure arises before any test runs (F-05 review 1), so the order changes only which killing
/// program is found first (and hence becomes the hint and the reported killer) and what the
/// search costs. That needs each program's outcome to be independent of the programs run before
/// it in the same call, which k-rust's Execute promise gives without Z3 only: under Z3 a solver
/// query can time out and the mutant's reused backend caches satisfiability answers across
/// programs, so the order can move a status between killed, unknown and survived (a timed-out
/// query is unknown, a warmed answer can kill or agree, and with no kill the fold reads survived;
/// never a false kill: a kill is still a proved distinction; re-pin L2-1-tail, review L2-1-1 D4,
/// review L2-1-tail-1 D1).
///
/// Under [`ProgramOrder::Cost`] the order comes from measured wall times, so the killer found
/// first, the hint, and the SET of tier-1 records written (under FirstKill the programs after
/// the first kill get none) depend on host timing; no record's content does (flow F-16, F-13
/// review 1). The byte-equality of `outcomes/` and `hints.json` across runs holds under
/// [`ProgramOrder::Corpus`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ProgramOrder {
    /// Cheaper killers first (flow F-13): by the result record's `wall_ms` ascending (the wall
    /// time of the program's live baseline run), then corpus order; a record without `wall_ms`
    /// comes last in its tier.
    #[default]
    Cost,
    /// Corpus order (F-05's order), for a reproducible search.
    Corpus,
}

impl ProgramOrder {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Cost => "cost",
            Self::Corpus => "corpus",
        }
    }
}

/// How `run` uses the outcome cache.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum RunMode {
    /// The kill search with both tiers (`kink-flow run`).
    #[default]
    Search,
    /// Re-prove every valid tier-1 record and decide nothing from it (`kink-flow run
    /// --verify`, README 7.5.3): no tier-1 decision, no hint, no write but the report.
    Verify,
}

/// One comparable program: a possible killer.
struct Candidate<'r> {
    /// The manifest's program index.
    index: usize,
    id: &'r str,
    digest: Sha256Digest,
    /// The cached record's run digest (a comparable record always has one, unless edited).
    run_sha256: Option<&'r str>,
    /// The cached record's `wall_ms`: the cost key of [`ProgramOrder::Cost`].
    wall_ms: Option<u64>,
    /// The cached coverage's `complete`: a run that is not complete covers only what it explored
    /// before it stopped, so it witnesses every edit (kink-campaign `coverage_selected`).
    complete: bool,
    /// The `(module, index)` of every baseline sentence its cached coverage matches (k-rust
    /// `matched`, the record's `coverage.sentences`).
    matches: BTreeSet<(String, u64)>,
    /// The `(module, index)` of every baseline sentence its cached coverage applies (k-rust
    /// `applied`, the record's `coverage.applied_sentences`; re-pin L2-1-tail): every candidate a
    /// step built of the sentence, defined or rolled back. Wider than `fired_by` (k-rust
    /// `committed`, KINK-R4) on purpose: an edit can make a rolled-back candidate defined, so a
    /// program holding one witnesses the edit.
    applies: BTreeSet<(String, u64)>,
}

fn candidate<'r>(index: usize, id: &'r str, row: &'r ProgramRow) -> Option<Candidate<'r>> {
    if row.class() != Some(ResultClass::Comparable.as_str()) {
        return None;
    }
    let record = row.record.as_ref()?;
    let sentences = |key: &str| {
        record["coverage"][key]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|sentence| {
                Some((
                    sentence["module"].as_str()?.to_owned(),
                    sentence["index"].as_u64()?,
                ))
            })
            .collect()
    };
    Some(Candidate {
        index,
        id,
        digest: row.digest?,
        run_sha256: record["run_sha256"].as_str(),
        wall_ms: record["wall_ms"].as_u64(),
        complete: record["coverage"]["complete"].as_bool().unwrap_or(false),
        matches: sentences("sentences"),
        applies: sentences("applied_sentences"),
    })
}

/// A corpus error: no verdict for the mutation, and the run stops.
struct CorpusError {
    reason: String,
    detail: String,
}

/// What the command counts about tier 1, for the run document's `outcome_cache`.
#[derive(Clone, Copy, Debug, Default)]
struct Stats {
    /// Mutations whose status came from tier 1 with no campaign call.
    mutations_from_cache: usize,
    /// (mutation, program) outcomes taken from valid records into a status.
    programs_from_cache: usize,
    /// Tier-1 records written.
    records_written: usize,
}

/// One live campaign call of the kill search: the mutant's run, the call's baseline evidence
/// (for the sides of a distinguishing slot), what the session recorded (wall times and leaf
/// censuses) and the call's wall time.
struct LiveCall {
    mutant: MutantRun,
    /// The candidates in the order the call ran them ([`Search::call_untimed`]): the programs
    /// whose coverage witnesses the mutant's compiled edit first, under the first-kill search.
    order: Vec<usize>,
    /// The compiled edit of the side the call's programs ran on (kink-campaign
    /// [`CompiledEdit::between`]) read through the baseline's rule authors; `None` when the
    /// mutant was refused before that side compiled.
    witness: Option<EditWitness>,
    baseline: Vec<TestEvidence>,
    recording: CallRecording,
    /// The functions some of whose equations the mutation edits (kink-patch
    /// `ClaimSupport::edited_equation_heads`): the open applications a cause may name.
    edited: BTreeSet<String>,
    /// The kill evidence of each distinguishing test, by test id (CF-16, [`kill_differences`]).
    differences: BTreeMap<String, Value>,
}

/// The campaign calls of one mutation row: the programs of each call (candidate indices), its
/// status and its wall time in milliseconds.
type Calls = Vec<(Vec<usize>, Value, u64)>;

/// A live program's outcome in `run --verify`.
enum Live {
    /// The test ran: its run and the run digest of the mutant's evidence row.
    Ran(TestRun, Option<String>),
    /// The one-program call ran no test (a mutant-scope failure): the call's status.
    NotRun(&'static str),
}

/// The command's state: the admitted specification, its one validator, the corpus, the
/// caches.
struct Search<'a, 's> {
    spec: &'a AdmittedSpec,
    manifest: &'a FlowManifest,
    inputs: &'a mut InputSession<'s>,
    /// The command's campaign calls, through its one baseline session.
    runner: &'a BaselineRunner<'a>,
    rows: &'a [ProgramRow],
    candidates: Vec<Candidate<'a>>,
    /// Each candidate's test case with the specification's oracles, assembled on first use.
    tests: Vec<Option<TestCase>>,
    mode: RunMode,
    /// The tier-1 store; `None` when kink's build identity cannot be computed.
    tier1: Option<OutcomeStore>,
    hints: Hints,
    store: Store,
    stats: Stats,
    /// `run --verify`'s disagreements, for the run document's `mismatches`.
    mismatches: Vec<Value>,
    /// How the programs are ordered inside each tier of O.
    order: ProgramOrder,
    /// Which programs each mutation runs on ([`RunOptions::schedule`]).
    schedule: ScheduleMode,
    /// The baseline's claim support, for each row's `removed_claims` (the runner builds every
    /// mutant with the same function, re-pin R0c-fix-2).
    support: ClaimSupport,
    /// How next steps spell the front end's commands.
    spelling: &'a dyn CommandSpelling,
}

impl Search<'_, '_> {
    fn test(&mut self, candidate: usize) -> Result<TestCase, CorpusError> {
        if let Some(test) = &self.tests[candidate] {
            return Ok(test.clone());
        }
        let index = self.candidates[candidate].index;
        let program = &self.manifest.programs[index];
        let row = &self.rows[index];
        let mut test = match (&row.test, &row.inputs) {
            (Some(test), _) => test.clone(),
            (None, Some(case)) => {
                self.inputs
                    .test_case(program, case)
                    .map_err(|refusal| CorpusError {
                        reason: format!("program-refused:{}", program.id),
                        detail: format!("{}/{}: {}", refusal.stage, refusal.reason, refusal.detail),
                    })?
            }
            (None, None) => {
                return Err(CorpusError {
                    reason: format!("program-refused:{}", program.id),
                    detail: "the program has a comparable record but no inputs".into(),
                });
            }
        };
        test.oracles = self.spec.result.oracles();
        self.tests[candidate] = Some(test.clone());
        Ok(test)
    }

    /// One campaign call over `order` (candidate indices), then the drift check: the call's
    /// wall time in milliseconds (outside every digest and key), and the live call or the
    /// corpus error.
    fn call(
        &mut self,
        generation: &CandidateGeneration<'_>,
        order: &[usize],
    ) -> (u64, Result<LiveCall, CorpusError>) {
        let started = Instant::now();
        let result = self.call_untimed(generation, order);
        (millis(started.elapsed()), result)
    }

    fn call_untimed(
        &mut self,
        generation: &CandidateGeneration<'_>,
        order: &[usize],
    ) -> Result<LiveCall, CorpusError> {
        let mut tests = Vec::with_capacity(order.len());
        for &candidate in order {
            tests.push(self.test(candidate)?);
        }
        let options = CampaignOptions {
            schedule: self.schedule,
            selection: kink_campaign::SelectionPolicy::None,
            share_evidence: false,
            run: kink_campaign::RunOptions {
                work: self.manifest.budget.work(),
                // Re-pin L1-2 (decision 6): a work-bound mutant run can kill one-sidedly. Every
                // campaign call of the flow classifies with `all_normal` (`results::classify`),
                // which never answers a semantic crash.
                one_sided: kink_campaign::OneSided::NoCrashClassifier,
                ..kink_campaign::RunOptions::default()
            },
            // The command compiles ahead across mutations ([`run_with`]); a call holds one.
            compile_workers: 1,
        };
        // The witness order (README 5.6 step 2): once the mutant's claim-free side compiles, the
        // runner asks which programs come first, from that side's compiled edit. The full
        // schedule keeps corpus order and only records the edit, for the row's `witnesses`.
        let candidates = &self.candidates;
        let authors = self.runner.authors();
        let schedule = self.schedule;
        let mut witness = None;
        let mut first = |compiled: &CompiledEdit| {
            let read = EditWitness::of(compiled, authors);
            let first = match schedule {
                ScheduleMode::FirstKill => order
                    .iter()
                    .map(|&c| &candidates[c])
                    .filter(|candidate| witnesses(candidate, &read))
                    .map(|candidate| candidate.id.to_owned())
                    .collect(),
                ScheduleMode::Full => BTreeSet::new(),
            };
            witness = Some(read);
            first
        };
        let run = self.runner.call_ordered(
            &tests,
            std::slice::from_ref(generation),
            &options,
            &mut first,
        );
        let mut run = run.map_err(|failure| CorpusError {
            reason: "campaign-refused".into(),
            detail: format!(
                "the campaign runner refused the call over {:?}: {failure}; the cached \
                         results no longer describe the baseline runs: run `{} --verify`",
                self.ids(order),
                self.spelling.verb(Verb::Results)
            ),
        })?;
        // The drift check (README 5.4): every program's baseline row of this call must have
        // its cached record's run digest. The reason names the program from the candidate,
        // never from a message (F-05 review 1 minor 2).
        let mut mismatched = Vec::new();
        for &candidate in order {
            let candidate = &self.candidates[candidate];
            let now = run
                .baseline
                .iter()
                .find(|evidence| evidence.test_id == candidate.id)
                .and_then(|evidence| CampaignReport::baseline_row(evidence).ok())
                .as_ref()
                .and_then(run_digest)
                .map(|digest| digest.to_string());
            if now.is_none() || now.as_deref() != candidate.run_sha256 {
                mismatched.push((
                    candidate.id,
                    format!(
                        "{}: cached run_sha256 {}, now {}",
                        candidate.id,
                        candidate.run_sha256.unwrap_or("null"),
                        now.as_deref().unwrap_or("no baseline row"),
                    ),
                ));
            }
        }
        let count = (run.baseline.len() != order.len()).then(|| {
            format!(
                "the call ran {} baseline programs for {} tests",
                run.baseline.len(),
                order.len()
            )
        });
        if let Some(reason) = drift_reason(mismatched.first().map(|(id, _)| *id), count.is_some()) {
            let details = mismatched
                .into_iter()
                .map(|(_, detail)| detail)
                .chain(count)
                .collect::<Vec<_>>();
            return Err(CorpusError {
                reason,
                detail: format!(
                    "{}; run `{} --verify`",
                    details.join("; "),
                    self.spelling.verb(Verb::Results)
                ),
            });
        }
        if run.mutants.len() != 1 {
            return Err(CorpusError {
                reason: "campaign-refused".into(),
                detail: format!("the runner returned {} mutants for one", run.mutants.len()),
            });
        }
        let mutant = run.mutants.remove(0);
        // The plan lists every test in the order it ran (later ones skipped after a kill), or
        // none when the mutant was refused before running any.
        let ran = if mutant.plan.tests.is_empty() {
            order.to_vec()
        } else {
            mutant
                .plan
                .tests
                .iter()
                .filter_map(|test| self.position(&test.test_id))
                .collect()
        };
        Ok(LiveCall {
            differences: kill_differences(&mutant, &run.baseline, self.runner.end_reader()),
            mutant,
            order: ran,
            witness,
            baseline: run.baseline,
            recording: self.runner.last_call(),
            edited: self.support.edited_equation_heads(
                self.spec.validator.baseline(),
                &generation.candidates()[0].patch,
            ),
        })
    }

    fn ids(&self, order: &[usize]) -> Vec<&str> {
        order.iter().map(|&c| self.candidates[c].id).collect()
    }

    fn position(&self, id: &str) -> Option<usize> {
        self.candidates.iter().position(|c| c.id == id)
    }

    /// The `calls` of a mutation row (the programs each campaign call ran, and its status) and
    /// its `call_wall_ms` (each call's wall time, in the same order).
    fn calls(&self, calls: &Calls) -> (Vec<Value>, Vec<Value>) {
        calls
            .iter()
            .map(|(order, status, wall_ms)| {
                (
                    json!({"programs": self.ids(order), "status": status}),
                    json!(wall_ms),
                )
            })
            .unzip()
    }

    /// The executed entry of a valid tier-1 record (`cached: true`): no run in this command,
    /// so no timings or cause; a kill's difference and sides are the record's (CF-16).
    fn cached_entry(&self, candidate: usize, record: &OutcomeRecord) -> Value {
        json!({
            "program": self.candidates[candidate].id,
            "outcome": compared_outcome(&record.slots),
            "slots": slots_value(
                &self.spec.result.slots(),
                &record.slots,
                None,
                None,
                false,
                &record.difference,
            ),
            "difference": record.difference,
            "cause": null,
            "cached": true,
            "wall_ms": null,
            "baseline_ms": null,
            "baseline_reused": null,
        })
    }

    /// The valid tier-1 records of the programs of `order`, in that order (README 7.5.3): the
    /// store's integrity checks, then the program is a current comparable candidate whose
    /// result record has the record's baseline run digest. A `killed` record of a program
    /// that is in the corpus but not comparable is reported as the row's `unusable_killer`.
    fn valid_records(
        &self,
        identity: Option<Sha256Digest>,
        order: &[usize],
        row: &mut Map<String, Value>,
    ) -> (Vec<(usize, OutcomeRecord)>, Option<EditWitness>) {
        let (Some(store), Some(identity)) = (&self.tier1, identity) else {
            return (Vec::new(), None);
        };
        let (stored, witness) = store.read_with_witness(identity);
        // A row decided with no compile reads the compiled edit the file keeps; a live call
        // replaces it with its own ([`Search::set_witnesses`]).
        let witness = EditWitness::from_value(&witness);
        if let Some(witness) = &witness {
            row.insert("witnesses".into(), self.witness_programs(order, witness));
        }
        for (program, record) in &stored {
            if record.outcome == CachedOutcome::Killed
                && !self
                    .candidates
                    .iter()
                    .any(|c| c.digest.to_string() == *program)
            {
                self.unusable(row, program, SOURCE_OUTCOME_CACHE);
            }
        }
        let records = order
            .iter()
            .filter_map(|&c| {
                let candidate = &self.candidates[c];
                let record = stored.get(&candidate.digest.to_string())?;
                (candidate.run_sha256 == Some(record.baseline_run_sha256.as_str()))
                    .then(|| (c, record.clone()))
            })
            .collect();
        (records, witness)
    }

    /// Report, once per row, a killer that names a program of the corpus whose class is not
    /// comparable: `unusable_killer: {program, class, cause, source}` (README 7.5.7).
    fn unusable(&self, row: &mut Map<String, Value>, digest: &str, source: &str) {
        if row.contains_key("unusable_killer") {
            return;
        }
        let found = self
            .manifest
            .programs
            .iter()
            .zip(self.rows)
            .find(|(_, r)| r.digest.is_some_and(|d| d.to_string() == digest));
        if let Some((program, program_row)) = found {
            row.insert(
                "unusable_killer".into(),
                json!({
                    "program": program.id,
                    "class": program_row.row["class"],
                    "cause": program_row.row["cause"],
                    "source": source,
                }),
            );
        }
    }

    /// The assembled plan's report (README 7.5.3 step 5): the cached outcomes in the given
    /// order, then the live plan's tests (`live`: the call's order and plan), with the live
    /// plan's mutant-scope failure, mutant id and claims; the manifest lists the same ids in
    /// the same order. The fold is kink-campaign's own.
    ///
    /// A live mutant-scope `Infrastructure` failure (the equivalence check or the mutant's
    /// backend failing while the mutant is prepared, before any test runs) is not the
    /// determinism failure `outcome-conflict` stands for (F-14 review 1 m2, flow F-16): it
    /// dominates every test's evidence and does not depend on which programs the call has, so
    /// the status is the live plan's alone, which is the status a cold call gives (`error`,
    /// with the failure as its reason), and the cached agreements do not enter the plan.
    fn assemble(
        &self,
        cached: &[(usize, OutcomeRecord)],
        live: Option<(&[usize], &MutantPlan)>,
    ) -> Result<MutantReport, CampaignFailure> {
        let cached = match live {
            Some((_, plan)) if plan.mutant_failure == Some(MutantScopeFailure::Infrastructure) => {
                &[][..]
            }
            _ => cached,
        };
        let mut tests = cached
            .iter()
            .map(|(c, record)| TestPlan {
                test_id: self.candidates[*c].id.to_owned(),
                run: record.test_run(),
            })
            .collect::<Vec<_>>();
        let mut ids = cached
            .iter()
            .map(|(c, _)| self.candidates[*c].id.to_owned())
            .collect::<Vec<_>>();
        let (mutant_failure, mutant_id, claims, inconsistent_pairs) = match live {
            Some((order, plan)) => {
                tests.extend(plan.tests.iter().cloned());
                ids.extend(self.ids(order).into_iter().map(str::to_owned));
                (
                    plan.mutant_failure,
                    plan.mutant_id,
                    plan.claims.clone(),
                    plan.inconsistent_pairs.clone(),
                )
            }
            None => (None, MutantId(0), Withdrawal::default(), Vec::new()),
        };
        let plan = MutantPlan {
            selection: None,
            mutant_id,
            tests,
            mutant_failure,
            claims,
            inconsistent_pairs,
        };
        let manifest = ids
            .into_iter()
            .map(|test_id| ManifestTest {
                test_id,
                slot_count: self.spec.result.slots().len(),
            })
            .collect::<Vec<_>>();
        derive_mutant_report(&plan, &manifest, self.schedule)
    }

    /// The programs O of a mutation (README 5.6 step 2), as candidate indices, before its mutant
    /// compiles: under [`ScheduleMode::Full`] every candidate in corpus order (the candidates are
    /// built in manifest order), under [`ScheduleMode::FirstKill`] by [`ProgramOrder`]
    /// ([`order`]). A live call then runs first the programs whose coverage witnesses the
    /// mutant's compiled edit ([`Search::call_untimed`]); what is decided before any compile
    /// (tier 1, the compiles ahead) depends only on the set of programs, not on their order.
    fn program_order(&self) -> Vec<usize> {
        match self.schedule {
            ScheduleMode::Full => (0..self.candidates.len()).collect(),
            ScheduleMode::FirstKill => order(&self.candidates, self.order),
        }
    }

    /// The row's `witnesses`: the programs of `order` (O) whose coverage witnesses the compiled
    /// edit ([`witnesses`]), in O's order, which is the order a live call tries them in.
    fn witness_programs(&self, order: &[usize], witness: &EditWitness) -> Value {
        json!(
            order
                .iter()
                .map(|&c| &self.candidates[c])
                .filter(|candidate| witnesses(candidate, witness))
                .map(|candidate| candidate.id)
                .collect::<Vec<_>>()
        )
    }

    /// Set the row's `witnesses` from a live call's compiled edit, and keep the edit for the
    /// outcome file (`kept`). Every call of one mutation compiles the same mutant, so a later
    /// call's edit is the earlier one's.
    fn set_witnesses(
        &self,
        row: &mut Map<String, Value>,
        order: &[usize],
        live: &LiveCall,
        kept: &mut Option<EditWitness>,
    ) {
        if let Some(witness) = &live.witness {
            row.insert("witnesses".into(), self.witness_programs(order, witness));
            *kept = Some(witness.clone());
        }
    }

    /// The row's `killed_by` of a report a fold decided: null under [`ScheduleMode::FirstKill`]
    /// (its killer is the first the search reached, which depends on the order and on what the
    /// cache holds); under [`ScheduleMode::Full`] every killing program in corpus order, empty
    /// unless the status is `killed`.
    fn killed_by(&self, report: &MutantReport) -> Option<Vec<String>> {
        if self.schedule != ScheduleMode::Full {
            return None;
        }
        if report.status != MutantStatus::Killed {
            return Some(Vec::new());
        }
        let mut killers = report
            .killing_test_ids
            .iter()
            .filter_map(|id| self.position(id))
            .collect::<Vec<_>>();
        killers.sort_unstable();
        killers.dedup();
        Some(
            killers
                .into_iter()
                .map(|c| self.candidates[c].id.to_owned())
                .collect(),
        )
    }

    /// Write the tier-1 records of a mutation's live calls (README 7.5.3 step 7); a failed write
    /// is the row's `cache_error`.
    fn write_records(
        &mut self,
        identity: Option<Sha256Digest>,
        mutation: &Mutation,
        row: &mut Map<String, Value>,
        records: &[(String, OutcomeRecord)],
        witness: Option<&EditWitness>,
    ) {
        let (Some(store), Some(identity)) = (&self.tier1, identity) else {
            return;
        };
        if records.is_empty() {
            return;
        }
        match store.write(
            &self.store,
            identity,
            &mutation.id,
            &row["removed_claims"],
            &witness.map_or(Value::Null, EditWitness::value),
            records,
        ) {
            Ok(written) => self.stats.records_written += written,
            Err(e) => {
                row.insert(
                    "cache_error".into(),
                    json!(format!("cannot write the outcome records: {e}")),
                );
            }
        }
    }

    /// The tier-1 records a live call gives (README 7.5.3 step 7): one per test whose outcome
    /// is cacheable, none when the call's plan carries a mutant-scope failure. A `killed`
    /// record carries the test's kill evidence from `differences` (CF-16).
    fn live_records(
        &self,
        run: &MutantRun,
        differences: &BTreeMap<String, Value>,
    ) -> Vec<(String, OutcomeRecord)> {
        if run.plan.mutant_failure.is_some() {
            return Vec::new();
        }
        run.plan
            .tests
            .iter()
            .filter_map(|test| {
                let (outcome, slots) = cacheable(&test.run)?;
                let candidate = &self.candidates[self.position(&test.test_id)?];
                Some((
                    candidate.digest.to_string(),
                    OutcomeRecord {
                        program_id: candidate.id.to_owned(),
                        // Equal to the live baseline row's digest: the drift check passed.
                        baseline_run_sha256: candidate.run_sha256?.to_owned(),
                        outcome,
                        slots: slots.to_vec(),
                        mutant_run_sha256: mutant_run_sha256(run, &test.test_id)?,
                        difference: match outcome {
                            CachedOutcome::Killed => differences
                                .get(&test.test_id)
                                .cloned()
                                .unwrap_or(Value::Null),
                            CachedOutcome::Agree => Value::Null,
                        },
                        allowance_bytes: Some(
                            k_rust::k_rust_backend::allowance::Allowance::of_process().bytes(),
                        ),
                    },
                ))
            })
            .collect()
    }

    fn hint_entry(&self, candidate: usize, mutation: &Mutation) -> HintEntry {
        let candidate = &self.candidates[candidate];
        HintEntry {
            program_digest: candidate.digest.to_string(),
            program_id: candidate.id.to_owned(),
            mutation_id: mutation.id.clone(),
        }
    }

    /// The kill search for one mutation: its row of the run document, and whether it ended in
    /// a corpus error (the run then stops, and nothing is written to tier 1 for it).
    /// The mutants [`Search::search_one`] would compile for `resolution` given the stores now
    /// (re-pin L1-3, for compiling ahead): none when the mutation resolves to no generation, no
    /// program is in O, or tier 1 decides it with no call (a valid killed record, or a valid
    /// agreement for every program of O); otherwise each candidate's patch and its withdrawing
    /// patch ([`kink_campaign::mutant_compiles`]). Under [`ScheduleMode::Full`] a valid killed
    /// record does not decide ([`tier1_decides`]). A guess that differs from what the search then
    /// does costs a compile, never a row.
    fn live_compiles(&self, resolution: &Result<ResolvedMutation, InvalidMutation>) -> Vec<Patch> {
        let Ok(resolved) = resolution else {
            return Vec::new();
        };
        let baseline = self.spec.validator.baseline();
        // An unkillable mutation compiles nothing (kink27 R5-WEAKENING).
        if self.support.weakening(baseline, &resolved.patch).is_some() {
            return Vec::new();
        }
        let Ok(generation) = resolved.generation(baseline) else {
            return Vec::new();
        };
        let order = self.program_order();
        if order.is_empty() || self.gated() {
            return Vec::new();
        }
        if self.mode == RunMode::Search {
            let identity = mutation_identity(&self.spec.loaded.baseline, &resolved.patch);
            let (records, _) = self.valid_records(identity, &order, &mut Map::new());
            if tier1_decides(&order, &records, self.schedule) {
                return Vec::new();
            }
        }
        generation
            .candidates()
            .iter()
            .flat_map(|candidate| {
                kink_campaign::mutant_compiles(baseline, &self.support, &candidate.patch)
            })
            .collect()
    }

    fn search_one(
        &mut self,
        mutation: &Mutation,
        resolution: &Result<ResolvedMutation, InvalidMutation>,
    ) -> (Value, bool) {
        let mut row = Map::new();
        row.insert("id".into(), json!(mutation.id));
        // The row's `note` is the mutation's misunderstanding (its key keeps the run schema).
        row.insert("note".into(), json!(mutation.misunderstanding));
        let resolved = match resolution {
            Ok(resolved) => resolved,
            Err(e) => return (invalid(row, e.clone(), Value::Null), false),
        };
        let digest = resolved.digest;
        row.insert("digest".into(), json!(digest.to_string()));
        // The survivor report's rule texts (README 5.7); a killed mutation drops them below.
        row.insert("rules".into(), rules_value(&resolved.rules));
        // The generation must derive from the validator's own baseline (the runner refuses any
        // other); the patch is pinned, so it applies to it as to the loaded baseline.
        let generation = match resolved.generation(self.spec.validator.baseline()) {
            Ok(generation) => generation,
            Err(e) => return (invalid(row, e, json!(digest.to_string())), false),
        };
        let facts = self.facts(resolved, &generation);
        self.search_facts(mutation, row, &facts, Some(&generation))
            .expect("a live resolution's search always gives a row")
    }

    /// Whether the baseline has a finding no `[spec] assume_joined` name assumes, so that no end
    /// of it is data (kink-native `data::data_ends`) and no mutation can be killed (fz26
    /// KINK-BASELINE-FINDINGS).
    fn gated(&self) -> bool {
        data_ends(&self.spec.data) == DataEnds::None
    }

    /// The row of a mutation of a baseline with findings left ([`Search::gated`]): `unknown`
    /// with reason `baseline-findings` (kink-campaign's fold of a mutant-scope failure that
    /// precedes execution, over the programs of O), the findings named with their verdicts, and
    /// no call.
    fn baseline_findings_row(&self, mut row: Map<String, Value>, order: &[usize]) -> Value {
        let report = self
            .assemble(
                &[],
                Some((
                    order,
                    &MutantPlan {
                        selection: None,
                        mutant_id: MutantId(0),
                        tests: Vec::new(),
                        mutant_failure: Some(MutantScopeFailure::BaselineFindings),
                        claims: Withdrawal::default(),
                        inconsistent_pairs: Vec::new(),
                    },
                )),
            )
            .expect("a mutant-scope failure with no test is a valid plan");
        row.insert(
            "findings".into(),
            json!(
                self.spec
                    .data
                    .unnamed()
                    .iter()
                    .map(NamedFinding::value)
                    .collect::<Vec<_>>()
            ),
        );
        let killed_by = self.killed_by(&report);
        verdict_row(
            row,
            &report,
            killed_by,
            Some(kebab(&format!(
                "{:?}",
                MutantScopeFailure::BaselineFindings
            ))),
            None,
            RowCalls::default(),
            Vec::new(),
        )
    }

    /// The facts of `resolved` that a row reads before any call ([`Facts`]; re-pin L1-4): what
    /// the resolution memo stores.
    fn facts(&self, resolved: &ResolvedMutation, generation: &CandidateGeneration<'_>) -> Facts {
        let baseline = self.spec.validator.baseline();
        Facts {
            digest: resolved.digest,
            rules: resolved.rules.clone(),
            identity: mutation_identity(&self.spec.loaded.baseline, &resolved.patch),
            // Re-pin L2-2-fix-1: the edited rules' typing errors in compilation's view,
            // diagnostics only (compilation decides whether the mutant is valid).
            typing_diagnostics: typing_diagnostics_value(
                baseline,
                &generation.candidates()[0].typing_diagnostics,
            ),
            removed_claims: self
                .support
                .withdraw(baseline, &resolved.patch)
                .map_or(Value::Null, |withdrawal| {
                    claims_value(baseline, &withdrawal)
                }),
            weakening: weakening_value(
                baseline,
                self.support.weakening(baseline, &resolved.patch).as_ref(),
            ),
        }
    }

    /// Whether tier 1 decides the mutation of `facts` with no call given the stores now: no
    /// program is in O (the row is the corpus error `no-comparable-program`), or a valid killed
    /// record (first-kill only), or a valid record for every program of O ([`tier1_decides`],
    /// [`Search::search_facts`] steps 2 and 3). Only in search mode. The resolution memo is used only then (re-pin L1-4).
    fn decided(&self, facts: &Facts) -> bool {
        if self.mode != RunMode::Search {
            return false;
        }
        // An unkillable mutation is decided by its edit alone (kink27 R5-WEAKENING).
        if !facts.weakening.is_null() {
            return true;
        }
        let order = self.program_order();
        if !order.is_empty() && self.gated() {
            return true;
        }
        let (records, _) = self.valid_records(facts.identity, &order, &mut Map::new());
        tier1_decides(&order, &records, self.schedule)
    }

    /// The row of a mutation whose facts the resolution memo holds, when tier 1 decides it with
    /// no call ([`Search::decided`]): the row [`Search::search_one`] gives the live resolution
    /// of the same inputs, built from the same facts by the same code. `None` when tier 1 does
    /// not decide it; the caller then resolves the mutation live.
    fn search_memo(&mut self, mutation: &Mutation, facts: &Facts) -> Option<(Value, bool)> {
        if !self.decided(facts) {
            return None;
        }
        let mut row = Map::new();
        row.insert("id".into(), json!(mutation.id));
        // The row's `note` is the mutation's misunderstanding (its key keeps the run schema).
        row.insert("note".into(), json!(mutation.misunderstanding));
        row.insert("digest".into(), json!(facts.digest.to_string()));
        row.insert("rules".into(), rules_value(&facts.rules));
        self.search_facts(mutation, row, facts, None)
    }

    /// The kill search for one mutation from the facts of its resolution: steps 2 to 7 of the
    /// module docs. `generation` is the live resolution's, or `None` for the facts of the
    /// resolution memo; then the search stops with `None`, before it reads or removes the hint
    /// and before it counts or writes anything, if tier 1 does not decide after all (another
    /// command wrote the tier-1 store since [`Search::decided`] read it), and the caller resolves
    /// the mutation live, so the live search sees the hint as a run without memos does.
    fn search_facts(
        &mut self,
        mutation: &Mutation,
        mut row: Map<String, Value>,
        facts: &Facts,
        generation: Option<&CandidateGeneration<'_>>,
    ) -> Option<(Value, bool)> {
        row.insert(
            "typing_diagnostics".into(),
            facts.typing_diagnostics.clone(),
        );
        let order = self.program_order();
        // Null until the outcome file's compiled edit ([`Search::valid_records`]) or a live call's
        // ([`Search::set_witnesses`]) gives it, or an empty O makes it empty.
        row.insert("witnesses".into(), Value::Null);
        let identity = facts.identity;
        row.insert(
            "identity".into(),
            json!(identity.map(|identity| identity.to_string())),
        );
        row.insert("removed_claims".into(), facts.removed_claims.clone());
        // Filled from the verdict's plan (re-pin R0c-fix-3): the pairs of equations that refuse
        // an inconsistent mutant; empty otherwise.
        row.insert("inconsistent_pairs".into(), json!([]));
        row.insert("weakening".into(), facts.weakening.clone());
        let key = hint_key_of(mutation, &facts.rules);
        // fz26 KINK-BASELINE-FINDINGS: on a baseline with a finding no `[spec] assume_joined`
        // name assumes, no end is data, so no program can kill: the mutation is unknown before
        // any store is read or any call made (no cached outcome decides it, whatever it says).
        if !order.is_empty() && self.gated() {
            if self.mode == RunMode::Search {
                self.hints.remove(key);
            }
            return Some((self.baseline_findings_row(row, &order), false));
        }
        // kink27 R5-WEAKENING: a mutation whose edit only weakens the specification has every
        // model of the specification among its models, so no program can kill it. The verdict
        // depends on the mutation alone: no store is read, no call made, nothing re-run. It is
        // decided after the baseline-findings check (fix round 1): the argument reads the
        // baseline's normal forms as a model, which an unassumed finding puts in doubt, and the
        // specification's own findings are what the author has to fix first.
        if !facts.weakening.is_null() {
            row.insert("status".into(), json!(UNKILLABLE));
            row.insert("reason".into(), json!(WEAKENING_REASON));
            if self.mode == RunMode::Search {
                self.hints.remove(key);
            }
            return Some((
                finish(row, None, None, RowCalls::default(), Vec::new()),
                false,
            ));
        }
        let (records, stored) = self.valid_records(identity, &order, &mut row);
        // A memo's facts carry no generation (re-pin L1-4): they are used only when tier 1
        // decides with no call. Otherwise the search stops here, on the records it decides from,
        // before the hint is read or removed and before anything is counted or written (re-pin
        // L1-4 fix 1, review D6), and the caller resolves the mutation live.
        if generation.is_none() && !tier1_decides(&order, &records, self.schedule) {
            return None;
        }
        // Tier 2: the hint, when it names a comparable program; otherwise it is removed.
        let mut hint = None;
        if self.mode == RunMode::Search
            && let Some(entry) = self.hints.get(key).cloned()
        {
            hint = self
                .candidates
                .iter()
                .position(|c| c.digest.to_string() == entry.program_digest);
            if hint.is_none() {
                row.insert(
                    "stale_killer".into(),
                    json!(format!(
                        "the hinted killer {} (digest {}) is not a comparable program; the hint \
                         is removed",
                        entry.program_id, entry.program_digest
                    )),
                );
                self.unusable(&mut row, &entry.program_digest, SOURCE_HINT);
                self.hints.remove(key);
            }
        }
        if order.is_empty() {
            row.insert("status".into(), json!("error"));
            row.insert("reason".into(), json!("no-comparable-program"));
            // No program of an empty O witnesses any edit, so `witnesses` is exactly empty,
            // whatever the edit, with no compile.
            row.insert("witnesses".into(), json!([]));
            row.insert(
                "detail".into(),
                json!("no program of the corpus has a comparable result, so nothing can kill"),
            );
            if self.mode == RunMode::Search {
                self.hints.remove(key);
            }
            return Some((
                finish(row, None, None, RowCalls::default(), Vec::new()),
                false,
            ));
        }
        if self.mode == RunMode::Verify {
            let generation = generation.expect("run --verify resolves every mutation live");
            return Some(self.verify_one(
                row,
                mutation,
                generation,
                &order,
                &records,
                stored.as_ref(),
            ));
        }
        if self.schedule == ScheduleMode::Full {
            return Some(self.search_full(mutation, row, facts, generation, &order, records));
        }

        // The valid records in the order a live call would run O: the programs the outcome file's
        // compiled edit says witness it first, then the rest, each in O's order (O's order
        // without one). It names the cached killer and orders the cached entries.
        let mut records = records;
        if let Some(witness) = &stored {
            records.sort_by_key(|(c, _)| !witnesses(&self.candidates[*c], witness));
        }
        // Tier 1, step 2: a valid killed record decides, with no call, its killer the first.
        if let Some((c, record)) = records
            .iter()
            .find(|(_, record)| record.outcome == CachedOutcome::Killed)
        {
            let report = self.assemble(&[(*c, record.clone())], None);
            let report = report.expect("one cached killed test is a valid plan");
            debug_assert_eq!(report.status, MutantStatus::Killed);
            self.stats.mutations_from_cache += 1;
            self.stats.programs_from_cache += 1;
            self.hints.insert(key, self.hint_entry(*c, mutation));
            let executed = vec![self.cached_entry(*c, record)];
            return Some((
                verdict_row(
                    row,
                    &report,
                    None,
                    None,
                    Some(SOURCE_OUTCOME_CACHE),
                    RowCalls::default(),
                    executed,
                ),
                false,
            ));
        }
        // Step 3: A (every valid record is now an agreement) and L.
        let agree = records;
        let live_order = order
            .iter()
            .copied()
            .filter(|c| !agree.iter().any(|(a, _)| a == c))
            .collect::<Vec<_>>();
        let mut executed = agree
            .iter()
            .map(|(c, record)| self.cached_entry(*c, record))
            .collect::<Vec<_>>();
        self.stats.programs_from_cache += agree.len();
        if live_order.is_empty() {
            let report = self
                .assemble(&agree, None)
                .expect("cached agreements form a valid plan");
            self.stats.mutations_from_cache += 1;
            self.hints.remove(key);
            return Some((
                verdict_row(
                    row,
                    &report,
                    None,
                    None,
                    None,
                    RowCalls::default(),
                    executed,
                ),
                false,
            ));
        }

        // Step 4: live calls, the hinted program alone first. A memo's facts never reach here:
        // tier 1 decides them (checked above on these records), so step 2 or 3 returned.
        let generation = generation
            .expect("a memo's facts are searched only when tier 1 decides, in step 2 or 3");
        let mut calls = Calls::new();
        let mut runs = Vec::<(Vec<usize>, MutantRun)>::new();
        // The kill evidence of the live calls, by program; a later call's replaces an earlier's,
        // as its record does (step 7).
        let mut differences = BTreeMap::<String, Value>::new();
        let mut witness = None;
        let mut source = SOURCE_SEARCH;
        if let Some(h) = hint.filter(|h| live_order.contains(h)) {
            match self.call(generation, &[h]) {
                (wall_ms, Err(error)) => {
                    calls.push((vec![h], json!("error"), wall_ms));
                    return Some(self.corpus_error(row, error, &calls, executed));
                }
                (wall_ms, Ok(live)) => {
                    let status = live.mutant.report.status;
                    calls.push((vec![h], json!(status_name(status)), wall_ms));
                    self.set_witnesses(&mut row, &order, &live, &mut witness);
                    executed.extend(executed_entries(
                        &live,
                        self.spec.result.slots(),
                        self.manifest.budget,
                        first_killer(&live),
                    ));
                    if status == MutantStatus::Killed {
                        source = SOURCE_HINT;
                    }
                    differences.extend(live.differences);
                    runs.push((vec![h], live.mutant));
                }
            }
        }
        if source != SOURCE_HINT {
            match self.call(generation, &live_order) {
                (wall_ms, Err(error)) => {
                    calls.push((live_order.clone(), json!("error"), wall_ms));
                    return Some(self.corpus_error(row, error, &calls, executed));
                }
                (wall_ms, Ok(live)) => {
                    calls.push((
                        live.order.clone(),
                        json!(status_name(live.mutant.report.status)),
                        wall_ms,
                    ));
                    self.set_witnesses(&mut row, &order, &live, &mut witness);
                    // Each program is listed once (F-14 review 1 m3, flow F-16): a hinted
                    // program this call ran again is listed with this call's run, the one the
                    // status is folded from.
                    let entries = executed_entries(
                        &live,
                        self.spec.result.slots(),
                        self.manifest.budget,
                        first_killer(&live),
                    );
                    executed.retain(|entry| {
                        entry["cached"] == true
                            || !entries
                                .iter()
                                .any(|again| again["program"] == entry["program"])
                    });
                    executed.extend(entries);
                    differences.extend(live.differences);
                    runs.push((live.order, live.mutant));
                }
            }
        }
        // Step 5: the status of the assembled plan.
        let (last_order, last) = runs.last().expect("a live call");
        let report = match self.assemble(&agree, Some((last_order, &last.plan))) {
            Ok(report) => report,
            Err(failure) => {
                let error = CorpusError {
                    reason: "outcome-conflict".into(),
                    detail: format!(
                        "the cached agreements of {:?} and the live call over {:?} do not form \
                         one plan ({failure}): a cached outcome says the mutant ran, the live \
                         call says it did not; run `{} --verify`",
                        agree
                            .iter()
                            .map(|(c, _)| self.candidates[*c].id)
                            .collect::<Vec<_>>(),
                        self.ids(last_order),
                        self.spelling.command(Verb::Run)
                    ),
                };
                return Some(self.corpus_error(row, error, &calls, executed));
            }
        };
        if last.plan.mutant_failure == Some(MutantScopeFailure::Infrastructure) && !agree.is_empty()
        {
            // `assemble` left the cached agreements out of the plan (flow F-16): they leave the
            // row and the counts too, so the row is the cold call's.
            self.stats.programs_from_cache -= agree.len();
            executed.retain(|entry| entry["cached"] != true);
        }
        let reason = last
            .plan
            .mutant_failure
            .map(|failure| kebab(&format!("{failure:?}")))
            .or_else(|| exclusion_reason(&report, runs.iter().map(|(_, run)| run)));
        verdict_claims(&mut row, &last.plan.claims, |claims| {
            claims_value(self.spec.validator.baseline(), claims)
        });
        // Step 7: the records of the live calls, then the hint. A program both calls ran has
        // one record, the second call's (the store keeps the last of equal program digests and
        // counts each program once).
        let records = runs
            .iter()
            .flat_map(|(_, run)| self.live_records(run, &differences))
            .collect::<Vec<_>>();
        self.write_records(identity, mutation, &mut row, &records, witness.as_ref());
        let killer = (report.status == MutantStatus::Killed)
            .then(|| report.killing_test_ids.first())
            .flatten()
            .and_then(|program| self.position(program));
        match killer {
            Some(killer) => self.hints.insert(key, self.hint_entry(killer, mutation)),
            None => self.hints.remove(key),
        }
        let source = (report.status == MutantStatus::Killed).then_some(source);
        let calls = self.calls(&calls);
        Some((
            verdict_row(row, &report, None, reason, source, calls, executed),
            false,
        ))
    }

    /// A full row (`run --full`, module documentation): every program of O, in corpus order, is a
    /// cell, cached (C: every valid record, killed or agreement) or live (L = O minus C, one call
    /// under [`ScheduleMode::Full`]). Tier 1 decides with no call only when L is empty; no
    /// one-program call is made for the hint. The status is the fold over C then the call's tests,
    /// under `Full`; `killed_by` lists every killing program in corpus order, `killer` is the
    /// first, from the outcome cache when its cell is cached; `executed` lists every cell in corpus
    /// order. Records and the hint follow the first-kill rules (step 7).
    fn search_full(
        &mut self,
        mutation: &Mutation,
        mut row: Map<String, Value>,
        facts: &Facts,
        generation: Option<&CandidateGeneration<'_>>,
        order: &[usize],
        cached: Vec<(usize, OutcomeRecord)>,
    ) -> (Value, bool) {
        let key = hint_key_of(mutation, &facts.rules);
        let live_order = order
            .iter()
            .copied()
            .filter(|c| !cached.iter().any(|(a, _)| a == c))
            .collect::<Vec<_>>();
        // Each cell's entry with its candidate index, so that the row lists them in corpus order.
        let mut executed = cached
            .iter()
            .map(|(c, record)| (*c, self.cached_entry(*c, record)))
            .collect::<Vec<_>>();
        let entries = |mut executed: Vec<(usize, Value)>| {
            executed.sort_by_key(|(c, _)| *c);
            executed
                .into_iter()
                .map(|(_, entry)| entry)
                .collect::<Vec<_>>()
        };
        self.stats.programs_from_cache += cached.len();
        let mut calls = Calls::new();
        let mut witness = None;
        let live = if live_order.is_empty() {
            self.stats.mutations_from_cache += 1;
            None
        } else {
            // A memo's facts never reach here: tier 1 decides them ([`Search::search_facts`]).
            let generation = generation
                .expect("a memo's facts are searched only when tier 1 decides, with L empty");
            match self.call(generation, &live_order) {
                (wall_ms, Err(error)) => {
                    calls.push((live_order.clone(), json!("error"), wall_ms));
                    return self.corpus_error(row, error, &calls, entries(executed));
                }
                (wall_ms, Ok(live)) => {
                    calls.push((
                        live.order.clone(),
                        json!(status_name(live.mutant.report.status)),
                        wall_ms,
                    ));
                    self.set_witnesses(&mut row, order, &live, &mut witness);
                    Some(live)
                }
            }
        };
        let report = match &live {
            None => self
                .assemble(&cached, None)
                .expect("cached outcomes of executed tests form a valid plan"),
            Some(live) => match self.assemble(&cached, Some((&live.order, &live.mutant.plan))) {
                Ok(report) => report,
                Err(failure) => {
                    let error = CorpusError {
                        reason: "outcome-conflict".into(),
                        detail: format!(
                            "the cached outcomes of {:?} and the live call over {:?} do not form \
                             one plan ({failure}): a cached outcome says the mutant ran, the live \
                             call says it did not; run `{} --full --verify`",
                            cached
                                .iter()
                                .map(|(c, _)| self.candidates[*c].id)
                                .collect::<Vec<_>>(),
                            self.ids(&live_order),
                            self.spelling.command(Verb::Run)
                        ),
                    };
                    executed.extend(self.indexed(executed_entries(
                        live,
                        self.spec.result.slots(),
                        self.manifest.budget,
                        None,
                    )));
                    return self.corpus_error(row, error, &calls, entries(executed));
                }
            },
        };
        let mut reason = None;
        if let Some(live) = &live {
            if live.mutant.plan.mutant_failure == Some(MutantScopeFailure::Infrastructure) {
                // `assemble` left the cached cells out of the plan (flow F-16): they leave the
                // row and the counts too, so the row is the cold call's.
                self.stats.programs_from_cache -= cached.len();
                executed.clear();
            }
            reason = live
                .mutant
                .plan
                .mutant_failure
                .map(|failure| kebab(&format!("{failure:?}")))
                .or_else(|| exclusion_reason(&report, std::iter::once(&live.mutant)));
            verdict_claims(&mut row, &live.mutant.plan.claims, |claims| {
                claims_value(self.spec.validator.baseline(), claims)
            });
            let records = self.live_records(&live.mutant, &live.differences);
            self.write_records(
                facts.identity,
                mutation,
                &mut row,
                &records,
                witness.as_ref(),
            );
        }
        let killed_by = self.killed_by(&report);
        let killer = killed_by
            .as_ref()
            .and_then(|killers| killers.first())
            .and_then(|id| self.position(id));
        match killer {
            Some(killer) => self.hints.insert(key, self.hint_entry(killer, mutation)),
            None => self.hints.remove(key),
        }
        let source = killer.map(|killer| {
            if cached.iter().any(|(c, _)| *c == killer) {
                SOURCE_OUTCOME_CACHE
            } else {
                SOURCE_SEARCH
            }
        });
        if let Some(live) = &live {
            // The row's killer shows the mutant's KORE when its cell is live.
            let live_killer = killer
                .filter(|killer| live_order.contains(killer))
                .map(|killer| self.candidates[killer].id);
            executed.extend(self.indexed(executed_entries(
                live,
                self.spec.result.slots(),
                self.manifest.budget,
                live_killer,
            )));
        }
        let calls = self.calls(&calls);
        (
            verdict_row(
                row,
                &report,
                killed_by,
                reason,
                source,
                calls,
                entries(executed),
            ),
            false,
        )
    }

    /// Live executed entries with the candidate index of their program.
    fn indexed(&self, entries: Vec<Value>) -> Vec<(usize, Value)> {
        entries
            .into_iter()
            .map(|entry| {
                let c = entry["program"]
                    .as_str()
                    .and_then(|id| self.position(id))
                    .unwrap_or(usize::MAX);
                (c, entry)
            })
            .collect()
    }

    /// `run --verify` for one resolved mutation (README 7.5.3): the cold call over O, a
    /// one-program call per valid record the cold call did not execute, and the comparison of
    /// every valid record and of the cached path's status with the live ones.
    fn verify_one(
        &mut self,
        mut row: Map<String, Value>,
        mutation: &Mutation,
        generation: &CandidateGeneration<'_>,
        order: &[usize],
        records: &[(usize, OutcomeRecord)],
        stored: Option<&EditWitness>,
    ) -> (Value, bool) {
        let mut calls = Calls::new();
        let mut executed = Vec::new();
        let mut witness = None;
        let cold = match self.call(generation, order) {
            (wall_ms, Err(error)) => {
                calls.push((order.to_vec(), json!("error"), wall_ms));
                return self.corpus_error(row, error, &calls, executed);
            }
            (wall_ms, Ok(live)) => {
                calls.push((
                    live.order.clone(),
                    json!(status_name(live.mutant.report.status)),
                    wall_ms,
                ));
                self.set_witnesses(&mut row, order, &live, &mut witness);
                executed.extend(executed_entries(
                    &live,
                    self.spec.result.slots(),
                    self.manifest.budget,
                    first_killer(&live),
                ));
                live.mutant
            }
        };
        let mut live = BTreeMap::new();
        self.collect_live(&cold, &mut live);
        for (c, _) in records {
            if live.contains_key(c) {
                continue;
            }
            match self.call(generation, &[*c]) {
                (wall_ms, Err(error)) => {
                    calls.push((vec![*c], json!("error"), wall_ms));
                    return self.corpus_error(row, error, &calls, executed);
                }
                (wall_ms, Ok(one)) => {
                    let status = status_name(one.mutant.report.status);
                    calls.push((vec![*c], json!(status), wall_ms));
                    // An audit call: its kill is not the row's killer, so it shows no KORE.
                    executed.extend(executed_entries(
                        &one,
                        self.spec.result.slots(),
                        self.manifest.budget,
                        None,
                    ));
                    self.collect_live(&one.mutant, &mut live);
                    live.entry(*c).or_insert(Live::NotRun(status));
                }
            }
        }
        // Every valid record against its program's live outcome.
        let mut mismatches = Vec::new();
        for (c, record) in records {
            let (outcome, mutant) = match &live[c] {
                Live::Ran(run, mutant) => (
                    cacheable(run)
                        .map_or_else(|| run_label(run).to_owned(), |(o, _)| o.as_str().to_owned()),
                    mutant.clone(),
                ),
                Live::NotRun(status) => ((*status).to_owned(), None),
            };
            if outcome != record.outcome.as_str()
                || mutant.as_deref() != Some(record.mutant_run_sha256.as_str())
            {
                mismatches.push(json!({
                    "mutation": mutation.id,
                    "program": self.candidates[*c].id,
                    "cached": {"outcome": record.outcome.as_str(),
                               "mutant_run_sha256": record.mutant_run_sha256},
                    "live": {"outcome": outcome, "mutant_run_sha256": mutant},
                }));
            }
        }
        // The compiled edit the outcome file keeps, against the cold call's. It decides no status
        // (it gives a row decided with no compile only its `witnesses` and which cached killer it
        // names), so the row keeps its status; the difference is reported and the run exits 1.
        if let Some(stored) = stored
            && Some(stored) != witness.as_ref()
        {
            self.mismatches.push(json!({
                "mutation": mutation.id,
                "program": null,
                "cached": {"witness": stored.value()},
                "live": {"witness": witness.as_ref().map(EditWitness::value)},
            }));
        }
        // The status the cached path would have given, against the cold call's.
        let cached_status = self.cached_path_status(order, records, &cold);
        if cached_status != Some(cold.report.status) {
            mismatches.push(json!({
                "mutation": mutation.id,
                "program": null,
                "cached": {"status": cached_status.map(status_name)},
                "live": {"status": status_name(cold.report.status)},
            }));
        }
        let calls = self.calls(&calls);
        if let Some(first) = mismatches.first() {
            let program = first["program"]
                .as_str()
                .map(str::to_owned)
                .or_else(|| {
                    records
                        .first()
                        .map(|(c, _)| self.candidates[*c].id.to_owned())
                })
                .unwrap_or_else(|| "status".to_owned());
            row.insert("status".into(), json!("error"));
            row.insert(
                "reason".into(),
                json!(format!("outcome-mismatch:{program}")),
            );
            row.insert(
                "detail".into(),
                json!(format!(
                    "{} cached outcome(s) differ from the live runs (top-level mismatches); \
                     delete the cache's outcomes/ directory and report it",
                    mismatches.len()
                )),
            );
            self.mismatches.extend(mismatches);
            return (finish(row, None, None, calls, executed), false);
        }
        let reason = cold
            .plan
            .mutant_failure
            .map(|failure| kebab(&format!("{failure:?}")));
        verdict_claims(&mut row, &cold.plan.claims, |claims| {
            claims_value(self.spec.validator.baseline(), claims)
        });
        let source = (cold.report.status == MutantStatus::Killed).then_some(SOURCE_SEARCH);
        // Under `Full` the cold call ran every program of O in corpus order, so its killers are
        // the row's `killed_by`.
        let killed_by = self.killed_by(&cold.report);
        (
            verdict_row(
                row,
                &cold.report,
                killed_by,
                reason,
                source,
                calls,
                executed,
            ),
            false,
        )
    }

    /// Each executed test of a live run, by candidate.
    fn collect_live(&self, run: &MutantRun, live: &mut BTreeMap<usize, Live>) {
        for test in &run.plan.tests {
            if test.run == TestRun::SkippedAfterKill {
                continue;
            }
            if let Some(c) = self.position(&test.test_id) {
                live.insert(
                    c,
                    Live::Ran(test.run.clone(), mutant_run_sha256(run, &test.test_id)),
                );
            }
        }
    }

    /// The status the cached path gives for the records (README 7.5.3 steps 2-5), with the
    /// cold call's tests of L standing in for the live call over L; `None` when that plan is
    /// refused (the cached path's `outcome-conflict`). Under [`ScheduleMode::Full`] a killed
    /// record does not decide alone: the cached path folds every record with L's live tests.
    fn cached_path_status(
        &self,
        order: &[usize],
        records: &[(usize, OutcomeRecord)],
        cold: &MutantRun,
    ) -> Option<MutantStatus> {
        if self.schedule == ScheduleMode::FirstKill
            && records
                .iter()
                .any(|(_, record)| record.outcome == CachedOutcome::Killed)
        {
            return Some(MutantStatus::Killed);
        }
        let live_order = order
            .iter()
            .copied()
            .filter(|c| !records.iter().any(|(a, _)| a == c))
            .collect::<Vec<_>>();
        if live_order.is_empty() {
            return self.assemble(records, None).ok().map(|r| r.status);
        }
        let ids = self.ids(&live_order);
        let mut plan = cold.plan.clone();
        plan.tests
            .retain(|test| ids.contains(&test.test_id.as_str()));
        // The cold call ran L in its own order (the witnessing programs first): the plan's.
        let live_order = if plan.tests.is_empty() {
            live_order
        } else {
            plan.tests
                .iter()
                .filter_map(|test| self.position(&test.test_id))
                .collect()
        };
        self.assemble(records, Some((&live_order, &plan)))
            .ok()
            .map(|r| r.status)
    }

    fn corpus_error(
        &self,
        mut row: Map<String, Value>,
        error: CorpusError,
        calls: &Calls,
        executed: Vec<Value>,
    ) -> (Value, bool) {
        row.insert("status".into(), json!("error"));
        row.insert("reason".into(), json!(error.reason));
        row.insert("detail".into(), json!(error.detail));
        (finish(row, None, None, self.calls(calls), executed), true)
    }
}

/// The reason of a failed drift check (README 5.4): `baseline-mismatch:<program id>` for the
/// first program whose baseline row does not have its cached run digest (the id is the
/// candidate's, so an id containing ':' stays whole), else `baseline-count-mismatch` when the
/// call ran another number of baseline programs than it had tests; `None` when the check
/// passed. The runner returns one baseline row per test, so the count mismatch is defensive.
pub fn drift_reason(first_mismatch: Option<&str>, count_mismatch: bool) -> Option<String> {
    match (first_mismatch, count_mismatch) {
        (Some(program), _) => Some(format!("baseline-mismatch:{program}")),
        (None, true) => Some("baseline-count-mismatch".to_owned()),
        (None, false) => None,
    }
}

/// The run digest of the mutant's evidence row for `test_id`: the mutant's `TestEvidence`
/// encoded by `CampaignReport::baseline_row`, which is the `side_run` encoding the campaign
/// report uses for mutant evidence too (kink-campaign report.rs, `baseline_row` and the
/// mutants' `tests[].mutant`).
fn mutant_run_sha256(run: &MutantRun, test_id: &str) -> Option<String> {
    let evidence = run.evidence.iter().find(|e| e.test_id == test_id)?;
    let row = CampaignReport::baseline_row(evidence).ok()?;
    run_digest(&row).map(|digest| digest.to_string())
}

/// The kill evidence of each test of a live call some slot of which distinguished (CF-16,
/// [`crate::evidence`]): the first differing cell path of its two sides' ends and both values,
/// computed from the call's own evidence, by test id. A test whose sides hold no whole-term value
/// to compare has none.
fn kill_differences<'a>(
    mutant: &'a MutantRun,
    baseline: &'a [TestEvidence],
    reader: &crate::evidence::EndReader,
) -> BTreeMap<String, Value> {
    mutant
        .plan
        .tests
        .iter()
        .filter(|test| {
            matches!(&test.run, TestRun::Compared(outcomes) if outcomes.contains(&OracleOutcome::Distinguish))
        })
        .filter_map(|test| {
            let of = |evidence: &'a [TestEvidence]| {
                evidence
                    .iter()
                    .find(|evidence| evidence.test_id == test.test_id)
            };
            let difference = reader.test_difference(of(baseline)?, of(&mutant.evidence)?)?;
            Some((test.test_id.clone(), difference))
        })
        .collect()
}

/// The programs a live mutant run ran on, in the runner's order (`cached: false`), each with
/// its outcome, its named slots (README 6.4: for a distinguishing slot the sides; on the row's
/// killer `killer`, when the call ran it, the mutant's final configurations as KORE text),
/// unless it agreed or distinguished the cause the runner's evidence and the session's leaf
/// census give, and the session's timings: `wall_ms` (the mutant's run), `baseline_ms` (the
/// program's live baseline run in this command) and `baseline_reused`.
fn executed_entries(
    live: &LiveCall,
    slots: [&str; 2],
    budget: Budget,
    killer: Option<&str>,
) -> Vec<Value> {
    let mutant = &live.mutant;
    mutant
        .plan
        .tests
        .iter()
        .filter_map(|test| {
            let found = mutant
                .evidence
                .iter()
                .find(|evidence| evidence.test_id == test.test_id);
            let evidence = found.map(|evidence| &evidence.run);
            let notes = found.map(|evidence| &evidence.notes);
            let baseline = live
                .baseline
                .iter()
                .find(|evidence| evidence.test_id == test.test_id)
                .map(|evidence| &evidence.run);
            let run = live
                .recording
                .mutant_run(mutant.plan.mutant_id, &test.test_id);
            let baseline_run = live.recording.baseline_of(&test.test_id);
            let cause = executed_cause(
                &slots,
                &test.run,
                evidence,
                found.map_or(&[][..], |evidence| evidence.notes.across.as_slice()),
                budget,
                run.map(|run| (&run.census, &live.edited)),
            );
            let difference = live
                .differences
                .get(&test.test_id)
                .cloned()
                .unwrap_or(Value::Null);
            let mut entry = match &test.run {
                TestRun::SkippedAfterKill => return None,
                TestRun::Compared(outcomes) => json!({
                    "program": test.test_id,
                    "outcome": compared_outcome(outcomes),
                    "slots": slots_value(
                        &slots,
                        outcomes,
                        baseline,
                        evidence,
                        killer == Some(test.test_id.as_str()),
                        &difference,
                    ),
                    "difference": difference,
                    "cause": cause,
                    "cached": false,
                }),
                TestRun::Failed(kind) => json!({
                    "program": test.test_id,
                    "outcome": status_name(kind.status()),
                    "failure": kebab(&format!("{kind:?}")),
                    "cause": cause,
                    "cached": false,
                }),
            };
            entry["wall_ms"] = json!(run.map(|run| millis(run.wall)));
            entry["baseline_ms"] = json!(baseline_run.map(|b| millis(b.run.wall)));
            entry["baseline_reused"] = json!(baseline_run.map(|b| b.reused));
            // Re-pin adoption A-1: what the mutant's run says about the specification, and its
            // undecided solver answers (D-7 (a1)), when there are any.
            if let Some(notes) = notes {
                if !notes.contradicted_claims.is_empty() {
                    entry["specification_diagnostics"] =
                        specification_diagnostics_value(&notes.contradicted_claims);
                }
                if notes.smt_unknowns > 0 {
                    entry["smt_unknowns"] = json!(notes.smt_unknowns);
                }
                // CF-03: the readings that count against the mutant's run, the step that
                // excluded it.
                if !notes.short_circuit_readings.is_empty() {
                    entry["short_circuit_readings"] =
                        crate::exclusion::readings_value(&notes.short_circuit_readings);
                    if let (
                        TestRun::Failed(kink_campaign::ExecutionFailureKind::ShortCircuitReading),
                        Some(cause),
                    ) = (&test.run, &cause)
                    {
                        entry["cause"] = json!(format!(
                            "{cause}; the mutant's run: {}",
                            crate::exclusion::readings_text(&notes.short_circuit_readings)
                        ));
                    }
                }
            }
            Some(entry)
        })
        .collect()
}

/// The first killing program of a live call, the one whose executed entry shows the mutant's
/// KORE under first-kill (and in `run --verify`'s cold call, where under `Full` it is also the
/// row's first killer in corpus order).
fn first_killer(live: &LiveCall) -> Option<&str> {
    live.mutant
        .report
        .killing_test_ids
        .first()
        .map(String::as_str)
}

/// The executed entry's `outcome` label of a test run.
fn run_label(run: &TestRun) -> &'static str {
    match run {
        TestRun::Compared(outcomes) => compared_outcome(outcomes),
        TestRun::Failed(kind) => status_name(kind.status()),
        TestRun::SkippedAfterKill => "skipped",
    }
}

/// A label for a compared program's slot outcomes (for the reader; the status is the
/// runner's): `distinguish` if a slot distinguished, `agree` if every slot agreed, else the
/// first inconclusive slot's outcome.
fn compared_outcome(outcomes: &[OracleOutcome]) -> &'static str {
    if outcomes.contains(&OracleOutcome::Distinguish) {
        "distinguish"
    } else {
        outcomes
            .iter()
            .find(|outcome| **outcome != OracleOutcome::Agree)
            .map_or("agree", |outcome| slot_name(*outcome))
    }
}

/// `kink-flow run`: the run document and whether the command found no corpus or
/// infrastructure error (the caller's exit status). Survivors, timeouts and invalid mutations
/// are results, not errors.
pub fn run(manifest: &FlowManifest, list: &MutationList, options: &RunOptions) -> (Value, bool) {
    run_with(manifest, list, options, RunMode::Search)
}

/// `kink-flow run` (mode [`RunMode::Search`]) or `kink-flow run --verify` (mode
/// [`RunMode::Verify`]).
pub fn run_with(
    manifest: &FlowManifest,
    list: &MutationList,
    options: &RunOptions,
    mode: RunMode,
) -> (Value, bool) {
    run_front(manifest, list, options, mode, &FrontEnd::default())
}

/// [`run_with`] for a front end ([`FrontEnd`]): next steps take its spelling; a mutation it
/// refused ([`FrontEnd::refused`]) gets the row of a mutation that does not resolve, with the
/// front end's reason, and is not resolved, looked up in a memo, compiled or run, so no outcome
/// record, hint or memo record is written for it; and the document is annotated
/// ([`FrontEnd::annotate`]) before every write of the report and before it is returned, so that
/// `report` prints what `run` printed.
pub fn run_front(
    manifest: &FlowManifest,
    list: &MutationList,
    options: &RunOptions,
    mode: RunMode,
    front: &FrontEnd<'_>,
) -> (Value, bool) {
    let annotated = |mut document: Value| {
        if let Some(annotate) = front.annotate {
            annotate(&mut document);
        }
        document
    };
    let cache = cache_directory(manifest, options.cache.as_deref());
    let store = Store::new(&cache);
    let report_path = cache.join(REPORT_FILE);
    // A run that admits no specification still replaces the report, so `report` always prints
    // the last run's document. Its `mismatches` are the census memo's (re-pin L1-4 fix 1, review
    // D1): under `--verify`, a stored census that differs from the live one, above all a stored
    // census that admits what the live one refuses, is reported whether or not the live census
    // admits the specification; otherwise there is none.
    let refused = |record: &AdmissionRecord, mismatches: &[Value]| {
        let document = annotated(document(
            record,
            None,
            &[],
            Vec::new(),
            None,
            Accounting {
                mismatches,
                schedule: json!(schedule_name(options.schedule)),
                ..Accounting::NONE
            },
        ));
        let _ = store.write_json(&report_path, &document);
        (document, false)
    };
    let verify = mode == RunMode::Verify;
    // Re-pin L1-4: the memos of the warm path (`memo`), under the conditions tier 1 has (no Z3
    // profile, a known build) and unless `--no-memo`. `--verify` reads none of them for a
    // decision and writes none: it compares each stored record with the live value.
    let memo_build = match (
        options.memo,
        tier1_refusal(SolverProfile::BUILD),
        kink_campaign::kink_build(),
    ) {
        (MemoUse::On, None, Ok(build)) => Some(build),
        _ => None,
    };
    let mut census_mismatch = None;
    let (mut record, admitted) = admit_spec_with(manifest, &mut |loaded, side| {
        let Some(build) = memo_build else {
            return declaration_census(side);
        };
        let spec = spec_digest(manifest, &loaded.files);
        let (key, path) = (
            memo::census_key(spec, build),
            memo::census_path(&cache, spec),
        );
        let stored = memo::read_census(&path, &key);
        if !verify && let Some(census) = stored {
            return Ok(census);
        }
        let live = declaration_census(side);
        match (&live, stored) {
            (Ok(census), None) if !verify => memo::write_census(&store, &path, &key, census),
            (live, Some(stored)) if live.as_ref().ok() != Some(&stored) => {
                census_mismatch = Some(json!({
                    "mutation": null,
                    "program": null,
                    "cached": {"census": stored.value()},
                    "live": {"census": live.as_ref().map_or_else(
                        |e| json!({"error": e.to_string()}),
                        DeclarationCensus::value,
                    )},
                }));
            }
            _ => {}
        }
        live
    });
    let census_mismatch = census_mismatch.into_iter().collect::<Vec<_>>();
    let Some((spec, mut inputs)) = admitted else {
        return refused(&record, &census_mismatch);
    };
    let mut inputs = inputs.session(&spec);
    let runner = match BaselineRunner::new(&spec, manifest) {
        Ok(runner) => runner,
        Err(e) => {
            record.refusal = Some(runner_refusal(e));
            return refused(&record, &census_mismatch);
        }
    };
    // A stored result is never a timeout, so no cached row needs a re-run here: a
    // program whose baseline timed out was run live by this command's results update.
    let update = update_results(&spec, manifest, &mut inputs, &runner, &cache, verify);
    // Once per command: the definition exclusion every document this run writes names.
    let exclusion = runner.definition_exclusion();
    let hints = Hints::read(&cache);
    let mut ok = update.ok();
    let (tier1, tier1_reason) = match (
        tier1_refusal(SolverProfile::BUILD),
        kink_campaign::kink_build(),
    ) {
        (Some(reason), _) => (None, Some(reason.to_owned())),
        (None, Ok(build)) => (
            Some(OutcomeStore::new(
                &cache,
                outcome_context(build, update.execution, manifest.budget, &spec.result),
            )),
            None,
        ),
        (None, Err(e)) => (
            None,
            Some(format!(
                "tier 1 is disabled: kink's build identity is unknown ({e}); every mutation runs \
                 live"
            )),
        ),
    };
    let candidates = manifest
        .programs
        .iter()
        .zip(&update.rows)
        .enumerate()
        .filter_map(|(index, (program, row))| candidate(index, &program.id, row))
        .collect::<Vec<_>>();
    let program_rows = crate::results::data_marked(
        update.rows.iter().map(|row| row.row.clone()).collect(),
        &spec.data,
    );
    let mut search = Search {
        spec: &spec,
        manifest,
        inputs: &mut inputs,
        runner: &runner,
        rows: &update.rows,
        tests: vec![None; candidates.len()],
        candidates,
        mode,
        tier1,
        hints,
        store: Store::new(&cache),
        stats: Stats::default(),
        mismatches: Vec::new(),
        order: options.order,
        schedule: options.schedule,
        support: ClaimSupport::new(spec.validator.baseline()),
        spelling: front.spelling,
    };
    let outcome_cache = |search: &Search<'_, '_>| {
        json!({
            "context_sha256": search.tier1.as_ref().map(OutcomeStore::context_sha256),
            "enabled": search.tier1.is_some() && !verify,
            "verify": verify,
            "reason": if verify {
                Some("run --verify decides nothing from the outcome cache: it re-proves every \
                      valid record and writes none".to_owned())
            } else {
                tier1_reason.clone()
            },
            "mutations_from_cache": search.stats.mutations_from_cache,
            "programs_from_cache": search.stats.programs_from_cache,
            "records_written": search.stats.records_written,
        })
    };
    search.mismatches.extend(census_mismatch);
    // Every mutation of the list is resolved first (resolution only loads), so that the report
    // lists, from its first write on, the rules no resolving mutation of the list targets
    // (flow F-13, informational only); `--only` limits the search, not this list.
    //
    // Re-pin L1-4: a mutation whose resolution memo record holds its facts under exactly the
    // current key, and that tier 1 decides with no call, is not resolved: its row is built from
    // the facts (`Search::search_memo`). Every other mutation is resolved live, as before, and
    // its facts are written. The memo is read only while every source file still has the
    // SHA-256 the admission recorded (`memo::sources_unchanged`).
    let consult = memo_build.filter(|_| memo::sources_unchanged(&manifest.directory, &spec.loaded));
    let mut resolution_mismatches = BTreeMap::new();
    let resolutions = list
        .mutations
        .iter()
        .enumerate()
        .map(|(index, mutation)| {
            if let Some(refusal) = front.refused.get(&mutation.id) {
                return Resolution::Live(Err(refusal.clone()));
            }
            let memo = consult.map(|build| {
                (
                    memo::resolution_key(update.spec_digest, build, mutation),
                    memo::resolution_path(&cache, update.spec_digest, mutation),
                )
            });
            let stored = memo
                .as_ref()
                .and_then(|(key, path)| memo::read_facts(path, key));
            if !verify && let Some(facts) = stored.as_ref().filter(|facts| search.decided(facts)) {
                return Resolution::Memo(facts.clone());
            }
            let live = resolve(manifest, &spec.loaded, mutation);
            if let Some((key, path)) = &memo {
                let facts = live.as_ref().ok().and_then(|resolved| {
                    let generation = resolved.generation(spec.validator.baseline()).ok()?;
                    Some(search.facts(resolved, &generation))
                });
                match (&facts, &stored) {
                    (Some(facts), stored) if !verify && stored.as_ref() != Some(facts) => {
                        memo::write_facts(&store, path, key, facts);
                    }
                    (live_facts, Some(stored)) if verify && live_facts.as_ref() != Some(stored) => {
                        let live_value = match (live_facts, &live) {
                            (Some(facts), _) => facts.value(),
                            (None, Err(invalid)) => json!({
                                "status": invalid.reason.status(),
                                "reason": invalid.reason.as_str(),
                                "detail": invalid.detail,
                            }),
                            (None, Ok(_)) => json!({"generation": "refused"}),
                        };
                        resolution_mismatches.insert(
                            index,
                            json!({
                                "mutation": mutation.id,
                                "program": null,
                                "cached": {"resolution": stored.value()},
                                "live": {"resolution": live_value},
                            }),
                        );
                    }
                    _ => {}
                }
            }
            Resolution::Live(live)
        })
        .collect::<Vec<_>>();
    let untargeted = Value::Array(untargeted_rules(
        &rule_texts(manifest, &spec.loaded),
        &resolutions
            .iter()
            .flat_map(|resolution| resolution.rules().iter().map(|rule| rule.at.clone()))
            .collect(),
    ));
    let mut rows = Vec::new();
    let mut stopped = None;
    let selected = list
        .mutations
        .iter()
        .zip(&resolutions)
        .enumerate()
        .filter(|(_, (mutation, _))| options.only.is_empty() || options.only.contains(&mutation.id))
        .map(|(index, (mutation, resolution))| (index, mutation, resolution))
        .collect::<Vec<_>>();
    // Re-pin L1-3: compile ahead, a chunk at a time, the mutants of the chunk's mutations that
    // would make a live call given the stores at the chunk's start; every worker is joined
    // before the chunk's first mutation runs, and each mutation then runs as with one worker,
    // in list order, one campaign call at a time. A mutant compiled ahead is the one its call
    // would compile (kink-native `NativeValidator::compile_ahead`), and a mutation that turns
    // out not to call (or one that calls after all) costs only a compile, so no row depends on
    // the worker count.
    let workers = spec
        .validator
        .compile_workers(options.compile_workers.unwrap_or(DEFAULT_COMPILE_WORKERS));
    let chunk = workers * kink_native::AHEAD_PER_WORKER;
    // The document as last written to the report file, if it was.
    let mut written = None;
    // The chunk compiled ahead; dropping it drops what its mutations did not take.
    let mut ahead = None;
    for (position, &(index, mutation, resolution)) in selected.iter().enumerate() {
        if workers > 1 && position % chunk == 0 {
            drop(ahead.take());
            let patches = selected[position..selected.len().min(position + chunk)]
                .iter()
                .flat_map(|(_, _, resolution)| match resolution {
                    Resolution::Live(resolution) => search.live_compiles(resolution),
                    // Tier 1 decides it with no call (or it is resolved live at its turn).
                    Resolution::Memo(_) => Vec::new(),
                })
                .collect::<Vec<_>>();
            ahead = Some(spec.validator.compile_ahead(&patches, workers));
        }
        let (mut row, corpus_error) = match resolution {
            Resolution::Live(resolution) => search.search_one(mutation, resolution),
            Resolution::Memo(facts) => search.search_memo(mutation, facts).unwrap_or_else(|| {
                search.search_one(mutation, &resolve(manifest, &spec.loaded, mutation))
            }),
        };
        if let Some(mismatch) = resolution_mismatches.remove(&index) {
            search.mismatches.push(mismatch);
            row = resolution_mismatch(row);
        }
        row["action"] = json!(
            front
                .refused
                .get(&mutation.id)
                .and_then(|refusal| refused_action(refusal.reason))
                .or_else(|| action_spelled(
                    row["status"].as_str().unwrap_or_default(),
                    row["reason"].as_str(),
                    front.spelling,
                ))
        );
        if corpus_error {
            stopped = Some(json!({"mutation": mutation.id, "reason": row["reason"]}));
            ok = false;
        }
        // The hints are written after every mutation, a corpus error included (F-05 review 1
        // minor 3); `--verify` writes none.
        if !verify && let Err(e) = search.hints.write(&store) {
            row["cache_error"] = json!(format!("cannot write the hints: {e}"));
        }
        if row.get("cache_error").is_some()
            || (row["status"] == "error" && row["reason"] == "no-comparable-program")
        {
            ok = false;
        }
        rows.push(row);
        let document = annotated(document(
            &record,
            Some(update.spec_digest),
            &program_rows,
            rows.clone(),
            stopped.clone(),
            Accounting {
                outcome_cache: outcome_cache(&search),
                mismatches: &search.mismatches,
                baseline_runs: runner.baseline_runs(),
                order: order_value(options),
                schedule: json!(schedule_name(options.schedule)),
                untargeted_rules: untargeted.clone(),
                data: spec.data.value(),
                exclusion: exclusion.clone(),
                result: spec.result.value(),
                execution: update.execution.value(),
            },
        ));
        match store.write_json(&report_path, &document) {
            Ok(()) => written = Some(document),
            Err(e) => {
                if let Some(last) = rows.last_mut() {
                    last["cache_error"] = json!(format!("cannot write the report: {e}"));
                }
                ok = false;
            }
        }
        if stopped.is_some() {
            break;
        }
    }
    drop(ahead);
    // Re-pin L1-4 fix 1 (review D5): `--verify` resolved every mutation of the list, so a memo
    // record that differs from the live resolution of a mutation it did not search (not selected
    // by `--only`, or after the corpus error that stopped the run) is reported too; it has no row.
    search
        .mismatches
        .extend(resolution_mismatches.into_values());
    if !search.mismatches.is_empty() {
        ok = false;
    }
    let document = annotated(document(
        &record,
        Some(update.spec_digest),
        &program_rows,
        rows,
        stopped,
        Accounting {
            outcome_cache: outcome_cache(&search),
            mismatches: &search.mismatches,
            baseline_runs: runner.baseline_runs(),
            order: order_value(options),
            schedule: json!(schedule_name(options.schedule)),
            untargeted_rules: untargeted,
            data: spec.data.value(),
            exclusion,
            result: spec.result.value(),
            execution: update.execution.value(),
        },
    ));
    // The stored report is the document the command prints: write it unless the last write
    // already stored exactly this document (no mutation was selected, or a write failed).
    if written.as_ref() != Some(&document) && store.write_json(&report_path, &document).is_err() {
        ok = false;
    }
    (document, ok)
}

/// Whether tier 1 decides, with no call, a mutation whose comparable programs in search order are
/// `order` and whose valid tier-1 records are `records` (of programs of `order`): no program is in
/// O, or every program of O has a record (step 3), or, under [`ScheduleMode::FirstKill`], a
/// record is killed (step 2). Under [`ScheduleMode::Full`] a killed record does not decide: the
/// row needs every cell.
fn tier1_decides(
    order: &[usize],
    records: &[(usize, OutcomeRecord)],
    schedule: ScheduleMode,
) -> bool {
    order.is_empty()
        || records.len() == order.len()
        || (schedule == ScheduleMode::FirstKill
            && records
                .iter()
                .any(|(_, record)| record.outcome == CachedOutcome::Killed))
}

/// What `run` knows of a mutation's resolution (re-pin L1-4).
enum Resolution {
    /// Resolved in this command.
    Live(Result<ResolvedMutation, InvalidMutation>),
    /// Not resolved: the resolution memo's facts of a mutation tier 1 decides with no call.
    Memo(Facts),
}

impl Resolution {
    /// The rules the mutation edits; none when it does not resolve.
    fn rules(&self) -> &[EditedRule] {
        match self {
            Self::Live(Ok(resolved)) => &resolved.rules,
            Self::Live(Err(_)) => &[],
            Self::Memo(facts) => &facts.rules,
        }
    }
}

/// The row of a mutation whose resolution memo record differs from its live resolution in `run
/// --verify` (re-pin L1-4): status `error`, reason `resolution-mismatch`, whatever the live row
/// said; the record and the live facts are in the top-level `mismatches`.
fn resolution_mismatch(mut row: Value) -> Value {
    row["status"] = json!("error");
    row["reason"] = json!("resolution-mismatch");
    row["detail"] = json!(
        "the resolution memo's record of this mutation differs from its live resolution \
         (top-level mismatches); delete the cache's memo/ directory and report it"
    );
    row["action"] = json!(action("error", Some("resolution-mismatch")));
    row
}

/// The row's `weakening`: null, or for each sentence a weakening patch edits `{module, index,
/// label, head, kind}`, `label` the baseline sentence's (null without one), `head` the K label of
/// the function (null for a lemma), `kind` `deleted` or `narrowed` (kink27 R5-WEAKENING).
fn weakening_value(baseline: &kink_patch::Baseline, weakening: Option<&Weakening>) -> Value {
    weakening.map_or(Value::Null, |weakening| {
        Value::Array(
            weakening
                .equations
                .iter()
                .map(|weakened| {
                    json!({
                        "module": weakened.at.module,
                        "index": weakened.at.index,
                        "label": baseline
                            .sentence(&weakened.at)
                            .and_then(|sentence| sentence.attributes().string(AttributeKey::Label)),
                        "head": weakened.head,
                        "kind": match weakened.kind {
                            WeakeningKind::Deleted => "deleted",
                            WeakeningKind::Narrowed => "narrowed",
                        },
                    })
                })
                .collect(),
        )
    })
}

/// The row of a mutation that does not resolve (or whose patch kink-patch refuses), or whose
/// patch the host refused the stack to encode (status `error`;
/// [`crate::mutation::InvalidReason::status`]).
fn invalid(mut row: Map<String, Value>, invalid: InvalidMutation, digest: Value) -> Value {
    row.insert("digest".into(), digest);
    row.insert("status".into(), json!(invalid.reason.status()));
    row.insert("reason".into(), json!(invalid.reason.as_str()));
    row.insert("edit".into(), json!(invalid.edit));
    row.insert("detail".into(), json!(invalid.detail));
    row.insert("rules".into(), Value::Null);
    finish(row, None, None, RowCalls::default(), Vec::new())
}

/// Fills the row's `removed_claims` from the deciding call's plan (re-pin R0-tail, R0c-fix-4
/// review minor 2), as `inconsistent_pairs` is filled from its report. The runner records there
/// the claims the mutant ran without and those that refuse it, among them each compiled equation
/// the source reading does not explain (`unsupported`, key `unread-equation`), which the row's own
/// reading before the call (`ClaimSupport::withdraw`) cannot know. Otherwise both readings come
/// from the same withdrawal of the same patch. A plan that records no claim (a refusal before
/// claim removal, such as `equivalent-compilation`) leaves the row's own reading.
fn verdict_claims(
    row: &mut Map<String, Value>,
    claims: &Withdrawal,
    value: impl FnOnce(&Withdrawal) -> Value,
) {
    if *claims != Withdrawal::default() {
        row.insert("removed_claims".into(), value(claims));
    }
}

/// The row of a verdict: the report's status, the killer, the killer's source, the deciding
/// call's mutant-scope failure as the reason. Under first-kill (`killed_by` `None`) the killer
/// is the report's first killing program; under `Full` it is the first of `killed_by`
/// ([`Search::killed_by`]), which the row carries.
fn verdict_row(
    mut row: Map<String, Value>,
    report: &MutantReport,
    killed_by: Option<Vec<String>>,
    reason: Option<String>,
    source: Option<&str>,
    calls: RowCalls,
    executed: Vec<Value>,
) -> Value {
    row.insert("status".into(), json!(status_name(report.status)));
    row.insert("reason".into(), json!(reason));
    row.insert(
        "inconsistent_pairs".into(),
        json!(
            report
                .inconsistent_pairs
                .iter()
                .map(kink_native::consistency::UnjoinedEquations::value)
                .collect::<Vec<_>>()
        ),
    );
    let killer = match &killed_by {
        None => (report.status == MutantStatus::Killed)
            .then(|| report.killing_test_ids.first().cloned())
            .flatten(),
        Some(killers) => killers.first().cloned(),
    };
    if let Some(killers) = killed_by {
        row.insert("killed_by".into(), json!(killers));
    }
    if killer.is_some() {
        row.insert("rules".into(), Value::Null);
    }
    let source = killer.as_ref().and(source);
    finish(row, killer, source, calls, executed)
}

/// The reason of an `unknown` status when a live test of the mutation was excluded
/// (kink-native `exclusion`: the run is no evidence, for example `implementation-chosen-hook`):
/// the first such exclusion in run order.
fn exclusion_reason<'r>(
    report: &MutantReport,
    runs: impl IntoIterator<Item = &'r MutantRun>,
) -> Option<String> {
    if report.status != MutantStatus::Unknown {
        return None;
    }
    runs.into_iter()
        .flat_map(|run| &run.plan.tests)
        .find_map(|test| match test.run {
            TestRun::Failed(kind) => kind
                .exclusion()
                .map(|exclusion| exclusion.name().to_owned()),
            TestRun::Compared(_) | TestRun::SkippedAfterKill => None,
        })
}

/// A row's `calls` and `call_wall_ms` (the same order).
type RowCalls = (Vec<Value>, Vec<Value>);

/// Complete a mutation row: killer, killer_source, killer_from_cache, executed, calls, their
/// wall times and the survivor report's action (`rules` is null unless the mutation resolved
/// and was not killed; `killed_by` is null unless a full row's fold decided it).
fn finish(
    mut row: Map<String, Value>,
    killer: Option<String>,
    source: Option<&str>,
    (calls, call_wall_ms): RowCalls,
    executed: Vec<Value>,
) -> Value {
    row.entry("reason").or_insert(Value::Null);
    row.entry("witnesses").or_insert(Value::Null);
    row.entry("rules").or_insert(Value::Null);
    row.entry("identity").or_insert(Value::Null);
    row.entry("unusable_killer").or_insert(Value::Null);
    row.entry("weakening").or_insert(Value::Null);
    row.entry("killed_by").or_insert(Value::Null);
    let action = action(
        row["status"].as_str().unwrap_or_default(),
        row["reason"].as_str(),
    );
    row.insert("action".into(), json!(action));
    row.insert("killer".into(), json!(killer));
    row.insert("killer_source".into(), json!(source));
    row.insert(
        "killer_from_cache".into(),
        json!(matches!(
            source,
            Some(SOURCE_OUTCOME_CACHE) | Some(SOURCE_HINT)
        )),
    );
    row.insert("executed".into(), json!(executed));
    row.insert("calls".into(), json!(calls));
    row.insert("call_wall_ms".into(), json!(call_wall_ms));
    Value::Object(row)
}

/// A mutant's compiled edit (kink-campaign [`CompiledEdit::between`] on the side the programs
/// run on, the rule kink-campaign's coverage selection reads) read through the baseline's
/// [`RuleAuthors`], since kink-flow's result records keep coverage by baseline sentence: the
/// baseline sentences behind the removed compiled ids that a run witnesses by k-rust `matched`
/// (an id whose edit changed its condition, alone or with its right-hand side or `ensures`;
/// [`Witness::Matched`]) and those it witnesses by `applied` (every other removed id of a
/// site-local edit). The outcome file keeps it (`witness`, [`crate::outcomes`]), so that a row
/// tier 1 decides with no compile still has its `witnesses`.
///
/// Reading by baseline sentence differs from kink-campaign's reading by compiled id in two ways,
/// both in which programs come first only, never in a status: a removed id with no baseline
/// sentence (a generated axiom, [`Authorship::Unmapped`]) is witnessed by no program, and a
/// sentence behind several compiled ids is witnessed by a program that matched or applied any of
/// them, not only the removed one.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct EditWitness {
    /// The edit is not site-local: every program witnesses it.
    global: bool,
    matched: BTreeSet<(String, u64)>,
    applied: BTreeSet<(String, u64)>,
}

impl EditWitness {
    fn of(edit: &CompiledEdit, authors: &RuleAuthors) -> Self {
        let mut witness = Self {
            global: edit.global,
            ..Self::default()
        };
        if edit.global {
            return witness;
        }
        for id in &edit.removed_rule_ids {
            let Some(Authorship::Sentences(sentences)) = authors.get(id) else {
                continue;
            };
            let into = match edit.witness(id) {
                Witness::Matched => &mut witness.matched,
                Witness::Applied => &mut witness.applied,
            };
            into.extend(
                sentences
                    .iter()
                    .map(|at| (at.module.clone(), u64::from(at.index))),
            );
        }
        witness
    }

    /// `{global, matched: [{module, index}], applied: [{module, index}]}`, each list sorted.
    fn value(&self) -> Value {
        let sentences = |set: &BTreeSet<(String, u64)>| {
            set.iter()
                .map(|(module, index)| json!({"module": module, "index": index}))
                .collect::<Vec<_>>()
        };
        json!({
            "global": self.global,
            "matched": sentences(&self.matched),
            "applied": sentences(&self.applied),
        })
    }

    /// The inverse of [`Self::value`]; `None` for null or a value of another shape.
    fn from_value(value: &Value) -> Option<Self> {
        let sentences = |key: &str| {
            value[key]
                .as_array()?
                .iter()
                .map(|at| Some((at["module"].as_str()?.to_owned(), at["index"].as_u64()?)))
                .collect::<Option<BTreeSet<_>>>()
        };
        Some(Self {
            global: value["global"].as_bool()?,
            matched: sentences("matched")?,
            applied: sentences("applied")?,
        })
    }
}

/// Whether the candidate's cached coverage witnesses the mutant's compiled edit
/// ([`EditWitness`]): every program witnesses an edit that is `global`, and a program whose
/// coverage is not complete witnesses every edit; otherwise a program witnesses the edit when it
/// matched (k-rust `matched`: began to decide the condition) a sentence of `matched`, or applied
/// (`applied`: built a candidate, defined or rolled back) one of `applied`
/// ([`CompiledEdit::witness`]). A program that only matched a rule whose guard it refuted cannot
/// witness a change of what the rule does once it applies; one whose candidate was rolled back
/// can, since an edit can make that candidate defined.
fn witnesses(candidate: &Candidate<'_>, witness: &EditWitness) -> bool {
    witness.global
        || !candidate.complete
        || !witness.matched.is_disjoint(&candidate.matches)
        || !witness.applied.is_disjoint(&candidate.applies)
}

/// The order of O before the mutant compiles (README 5.6 step 2, 6.4): by cost (the record's
/// `wall_ms` ascending, then corpus order) or in corpus order ([`ProgramOrder`]). A live call
/// keeps it inside each of its two tiers, the programs whose coverage witnesses the compiled
/// edit and the rest ([`Search::call_untimed`]). The order changes only which killing program is
/// found first and the cost, never a status in the no-Z3 profile (README 6.4; under Z3 see
/// README.md's coverage paragraph).
fn order(candidates: &[Candidate<'_>], program_order: ProgramOrder) -> Vec<usize> {
    let mut order = (0..candidates.len()).collect::<Vec<_>>();
    if program_order == ProgramOrder::Cost {
        order.sort_by_key(|&c| {
            (
                candidates[c].wall_ms.unwrap_or(u64::MAX),
                candidates[c].index,
            )
        });
    }
    order
}

/// The run document's `order`: `corpus` under [`ScheduleMode::Full`], which runs every program in
/// corpus order whatever [`RunOptions::order`] says.
fn order_value(options: &RunOptions) -> Value {
    match options.schedule {
        ScheduleMode::Full => json!(ProgramOrder::Corpus.as_str()),
        ScheduleMode::FirstKill => json!(options.order.as_str()),
    }
}

/// The run document's accounting of the command: `outcome_cache`, `mismatches`,
/// `baseline_runs`, the program `order`, the `schedule` and `untargeted_rules` (outside every
/// digest and key).
struct Accounting<'m> {
    outcome_cache: Value,
    mismatches: &'m [Value],
    baseline_runs: Value,
    order: Value,
    /// [`schedule_name`] of the run's schedule; under `full` the document carries the `matrix`.
    schedule: Value,
    untargeted_rules: Value,
    /// The baseline's data facts (kink-native `DataFacts::value`): the premises and findings.
    data: Value,
    /// The specification's definition exclusion, as `spec.exclusion` prints it
    /// (`crate::exclusion::definition_exclusion`).
    exclusion: Value,
    /// The slots and the cells the programs' second slot compares
    /// (`crate::observed::ResultProjection::value`), so that every survivor is reported with the
    /// cells it was compared on.
    result: Value,
    /// The execution digest `{kind, digest}` that keyed the result cache and tier 1
    /// (`digest::execution_digest`), so a reader can see why a store hit or missed.
    execution: Value,
}

impl Accounting<'_> {
    const NONE: Accounting<'static> = Accounting {
        outcome_cache: Value::Null,
        mismatches: &[],
        baseline_runs: Value::Null,
        order: Value::Null,
        schedule: Value::Null,
        untargeted_rules: Value::Null,
        data: Value::Null,
        exclusion: Value::Null,
        result: Value::Null,
        execution: Value::Null,
    };
}

/// The rules the resolving mutations address.
pub fn targeted(
    resolutions: &[Result<ResolvedMutation, InvalidMutation>],
) -> BTreeSet<SentenceRef> {
    resolutions
        .iter()
        .flatten()
        .flat_map(|resolved| resolved.rules.iter().map(|rule| rule.at.clone()))
        .collect()
}

fn document(
    record: &AdmissionRecord,
    digest: Option<Sha256Digest>,
    programs: &[Value],
    mutations: Vec<Value>,
    stopped: Option<Value>,
    accounting: Accounting<'_>,
) -> Value {
    let refusal = record.refusal.as_ref();
    let survivors = survivors(&mutations);
    // The kill matrix of a full run, from its rows (`report::matrix`); null under first-kill, whose
    // rows hold only the cells up to the first kill, and when the specification is refused.
    let matrix = if refusal.is_none() && accounting.schedule == schedule_name(ScheduleMode::Full) {
        matrix(programs, &mutations)
    } else {
        Value::Null
    };
    let counts = STATUSES
        .iter()
        .map(|status| {
            (
                (*status).to_owned(),
                json!(mutations.iter().filter(|m| m["status"] == *status).count()),
            )
        })
        .collect::<Map<_, _>>();
    json!({
        "schema": RUN_SCHEMA,
        "version": RUN_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "result_schema_version": RESULT_SCHEMA_VERSION,
        "kink_build": run_document_build(),
        "kink": kink_campaign::kink_identity(),
        "spec": {
            "outcome": if refusal.is_some() { "refused" } else { "admitted" },
            "stage": refusal.map(|r| &r.stage),
            "reason": refusal.map(|r| &r.reason),
            "detail": refusal.map(|r| &r.detail),
            "digest": digest.map(|d| d.to_string()),
            "execution_digest": accounting.execution,
            "files": record
                .files
                .iter()
                .map(|f| json!({"name": f.name, "sha256": f.sha256.to_string()}))
                .collect::<Vec<_>>(),
            "exclusion": accounting.exclusion,
        },
        "programs": programs,
        "unusable_programs": unusable_programs(programs),
        "mutations": mutations,
        "counts": counts,
        "survivors": survivors,
        "result": accounting.result,
        "stopped": stopped,
        "outcome_cache": accounting.outcome_cache,
        "mismatches": accounting.mismatches,
        "baseline_runs": accounting.baseline_runs,
        "order": accounting.order,
        "schedule": accounting.schedule,
        "matrix": matrix,
        "untargeted_rules": accounting.untargeted_rules,
        "data": accounting.data,
    })
}

/// The run document's `kink_build`: the build that wrote it (kink-campaign `identity::kink_build`,
/// packet CACHE-ID-fix-1), or null when the executable cannot be read, which `kink-flow report`
/// never accepts.
fn run_document_build() -> Value {
    kink_campaign::kink_build().map_or(Value::Null, |build| json!(build.to_string()))
}

/// The run document of a mutation list that does not decode, for a run under `schedule`: it names
/// the schedule, and its `matrix` is null, since no specification was admitted for it.
pub fn mutation_list_refused(detail: &str, schedule: ScheduleMode) -> Value {
    json!({
        "schema": RUN_SCHEMA,
        "version": RUN_VERSION,
        "schedule": schedule_name(schedule),
        "matrix": null,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "kink_build": run_document_build(),
        "kink": kink_campaign::kink_identity(),
        "mutation_list": {"outcome": "refused", "detail": detail},
    })
}

/// The path of the run document of the cache `cache` (or the manifest's default cache).
pub fn report_path(manifest: &FlowManifest, cache: Option<&Path>) -> PathBuf {
    cache_directory(manifest, cache).join(REPORT_FILE)
}

#[cfg(test)]
mod tests {
    use super::*;
    use kink_patch::{Claim, SentenceOrigin, UNREAD_EQUATION_CLAIM};

    /// Re-pin R0-tail (R0c-fix-4 review minor 2): a refusal the compiled reading's cross-check
    /// gives is named in the row's `removed_claims`, from the plan's claims. No input is known to
    /// reach that refusal through the binary (R0c-fix-4 and its review), so this pins the fill
    /// rule itself: a plan with claims replaces the row's reading, and a plan without leaves it.
    #[test]
    fn the_deciding_plans_claims_fill_the_row() {
        let reading = json!({"removed": [], "unsupported": []});
        let mut row = Map::new();
        row.insert("removed_claims".into(), reading.clone());
        verdict_claims(&mut row, &Withdrawal::default(), |_| {
            panic!("a plan without claims is not read")
        });
        assert_eq!(row["removed_claims"], reading);
        let mut claims = Withdrawal::default();
        claims.unsupported.push(Claim {
            origin: SentenceOrigin::Inserted { edit: 0 },
            key: UNREAD_EQUATION_CLAIM.to_owned(),
            value: json!({"head": "Lblf", "equation": "f"}),
        });
        verdict_claims(&mut row, &claims, |claims| {
            json!(
                claims
                    .unsupported
                    .iter()
                    .map(|claim| claim.key.clone())
                    .collect::<Vec<_>>()
            )
        });
        assert_eq!(row["removed_claims"], json!(["unread-equation"]));
    }

    /// The tier-1 rule that both the search ([`Search::search_facts`]) and the compile-ahead
    /// guess ([`Search::live_compiles`]) decide by, under each schedule. No run document can
    /// show the guess: a wrong one costs a compile, never a row, a record or a hint, so the
    /// rule they share is pinned here.
    #[test]
    fn tier_one_decides_by_the_schedule() {
        let record = |outcome| OutcomeRecord {
            program_id: String::new(),
            baseline_run_sha256: String::new(),
            outcome,
            slots: Vec::new(),
            mutant_run_sha256: String::new(),
            difference: Value::Null,
            allowance_bytes: None,
        };
        let killed = |c| (c, record(CachedOutcome::Killed));
        let agree = |c| (c, record(CachedOutcome::Agree));
        let decides = |order: &[usize], records: &[(usize, OutcomeRecord)]| {
            [ScheduleMode::FirstKill, ScheduleMode::Full]
                .map(|schedule| tier1_decides(order, records, schedule))
        };
        // No program in O: nothing can run, under either schedule.
        assert_eq!(decides(&[], &[]), [true, true]);
        // No record, or agreements for part of O: the rest of O runs.
        assert_eq!(decides(&[0, 1, 2], &[]), [false, false]);
        assert_eq!(decides(&[0, 1, 2], &[agree(0), agree(2)]), [false, false]);
        // A cached kill decides a first-kill row, never a full one, which needs every cell.
        assert_eq!(decides(&[0, 1, 2], &[agree(0), killed(2)]), [true, false]);
        assert_eq!(decides(&[0, 1, 2], &[killed(1)]), [true, false]);
        // A record for every program of O decides both.
        assert_eq!(
            decides(&[0, 1, 2], &[killed(0), agree(1), killed(2)]),
            [true, true]
        );
        assert_eq!(
            decides(&[0, 1, 2], &[agree(0), agree(1), agree(2)]),
            [true, true]
        );
    }
}
