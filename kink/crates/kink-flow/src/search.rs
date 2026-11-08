//! The kill search with its outcome cache (flow README 5.4, 5.6 and 7.5): `kink-flow run`.
//!
//! One command admits the specification once and uses its one `NativeValidator` for the
//! result cache update and for every mutation. Per mutation, in the list's order:
//!
//! 1. Resolve it into one pinned patch (F-04); an `invalid-mutation` ends there. A mutation
//!    whose edit only weakens the specification (kink-patch `ClaimSupport::weakening`: it deletes
//!    equations of functions or lemmas, or replaces one by an instance of itself, a narrower
//!    pattern or `requires`) is `unkillable`
//!    there too, with reason `weakening`: every model of the specification is a model of the
//!    mutant, so no program can kill it, and nothing runs (kink27 R5-WEAKENING). It is decided
//!    after the `baseline-findings` check (before tier 1, a baseline with a finding no
//!    `[spec] assume_joined` name assumes makes every mutation with a program in O `unknown`),
//!    since the argument reads the baseline's normal forms as a model (fix round 1). When every
//!    edited sentence keeps its axiom (kind `valid-condition`: its `requires` adds only
//!    conjuncts that hold under every valuation of their variables, such as `isNat ( N:Nat )`),
//!    the mutant has exactly the specification's models, and the mutation is `equivalent` with
//!    reason [`VALID_CONDITION_REASON`] instead.
//! 2. Choose the programs O: the comparable programs of the up-to-date result cache, in
//!    `FLOW.toml`'s order. Every live call runs first the programs of the call whose cached
//!    coverage witnesses the mutant's edit, then the rest, each group in O's order (the search
//!    order C, README 5.6 step 3): once the mutant's claim-free side
//!    compiles, the runner gives its compiled edit as a ground program witnesses it
//!    (kink-campaign `CompiledEdit::for_ground_tests`: `CompiledEdit::between` of that side, the
//!    rule its coverage selection reads, or of the mutant as written when only definedness claims
//!    were withdrawn, whose withdrawal adds no witness through a ground program's coverage;
//!    `run_campaign_multi_ordered`), and a program witnesses
//!    it as [`witnesses`] says (applied, k-rust `applied`, for an axiom whose edit is confined to
//!    its right-hand side or `ensures`; matched, k-rust `matched`, for every other axiom of a
//!    site-local edit: a rewrite rule's `requires`, left-hand side or attribute, a deleted rewrite
//!    rule, an equation's `requires`; every program for an edit that is not site-local), and a
//!    program whose cached coverage is not complete witnesses every edit, since it covers only
//!    what its run explored before it stopped. The row's `witnesses` lists the witnessing
//!    programs of O, from a live call's compiled edit or, on a row tier 1 decides with no call,
//!    from the one the mutation's outcome file keeps ([`EditWitness`]); it is empty on the
//!    `no-comparable-program` row of an empty O, and otherwise null when there is neither. C is
//!    a function of the inputs: the witness set is computed from the compiled edit and the result
//!    records' coverage, both keyed facts, by the one predicate the live call and the tier-1 sort
//!    share. What is decided before any compile
//!    (tier 1, the compiles ahead) depends only on the set of programs in O, not on their
//!    order. Which program a call runs first changes which killing program it finds first and the
//!    cost, never a status while no `budget.time_ms` bound fires, in either profile: under Z3 every
//!    solver query is bounded by Z3 resource units (`[budget] smt_resource_limit`), so its
//!    answer does not depend on what a reused backend asked before ([`tier1_refusal`]; under a
//!    clock-bounded solver it could move a status between killed, unknown and survived, never
//!    to a false kill; review L2-1-tail-1 D1, D2).
//! 3. Tier 1 (README 7.5.3): the valid outcome records of the programs of O, under a key that
//!    names every input of the outcome (kink's build, the k-rust revision, the solver profile,
//!    the specification's execution digest, the budget, the oracles, the mutation's identity,
//!    the program digest and the program's baseline run digest), decide with no call
//!    ([`tier1_decision`]) when the killer the row must name is decided by them. Let k be the
//!    lock's killer of the mutation ([`crate::lock`]) when it names a program of O. A valid
//!    `killed` record of k decides: the killer is k. If k has no valid record, tier 1 does not
//!    decide: k must run. Otherwise the killer is the canonical one, the first killing program in
//!    C, and the records decide when every program of O has one (with no cached kill, the status
//!    is the fold over them: survived, or unknown when some record is), or when C is known from
//!    the compiled edit the outcome file keeps and every program before the first cached kill in
//!    C has a record (that kill is the killer), or when every program has a record and exactly one
//!    is a kill. With several cached kills, every program cached and no stored compiled edit, the
//!    row runs live as if no record were valid (the no-witness fallback; records are written with
//!    the edit, so this does not arise from the records this command writes). A cached unknown
//!    (CF-33d) is a function of the key ([`crate::outcomes`]), as an agreement is.
//! 4. Otherwise the mutant runs live. Tier 2: when k is a program of O with no valid record, one
//!    call runs k alone; if it kills, that is the verdict (`killer_source` `record`). Otherwise the
//!    canonical call runs every program of O without a valid record (k included), the programs
//!    that witness the compiled edit first, then the rest, each in O's order, so in C; when a
//!    cached kill exists and C is known (from k's call's compiled edit or the stored one), it takes
//!    only the programs before the first cached kill in C. That cut saves cost only: the killer is
//!    the earlier in C of the call's first kill and the first cached kill, since the call ran every
//!    program before its own first kill in C that had no record.
//! 5. Every status is `kink_campaign::derive_mutant_report` (schedule `FirstKill`) over the
//!    assembled plan: the valid records' cached outcomes in O's order, then the last live call's
//!    tests in their order, with that call's mutant-scope failure. kink-flow adds no fold and compares
//!    no terms: a mutation is killed only by a proved `Distinguish`, live from
//!    `run_campaign_multi` in this command or cached under an exactly matching key. A cached
//!    agreement is the fold's bottom, and a cached unknown is the outcome the cold call's test of
//!    that program gives, so the assembled status is the cold call's status; a live mutant-scope
//!    failure that precedes execution next to a cached record (which says the mutant ran) is the
//!    corpus error `outcome-conflict`. A live mutant-scope `Infrastructure` failure is not
//!    (flow F-16): the status is the live plan's alone (`error`), as a cold call gives it, and
//!    the cached records leave the plan and the row.
//! 6. After every call, each program's baseline row from that call is compared, by run
//!    digest, with its cached record. Any difference is a corpus error: the mutation gets the
//!    status `error` with reason `baseline-mismatch:<program id>` (or
//!    `baseline-count-mismatch`), nothing is written to tier 1 for it, and the run stops.
//! 7. After a verdict, every live test whose outcome is cacheable (killed, agree, or, since
//!    CF-33d, an unknown of a judged run, with its cause; [`crate::outcomes::cacheable`]) gets a
//!    tier-1 record, unless its call's plan carries a mutant-scope failure, and the mutation's
//!    outcome file keeps the call's compiled edit ([`EditWitness`]). The report is written after
//!    every mutation, corpus errors included; the lock is settled once, after the last
//!    ([`crate::lock::Lock::settle`]: rewritten after a run that judged every mutation of the
//!    list, compared under `--locked`). Each row carries `recorded_killer` and `killer_change`,
//!    why its killer is not the recorded one ([`Search::record_fields`]).
//!
//! The steps above are the first-kill search ([`ScheduleMode::FirstKill`], the default).
//! `run --full` ([`RunOptions::schedule`] [`ScheduleMode::Full`]) runs every comparable program on
//! every selected mutation, so that each row holds every cell of the kill matrix:
//!
//! - O is every comparable program in corpus order, and a live call keeps that order (step 2;
//!   `witnesses` still names the programs that witness the compiled edit, in that order).
//! - Tier 1 decides with no call only when every program of O has a valid record (step 3): a
//!   `killed` record does not decide a full row, which needs every cell. The valid records,
//!   killed, agreements and unknowns alike, are the cached cells C, and L = O minus C.
//! - No one-program call is made for k (step 4): under `Full` every program of L runs in one
//!   call anyway.
//! - The fold (step 5) is `derive_mutant_report` under `Full` over C's outcomes then the call's
//!   tests, with the same `outcome-conflict` and `Infrastructure` rules.
//! - Records follow step 7 unchanged. Each row carries `killed_by`, every killing program in
//!   corpus order (null under first-kill, which establishes one killer), its `killer` is k when k
//!   is among them, else the first of them in C (C from the call's compiled edit or the stored
//!   one, with the same no-witness fallback), so it is the first-kill row's killer, and its
//!   `executed` lists every program of O in corpus order, cached and live; the document carries
//!   the per-program `matrix` ([`crate::report::matrix`]).
//!
//! A tier-1 record is the outcome of one executed test, and the schedule decides only whether a
//! test is executed, never what an executed test's request, sides or slots are; wherever tier 1
//! is on, a program's outcome does not depend on which programs ran before it in the call
//! (step 2). So a record does not depend on the schedule, the tier-1 context does not name it,
//! and the records either schedule writes serve both. A full row's status is the first-kill
//! row's: both are kink-campaign's fold over the same per-program outcomes, in which a kill ranks
//! above every inconclusive outcome, and under `FirstKill` the fold only reads fewer outcomes
//! below a kill. And both choose k when k's cell is a kill, else the first kill in C, from the
//! same per-program outcomes, so both write the same lock: the killer is a function of the lock
//! and the inputs, never of the cache, the compile workers or the memos.
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
//! evidence row, a digest, a key, an outcome record or a lock.
//!
//! CF-16: every live call computes the kill evidence of each distinguishing test from its own
//! evidence ([`crate::evidence`]: the first differing cell path of the two sides' ends and both
//! values as K text), which the test's executed entry shows and its `killed` tier-1 record keeps
//! (outside the key, inside the record digest), so a kill decided from tier 1 shows it too. It
//! enters no evidence row, run digest, key or lock, and nothing decides a status from it.
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
//! `run --verify` ([`RunMode::Verify`]) decides nothing from tier 1: it runs step 4 with tier 1
//! off for every mutation (under first-kill k alone when k is in O, then the cold call over O
//! unless k killed), then one call per valid record whose program those calls did not execute,
//! and reports every record (and the cached path's status) that differs from the live runs as
//! `outcome-mismatch:<program id>`; a killer that differs implies such an outcome. A compiled
//! edit the outcome file keeps that differs from the cold call's is reported in `mismatches`
//! (`{cached: {witness}, live: {witness}}`) and leaves the row's status alone, since it decides
//! none. It writes no record and no lock.
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

use crate::evidence::EndReader;
use crate::{
    admit::{AdmittedSpec, InputSession, admit_spec_with},
    cli::{CommandSpelling, FrontEnd, Verb},
    digest::{mutation_identity, outcome_context, spec_digest},
    lock::{Lock, Settle},
    manifest::{Budget, FlowManifest},
    memo::{self, Facts, MemoUse},
    mutation::{
        EditedRule, InvalidMutation, Mutation, MutationList, ResolvedMutation, resolve, rule_texts,
    },
    outcomes::{CachedOutcome, OutcomeRecord, OutcomeStore, cacheable, slot_name},
    report::{
        MutantCensus, OPEN_APPLICATION_REASON, RUN_SCHEMA, RUN_VERSION, action, action_spelled,
        claims_value, executed_cause, matrix, open_application_cause, refused_action, rules_value,
        slots_value, specification_diagnostics_value, survivors, typing_diagnostics_value,
        untargeted_rules, unusable_programs,
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
    selection::ground_reading_is_as_written,
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

/// Why tier 1 is off for a build of `profile` whose backends are built with `solver`, or `None`
/// when it may be used (re-pin decision 5, finding B-09). An outcome is a function of its key
/// only if every solver answer it rests on is: the answers to a run's queries and to kink's own
/// queries outside a run (leaf feasibility, the observation decider), each of which kink counts
/// when undecided (k-rust's `smtUnknowns` and kink-native's `decider_smt_unknowns`, reported,
/// never an exclusion). Without Z3 no solver is asked. Under the Z3 profile with `solver` bounded
/// by Z3 resource units (`[budget] smt_resource_limit`, which every command's backends take) an
/// answer, decided or not, is a function of the query, the units and the Z3 build, whatever the
/// host's load and whatever the backend asked before (k-rust's Execute promise covers that
/// mode), and the context names the units and the build (`results::budget_value`): tier 1 reads
/// and writes, as do the result cache, the memos and the pattern cache, unless the build cannot
/// be named (kink-native `UNNAMED_Z3_BUILD`). Under a clock-bounded `solver` an answer depends on
/// the host's load, which no key names, and all of them are off. The profile is the build's
/// (`SolverProfile::BUILD`, kink-native's `z3` feature), so it follows workspace feature
/// unification.
pub fn tier1_refusal(
    profile: SolverProfile,
    solver: k_rust::backend::BackendOptions,
) -> Option<&'static str> {
    match profile {
        SolverProfile::NoZ3 => None,
        SolverProfile::Z3 if solver.smt_resource_limit.is_none() => Some(TIER1_CLOCK),
        SolverProfile::Z3 => kink_native::solver_named().err(),
    }
}

/// Why tier 1 is off under the Z3 profile when its solver is bounded by the clock
/// ([`tier1_refusal`]).
pub const TIER1_CLOCK: &str = "tier 1 is disabled under the z3 profile when solver queries are \
     bounded by the clock: an answer then depends on the host's load, which no key can name, so \
     no outcome is cached or read; every mutation runs live";

/// The `killer_source` of a status decided by a valid tier-1 `killed` record.
pub const SOURCE_OUTCOME_CACHE: &str = "outcome-cache";
/// The `killer_source` of a kill found by the one-program call over the recorded killer (the
/// lock's, [`crate::lock`]).
pub const SOURCE_RECORD: &str = "record";
/// The `killer_source` of a kill found by the cold call.
pub const SOURCE_SEARCH: &str = "search";

/// The status of a mutation whose edit only weakens the specification (kink27 R5-WEAKENING):
/// kink-flow's own, decided at resolution with reason [`WEAKENING_REASON`]; kink-corpus and the
/// campaign runner keep their statuses for it.
pub const UNKILLABLE: &str = "unkillable";
/// The reason of an [`UNKILLABLE`] mutation.
pub const WEAKENING_REASON: &str = "weakening";
/// The reason of an `equivalent` mutation every edited sentence of which keeps its axiom
/// (kink-patch `WeakeningKind::ValidCondition`): its `requires` adds only conjuncts that hold
/// under every valuation of their variables, so the mutant has exactly the specification's
/// models. kink-flow decides it at resolution, as it decides [`UNKILLABLE`].
pub const VALID_CONDITION_REASON: &str = "valid-condition";

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
    /// How many threads compile mutants ahead of their turn (`--compile-workers`; `None`:
    /// [`DEFAULT_COMPILE_WORKERS`]). 1 compiles each mutant in its own campaign call, on the
    /// calling thread. Every run document, outcome record and lock is the same for every value
    /// (re-pin L1-3; [`run_with`]).
    pub compile_workers: Option<usize>,
    /// Whether the warm path's memos are used (`--no-memo`: [`MemoUse::Off`]; re-pin L1-4,
    /// [`crate::memo`]). Every run document, outcome record and lock is the same either way.
    pub memo: MemoUse,
    /// Which programs each mutation runs on: [`ScheduleMode::FirstKill`] (the default), the kill
    /// search, which stops at the first killing program; [`ScheduleMode::Full`] (`--full`), every
    /// comparable program in corpus order, so that each row holds every cell of the kill matrix
    /// (module documentation).
    pub schedule: ScheduleMode,
    /// The killer record (`--lock FILE`, [`crate::lock`]): read before admission, its killers
    /// tried first, and rewritten after a run that judged every mutation of the list. `None`: no
    /// record, and nothing is written outside the cache.
    pub lock: Option<PathBuf>,
    /// `--locked`: compare the lock the run would write with the file and leave the lock
    /// unwritten (the cache is written as in any run); a difference is a finding (exit 1).
    pub locked: bool,
}

// `ScheduleMode` has no default of its own: a campaign schedule is not something kink-campaign's
// other callers should get implicitly.
impl Default for RunOptions {
    fn default() -> Self {
        Self {
            only: Vec::new(),
            cache: None,
            compile_workers: None,
            memo: MemoUse::default(),
            schedule: ScheduleMode::FirstKill,
            lock: None,
            locked: false,
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

/// How `run` uses the outcome cache.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum RunMode {
    /// The kill search with both tiers (`kink-flow run`).
    #[default]
    Search,
    /// Re-prove every valid tier-1 record and decide nothing from it (`kink-flow run
    /// --verify`, README 7.5.3): no tier-1 decision, no write but the report.
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
    /// The mutant's compiled edit as a ground program witnesses it (kink-campaign
    /// [`CompiledEdit::for_ground_tests`]) read through the baseline's rule authors; `None` when
    /// the mutant was refused before the side its programs run on compiled.
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
    /// The test ran: its outcome as a record names it (the cacheable outcome, else the executed
    /// entry's label), the run digest of the mutant's evidence row, and the report a record of it
    /// holds ([`OutcomeRecord::report`]).
    Ran(String, Option<String>, Value),
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
    /// The lock's killer of each mutation, by mutation id (program ids).
    recorded: BTreeMap<String, String>,
    store: Store,
    stats: Stats,
    /// `run --verify`'s disagreements, for the run document's `mismatches`.
    mismatches: Vec<Value>,
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
                self.spelling.verb(Verb::Coverage)
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
                .map(CampaignReport::baseline_row)
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
                    self.spelling.verb(Verb::Coverage)
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
    /// so no timings; a kill's difference and sides are the record's (CF-16), and an unknown's
    /// cause and every record's undecided-answer counts are the record's (CF-33d), as the live
    /// entry that wrote it gave them.
    fn cached_entry(&self, candidate: usize, record: &OutcomeRecord) -> Value {
        let mut entry = json!({
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
            "cause": record.cause,
            "cached": true,
            "wall_ms": null,
            "baseline_ms": null,
            "baseline_reused": null,
        });
        if record.smt_unknowns > 0 {
            entry["smt_unknowns"] = json!(record.smt_unknowns);
        }
        if record.decider_smt_unknowns > 0 {
            entry["decider_smt_unknowns"] = json!(record.decider_smt_unknowns);
        }
        entry
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
        let removed_claims = row.get("removed_claims").unwrap_or(&Value::Null);
        let witness = EditWitness::from_value(&witness, removed_claims);
        if let Some(witness) = &witness {
            self.insert_witnesses(row, order, witness);
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
    /// compiles: every candidate in corpus order (the candidates are built in manifest order). A
    /// first-kill call then runs first the programs whose coverage witnesses the mutant's
    /// compiled edit ([`Search::call_untimed`]); what is decided before any compile (tier 1, the
    /// compiles ahead) depends only on the set of programs, not on their order.
    fn program_order(&self) -> Vec<usize> {
        (0..self.candidates.len()).collect()
    }

    /// The search order C of `order` for a compiled edit: the programs whose coverage witnesses
    /// it ([`witnesses`]) first, then the rest, each group in `order`'s order, which is the order
    /// a first-kill call runs them in ([`Search::call_untimed`]).
    fn search_order(&self, order: &[usize], witness: &EditWitness) -> Vec<usize> {
        let mut search = order.to_vec();
        search.sort_by_key(|&c| !witnesses(&self.candidates[c], witness));
        search
    }

    /// The lock's killer of the mutation `id` as a candidate, when it names a comparable program.
    fn recorded_candidate(&self, id: &str) -> Option<usize> {
        self.recorded
            .get(id)
            .and_then(|program| self.position(program))
    }

    /// What tier 1 decides for the mutation `id` from its valid `records` ([`tier1_decision`]),
    /// with C from the compiled edit the outcome file keeps (`stored`).
    fn tier1(
        &self,
        id: &str,
        order: &[usize],
        records: &[(usize, OutcomeRecord)],
        stored: Option<&EditWitness>,
    ) -> Tier1 {
        let search = stored.map(|witness| self.search_order(order, witness));
        tier1_decision(
            order,
            records,
            search.as_deref(),
            self.recorded_candidate(id),
            self.schedule,
        )
    }

    /// The first of `programs` in the search order `search` (in `order` when C is unknown, which
    /// only a row with at most one killing program meets).
    fn first_in(
        &self,
        search: Option<&[usize]>,
        order: &[usize],
        programs: impl IntoIterator<Item = usize>,
    ) -> Option<usize> {
        let programs = programs.into_iter().collect::<BTreeSet<_>>();
        search
            .unwrap_or(order)
            .iter()
            .copied()
            .find(|c| programs.contains(c))
    }

    /// The killer of a full row whose killing programs are `killed_by` (ids, corpus order): the
    /// recorded killer of the mutation `id` when it is one of them, else the first of them in C
    /// (`search`); `None` without a kill.
    fn full_killer(
        &self,
        killed_by: Option<&[String]>,
        id: &str,
        search: Option<&[usize]>,
        order: &[usize],
    ) -> Option<usize> {
        let killers = killed_by?
            .iter()
            .filter_map(|program| self.position(program))
            .collect::<Vec<_>>();
        if let Some(recorded) = self.recorded_candidate(id).filter(|k| killers.contains(k)) {
            return Some(recorded);
        }
        self.first_in(search, order, killers)
    }

    /// The row's `recorded_killer`, the lock's killer of the mutation or null, and its
    /// `killer_change`, why the row's killer is not the recorded one (README, "The killer
    /// record"): null when they are equal, else `no-record`, `not-in-corpus`, `not-comparable`
    /// (with the row's `unusable_killer`, `source: "record"`, unless it reports a cached kill's),
    /// `no-longer-kills` (the recorded killer ran, live or cached, and did not distinguish) or
    /// `not-run` (no program ran it: the status was decided before any run).
    fn record_fields(&self, row: &mut Value, mutation: &Mutation) {
        let recorded = self.recorded.get(&mutation.id).cloned();
        let killer = row["killer"].as_str().map(str::to_owned);
        let change = match &recorded {
            _ if killer == recorded => None,
            None => Some("no-record"),
            Some(id) => Some(
                match self.manifest.programs.iter().position(|p| &p.id == id) {
                    None => "not-in-corpus",
                    Some(index) if self.position(id).is_none() => {
                        if row["unusable_killer"].is_null() {
                            row["unusable_killer"] = json!({
                                "program": id,
                                "class": self.rows[index].row["class"],
                                "cause": self.rows[index].row["cause"],
                                "source": SOURCE_RECORD,
                            });
                        }
                        "not-comparable"
                    }
                    Some(_)
                        if row["executed"]
                            .as_array()
                            .into_iter()
                            .flatten()
                            .any(|entry| entry["program"] == id.as_str()) =>
                    {
                        "no-longer-kills"
                    }
                    Some(_) => "not-run",
                },
            ),
        };
        row["recorded_killer"] = json!(recorded);
        row["killer_change"] = json!(change);
    }

    /// The row's `witnesses` ([`Self::witness_programs`]) and `witnesses_global`: whether the
    /// compiled edit is not site-local, so that every program is a witness whatever its coverage
    /// reaches (an equation's left-hand side or attribute, a declaration, ...;
    /// [`EditWitness::global`]).
    fn insert_witnesses(
        &self,
        row: &mut Map<String, Value>,
        order: &[usize],
        witness: &EditWitness,
    ) {
        row.insert("witnesses".into(), self.witness_programs(order, witness));
        row.insert("witnesses_global".into(), json!(witness.global));
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
            self.insert_witnesses(row, order, witness);
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
    /// is cacheable ([`cacheable`]: `killed`, `agree`, or an `unknown` of a judged run), none when
    /// the call's plan carries a mutant-scope failure. A `killed` record carries the test's kill
    /// evidence from `differences` (CF-16), an `unknown` record its executed entry's cause from
    /// `causes` (CF-33d, [`entry_causes`]; none without one) and whether that cause is an open
    /// application of an edited function from `opens` ([`entry_opens`]), and every record the
    /// run's undecided-answer counts.
    fn live_records(
        &self,
        run: &MutantRun,
        differences: &BTreeMap<String, Value>,
        causes: &BTreeMap<String, String>,
        opens: &BTreeMap<String, bool>,
    ) -> Vec<(String, OutcomeRecord)> {
        if run.plan.mutant_failure.is_some() {
            return Vec::new();
        }
        run.plan
            .tests
            .iter()
            .filter_map(|test| {
                let notes = run
                    .evidence
                    .iter()
                    .find(|evidence| evidence.test_id == test.test_id)
                    .map(|evidence| &evidence.notes);
                let (outcome, slots) = cacheable(&test.run, notes)?;
                let candidate = &self.candidates[self.position(&test.test_id)?];
                let cause = match outcome {
                    CachedOutcome::Unknown => Some(causes.get(&test.test_id)?.clone()),
                    CachedOutcome::Killed | CachedOutcome::Agree => None,
                };
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
                            CachedOutcome::Agree | CachedOutcome::Unknown => Value::Null,
                        },
                        open_application: outcome == CachedOutcome::Unknown
                            && opens.get(&test.test_id) == Some(&true),
                        cause,
                        smt_unknowns: notes.map_or(0, |notes| count(notes.smt_unknowns)),
                        decider_smt_unknowns: notes
                            .map_or(0, |notes| count(notes.decider_smt_unknowns)),
                        allowance_bytes: Some(
                            k_rust::k_rust_backend::allowance::Allowance::of_process().bytes(),
                        ),
                    },
                ))
            })
            .collect()
    }

    /// The kill search for one mutation: its row of the run document, and whether it ended in
    /// a corpus error (the run then stops, and nothing is written to tier 1 for it).
    /// The mutants [`Search::search_one`] would compile for `resolution` given the stores now
    /// (re-pin L1-3, for compiling ahead): none when the mutation resolves to no generation, no
    /// program is in O, or tier 1 decides it with no call (a valid killed record, or a valid
    /// record for every program of O); otherwise each candidate's patch and its withdrawing
    /// patch ([`kink_campaign::mutant_compiles`]). Under [`ScheduleMode::Full`] a valid killed
    /// record does not decide ([`tier1_decides`]). A guess that differs from what the search then
    /// does costs a compile, never a row.
    fn live_compiles(
        &self,
        mutation: &Mutation,
        resolution: &Result<ResolvedMutation, InvalidMutation>,
    ) -> Vec<Patch> {
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
            let (records, stored) = self.valid_records(identity, &order, &mut Map::new());
            if self
                .tier1(&mutation.id, &order, &records, stored.as_ref())
                .decides()
            {
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
            None,
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

    /// Whether tier 1 decides the mutation of `facts` with no call given the stores and the lock
    /// now ([`tier1_decision`], [`Search::search_facts`] step 3). Only in search mode. The
    /// resolution memo is used only then (re-pin L1-4).
    fn decided(&self, mutation: &Mutation, facts: &Facts) -> bool {
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
        let (records, stored) = self.valid_records(facts.identity, &order, &mut Map::new());
        self.tier1(&mutation.id, &order, &records, stored.as_ref())
            .decides()
    }

    /// The row of a mutation whose facts the resolution memo holds, when tier 1 decides it with
    /// no call ([`Search::decided`]): the row [`Search::search_one`] gives the live resolution
    /// of the same inputs, built from the same facts by the same code. `None` when tier 1 does
    /// not decide it; the caller then resolves the mutation live.
    fn search_memo(&mut self, mutation: &Mutation, facts: &Facts) -> Option<(Value, bool)> {
        if !self.decided(mutation, facts) {
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
    /// resolution memo; then the search stops with `None`, before it counts or writes anything,
    /// if tier 1 does not decide after all (another command wrote the tier-1 store since
    /// [`Search::decided`] read it), and the caller resolves the mutation live.
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
        row.insert("witnesses_global".into(), Value::Null);
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
        // fz26 KINK-BASELINE-FINDINGS: on a baseline with a finding no `[spec] assume_joined`
        // name assumes, no end is data, so no program can kill: the mutation is unknown before
        // any store is read or any call made (no cached outcome decides it, whatever it says).
        if !order.is_empty() && self.gated() {
            return Some((self.baseline_findings_row(row, &order), false));
        }
        // kink27 R5-WEAKENING: a mutation whose edit only weakens the specification has every
        // model of the specification among its models, so no program can kill it. The verdict
        // depends on the mutation alone: no store is read, no call made, nothing re-run. It is
        // decided after the baseline-findings check (fix round 1): the argument reads the
        // baseline's normal forms as a model, which an unassumed finding puts in doubt, and the
        // specification's own findings are what the author has to fix first.
        if !facts.weakening.is_null() {
            let (status, reason) = weakening_status(&facts.weakening);
            row.insert("status".into(), json!(status));
            row.insert("reason".into(), json!(reason));
            return Some((
                finish(row, None, None, RowCalls::default(), Vec::new()),
                false,
            ));
        }
        let (records, stored) = self.valid_records(identity, &order, &mut row);
        let decision = self.tier1(&mutation.id, &order, &records, stored.as_ref());
        // A memo's facts carry no generation (re-pin L1-4): they are used only when tier 1
        // decides with no call. Otherwise the search stops here, on the records it decides from,
        // before anything is counted or written (re-pin L1-4 fix 1, review D6), and the caller
        // resolves the mutation live.
        if generation.is_none() && !decision.decides() {
            return None;
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
            let cached = match decision {
                Tier1::Call { records: false } => Vec::new(),
                _ => records,
            };
            return Some(self.search_full(
                mutation,
                row,
                facts,
                generation,
                &order,
                cached,
                stored.as_ref(),
            ));
        }

        // The search order C from the outcome file's compiled edit, until a live call gives its
        // own; every call of one mutation compiles the same mutant. The cached entries are listed
        // in it, the order a live call would run them in.
        let mut search_order = stored.as_ref().map(|w| self.search_order(&order, w));
        let in_search_order = |records: &mut Vec<(usize, OutcomeRecord)>| {
            if let Some(search) = &search_order {
                records.sort_by_key(|(c, _)| search.iter().position(|p| p == c));
            }
        };
        let keep = match decision {
            // Tier 1, step 3: the recorded killer's cached kill, or the first cached kill in C
            // with every program before it in C cached, or every program of O cached.
            Tier1::Decided { killer, read } => {
                let mut read = read
                    .iter()
                    .filter_map(|c| records.iter().find(|(r, _)| r == c).cloned())
                    .collect::<Vec<_>>();
                in_search_order(&mut read);
                let report = self
                    .assemble(&read, None)
                    .expect("cached outcomes of executed tests form a valid plan");
                debug_assert_eq!(report.status == MutantStatus::Killed, killer.is_some());
                self.stats.mutations_from_cache += 1;
                self.stats.programs_from_cache += read.len();
                let executed = read
                    .iter()
                    .map(|(c, record)| self.cached_entry(*c, record))
                    .collect::<Vec<_>>();
                let reason = open_reason(&report, &cached_opens(&read, |c| self.candidates[c].id));
                let killer = killer.map(|c| self.candidates[c].id.to_owned());
                let source = killer.as_ref().map(|_| SOURCE_OUTCOME_CACHE);
                return Some((
                    verdict_row(
                        row,
                        &report,
                        None,
                        killer,
                        reason,
                        source,
                        RowCalls::default(),
                        executed,
                    ),
                    false,
                ));
            }
            Tier1::Empty => unreachable!("an empty O returned above"),
            Tier1::Call { records } => records,
        };
        // Step 4: the valid records the plan reads (none when the no-witness fallback ignores
        // them) and the live calls.
        let mut agree = if keep { records } else { Vec::new() };
        in_search_order(&mut agree);
        let known = |c: usize| agree.iter().any(|(a, _)| *a == c);
        let mut executed = agree
            .iter()
            .map(|(c, record)| self.cached_entry(*c, record))
            .collect::<Vec<_>>();
        self.stats.programs_from_cache += agree.len();
        // Each undecided program's [`report::open_application_cause`], by program: a cached
        // unknown's from its record, a live one's from its call's census, a later call's
        // replacing an earlier's, as its record does (step 7).
        let mut opens = cached_opens(&agree, |c| self.candidates[c].id);
        let generation =
            generation.expect("a memo's facts are searched only when tier 1 decides, in step 3");
        let cached_kills = agree
            .iter()
            .filter(|(_, record)| record.outcome == CachedOutcome::Killed)
            .map(|(c, _)| *c)
            .collect::<Vec<_>>();
        let mut calls = Calls::new();
        // Each live call's order, run, and its entries' causes and open applications (CF-33d): a
        // record keeps those of its own call's run.
        let mut runs = Vec::<(
            Vec<usize>,
            MutantRun,
            BTreeMap<String, String>,
            BTreeMap<String, bool>,
        )>::new();
        // The kill evidence of the live calls, by program; a later call's replaces an earlier's,
        // as its record does (step 7).
        let mut differences = BTreeMap::<String, Value>::new();
        let mut witness = None;
        let mut source = SOURCE_SEARCH;
        // The killer the row names, once a call or the records give it (its status decides
        // whether it is one).
        let mut killer = None;
        // Tier 2: the recorded killer, when it is a program of O with no valid record, alone.
        if let Some(k) = self.recorded_candidate(&mutation.id).filter(|k| !known(*k)) {
            match self.call(generation, &[k]) {
                (wall_ms, Err(error)) => {
                    calls.push((vec![k], json!("error"), wall_ms));
                    return Some(self.corpus_error(row, error, &calls, executed));
                }
                (wall_ms, Ok(live)) => {
                    let status = live.mutant.report.status;
                    calls.push((vec![k], json!(status_name(status)), wall_ms));
                    self.set_witnesses(&mut row, &order, &live, &mut witness);
                    if search_order.is_none() {
                        search_order = live.witness.as_ref().map(|w| self.search_order(&order, w));
                    }
                    executed.extend(executed_entries(
                        &live,
                        self.runner.end_reader(),
                        self.spec.result.slots(),
                        self.manifest.budget,
                        first_killer(&live),
                    ));
                    if status == MutantStatus::Killed {
                        source = SOURCE_RECORD;
                        killer = Some(k);
                    }
                    let causes = entry_causes(
                        &live,
                        self.runner.end_reader(),
                        self.spec.result.slots(),
                        self.manifest.budget,
                    );
                    let open = entry_opens(&live);
                    opens.extend(open.clone());
                    differences.extend(live.differences);
                    runs.push((vec![k], live.mutant, causes, open));
                }
            }
        }
        if source != SOURCE_RECORD {
            // The canonical call: every program of O with no valid record (the recorded killer
            // included), cut before the first cached kill in C when C is known (a saving only:
            // the killer is the earlier in C of the call's first kill and that cached kill).
            let first_cached = search_order
                .as_ref()
                .and_then(|c| c.iter().position(|p| cached_kills.contains(p)));
            let live_order = order
                .iter()
                .copied()
                .filter(|c| !known(*c))
                .filter(|c| match (&search_order, first_cached) {
                    (Some(search), Some(cut)) => search[..cut].contains(c),
                    _ => true,
                })
                .collect::<Vec<_>>();
            if live_order.is_empty() {
                // Every program before the first cached kill in C is cached: it is the killer.
                killer = search_order
                    .as_ref()
                    .zip(first_cached)
                    .map(|(search, cut)| search[cut]);
            } else {
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
                        if search_order.is_none() {
                            search_order =
                                live.witness.as_ref().map(|w| self.search_order(&order, w));
                        }
                        let call_kill = first_killer(&live).and_then(|id| self.position(id));
                        killer = self.first_in(
                            search_order.as_deref(),
                            &order,
                            cached_kills.iter().copied().chain(call_kill),
                        );
                        let live_killer = killer
                            .filter(|k| Some(*k) == call_kill)
                            .map(|k| self.candidates[k].id);
                        // Each program is listed once (F-14 review 1 m3, flow F-16): a recorded
                        // killer this call ran again is listed with this call's run, the one
                        // the status is folded from.
                        let entries = executed_entries(
                            &live,
                            self.runner.end_reader(),
                            self.spec.result.slots(),
                            self.manifest.budget,
                            live_killer,
                        );
                        executed.retain(|entry| {
                            entry["cached"] == true
                                || !entries
                                    .iter()
                                    .any(|again| again["program"] == entry["program"])
                        });
                        executed.extend(entries);
                        let causes = entry_causes(
                            &live,
                            self.runner.end_reader(),
                            self.spec.result.slots(),
                            self.manifest.budget,
                        );
                        let open = entry_opens(&live);
                        opens.extend(open.clone());
                        differences.extend(live.differences);
                        runs.push((live.order, live.mutant, causes, open));
                    }
                }
            }
        }
        // Step 5: the status of the assembled plan.
        let (last_order, last, ..) = runs.last().expect("a live call");
        let report = match self.assemble(&agree, Some((last_order, &last.plan))) {
            Ok(report) => report,
            Err(failure) => {
                let error = CorpusError {
                    reason: "outcome-conflict".into(),
                    detail: format!(
                        "the cached outcomes of {:?} and the live call over {:?} do not form \
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
            // `assemble` left the cached records out of the plan (flow F-16): they leave the
            // row and the counts too, so the row is the cold call's.
            self.stats.programs_from_cache -= agree.len();
            executed.retain(|entry| entry["cached"] != true);
        }
        let reason = last
            .plan
            .mutant_failure
            .map(|failure| kebab(&format!("{failure:?}")))
            .or_else(|| exclusion_reason(&report, runs.iter().map(|(_, run, ..)| run)))
            .or_else(|| open_reason(&report, &opens));
        verdict_claims(&mut row, &last.plan.claims, |claims| {
            claims_value(self.spec.validator.baseline(), claims)
        });
        // Step 7: the records of the live calls. A program both calls ran has one record, the
        // second call's (the store keeps the last of equal program digests and counts each
        // program once).
        let records = runs
            .iter()
            .flat_map(|(_, run, causes, opens)| self.live_records(run, &differences, causes, opens))
            .collect::<Vec<_>>();
        self.write_records(identity, mutation, &mut row, &records, witness.as_ref());
        let killer = killer.filter(|_| report.status == MutantStatus::Killed);
        let source = killer.map(|k| {
            if cached_kills.contains(&k) {
                SOURCE_OUTCOME_CACHE
            } else {
                source
            }
        });
        let killer = killer.map(|k| self.candidates[k].id.to_owned());
        let calls = self.calls(&calls);
        Some((
            verdict_row(row, &report, None, killer, reason, source, calls, executed),
            false,
        ))
    }

    /// A full row (`run --full`, module documentation): every program of O, in corpus order, is a
    /// cell, cached (every valid record, killed, agreement or unknown) or live (the rest, one
    /// call under [`ScheduleMode::Full`]). Tier 1 decides with no call only when every cell is
    /// cached; no one-program call is made for the recorded killer. The status is the fold over
    /// the cached cells then the call's tests, under `Full`; `killed_by` lists every killing
    /// program in corpus order, `killer` is the recorded killer when it is among them, else the
    /// first of them in the search order C ([`Search::full_killer`]), from the outcome cache when
    /// its cell is cached; `executed` lists every cell in corpus order. Records follow the
    /// first-kill rules (step 7).
    #[allow(clippy::too_many_arguments)]
    fn search_full(
        &mut self,
        mutation: &Mutation,
        mut row: Map<String, Value>,
        facts: &Facts,
        generation: Option<&CandidateGeneration<'_>>,
        order: &[usize],
        cached: Vec<(usize, OutcomeRecord)>,
        stored: Option<&EditWitness>,
    ) -> (Value, bool) {
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
                        self.runner.end_reader(),
                        self.spec.result.slots(),
                        self.manifest.budget,
                        None,
                    )));
                    return self.corpus_error(row, error, &calls, entries(executed));
                }
            },
        };
        let mut opens = cached_opens(&cached, |c| self.candidates[c].id);
        let mut reason = open_reason(&report, &opens);
        if let Some(live) = &live {
            let open = entry_opens(live);
            opens.extend(open.clone());
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
                .or_else(|| exclusion_reason(&report, std::iter::once(&live.mutant)))
                .or_else(|| open_reason(&report, &opens));
            verdict_claims(&mut row, &live.mutant.plan.claims, |claims| {
                claims_value(self.spec.validator.baseline(), claims)
            });
            let causes = entry_causes(
                live,
                self.runner.end_reader(),
                self.spec.result.slots(),
                self.manifest.budget,
            );
            let records = self.live_records(&live.mutant, &live.differences, &causes, &open);
            self.write_records(
                facts.identity,
                mutation,
                &mut row,
                &records,
                witness.as_ref(),
            );
        }
        let killed_by = self.killed_by(&report);
        let witness = live
            .as_ref()
            .and_then(|live| live.witness.as_ref())
            .or(stored);
        let killer = self.full_killer(
            killed_by.as_deref(),
            &mutation.id,
            witness.map(|w| self.search_order(order, w)).as_deref(),
            order,
        );
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
                self.runner.end_reader(),
                self.spec.result.slots(),
                self.manifest.budget,
                live_killer,
            )));
        }
        let calls = self.calls(&calls);
        let killer = killer.map(|killer| self.candidates[killer].id.to_owned());
        (
            verdict_row(
                row,
                &report,
                killed_by,
                killer,
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

    /// `run --verify` for one resolved mutation (README 7.5.3): the search of step 4 with tier 1
    /// off (under first-kill the recorded killer alone, when it is a program of O, then, unless it
    /// killed, the cold call over O), a one-program call per valid record those calls did not
    /// execute, and the comparison of every valid record and of the cached path's status with the
    /// live ones.
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
        let mut executed = Vec::<Value>::new();
        let mut witness = None;
        let mut live = BTreeMap::new();
        let mut source = SOURCE_SEARCH;
        let mut cold = None;
        // Under first-kill the recorded killer runs alone first, as the search runs it; under
        // `Full` every program runs in the one call anyway.
        let recorded = self
            .recorded_candidate(&mutation.id)
            .filter(|_| self.schedule == ScheduleMode::FirstKill);
        let mut steps = recorded.map(|k| vec![k]).into_iter().collect::<Vec<_>>();
        steps.push(order.to_vec());
        for (step, programs) in steps.into_iter().enumerate() {
            let alone = recorded.is_some() && step == 0;
            let one = match self.call(generation, &programs) {
                (wall_ms, Err(error)) => {
                    calls.push((programs, json!("error"), wall_ms));
                    return self.corpus_error(row, error, &calls, executed);
                }
                (wall_ms, Ok(one)) => {
                    calls.push((
                        one.order.clone(),
                        json!(status_name(one.mutant.report.status)),
                        wall_ms,
                    ));
                    one
                }
            };
            self.set_witnesses(&mut row, order, &one, &mut witness);
            let entries = executed_entries(
                &one,
                self.runner.end_reader(),
                self.spec.result.slots(),
                self.manifest.budget,
                first_killer(&one),
            );
            // Each program is listed once, with its last live run.
            executed.retain(|entry| {
                !entries
                    .iter()
                    .any(|again| again["program"] == entry["program"])
            });
            executed.extend(entries);
            let causes = entry_causes(
                &one,
                self.runner.end_reader(),
                self.spec.result.slots(),
                self.manifest.budget,
            );
            let opens = entry_opens(&one);
            self.collect_live(&one.mutant, &causes, &opens, &mut live);
            let killed = one.mutant.report.status == MutantStatus::Killed;
            cold = Some((one.mutant, opens));
            if alone && killed {
                source = SOURCE_RECORD;
                break;
            }
        }
        let (cold, cold_opens) = cold.expect("the cold call ran");
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
                        self.runner.end_reader(),
                        self.spec.result.slots(),
                        self.manifest.budget,
                        None,
                    ));
                    let causes = entry_causes(
                        &one,
                        self.runner.end_reader(),
                        self.spec.result.slots(),
                        self.manifest.budget,
                    );
                    let opens = entry_opens(&one);
                    self.collect_live(&one.mutant, &causes, &opens, &mut live);
                    live.entry(*c).or_insert(Live::NotRun(status));
                }
            }
        }
        // Every valid record against its program's live outcome.
        let mut mismatches = Vec::new();
        // The record's report (an unknown's cause, the undecided-answer counts) is compared too:
        // it is a function of the key, as the outcome is (CF-33d).
        for (c, record) in records {
            let (outcome, mutant, report) = match &live[c] {
                Live::Ran(outcome, mutant, report) => {
                    (outcome.clone(), mutant.clone(), report.clone())
                }
                Live::NotRun(status) => ((*status).to_owned(), None, OutcomeRecord::no_report()),
            };
            let cached = record.report();
            if outcome != record.outcome.as_str()
                || mutant.as_deref() != Some(record.mutant_run_sha256.as_str())
                || report != cached
            {
                let side = |outcome: &str, mutant: Value, report: Value| {
                    let mut side = json!({"outcome": outcome, "mutant_run_sha256": mutant});
                    for field in [
                        "cause",
                        "open_application",
                        "smt_unknowns",
                        "decider_smt_unknowns",
                    ] {
                        side[field] = report[field].clone();
                    }
                    side
                };
                mismatches.push(json!({
                    "mutation": mutation.id,
                    "program": self.candidates[*c].id,
                    "cached": side(
                        record.outcome.as_str(),
                        json!(record.mutant_run_sha256),
                        cached,
                    ),
                    "live": side(&outcome, json!(mutant), report),
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
        // The cold call's reason, as `run` gives it for the same call.
        let reason = cold
            .plan
            .mutant_failure
            .map(|failure| kebab(&format!("{failure:?}")))
            .or_else(|| exclusion_reason(&cold.report, std::iter::once(&cold)))
            .or_else(|| open_reason(&cold.report, &cold_opens));
        verdict_claims(&mut row, &cold.plan.claims, |claims| {
            claims_value(self.spec.validator.baseline(), claims)
        });
        // Under `Full` the cold call ran every program of O in corpus order, so its killers are
        // the row's `killed_by`; under first-kill the call ran in C, so its first killer is the
        // first in C, unless the recorded killer killed alone.
        let killed_by = self.killed_by(&cold.report);
        let killer = match &killed_by {
            Some(killers) => self.full_killer(
                Some(killers),
                &mutation.id,
                witness
                    .as_ref()
                    .map(|w| self.search_order(order, w))
                    .as_deref(),
                order,
            ),
            None => cold
                .report
                .killing_test_ids
                .first()
                .and_then(|id| self.position(id)),
        };
        let killer = killer
            .filter(|_| cold.report.status == MutantStatus::Killed)
            .map(|k| self.candidates[k].id.to_owned());
        let source = killer.as_ref().map(|_| source);
        (
            verdict_row(
                row,
                &cold.report,
                killed_by,
                killer,
                reason,
                source,
                calls,
                executed,
            ),
            false,
        )
    }

    /// Each executed test of a live run, by candidate, with the outcome and report a record of it
    /// holds ([`Search::live_records`]; the label of an outcome that is not cacheable, with no
    /// cause).
    fn collect_live(
        &self,
        run: &MutantRun,
        causes: &BTreeMap<String, String>,
        opens: &BTreeMap<String, bool>,
        live: &mut BTreeMap<usize, Live>,
    ) {
        for test in &run.plan.tests {
            if test.run == TestRun::SkippedAfterKill {
                continue;
            }
            let Some(c) = self.position(&test.test_id) else {
                continue;
            };
            let notes = run
                .evidence
                .iter()
                .find(|evidence| evidence.test_id == test.test_id)
                .map(|evidence| &evidence.notes);
            let outcome = cacheable(&test.run, notes);
            let unknown = outcome.is_some_and(|(outcome, _)| outcome == CachedOutcome::Unknown);
            let report = OutcomeRecord::report_of(
                causes.get(&test.test_id).filter(|_| unknown),
                unknown && opens.get(&test.test_id) == Some(&true),
                notes.map_or(0, |notes| count(notes.smt_unknowns)),
                notes.map_or(0, |notes| count(notes.decider_smt_unknowns)),
            );
            live.insert(
                c,
                Live::Ran(
                    outcome.map_or_else(
                        || run_label(&test.run).to_owned(),
                        |(outcome, _)| outcome.as_str().to_owned(),
                    ),
                    mutant_run_sha256(run, &test.test_id),
                    report,
                ),
            );
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
    run_digest(&CampaignReport::baseline_row(evidence)).map(|digest| digest.to_string())
}

/// The kill evidence of each test of a live call some slot of which distinguished (CF-16,
/// [`crate::evidence`]): the first differing cell path of its two sides' ends and both values,
/// computed from the call's own evidence, by test id. A test whose sides hold no whole-term value
/// to compare has none.
fn kill_differences<'a>(
    mutant: &'a MutantRun,
    baseline: &'a [TestEvidence],
    reader: &EndReader,
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
    reader: &EndReader,
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
            let cause = entry_cause(live, reader, slots, budget, test);
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
            // undecided solver answers (D-7 (a1)), k-rust's and kink's, when there are any.
            if let Some(notes) = notes {
                if !notes.contradicted_claims.is_empty() {
                    entry["specification_diagnostics"] =
                        specification_diagnostics_value(&notes.contradicted_claims);
                }
                undecided_answers(&mut entry, notes);
                // CF-03: the readings that count against the mutant's run, the step that
                // excluded it (which the cause names, [`entry_cause`]).
                if !notes.short_circuit_readings.is_empty() {
                    entry["short_circuit_readings"] =
                        crate::exclusion::readings_value(&notes.short_circuit_readings);
                }
            }
            Some(entry)
        })
        .collect()
}

/// The `cause` of a live call's executed entry for `test` ([`executed_cause`]): from the runner's
/// evidence for the mutant's run and, when this call recorded the run, its leaf census; for a run
/// excluded by a short-circuit reading, followed by the readings (CF-03).
fn entry_cause(
    live: &LiveCall,
    reader: &EndReader,
    slots: [&str; 2],
    budget: Budget,
    test: &kink_campaign::TestPlan,
) -> Option<String> {
    let mutant = &live.mutant;
    let found = mutant
        .evidence
        .iter()
        .find(|evidence| evidence.test_id == test.test_id);
    let run = live
        .recording
        .mutant_run(mutant.plan.mutant_id, &test.test_id);
    let cause = executed_cause(
        &slots,
        &test.run,
        found.map(|evidence| &evidence.run),
        found.map_or(&[][..], |evidence| evidence.notes.across.as_slice()),
        budget,
        run.map(|run| MutantCensus {
            census: &run.census,
            edited: &live.edited,
            reader,
        }),
    )?;
    Some(match (found, &test.run) {
        (
            Some(evidence),
            TestRun::Failed(kink_campaign::ExecutionFailureKind::ShortCircuitReading),
        ) if !evidence.notes.short_circuit_readings.is_empty() => format!(
            "{cause}; the mutant's run: {}",
            crate::exclusion::readings_text(&evidence.notes.short_circuit_readings)
        ),
        _ => cause,
    })
}

/// The cause of every executed entry of a live call that has one ([`entry_cause`]), by program:
/// what an `unknown` outcome record of the call keeps (CF-33d).
fn entry_causes(
    live: &LiveCall,
    reader: &EndReader,
    slots: [&str; 2],
    budget: Budget,
) -> BTreeMap<String, String> {
    live.mutant
        .plan
        .tests
        .iter()
        .filter_map(|test| {
            Some((
                test.test_id.clone(),
                entry_cause(live, reader, slots, budget, test)?,
            ))
        })
        .collect()
}

/// A count of undecided answers as a record holds it.
fn count(answers: usize) -> u64 {
    u64::try_from(answers).unwrap_or(u64::MAX)
}

/// Writes on an executed entry of a live mutant run the undecided solver answers of the run that
/// `notes` describes, each count when it is not zero: k-rust's in the run (`smt_unknowns`) and
/// kink's own about the run (`decider_smt_unknowns`, its leaf feasibility and observation
/// decider). Reported, never an exclusion (decision D-7 (a1)).
fn undecided_answers(entry: &mut Value, notes: &kink_campaign::RunNotes) {
    if notes.smt_unknowns > 0 {
        entry["smt_unknowns"] = json!(notes.smt_unknowns);
    }
    if notes.decider_smt_unknowns > 0 {
        entry["decider_smt_unknowns"] = json!(notes.decider_smt_unknowns);
    }
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
/// infrastructure error and no `--verify` mismatch; the exit status joins it with the status the
/// document gives (`crate::cli::run_status`). Survivors, timeouts and invalid mutations are
/// results, not errors.
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
/// record or memo record is written for it; and the document is annotated
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
    // The killer record is an input: read after the manifest and the list decode, before
    // admission; one that does not decode refuses the run, as a list that does not decode does.
    let lock = match options.lock.as_deref().map(Lock::read).transpose() {
        Ok(lock) => lock,
        Err(detail) => {
            let path = options.lock.as_deref().unwrap_or_else(|| Path::new(""));
            return (
                annotated(lock_refused(path, &detail, options.schedule)),
                false,
            );
        }
    };
    let selected_count = list
        .mutations
        .iter()
        .filter(|mutation| options.only.is_empty() || options.only.contains(&mutation.id))
        .count();
    if let Some(progress) = front.progress {
        progress(&format!(
            "run: {} on {}, after the baseline results",
            plural(selected_count, "mutation"),
            plural(manifest.programs.len(), "program"),
        ));
    }
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
                stop: manifest.stop.as_ref().map(|_| manifest),
                lock: lock
                    .as_ref()
                    .map_or(Value::Null, |lock| lock.not_written("refused")),
                ..Accounting::NONE
            },
        ));
        let _ = store.write_json(&report_path, &document);
        (document, false)
    };
    let verify = mode == RunMode::Verify;
    // Re-pin L1-4: the memos of the warm path (`memo`), under the conditions tier 1 has
    // (answers that are functions of the key, a known build) and unless `--no-memo`. `--verify`
    // reads none of them for a decision and writes none: it compares each stored record with the
    // live value.
    let memo_build = match (
        options.memo,
        tier1_refusal(SolverProfile::BUILD, manifest.budget.backend_options()),
        kink_campaign::kink_build(),
    ) {
        (MemoUse::On, None, Ok(build)) => Some(build),
        _ => None,
    };
    let mut census_mismatch = None;
    let announce = |line: &str| {
        if let Some(progress) = front.progress {
            progress(line);
        }
    };
    announce("run: admitting the specification (its load, compile and checks)");
    let (mut record, admitted) = admit_spec_with(manifest, &mut |loaded, side| {
        let Some(build) = memo_build else {
            return declaration_census(side);
        };
        let spec = spec_digest(manifest, &loaded.files);
        let (key, path) = (
            memo::census_key(spec, build, manifest.budget),
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
    announce("run: preparing the baseline runner");
    let runner = match BaselineRunner::new(&spec, manifest) {
        Ok(runner) => runner,
        Err(e) => {
            record.refusal = Some(runner_refusal(e));
            return refused(&record, &census_mismatch);
        }
    };
    // A stored result is never a timeout, so no cached row needs a re-run here: a
    // program whose baseline timed out was run live by this command's results update.
    let update = update_results(
        &spec,
        manifest,
        &mut inputs,
        &runner,
        &cache,
        verify,
        front.progress,
    );
    // Once per command: the definition exclusion every document this run writes names.
    let exclusion = runner.definition_exclusion();
    let mut ok = update.ok();
    // The front end's evidence identity is asked for only where tier 1 could be on: it may cost
    // a pass over the front end's definition.
    let tier1 = match tier1_refusal(SolverProfile::BUILD, manifest.budget.backend_options()) {
        Some(reason) => Err(reason.to_owned()),
        None => kink_campaign::kink_build()
            .map_err(|e| {
                format!(
                    "tier 1 is disabled: kink's build identity is unknown ({e}); every mutation \
                     runs live"
                )
            })
            .and_then(|build| {
                let evidence = manifest.end_renderer.evidence().map_err(|e| {
                    format!(
                        "tier 1 is disabled: the front end cannot name what its kill evidence \
                         depends on ({e}); every mutation runs live"
                    )
                })?;
                Ok(OutcomeStore::new(
                    &cache,
                    outcome_context(
                        build,
                        update.execution,
                        manifest.budget,
                        &spec.result,
                        manifest.stop_value().as_ref(),
                        evidence.as_ref(),
                    ),
                ))
            }),
    };
    let (tier1, tier1_reason) = match tier1 {
        Ok(store) => (Some(store), None),
        Err(reason) => (None, Some(reason)),
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
        recorded: lock.as_ref().map(Lock::killers).unwrap_or_default(),
        store: Store::new(&cache),
        stats: Stats::default(),
        mismatches: Vec::new(),
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
    // (flow F-13, informational only); `--only` limits the search, not this list. What a mutation
    // targets is kink-flow's resolution alone: a mutation a front end refused gets the row of its
    // refusal and is neither memoised nor run, but it still targets the rules its edits resolve
    // to, since a rule with a refused mutation has one aimed at it, which the refusal row asks
    // the user to repair. So the list is the same for a full run and under `--only`, whichever
    // mutations a front end judged.
    //
    // Re-pin L1-4: a mutation whose resolution memo record holds its facts under exactly the
    // current key, and that tier 1 decides with no call, is not resolved: its row is built from
    // the facts (`Search::search_memo`). Every other mutation is resolved live, as before, and
    // its facts are written. The memo is read only while every source file still has the
    // SHA-256 the admission recorded (`memo::sources_unchanged`).
    let consult = memo_build.filter(|_| memo::sources_unchanged(&manifest.directory, &spec.loaded));
    if let Some(progress) = front.progress {
        progress(&format!(
            "run: resolving the list's {}",
            plural(list.mutations.len(), "mutation")
        ));
    }
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
                    memo::resolution_key(update.spec_digest, build, manifest.budget, mutation),
                    memo::resolution_path(&cache, update.spec_digest, mutation),
                )
            });
            let stored = memo
                .as_ref()
                .and_then(|(key, path)| memo::read_facts(path, key));
            if !verify
                && let Some(facts) = stored
                    .as_ref()
                    .filter(|facts| search.decided(mutation, facts))
            {
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
    let refused_targets = list
        .mutations
        .iter()
        .filter(|mutation| front.refused.contains_key(&mutation.id))
        .filter_map(|mutation| resolve(manifest, &spec.loaded, mutation).ok())
        .flat_map(|resolved| resolved.rules.into_iter().map(|rule| rule.at))
        .collect::<Vec<_>>();
    let untargeted = Value::Array(untargeted_rules(
        &rule_texts(manifest, &spec.loaded),
        &resolutions
            .iter()
            .flat_map(|resolution| resolution.rules().iter().map(|rule| rule.at.clone()))
            .chain(refused_targets)
            .collect(),
    ));
    let mut rows = Vec::new();
    let mut stopped = None;
    let stop_coverage = crate::check::rows_coverage(&update.rows);
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
                .flat_map(|(_, mutation, resolution)| match resolution {
                    Resolution::Live(resolution) => search.live_compiles(mutation, resolution),
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
        search.record_fields(&mut row, mutation);
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
        if let Some(progress) = front.progress {
            progress(&format!(
                "run: mutation {} of {selected_count}, `{}`: {}",
                position + 1,
                mutation.id,
                row["status"].as_str().unwrap_or("no status"),
            ));
        }
        if corpus_error {
            stopped = Some(json!({"mutation": mutation.id, "reason": row["reason"]}));
            ok = false;
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
                schedule: json!(schedule_name(options.schedule)),
                untargeted_rules: untargeted.clone(),
                data: spec.data.value(),
                exclusion: exclusion.clone(),
                result: spec.result.value(),
                execution: update.execution.value(),
                stop: manifest.stop.as_ref().map(|_| manifest),
                // Nothing is written to the lock before the run ends.
                lock: lock.as_ref().map_or(Value::Null, Lock::pending),
                coverage: Some(&stop_coverage),
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
    let was_stopped = stopped.is_some();
    let mut document = document(
        &record,
        Some(update.spec_digest),
        &program_rows,
        rows,
        stopped,
        Accounting {
            outcome_cache: outcome_cache(&search),
            mismatches: &search.mismatches,
            baseline_runs: runner.baseline_runs(),
            schedule: json!(schedule_name(options.schedule)),
            untargeted_rules: untargeted,
            data: spec.data.value(),
            exclusion,
            result: spec.result.value(),
            execution: update.execution.value(),
            stop: manifest.stop.as_ref().map(|_| manifest),
            lock: Value::Null,
            coverage: Some(&stop_coverage),
        },
    );
    // The lock, compared and written once the run's rows are final (README, "The killer
    // record"): its text is the rendering of this document, which neither the `lock` member nor
    // a front end's annotation is part of.
    if let Some(lock) = &lock {
        let (value, written) = lock.settle(
            &store,
            &document,
            Settle {
                locked: options.locked,
                verify,
                only: &options.only,
                stopped: was_stopped,
            },
        );
        document["lock"] = value;
        ok &= written;
    }
    let document = annotated(document);
    // The stored report is the document the command prints: write it unless the last write
    // already stored exactly this document (no mutation was selected, or a write failed).
    if written.as_ref() != Some(&document) && store.write_json(&report_path, &document).is_err() {
        ok = false;
    }
    (document, ok)
}

/// `count` and `noun`, plural when `count` is not 1 (`1 mutation`, `3 programs`).
fn plural(count: usize, noun: &str) -> String {
    format!("{count} {noun}{}", if count == 1 { "" } else { "s" })
}

/// What tier 1 decides for a mutation with no call ([`tier1_decision`]).
#[derive(Clone, Debug, Eq, PartialEq)]
enum Tier1 {
    /// No program is in O: the row is the corpus error `no-comparable-program`.
    Empty,
    /// The records decide: the killer (a candidate) when the status is killed, and the records
    /// the row reads (candidates, in the order the row lists them).
    Decided {
        killer: Option<usize>,
        read: Vec<usize>,
    },
    /// The mutant runs live. `records` is false for the no-witness fallback: the canonical killer
    /// needs C and no compiled edit is stored, so the row runs as if no record were valid.
    Call { records: bool },
}

impl Tier1 {
    const fn decides(&self) -> bool {
        !matches!(self, Self::Call { .. })
    }
}

/// What tier 1 decides, with no call, for a mutation whose comparable programs are `order` (O, in
/// corpus order), whose valid tier-1 records are `records` (of programs of O), whose search order
/// C is `search` when the outcome file keeps the compiled edit, and whose lock names the program
/// `recorded` of O (README, "The killer record").
///
/// Under [`ScheduleMode::FirstKill`]: an empty O decides; a recorded killer with a valid `killed`
/// record decides, as the killer; a recorded killer with no valid record does not (it must run);
/// otherwise (no recorded killer in O, or one whose record is not a kill) the canonical killer,
/// the first killing program in C, must be decided by the records alone: with no cached kill when
/// every program of O has a record (the fold), and with cached kills when C is known and every
/// program before the first cached kill in C has a record (that kill is the killer; the row reads
/// that prefix and the kill), or when every program has a record and exactly one is a kill (C
/// does not matter). Every program cached with several kills and no stored C is the no-witness
/// fallback.
///
/// Under [`ScheduleMode::Full`] the records decide only when every program of O has one: a
/// `killed` record does not decide a full row, which needs every cell. Its killer is the recorded
/// one when it is among the kills, else the only kill, else the first kill in C; several kills
/// with no stored C and no recorded killer among them is the no-witness fallback.
fn tier1_decision(
    order: &[usize],
    records: &[(usize, OutcomeRecord)],
    search: Option<&[usize]>,
    recorded: Option<usize>,
    schedule: ScheduleMode,
) -> Tier1 {
    if order.is_empty() {
        return Tier1::Empty;
    }
    let has = |program: usize| records.iter().any(|(c, _)| *c == program);
    let killed = |program: usize| {
        records
            .iter()
            .any(|(c, record)| *c == program && record.outcome == CachedOutcome::Killed)
    };
    let every = order.iter().all(|&program| has(program));
    let kills = order
        .iter()
        .copied()
        .filter(|&program| killed(program))
        .collect::<Vec<_>>();
    let cached = || {
        order
            .iter()
            .copied()
            .filter(|&program| has(program))
            .collect::<Vec<_>>()
    };
    let recorded = recorded.filter(|k| order.contains(k));
    if schedule == ScheduleMode::Full {
        if !every {
            return Tier1::Call { records: true };
        }
        let killer = if kills.is_empty() {
            None
        } else if let Some(k) = recorded.filter(|k| kills.contains(k)) {
            Some(k)
        } else if let [only] = kills[..] {
            Some(only)
        } else if let Some(search) = search {
            search.iter().copied().find(|c| kills.contains(c))
        } else {
            return Tier1::Call { records: false };
        };
        return Tier1::Decided {
            killer,
            read: cached(),
        };
    }
    if let Some(k) = recorded {
        if killed(k) {
            return Tier1::Decided {
                killer: Some(k),
                read: vec![k],
            };
        }
        if !has(k) {
            return Tier1::Call { records: true };
        }
    }
    if kills.is_empty() {
        return if every {
            Tier1::Decided {
                killer: None,
                read: cached(),
            }
        } else {
            Tier1::Call { records: true }
        };
    }
    // The recorded killer's record, not a kill, is part of what decides: the row reads it too.
    let with_recorded = |mut read: Vec<usize>| {
        if let Some(k) = recorded.filter(|k| !read.contains(k)) {
            read.push(k);
        }
        read
    };
    match search {
        Some(search) => {
            let first = search
                .iter()
                .position(|c| kills.contains(c))
                .expect("C orders every program of O");
            if search[..first].iter().all(|&program| has(program)) {
                Tier1::Decided {
                    killer: Some(search[first]),
                    read: with_recorded(search[..=first].to_vec()),
                }
            } else {
                Tier1::Call { records: true }
            }
        }
        None if every && kills.len() == 1 => Tier1::Decided {
            killer: Some(kills[0]),
            read: cached(),
        },
        None if every => Tier1::Call { records: false },
        None => Tier1::Call { records: true },
    }
}

/// What `run` knows of a mutation's resolution (re-pin L1-4).
enum Resolution {
    /// Resolved in this command.
    Live(Result<ResolvedMutation, InvalidMutation>),
    /// Not resolved: the resolution memo's facts of a mutation tier 1 decides with no call.
    Memo(Facts),
}

impl Resolution {
    /// The rules the mutation edits; none when it does not resolve, or when a front end refused it
    /// (whose targets the run's `untargeted_rules` takes from a resolution of its own).
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

/// The status and reason of a mutation whose row's `weakening` ([`weakening_value`]) is not null:
/// `equivalent` with [`VALID_CONDITION_REASON`] when every edited sentence keeps its axiom (kind
/// `valid-condition`), since the mutant then has exactly the specification's models;
/// [`UNKILLABLE`] with [`WEAKENING_REASON`] otherwise.
pub(crate) fn weakening_status(weakening: &Value) -> (&'static str, &'static str) {
    let kept = weakening.as_array().is_some_and(|sentences| {
        !sentences.is_empty()
            && sentences
                .iter()
                .all(|sentence| sentence["kind"] == WEAKENING_VALID_CONDITION)
    });
    if kept {
        ("equivalent", VALID_CONDITION_REASON)
    } else {
        (UNKILLABLE, WEAKENING_REASON)
    }
}

/// The `kind` of a sentence a weakening patch replaces by itself with conditions that hold
/// everywhere (kink-patch `WeakeningKind::ValidCondition`).
const WEAKENING_VALID_CONDITION: &str = "valid-condition";

/// The row's `weakening`: null, or for each sentence a weakening patch edits `{module, index,
/// label, head, kind}`, `label` the baseline sentence's (null without one), `head` the K label of
/// the function (null for a lemma), `kind` `deleted`, `narrowed` or `valid-condition` (the same
/// axiom: its `requires` adds only conjuncts that hold under every valuation of their variables;
/// kink27 R5-WEAKENING).
pub(crate) fn weakening_value(
    baseline: &kink_patch::Baseline,
    weakening: Option<&Weakening>,
) -> Value {
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
                            WeakeningKind::ValidCondition => WEAKENING_VALID_CONDITION,
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

/// The row of a verdict: the report's status, the killer (the search's choice: the recorded
/// killer while it kills, else the first killing program in C), the killer's source, the deciding
/// call's mutant-scope failure as the reason, and under `Full` `killed_by`
/// ([`Search::killed_by`]).
#[allow(clippy::too_many_arguments)]
fn verdict_row(
    mut row: Map<String, Value>,
    report: &MutantReport,
    killed_by: Option<Vec<String>>,
    killer: Option<String>,
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
    let killer = killer.filter(|_| report.status == MutantStatus::Killed);
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

/// Each program a live call left undecided (some slot neither `agree` nor `distinguish`, or a
/// failed run), by id, with whether it is undecided because the ends of the mutant's run hold
/// open applications of edited functions (`report::open_application_cause`); a failed run is
/// undecided for another reason. What an `unknown` record of the call keeps
/// (`OutcomeRecord::open_application`), and what the row's reason is folded from
/// ([`open_reason`]).
fn entry_opens(live: &LiveCall) -> BTreeMap<String, bool> {
    let mutant = &live.mutant;
    mutant
        .plan
        .tests
        .iter()
        .filter_map(|test| {
            let open = match &test.run {
                TestRun::SkippedAfterKill => return None,
                TestRun::Failed(_) => false,
                TestRun::Compared(outcomes) => {
                    if outcomes.contains(&OracleOutcome::Distinguish)
                        || outcomes
                            .iter()
                            .all(|outcome| *outcome == OracleOutcome::Agree)
                    {
                        return None;
                    }
                    open_application_cause(
                        &test.run,
                        mutant
                            .evidence
                            .iter()
                            .find(|evidence| evidence.test_id == test.test_id),
                        live.recording
                            .mutant_run(mutant.plan.mutant_id, &test.test_id)
                            .map(|run| &run.census),
                        &live.edited,
                    )
                }
            };
            Some((test.test_id.clone(), open))
        })
        .collect()
}

/// The undecided programs of cached records, by id, as [`entry_opens`] gives them for a live
/// call: each `unknown` record's `open_application`.
fn cached_opens<'c>(
    records: &[(usize, OutcomeRecord)],
    id: impl Fn(usize) -> &'c str,
) -> BTreeMap<String, bool> {
    records
        .iter()
        .filter(|(_, record)| record.outcome == CachedOutcome::Unknown)
        .map(|(c, record)| (id(*c).to_owned(), record.open_application))
        .collect()
}

/// The reason [`OPEN_APPLICATION_REASON`] of an `unknown` row every undecided program of which,
/// live or cached, is undecided because the ends of the mutant's run hold open applications of
/// edited functions (`opens`, from [`entry_opens`] and [`cached_opens`]); none when no program is
/// undecided or one is undecided for another reason.
fn open_reason(report: &MutantReport, opens: &BTreeMap<String, bool>) -> Option<String> {
    (report.status == MutantStatus::Unknown
        && !opens.is_empty()
        && opens.values().all(|open| *open))
    .then(|| OPEN_APPLICATION_REASON.to_owned())
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
    row.entry("witnesses_global").or_insert(Value::Null);
    row.entry("rules").or_insert(Value::Null);
    row.entry("identity").or_insert(Value::Null);
    row.entry("unusable_killer").or_insert(Value::Null);
    row.entry("weakening").or_insert(Value::Null);
    row.entry("killed_by").or_insert(Value::Null);
    // An `equivalent` mutant denotes the specification's theory (every edited equation keeps its
    // axiom, `valid-condition`, or it compiles to the baseline's definition,
    // `equivalent-compilation`), so every claim of the specification holds of it: it withdraws
    // none, whatever the edit's scope would withdraw from another edit.
    if row.get("status").and_then(Value::as_str) == Some("equivalent")
        && row.contains_key("removed_claims")
    {
        row.insert(
            "removed_claims".into(),
            json!({"removed": [], "unsupported": []}),
        );
    }
    let action = action(
        row["status"].as_str().unwrap_or_default(),
        row["reason"].as_str(),
    );
    row.insert("action".into(), json!(action));
    row.insert("killer".into(), json!(killer));
    row.insert("killer_source".into(), json!(source));
    row.insert(
        "killer_from_cache".into(),
        json!(source == Some(SOURCE_OUTCOME_CACHE)),
    );
    row.insert("executed".into(), json!(executed));
    row.insert("calls".into(), json!(calls));
    row.insert("call_wall_ms".into(), json!(call_wall_ms));
    Value::Object(row)
}

/// The `reading` of a stored [`EditWitness`]: the edit as a ground program witnesses it.
const GROUND_READING: &str = "ground-programs";

/// A mutant's compiled edit as a ground program witnesses it (kink-campaign
/// [`CompiledEdit::for_ground_tests`]: [`CompiledEdit::between`] on the side the programs run
/// on, the rule kink-campaign's coverage selection reads, or on the mutant as written when kink
/// withdrew only definedness claims from it, whose withdrawal adds no witness through a ground
/// program's coverage) read through the baseline's
/// [`RuleAuthors`], since kink-flow's result records keep coverage by baseline sentence: the
/// baseline sentences behind the removed compiled ids that a run witnesses by k-rust `matched`
/// (a rewrite rule id whose edit is not confined to its right-hand side or `ensures`, an equation
/// id whose edit changed its condition; [`Witness::Matched`]) and those it witnesses by `applied`
/// (an id whose edit is confined to its right-hand side or `ensures`). The outcome file keeps it
/// (`witness`, [`crate::outcomes`]), so that a row
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

    /// `{reading, global, matched: [{module, index}], applied: [{module, index}]}`, each list
    /// sorted; `reading` is [`GROUND_READING`].
    fn value(&self) -> Value {
        let sentences = |set: &BTreeSet<(String, u64)>| {
            set.iter()
                .map(|(module, index)| json!({"module": module, "index": index}))
                .collect::<Vec<_>>()
        };
        json!({
            "reading": GROUND_READING,
            "global": self.global,
            "matched": sentences(&self.matched),
            "applied": sentences(&self.applied),
        })
    }

    /// The inverse of [`Self::value`]; `None` for null or a value of another shape.
    ///
    /// A value without `reading` was written before the edit was read as a ground program
    /// witnesses it (kink-campaign [`CompiledEdit::for_ground_tests`]), from the claim-free side
    /// alone. That is the ground reading exactly when the mutant as written is not read instead:
    /// when kink withdrew no claim from the mutant (the two sides are one definition) or a claim
    /// other than a definedness claim (kink-campaign [`ground_reading_is_as_written`]). It is
    /// read only then, which `removed_claims`, the row's (`report::claims_value`, a function of
    /// the specification and the mutation, as the stored edit is), tells. Otherwise the
    /// claim-free side's edit can be wider than the author's: a withdrawn `total` or
    /// `functional` changes a declaration, which makes it `global`, and a withdrawn
    /// `preserves-definedness`, a rule attribute, makes a rule the author did not edit, or one
    /// whose right-hand side alone the author edited, witnessed by `matched`. A row whose
    /// `removed_claims` does not decode reads no value without `reading`.
    fn from_value(value: &Value, removed_claims: &Value) -> Option<Self> {
        match value.get("reading") {
            None => {
                let keys = removed_claims["removed"]
                    .as_array()?
                    .iter()
                    .map(|claim| claim["key"].as_str())
                    .collect::<Option<Vec<_>>>()?;
                if !keys.is_empty() && ground_reading_is_as_written(keys) {
                    return None;
                }
            }
            Some(reading) if reading == GROUND_READING => {}
            Some(_) => return None,
        }
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
/// witness a change of what the rule does once it applies, but can witness a change of its
/// `requires` or left-hand side, under which that guard can hold; an attribute edit or a deletion
/// it witnesses only where it left the guard undecided, which `matched` does not tell from a
/// refuted guard (kink-campaign `selection`, module doc). One whose candidate was rolled back
/// can witness any of these, since an edit can make that candidate defined.
fn witnesses(candidate: &Candidate<'_>, witness: &EditWitness) -> bool {
    witness.global
        || !candidate.complete
        || !witness.matched.is_disjoint(&candidate.matches)
        || !witness.applied.is_disjoint(&candidate.applies)
}

/// The run document's accounting of the command: `outcome_cache`, `mismatches`,
/// `baseline_runs`, the `schedule` and `untargeted_rules` (outside every digest and key).
struct Accounting<'m> {
    outcome_cache: Value,
    mismatches: &'m [Value],
    baseline_runs: Value,
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
    /// The manifest, when it declares `[stop]`: the document names the stop (`stop`), and each
    /// survivor that edits a rule the stop stops before says so (`stop_hides_edit`).
    stop: Option<&'m FlowManifest>,
    /// The document's `lock`: null without a lock ([`crate::lock`]).
    lock: Value,
    /// The coverage of the programs' current records (`crate::check::rows_coverage`), from which a
    /// survivor's `stop_hides_edit` is read under a stop condition; `None` where no run judged
    /// the programs.
    coverage: Option<&'m crate::check::CorpusCoverage>,
}

impl Accounting<'_> {
    const NONE: Accounting<'static> = Accounting {
        outcome_cache: Value::Null,
        mismatches: &[],
        baseline_runs: Value::Null,
        schedule: Value::Null,
        untargeted_rules: Value::Null,
        data: Value::Null,
        exclusion: Value::Null,
        result: Value::Null,
        execution: Value::Null,
        stop: None,
        lock: Value::Null,
        coverage: None,
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
    let mut mutations = mutations;
    if let Some(hides) = accounting
        .stop
        .and_then(|manifest| crate::check::StopHides::of(manifest, accounting.coverage))
    {
        for row in &mut mutations {
            hides.annotate_survivor(row);
        }
    }
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
    let mut document = crate::with_z3_build(json!({
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
        "schedule": accounting.schedule,
        "matrix": matrix,
        "untargeted_rules": accounting.untargeted_rules,
        "data": accounting.data,
        "lock": accounting.lock,
    }));
    // Absent without a stop, so a document without one is the document it was before stops.
    if let Some(stop) = accounting.stop.and_then(FlowManifest::stop_value) {
        document["stop"] = stop;
    }
    document
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
    crate::with_z3_build(json!({
        "schema": RUN_SCHEMA,
        "version": RUN_VERSION,
        "schedule": schedule_name(schedule),
        "matrix": null,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "kink_build": run_document_build(),
        "kink": kink_campaign::kink_identity(),
        "mutation_list": {"outcome": "refused", "detail": detail},
    }))
}

/// The run document of a run whose lock at `path` does not decode (README, "The killer record"):
/// it names the schedule and the refused lock (`lock: {path, outcome: "refused", detail}`), and has
/// no specification and no mutation row, since the lock is read before admission.
pub fn lock_refused(path: &Path, detail: &str, schedule: ScheduleMode) -> Value {
    crate::with_z3_build(json!({
        "schema": RUN_SCHEMA,
        "version": RUN_VERSION,
        "schedule": schedule_name(schedule),
        "matrix": null,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "kink_build": run_document_build(),
        "kink": kink_campaign::kink_identity(),
        "lock": crate::lock::refused_value(path, detail),
    }))
}

/// The path of the run document of the cache `cache` (or the manifest's default cache).
pub fn report_path(manifest: &FlowManifest, cache: Option<&Path>) -> PathBuf {
    cache_directory(manifest, cache).join(REPORT_FILE)
}

#[cfg(test)]
mod tests {
    use super::*;
    use kink_patch::{Claim, SentenceOrigin, UNREAD_EQUATION_CLAIM};

    /// An executed entry carries each count of undecided solver answers, k-rust's and kink's,
    /// exactly when it is not zero, whatever the other count is.
    #[test]
    fn an_entry_carries_each_nonzero_count_of_undecided_answers() {
        for (smt, decider) in [(0, 0), (2, 0), (0, 3), (2, 3)] {
            let notes = kink_campaign::RunNotes {
                smt_unknowns: smt,
                decider_smt_unknowns: decider,
                ..kink_campaign::RunNotes::default()
            };
            let mut entry = json!({"program": "p"});
            undecided_answers(&mut entry, &notes);
            for (count, value) in [("smt_unknowns", smt), ("decider_smt_unknowns", decider)] {
                assert_eq!(
                    entry.get(count),
                    (value > 0).then(|| json!(value)).as_ref(),
                    "{count} of ({smt}, {decider})"
                );
            }
        }
    }

    /// A stored witness is read back when it has the ground reading, whatever claims were
    /// withdrawn. One without `reading`, written from the claim-free side alone, is read only
    /// where that side's edit is the ground reading: no claim withdrawn, or one that is not a
    /// definedness claim, `global` or not. Where only definedness claims were withdrawn it is
    /// not read, `global` (a withdrawn `total`) or not (a withdrawn `preserves-definedness`,
    /// whose rule attribute the claim-free side reads as a site-local edit), nor where the row's
    /// `removed_claims` does not decode.
    #[test]
    fn a_stored_witness_without_reading_is_read_only_where_it_is_the_ground_reading() {
        let witness = EditWitness {
            global: false,
            matched: BTreeSet::from([("M".to_owned(), 3)]),
            applied: BTreeSet::from([("M".to_owned(), 4)]),
        };
        let global = EditWitness {
            global: true,
            ..EditWitness::default()
        };
        let claims = |keys: &[&str]| {
            json!({
                "removed": keys.iter().map(|key| json!({"module": "M", "index": 1, "label": null, "key": key, "value": ""})).collect::<Vec<_>>(),
                "unsupported": [],
            })
        };
        let legacy = |witness: &EditWitness| {
            let mut value = witness.value();
            value.as_object_mut().unwrap().remove("reading");
            value
        };
        for removed in [
            claims(&[]),
            claims(&["total"]),
            claims(&["preserves-definedness"]),
            claims(&["simplification"]),
            Value::Null,
        ] {
            for stored in [&witness, &global] {
                assert_eq!(
                    EditWitness::from_value(&stored.value(), &removed).as_ref(),
                    Some(stored),
                    "current reading, removed {removed}"
                );
                let mut other = stored.value();
                other["reading"] = json!("claim-free");
                assert_eq!(EditWitness::from_value(&other, &removed), None, "{removed}");
            }
        }
        for keys in [
            &[][..],
            &["injective"],
            &["simplification"],
            &["total", "smt-lemma"],
        ] {
            for stored in [&witness, &global] {
                assert_eq!(
                    EditWitness::from_value(&legacy(stored), &claims(keys)).as_ref(),
                    Some(stored),
                    "legacy, removed {keys:?}"
                );
            }
        }
        for keys in [
            &["total"][..],
            &["functional"],
            &["preserves-definedness"],
            &["total", "preserves-definedness"],
        ] {
            for stored in [&witness, &global] {
                assert_eq!(
                    EditWitness::from_value(&legacy(stored), &claims(keys)),
                    None,
                    "legacy, removed {keys:?}"
                );
            }
        }
        assert_eq!(
            EditWitness::from_value(&legacy(&witness), &Value::Null),
            None
        );
        assert_eq!(EditWitness::from_value(&Value::Null, &claims(&[])), None);
    }

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

    /// The tier-1 rule that the search ([`Search::search_facts`]), the memo stop and the
    /// compile-ahead guess ([`Search::live_compiles`]) decide by, under each schedule, with and
    /// without a recorded killer and a stored C. No run document can show the guess: a wrong one
    /// costs a compile, never a row, a record or a lock, so the rule they share is pinned here.
    #[test]
    fn tier_one_follows_the_record() {
        let record = |outcome| OutcomeRecord {
            program_id: String::new(),
            baseline_run_sha256: String::new(),
            outcome,
            slots: Vec::new(),
            mutant_run_sha256: String::new(),
            difference: Value::Null,
            cause: None,
            open_application: false,
            smt_unknowns: 0,
            decider_smt_unknowns: 0,
            allowance_bytes: None,
        };
        let killed = |c| (c, record(CachedOutcome::Killed));
        let agree = |c| (c, record(CachedOutcome::Agree));
        let unknown = |c| (c, record(CachedOutcome::Unknown));
        let o = [0, 1, 2];
        // C with the witness 2 first.
        let c = [2, 0, 1];
        let first = |records: &[(usize, OutcomeRecord)], search, recorded| {
            tier1_decision(&o, records, search, recorded, ScheduleMode::FirstKill)
        };
        let full = |records: &[(usize, OutcomeRecord)], search, recorded| {
            tier1_decision(&o, records, search, recorded, ScheduleMode::Full)
        };
        let decided = |killer, read: &[usize]| Tier1::Decided {
            killer,
            read: read.to_vec(),
        };
        let call = Tier1::Call { records: true };
        let fallback = Tier1::Call { records: false };
        // No program in O: nothing can run, under either schedule.
        for schedule in [ScheduleMode::FirstKill, ScheduleMode::Full] {
            assert_eq!(tier1_decision(&[], &[], None, None, schedule), Tier1::Empty);
        }
        // No record, or records for part of O with no kill: the rest of O runs.
        assert_eq!(first(&[], Some(&c), None), call);
        assert_eq!(first(&[agree(0), unknown(2)], Some(&c), None), call);
        assert_eq!(full(&[agree(0), killed(2)], Some(&c), None), call);
        // Every program cached with no kill: the fold, under both schedules.
        let all = [agree(0), unknown(1), agree(2)];
        assert_eq!(first(&all, None, None), decided(None, &[0, 1, 2]));
        assert_eq!(full(&all, None, Some(1)), decided(None, &[0, 1, 2]));
        // The recorded killer's cached kill decides a first-kill row, alone, wherever it is in C.
        assert_eq!(
            first(&[killed(1)], Some(&c), Some(1)),
            decided(Some(1), &[1])
        );
        assert_eq!(first(&[killed(1)], None, Some(1)), decided(Some(1), &[1]));
        // A recorded killer with no valid record runs, whatever else is cached.
        assert_eq!(first(&[killed(2), agree(0)], Some(&c), Some(1)), call);
        // A recorded killer that agreed: the canonical killer, the first cached kill in C once
        // every program before it in C is cached.
        assert_eq!(
            first(&[killed(0), agree(1)], Some(&c), Some(1)),
            call,
            "2 comes before 0 in C and has no record"
        );
        // The recorded killer's agreement is read beside the prefix: it decides that the
        // killer is not the recorded one.
        assert_eq!(
            first(&[agree(2), killed(0), agree(1)], Some(&c), Some(1)),
            decided(Some(0), &[2, 0, 1])
        );
        assert_eq!(first(&[killed(2)], Some(&c), None), decided(Some(2), &[2]));
        // A recorded killer outside O reads as none.
        assert_eq!(
            first(&[killed(2)], Some(&c), Some(7)),
            decided(Some(2), &[2])
        );
        // Kills cached and no stored C: the prefix is unknown, so the row runs; with every
        // program cached, one kill decides (C does not matter), several are the fallback.
        assert_eq!(first(&[killed(2), agree(0)], None, None), call);
        assert_eq!(
            first(&[agree(0), agree(1), killed(2)], None, None),
            decided(Some(2), &[0, 1, 2])
        );
        assert_eq!(
            first(&[killed(0), agree(1), killed(2)], None, None),
            fallback
        );
        assert_eq!(
            first(&[killed(0), agree(1), killed(2)], Some(&c), None),
            decided(Some(2), &[2])
        );
        // Full: a cached kill never decides alone; with every cell cached the killer is the
        // recorded one among the kills, else the only one, else the first in C.
        let kills = [killed(0), agree(1), killed(2)];
        assert_eq!(full(&kills, None, Some(0)), decided(Some(0), &[0, 1, 2]));
        assert_eq!(
            full(&kills, Some(&c), Some(1)),
            decided(Some(2), &[0, 1, 2])
        );
        assert_eq!(full(&kills, None, Some(1)), fallback);
        assert_eq!(
            full(&[killed(0), agree(1), agree(2)], None, None),
            decided(Some(0), &[0, 1, 2])
        );
    }
}
