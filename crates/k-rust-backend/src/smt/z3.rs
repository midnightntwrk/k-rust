//! ```toml algorithm
//! id = "backend.smt.cache"
//! name = "bounded FIFO memoization of SMT query scripts"
//! sites = ["Z3Solver::solve", "SolverResultCache::get", "SolverResultCache::insert", "Z3Solver::solve_uncached", "SolverResultCache", "Z3Solver::solve_model", "Z3Solver::confirm_answer", "Z3Solver::check_prelude"]
//! variable = "e = entries evicted; E = cached entries; L = script length in bytes"
//! counters = ["SmtQueries", "SmtSolverRuns", "SmtRlimitCount"]
//! span = "per call"
//! invariant = "entries and insertion_order agree; eviction stops once the entry and key-byte limits admit the new key"
//!
//! [[cost]]
//! mode = "cache hit"
//! bound = "O(L x log E) for the key comparison, after an O(L) copy of the base script in solve_query"
//!
//! [[cost]]
//! mode = "cache insertion"
//! bound = "O(e) evictions for e oldest entries removed to satisfy both limits"
//!
//! [[cost]]
//! mode = "prelude consistency"
//! bound = "zero checks after a sat query; otherwise at most one prelude check, with configured retries, before the first unsat answer or rejected script"
//! ```
//!
//! In-process Z3 behind a bounded FIFO result cache: `Counter::SmtQueries` in,
//! `Counter::SmtSolverRuns` out (the lazy prelude check and the model path count solver
//! runs without a query), O(L x log E) per hit for a script of L bytes among E cached entries,
//! eviction pops the oldest entry until the entry and key-byte limits admit the new key. The
//! attempts of an uncached query run on a Z3 context of their own (`on_own_context`), so its
//! answer is a function of its script and options only. Constructing a `Z3Solver` creates no Z3
//! context; a satisfiable query establishes prelude consistency, while the first unsatisfiable
//! answer, and the first script Z3 rejects, requires one explicit prelude check.
//! A validity check (`decide_validity`) issues a positive subquery, then a negative or a base
//! subquery, and a third on the unknown path; each subquery goes through the cache.
//!
//! ```toml algorithm
//! id = "backend.smt.check"
//! name = "Z3 satisfiability check"
//! sites = ["measured_check", "Z3Solver::solve_uncached", "Z3Solver::solve_model"]
//! variable = "R = Z3 resource-limit units consumed by one check"
//! counters = ["SmtSolverRuns", "SmtRlimitCount"]
//! span = "per call"
//! invariant = "the rlimit delta is read around each check from the cumulative statistics of its context"
//!
//! [[cost]]
//! mode = "solver check"
//! bound = "O(R) solver work as reported by Z3"
//! ```

#![deny(clippy::wildcard_enum_match_arm)]

use std::num::NonZeroU32;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    ffi::CStr,
    str::FromStr,
    sync::{Arc, Mutex},
};

#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};

use k_rust_kore::measure::{self, Algorithm, Counter};
use k_rust_kore::names::BuiltinSort;
use num_bigint::BigInt;
use z3::{
    Model, Params, SatResult, Solver,
    ast::{Bool, Int},
};

use super::{
    APPROXIMATE_MODEL_REASON, ModelResult, Satisfiability, SmtError, SmtPrelude, SmtSolver,
    TranslatedQuery, Validity,
};
use crate::{
    model::ModelQuery,
    rule::Predicate,
    stop::{self, PreludeFailure, PreludeSignal, Stop, Stoppable},
    substitution::Substitution,
    term::{DomainKind, Sort, Term, Variable},
};

#[cfg(feature = "measure")]
fn rlimit_count(solver: &Solver) -> u64 {
    match solver.get_statistics().value("rlimit count") {
        Some(z3::StatisticsValue::UInt(value)) => u64::from(value),
        _ => 0,
    }
}

fn measured_check(solver: &Solver) -> SatResult {
    #[cfg(feature = "measure")]
    let before = rlimit_count(solver);
    let result = {
        let _span = measure::algorithm_span(Algorithm::BackendSmtCheck);
        solver.check()
    };
    #[cfg(feature = "measure")]
    measure::add(
        Counter::SmtRlimitCount,
        rlimit_count(solver).saturating_sub(before),
    );
    result
}

/// Why Z3 did not load a script: its own message, or the reason the script never reached it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct RejectedScript {
    message: String,
}

/// Load `script` into `solver`, or say why Z3 rejected it. Every script reaches Z3 through here.
///
/// A check answers about the assertions the solver holds. Z3 adds a script's assertions only
/// once the whole script parses and sort-checks, so after a parse error, a sort error, or an
/// undeclared or redeclared symbol the solver holds none of them, and a check would answer `sat`
/// about the empty formula instead of the one the script states. A rejected script must
/// therefore never be checked. The `z3` crate's loader returns nothing and its contexts install
/// no error handler, so the rejection is recorded only as the error code of the solver's
/// context, which every later API call resets: it is read here, before any other call.
fn load(solver: &Solver, script: &str) -> Result<(), RejectedScript> {
    // Z3 reads the script as a C string, which a NUL byte would end early (and the `z3` crate
    // panics on one), so a script with one cannot be read as written.
    if script.as_bytes().contains(&0) {
        return Err(RejectedScript {
            message: "the script contains a NUL byte".into(),
        });
    }
    solver.from_string(script);
    let context = solver.get_context().get_z3_context();
    // SAFETY: `context` is the live context `solver` holds, and no API call ran on it since the
    // load, so its error code is the load's.
    let code = unsafe { z3_sys::Z3_get_error_code(context) };
    if code == z3_sys::ErrorCode::Ok {
        return Ok(());
    }
    // SAFETY: as above; the message is a NUL-terminated string the context owns until its next
    // API call, and it is copied before any.
    let message = unsafe { z3_sys::Z3_get_error_msg(context, code) };
    let message = if message.is_null() {
        format!("{code:?}")
    } else {
        // SAFETY: a non-null message is a NUL-terminated string, valid until the next API call.
        unsafe { CStr::from_ptr(message) }
            .to_string_lossy()
            .trim()
            .to_owned()
    };
    Err(RejectedScript { message })
}

/// Run one query's attempts on a Z3 context of their own, created for the query and deleted
/// after it.
///
/// Z3's search is a deterministic function of the assertions it checks, its parameters and the
/// state of the context it runs in: the terms the context holds and what earlier checks on it
/// left behind change the path the search takes. On a path that decides a query a check answers
/// at once; on another it runs until its limit and answers unknown, so one query can be decided
/// on one context and not on another (one nonlinear check on a context is enough to turn some
/// `sat` answers there into `unknown`). The `z3` crate's default context is per thread and
/// shared with every other Z3 user on the thread (checked sort inference among them), so an
/// answer on it would depend on unrelated earlier work and would in turn change theirs.
///
/// A query's attempts share the context: each retry starts from the state the attempts before it
/// left, which sets it on another path than theirs. A larger budget alone does not end a path
/// that never decides the query (with Z3 4.16.0, the backend's `H *Int I ==Int 2021027` factoring
/// check, from a fresh context, is undecided at 128,000,000 resource units, and decided by its
/// third attempt at 1,000,000 after two at 250,000 and 500,000). The answer is then a function of the script,
/// the attempts' parameters and the Z3 library only, as it is for the first query a process
/// asks on a thread.
///
/// Every Z3 object the query makes belongs to that context (the `z3` crate creates objects on
/// the thread's current context, which `with_z3_config` replaces for the call), and none can
/// leave it: Z3 objects are neither `Send` nor `Sync`, which the bound on `R` requires. The crate
/// puts the thread's previous context back only when the call returns, so a panic is caught
/// inside the call and raised again after it: the thread's later Z3 users (checked sort
/// inference after a caught panic, say) find their own context again.
///
/// Creating a context costs about 0.4 ms of mostly serial work in Z3: concurrent queries on many
/// threads share that cost, so a process running many uncached queries at once pays more per
/// query, and holds more memory at its peak, than one sharing a context per thread did
/// (docs/compatibility.md, "Clock-free solver mode").
fn on_own_context<R: Send + Sync>(query: impl FnOnce() -> R + Send + Sync) -> R {
    let outcome = z3::with_z3_config(&z3::Config::new(), || {
        // The query's state is dropped by the unwind and nothing observes it afterwards: the
        // panic is raised again as soon as the thread's context is back.
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(query))
            .map_err(|payload| Unwound(Mutex::new(payload)))
    });
    outcome.unwrap_or_else(|Unwound(payload)| {
        std::panic::resume_unwind(
            payload
                .into_inner()
                .unwrap_or_else(|poisoned| poisoned.into_inner()),
        )
    })
}

/// A panic caught inside [`on_own_context`], carried out of the call that installs the query's
/// context. The payload is `Send` but not `Sync`, and the call requires both of its result; a
/// mutex provides `Sync`, though the payload is only ever moved.
struct Unwound(Mutex<Box<dyn std::any::Any + Send>>);

/// How long each Z3 check of a query may run, and how often an unknown answer is retried.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Z3Options {
    /// The first attempt's wall-clock timeout, doubled on each retry; unused under
    /// [`Self::resource_limit`].
    pub timeout_ms: u32,
    /// The retries of an unknown answer.
    pub retry_limit: u32,
    /// The clock-free mode: when set, each attempt is bounded by this many Z3 resource units
    /// (`rlimit`), doubled on each retry, and by no wall-clock timeout. Z3 counts these units in
    /// its own search, and every query runs on a Z3 context of its own, so its answer (sat, unsat
    /// or unknown) does not depend on the machine's speed or load nor on any other Z3 work in
    /// the process: it is a function of the query, these options and the Z3 version. `None`
    /// (the default) bounds attempts by [`Self::timeout_ms`], with a resource limit only as a
    /// backstop ([`RESOURCE_UNITS_PER_MS`]).
    pub resource_limit: Option<NonZeroU32>,
}

impl Default for Z3Options {
    fn default() -> Self {
        Self {
            timeout_ms: 125,
            retry_limit: 3,
            resource_limit: None,
        }
    }
}

/// The version of the Z3 library this build links, as Z3 reports it (`Z3_get_full_version`):
/// the resource units of [`Z3Options::resource_limit`] are counted by this version's search.
#[must_use]
pub fn z3_version() -> &'static str {
    z3::full_version()
}

/// One attempt's wall-clock timeout (`None`: no clock) and resource limit, as tests read them.
#[cfg(test)]
pub(crate) type AttemptLimit = (Option<u32>, u32);

#[derive(Clone, Debug)]
pub struct Z3Solver {
    prelude: SmtPrelude,
    options: Z3Options,
    /// The kinds the definition gives `SortInt` and `SortBool`, with which a model's values of
    /// those sorts are built; a sort the definition gives no kind has no values to build.
    model_kinds: ModelKinds,
    result_cache: Arc<Mutex<SolverResultCache>>,
    prelude_state: Arc<Mutex<PreludeState>>,
    prelude_signal: PreludeSignal,
    #[cfg(test)]
    uncached_solve_count: Arc<AtomicUsize>,
    /// The timeout of every Z3 check this solver (and its clones) ran, in order.
    #[cfg(test)]
    attempt_timeouts: Arc<Mutex<Vec<u32>>>,
    /// Whether attempts run without Z3's wall-clock timeout, the state of a check whose timer's
    /// cancellation Z3 has lost (see `RESOURCE_UNITS_PER_MS`).
    #[cfg(test)]
    without_clock: bool,
    /// Every attempt's parameters, in order: its wall-clock timeout (`None`: no clock) and its
    /// resource limit.
    #[cfg(test)]
    attempt_limits: Arc<Mutex<Vec<AttemptLimit>>>,
}

/// Z3 resource-limit units granted to an attempt per millisecond of its timeout.
///
/// The timeout alone does not bound an attempt. Z3's timer raises one cancellation, and Z3 can
/// lose it: entering a resource scope resets the cancellation flag, and a scope opened for a
/// subsolver does not inherit a cancellation raised before it opened. A check whose cancellation
/// is lost runs until it decides its query, which for a query outside its decision procedures
/// (nonlinear integer arithmetic, say) is never. A resource limit is counted by the search
/// itself and handed down to every subsolver scope, so it cannot be lost that way, and every
/// attempt also carries one.
///
/// The rate is well above the rate at which Z3 consumes units on this backend's queries (about
/// 10,000 per millisecond on nonlinear arithmetic, and no more than about 25,000 on any query
/// of the backend's tests), so the clock still ends an attempt first and the limit binds only
/// once the clock has failed, ending such a check after a small multiple of its timeout.
const RESOURCE_UNITS_PER_MS: u32 = 100_000;

/// The resource limit of an attempt with the given timeout: proportional to it, saturating at
/// Z3's largest limit, and none for a timeout of `u32::MAX`, which is Z3's own value for no
/// timeout (a limit of 0 is Z3's value for no limit).
fn resource_limit(timeout_ms: u32) -> u32 {
    if timeout_ms == u32::MAX {
        0
    } else {
        timeout_ms.saturating_mul(RESOURCE_UNITS_PER_MS)
    }
}

const RESULT_CACHE_ENTRY_LIMIT: usize = 256;
const RESULT_CACHE_KEY_BYTE_LIMIT: usize = 8 * 1024 * 1024;

#[derive(Clone, Debug)]
enum PreludeState {
    Unchecked,
    Consistent,
    Failed(PreludeFailure),
}

#[derive(Debug)]
struct SolverResultCache {
    entries: BTreeMap<Arc<str>, Satisfiability>,
    insertion_order: VecDeque<Arc<str>>,
    key_bytes: usize,
    entry_limit: usize,
    key_byte_limit: usize,
}

impl SolverResultCache {
    fn new(entry_limit: usize, key_byte_limit: usize) -> Self {
        Self {
            entries: BTreeMap::new(),
            insertion_order: VecDeque::new(),
            key_bytes: 0,
            entry_limit,
            key_byte_limit,
        }
    }

    fn get(&self, script: &str) -> Option<Satisfiability> {
        self.entries.get(script).cloned()
    }

    fn insert(&mut self, script: &str, result: &Satisfiability) {
        if !matches!(result, Satisfiability::Sat | Satisfiability::Unsat)
            || self.entry_limit == 0
            || script.len() > self.key_byte_limit
            || self.entries.contains_key(script)
        {
            return;
        }

        // Invariant: `entries` and `insertion_order` agree; pops stop once both limits admit the key.
        while self.entries.len() >= self.entry_limit
            || self.key_bytes + script.len() > self.key_byte_limit
        {
            let Some(evicted) = self.insertion_order.pop_front() else {
                return;
            };
            if self.entries.remove(evicted.as_ref()).is_some() {
                self.key_bytes -= evicted.len();
            }
        }

        let script: Arc<str> = Arc::from(script);
        self.key_bytes += script.len();
        self.entries.insert(script.clone(), result.clone());
        self.insertion_order.push_back(script);
    }
}

impl Z3Solver {
    pub fn new(definition: &crate::definition::BackendDefinition) -> Result<Self, SmtError> {
        Self::with_options(definition, Z3Options::default())
    }

    pub fn with_options(
        definition: &crate::definition::BackendDefinition,
        options: Z3Options,
    ) -> Result<Self, SmtError> {
        Self::with_options_and_prelude(definition, options, None)
    }

    pub fn with_prelude(
        definition: &crate::definition::BackendDefinition,
        prelude: &str,
    ) -> Result<Self, SmtError> {
        Self::with_options_and_prelude(definition, Z3Options::default(), Some(prelude))
    }

    pub fn with_options_and_prelude(
        definition: &crate::definition::BackendDefinition,
        options: Z3Options,
        prelude: Option<&str>,
    ) -> Result<Self, SmtError> {
        let solver = Self {
            prelude: match prelude {
                Some(prelude) => SmtPrelude::from_definition_with_prelude(definition, prelude)?,
                None => SmtPrelude::from_definition(definition)?,
            },
            options,
            model_kinds: ModelKinds {
                int: definition.domain_kind(&Sort::builtin(BuiltinSort::Int)),
                bool: definition.domain_kind(&Sort::builtin(BuiltinSort::Bool)),
            },
            result_cache: Arc::new(Mutex::new(SolverResultCache::new(
                RESULT_CACHE_ENTRY_LIMIT,
                RESULT_CACHE_KEY_BYTE_LIMIT,
            ))),
            prelude_state: Arc::new(Mutex::new(PreludeState::Unchecked)),
            prelude_signal: PreludeSignal::default(),
            #[cfg(test)]
            uncached_solve_count: Arc::new(AtomicUsize::new(0)),
            #[cfg(test)]
            attempt_timeouts: Arc::new(Mutex::new(Vec::new())),
            #[cfg(test)]
            without_clock: false,
            #[cfg(test)]
            attempt_limits: Arc::new(Mutex::new(Vec::new())),
        };
        Ok(solver)
    }

    #[cfg(test)]
    fn record_attempt(&self, timeout: u32) {
        self.attempt_timeouts
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .push(timeout);
    }

    /// This solver with attempts that Z3's clock never stops, as when Z3 loses the cancellation
    /// its timer raises.
    #[cfg(test)]
    pub(crate) fn without_clock(mut self) -> Self {
        self.without_clock = true;
        self
    }

    /// The parameters of the attempt numbered `attempt` (0 first) with the given timeout: the
    /// timeout and its resource limit, or under [`Z3Options::resource_limit`] that limit doubled
    /// per retry and no timeout.
    fn attempt_parameters(&self, timeout: u32, attempt: u32) -> Params {
        let mut parameters = Params::new();
        let (clock, units) = match self.options.resource_limit {
            Some(units) => {
                let scale = 1_u32.checked_shl(attempt).unwrap_or(u32::MAX);
                (None, units.get().saturating_mul(scale))
            }
            None => {
                #[cfg(test)]
                let clocked = !self.without_clock;
                #[cfg(not(test))]
                let clocked = true;
                (clocked.then_some(timeout), resource_limit(timeout))
            }
        };
        parameters.set_u32("rlimit", units);
        if let Some(timeout) = clock {
            parameters.set_u32("timeout", timeout);
        }
        #[cfg(test)]
        self.attempt_limits
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .push((clock, units));
        parameters
    }

    /// Every attempt's wall-clock timeout (`None`: no clock) and resource limit, in order.
    #[cfg(test)]
    pub(crate) fn attempt_limits(&self) -> Vec<AttemptLimit> {
        self.attempt_limits
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
    }

    /// The timeouts of the Z3 checks run so far, in order, one per attempt.
    #[cfg(test)]
    pub(crate) fn attempt_timeouts(&self) -> Vec<u32> {
        self.attempt_timeouts
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
    }

    /// How the prelude failed, once a check found it failed.
    pub fn prelude_failure(&self) -> Option<PreludeFailure> {
        let state = self
            .prelude_state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        match &*state {
            PreludeState::Failed(failure) => Some(failure.clone()),
            PreludeState::Unchecked | PreludeState::Consistent => None,
        }
    }

    /// The stop every query of this solver returns once its prelude failed; it also raises the
    /// shared prelude-failure signal, so every operation using the solver observes the failure
    /// at its next poll.
    #[cfg_attr(debug_assertions, track_caller)]
    fn prelude_stop(&self, failure: PreludeFailure) -> Stop {
        self.prelude_signal.raise(failure.clone());
        Stop::solver_prelude(failure)
    }

    /// Check that the prelude (the definition's axioms and the user prelude) is a script Z3
    /// reads, and that it is satisfiable.
    ///
    /// A failed prelude is a stop, not a query failure: no answer of the solver means anything
    /// under it, whichever operation asked. A check interrupted by a stop before its solve
    /// answered leaves the prelude unchecked, so a later operation checks it again.
    pub fn check_prelude(&self) -> Stoppable<()> {
        let mut state = self
            .prelude_state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        match &*state {
            PreludeState::Consistent => return Ok(()),
            PreludeState::Failed(failure) => return Err(self.prelude_stop(failure.clone())),
            PreludeState::Unchecked => {}
        }
        // Invariant: the lock covers the solve and state transition, so only one thread
        // checks the prelude and no unsatisfiable answer can pass a concurrent failed check.
        // A completed check records its answer even when a stop is raised meanwhile; only a
        // solve that stopped before answering leaves the prelude unchecked. The poll before the
        // solve keeps a stopped check from counting as a solver run.
        stop::check()?;
        let failure = match self.solve_uncached(&self.prelude.declarations().join("\n"))? {
            Ok(Satisfiability::Sat) => {
                *state = PreludeState::Consistent;
                return Ok(());
            }
            Ok(Satisfiability::Unsat) => PreludeFailure::Inconsistent,
            Ok(Satisfiability::Unknown(reason)) => PreludeFailure::Unknown(reason.into()),
            Err(rejected) => PreludeFailure::Malformed(rejected.message.into()),
        };
        *state = PreludeState::Failed(failure.clone());
        Err(self.prelude_stop(failure))
    }

    /// Confirm an answer against the prelude: a `Sat` answer shows the prelude consistent, an
    /// `Unsat` answer means something only once the prelude is checked, and no answer means
    /// anything once the prelude failed.
    fn confirm_answer(&self, result: Satisfiability) -> Stoppable<Satisfiability> {
        match result {
            Satisfiability::Sat => {
                let mut state = self
                    .prelude_state
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                match &*state {
                    PreludeState::Failed(failure) => Err(self.prelude_stop(failure.clone())),
                    PreludeState::Unchecked | PreludeState::Consistent => {
                        *state = PreludeState::Consistent;
                        Ok(Satisfiability::Sat)
                    }
                }
            }
            Satisfiability::Unsat => {
                self.check_prelude()?;
                Ok(Satisfiability::Unsat)
            }
            Satisfiability::Unknown(reason) => match self.prelude_failure() {
                Some(failure) => Err(self.prelude_stop(failure)),
                None => Ok(Satisfiability::Unknown(reason)),
            },
        }
    }

    /// Confirm a rejected script, `script` posing `query`, against the prelude. Every script
    /// starts with the prelude, so the rejection is the query's own only once the prelude is
    /// known to load; a prelude that does not load (or fails otherwise) is a stop. A rejection
    /// itself never shows the prelude consistent: only the prelude's own check does.
    ///
    /// A query's rejection whose only possible cause is the text k-rust's translation wrote by
    /// itself is a defect of k-rust, not a property of the definition or the request: a debug
    /// build panics on it, so every test that reaches the solver checks that the translation
    /// writes scripts the solver reads. A consumer that falls back on any query failure stays
    /// sound, which is why a release build keeps the typed failure, but the fallback would hide
    /// the defect. A rejection that text from the definition or the user may cause
    /// (`SmtPrelude::blames_the_translation`) stays a typed failure in every build.
    fn confirm_rejection(
        &self,
        rejected: RejectedScript,
        query: &TranslatedQuery,
        script: &str,
    ) -> Stoppable<SmtError> {
        self.check_prelude()?;
        debug_assert!(
            !self.prelude.blames_the_translation(query, script),
            "Z3 rejected an SMT-LIB script k-rust's translation wrote by itself ({}):\n{script}",
            rejected.message
        );
        Ok(SmtError::MalformedScript {
            message: rejected.message,
        })
    }

    /// Solve `script` through the result cache. A stop observed before the lookup ends the
    /// query: its answer is not needed, and neither the cache nor Z3 is consulted. Only answers
    /// are cached; a rejected script is not, so the cache never answers for a script Z3 did not
    /// read.
    fn solve(&self, script: &str) -> Stoppable<Result<Satisfiability, RejectedScript>> {
        let _span = measure::algorithm_span(Algorithm::BackendSmtCache);
        stop::check()?;
        measure::bump(Counter::SmtQueries);
        if let Some(result) = self
            .result_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get(script)
        {
            return Ok(Ok(result));
        }

        let result = self.solve_uncached(script)?;
        if let Ok(answer) = &result {
            self.result_cache
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .insert(script, answer);
        }
        Ok(result)
    }

    /// Solve `script` with Z3, doubling the timeout on each retry of an unknown answer. Each
    /// attempt is preceded by a poll, so a stop raised meanwhile ends the query instead of
    /// starting another attempt. A script Z3 rejects is not checked, and not retried: the
    /// rejection does not depend on the timeout.
    fn solve_uncached(&self, script: &str) -> Stoppable<Result<Satisfiability, RejectedScript>> {
        measure::bump(Counter::SmtSolverRuns);
        #[cfg(test)]
        self.uncached_solve_count.fetch_add(1, Ordering::Relaxed);

        on_own_context(|| {
            let mut timeout = self.options.timeout_ms;
            for attempt in 0..=self.options.retry_limit {
                stop::check()?;
                let solver = Solver::new();
                solver.set_params(&self.attempt_parameters(timeout, attempt));
                #[cfg(test)]
                self.record_attempt(timeout);
                if let Err(rejected) = load(&solver, script) {
                    return Ok(Err(rejected));
                }
                match measured_check(&solver) {
                    SatResult::Sat => return Ok(Ok(Satisfiability::Sat)),
                    SatResult::Unsat => return Ok(Ok(Satisfiability::Unsat)),
                    SatResult::Unknown if attempt < self.options.retry_limit => {
                        timeout = timeout.saturating_mul(2);
                    }
                    SatResult::Unknown => {
                        return Ok(Ok(Satisfiability::Unknown(reason_unknown(&solver))));
                    }
                }
            }
            unreachable!("the retry loop always returns")
        })
    }

    fn solve_query(
        &self,
        query: &TranslatedQuery,
        assertion: Option<&str>,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        let mut script = query.base().to_owned();
        if let Some(assertion) = assertion {
            script.push_str("\n(assert ");
            script.push_str(assertion);
            script.push(')');
        }
        if let Some(failure) = self.prelude_failure() {
            return Err(self.prelude_stop(failure));
        }
        match self.solve(&script)? {
            Ok(answer) => self.confirm_answer(answer).map(Ok),
            Err(rejected) => self.confirm_rejection(rejected, query, &script).map(Err),
        }
    }

    fn solve_model(
        &self,
        query: &TranslatedQuery,
        variables: &BTreeSet<Variable>,
    ) -> Stoppable<Result<ModelResult, SmtError>> {
        let _span = measure::algorithm_span(Algorithm::BackendSmtCache);
        if let Some(failure) = self.prelude_failure() {
            return Err(self.prelude_stop(failure));
        }
        // The model is read on the query's own context, the only place its values exist; the
        // answer is confirmed against the prelude after the context is gone.
        let outcome = on_own_context(|| {
            let mut timeout = self.options.timeout_ms;
            for attempt in 0..=self.options.retry_limit {
                stop::check()?;
                measure::bump(Counter::SmtSolverRuns);
                let solver = Solver::new();
                solver.set_params(&self.attempt_parameters(timeout, attempt));
                #[cfg(test)]
                self.record_attempt(timeout);
                if let Err(rejected) = load(&solver, query.base()) {
                    return Ok(Err(rejected));
                }
                match measured_check(&solver) {
                    SatResult::Sat => {
                        let model = match query.model_mappings() {
                            None => Ok(ModelResult::Unknown(APPROXIMATE_MODEL_REASON.into())),
                            Some(mappings) => match solver.get_model() {
                                None => Err(SmtError::MissingModel),
                                Some(model) => self.extract_model(&model, mappings, variables),
                            },
                        };
                        return Ok(Ok(ModelAttempt::Sat(model)));
                    }
                    SatResult::Unsat => return Ok(Ok(ModelAttempt::Unsat)),
                    SatResult::Unknown if attempt < self.options.retry_limit => {
                        timeout = timeout.saturating_mul(2);
                    }
                    SatResult::Unknown => {
                        return Ok(Ok(ModelAttempt::Unknown(reason_unknown(&solver))));
                    }
                }
            }
            unreachable!("the retry loop always returns")
        })?;
        match outcome {
            Err(rejected) => Ok(Err(self.confirm_rejection(
                rejected,
                query,
                query.base(),
            )?)),
            Ok(ModelAttempt::Sat(model)) => {
                // confirm_answer returns its argument unchanged; only the prelude check matters
                // here.
                let _: Satisfiability = self.confirm_answer(Satisfiability::Sat)?;
                Ok(model)
            }
            Ok(ModelAttempt::Unsat) => {
                let _: Satisfiability = self.confirm_answer(Satisfiability::Unsat)?;
                Ok(Ok(ModelResult::Unsat))
            }
            Ok(ModelAttempt::Unknown(reason)) => {
                let _: Satisfiability =
                    self.confirm_answer(Satisfiability::Unknown(reason.clone()))?;
                Ok(Ok(ModelResult::Unknown(reason)))
            }
        }
    }

    fn extract_model(
        &self,
        model: &Model,
        mappings: &BTreeMap<Term, String>,
        variables: &BTreeSet<Variable>,
    ) -> Result<ModelResult, SmtError> {
        let mut substitution = Substitution::new();
        for variable in variables {
            let term = Term::variable(variable.clone());
            // The translation reads `SortInt` and `SortBool` by name as the integers and the
            // Booleans; a model value is built with the kind the definition gives the sort, which
            // is that one by name whenever the sort has domain values.
            let value = match &variable.sort {
                sort if sort.is_builtin(BuiltinSort::Int)
                    && self.model_kinds.int == Some(DomainKind::Int) =>
                {
                    let name = mappings
                        .get(&term)
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    let value = model
                        .eval(&Int::new_const(name.clone()), true)
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    let rendered = normalize_integer(&value.to_string()).ok_or_else(|| {
                        SmtError::InvalidModelValue {
                            variable: variable.clone(),
                            value: value.to_string(),
                        }
                    })?;
                    Term::domain_value_of(DomainKind::Int, variable.sort, rendered)
                }
                sort if sort.is_builtin(BuiltinSort::Bool)
                    && self.model_kinds.bool == Some(DomainKind::Bool) =>
                {
                    let name = mappings
                        .get(&term)
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    let value = model
                        .eval(&Bool::new_const(name.clone()), true)
                        .and_then(|value| value.as_bool())
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    Term::domain_value_of(DomainKind::Bool, variable.sort, value.to_string())
                }
                _ => term,
            };
            substitution.insert(variable.clone(), value);
        }
        Ok(ModelResult::Sat(substitution))
    }
}

/// What a model query's last attempt found, read off its Z3 context before the context goes.
enum ModelAttempt {
    /// Satisfiable, with the model read as a K valuation, or why none was read.
    Sat(Result<ModelResult, SmtError>),
    Unsat,
    /// Undecided, with Z3's reason.
    Unknown(String),
}

/// Z3's reason for an unknown answer of `solver`'s last check.
fn reason_unknown(solver: &Solver) -> String {
    solver
        .get_reason_unknown()
        .unwrap_or_else(|| "Z3 returned unknown".into())
}

/// The kinds a definition gives the sorts the SMT translation reads by name.
#[derive(Clone, Copy, Debug)]
struct ModelKinds {
    int: Option<DomainKind>,
    bool: Option<DomainKind>,
}

fn normalize_integer(rendered: &str) -> Option<String> {
    if let Ok(value) = BigInt::from_str(rendered) {
        return Some(value.to_string());
    }
    let magnitude = rendered.strip_prefix("(- ")?.strip_suffix(')')?;
    BigInt::from_str(magnitude)
        .ok()
        .map(|value| (-value).to_string())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ValiditySubquery {
    Base,
    Positive,
    Negative,
}

/// The validity the subqueries' answers decide. A subquery that fails (its script was not
/// read, say) ends the decision with that failure: the answers of the others alone do not decide
/// it.
fn decide_validity<E>(
    mut solve: impl FnMut(ValiditySubquery) -> Stoppable<Result<Satisfiability, E>>,
) -> Stoppable<Result<Validity, E>> {
    macro_rules! answer {
        ($subquery:expr) => {
            match solve($subquery)? {
                Ok(answer) => answer,
                Err(error) => return Ok(Err(error)),
            }
        };
    }
    Ok(Ok(match answer!(ValiditySubquery::Positive) {
        Satisfiability::Sat => match answer!(ValiditySubquery::Negative) {
            Satisfiability::Unsat => Validity::Valid,
            Satisfiability::Sat => Validity::Contingent,
            Satisfiability::Unknown(reason) => Validity::Unknown(reason),
        },
        Satisfiability::Unsat => match answer!(ValiditySubquery::Base) {
            Satisfiability::Unsat => Validity::InconsistentGroundTruth,
            Satisfiability::Sat => Validity::Refuted,
            Satisfiability::Unknown(reason) => Validity::Unknown(reason),
        },
        Satisfiability::Unknown(positive_reason) => match answer!(ValiditySubquery::Base) {
            Satisfiability::Unsat => Validity::InconsistentGroundTruth,
            Satisfiability::Unknown(reason) => Validity::Unknown(reason),
            Satisfiability::Sat => match answer!(ValiditySubquery::Negative) {
                Satisfiability::Unsat => Validity::Valid,
                Satisfiability::Sat | Satisfiability::Unknown(_) => {
                    Validity::Unknown(positive_reason)
                }
            },
        },
    }))
}

impl SmtSolver for Z3Solver {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        if let Some(failure) = self.prelude_failure() {
            return Err(self.prelude_stop(failure));
        }
        let query = match self.prelude.query(predicates, substitution, &[], false) {
            Ok(query) => query,
            Err(error) => return Ok(Err(error.into())),
        };
        self.solve_query(&query, None)
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        if let Some(failure) = self.prelude_failure() {
            return Err(self.prelude_stop(failure));
        }
        if checked.is_empty() {
            return Ok(Ok(Validity::Valid));
        }
        let query = match self.prelude.query(known, substitution, checked, true) {
            Ok(query) => query,
            Err(error) => return Ok(Err(error.into())),
        };
        let checked = query.checked().to_string();
        decide_validity(|subquery| match subquery {
            ValiditySubquery::Base => self.solve_query(&query, None),
            ValiditySubquery::Positive => self.solve_query(&query, Some(&checked)),
            ValiditySubquery::Negative => {
                self.solve_query(&query, Some(&format!("(not {checked})")))
            }
        })
    }

    fn get_model(&self, query: &ModelQuery<'_>) -> Stoppable<Result<ModelResult, SmtError>> {
        let (predicates, substitution) = (query.predicates(), query.substitution());
        if let Some(failure) = self.prelude_failure() {
            return Err(self.prelude_stop(failure));
        }
        if predicates.is_empty() && substitution.is_empty() {
            return Ok(Ok(ModelResult::Sat(Substitution::new())));
        }
        let variables = substitution
            .keys()
            .cloned()
            .chain(predicates.iter().flat_map(Predicate::free_variables))
            .collect::<BTreeSet<_>>();
        let query = match self.prelude.query(predicates, substitution, &[], false) {
            Ok(query) => query,
            Err(error) => return Ok(Err(error.into())),
        };
        self.solve_model(&query, &variables)
    }

    fn prelude_signal(&self) -> Option<&PreludeSignal> {
        Some(&self.prelude_signal)
    }
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use std::time::Duration;

    use super::*;
    use crate::{
        definition::BackendDefinition,
        rule::Predicate,
        stop::{CancellationToken, StopCause},
        term::{Sort, Variable},
        timeout::{StepTimeoutController, StepTimeoutMode, StepTimeoutOptions},
    };

    /// The cause of a stopped answer, published so that no stop is dropped armed.
    fn cause<T>(answer: Stoppable<T>) -> Result<T, StopCause> {
        answer.map_err(Stop::into_cause)
    }

    const INCONSISTENT: StopCause = StopCause::SolverPrelude(PreludeFailure::Inconsistent);

    /// An attempt's resource limit grows with its timeout, saturates at Z3's largest limit
    /// rather than wrapping to a small one, and is absent only when the timeout is.
    #[test]
    fn an_attempts_resource_limit_is_proportional_to_its_timeout() {
        assert_eq!(resource_limit(1), RESOURCE_UNITS_PER_MS);
        assert_eq!(resource_limit(125), 125 * RESOURCE_UNITS_PER_MS);
        assert_eq!(resource_limit(1_000_000), u32::MAX);
        assert_eq!(resource_limit(u32::MAX - 1), u32::MAX);
        assert_eq!(resource_limit(u32::MAX), 0);
    }

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortS{} []
                symbol opaque{}(SortInt{}) : SortInt{} [function{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                symbol bitwise{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), smtlib{}("bitwise")]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn term(definition: &BackendDefinition, source: &str) -> crate::term::Term {
        definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize")
    }

    fn x() -> Variable {
        Variable::new("X", crate::term::Sort::simple("SortInt"))
    }

    #[test]
    fn quantified_opaque_terms_retain_their_bound_variable_dependence() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        // f(x) = x + 1 is a model; replacing f(x) by a constant would make this false.
        let no_fixed_point = Predicate::Not(Arc::new(Predicate::Exists(
            x(),
            Arc::new(Predicate::Equals(
                term(&definition, "opaque{}(X:SortInt{})"),
                Term::variable(x()),
            )),
        )));
        assert_eq!(
            solver.is_sat(&[no_fixed_point], &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
    }

    #[test]
    fn quantified_opaque_predicates_can_hold_for_some_values_and_fail_for_others() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        for name in ["X", "Y"] {
            let some_defined = Predicate::Exists(
                x(),
                Arc::new(Predicate::Ceil(term(&definition, "opaque{}(X:SortInt{})"))),
            );
            let some_undefined = Predicate::Exists(
                Variable::new(name, Sort::simple("SortInt")),
                Arc::new(Predicate::Not(Arc::new(Predicate::Ceil(term(
                    &definition,
                    &format!("opaque{{}}({name}:SortInt{{}})"),
                ))))),
            );
            assert_eq!(
                solver.is_sat(&[some_defined, some_undefined], &Substitution::new()),
                Ok(Ok(Satisfiability::Sat))
            );
        }
    }

    #[test]
    fn alpha_equivalent_opaque_predicates_share_an_abstraction_without_capturing_free_variables() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let quantified = |bound: &str, free: &str| {
            Predicate::Exists(
                Variable::new(bound, Sort::simple("SortInt")),
                Arc::new(Predicate::In(
                    Term::variable(Variable::new(bound, Sort::simple("SortInt"))),
                    Term::variable(Variable::new(free, Sort::simple("SortInt"))),
                )),
            )
        };
        // Include the internal template prefix as a free backend variable name.
        let left = quantified("X", "#SMT-bound-0");
        let renamed = quantified("Y", "#SMT-bound-0");
        let different = quantified("Y", "F");
        assert_eq!(
            solver.check_predicates(
                std::slice::from_ref(&left),
                &Substitution::new(),
                &[renamed]
            ),
            Ok(Ok(Validity::Valid))
        );
        assert_eq!(
            solver.check_predicates(&[left], &Substitution::new(), &[different]),
            Ok(Ok(Validity::Contingent))
        );
    }

    #[test]
    fn nested_shadowing_restores_the_enclosing_and_free_variable_scopes() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let equals = |value: &str| {
            Predicate::Equals(
                Term::variable(x()),
                Term::raw_domain_value(Sort::simple("SortInt"), value),
            )
        };
        let constraints = [
            equals("7"),
            Predicate::Exists(
                x(),
                Arc::new(Predicate::And(
                    vec![
                        equals("1"),
                        Predicate::Exists(x(), Arc::new(equals("2"))),
                        equals("1"),
                    ]
                    .into(),
                )),
            ),
            equals("7"),
        ];
        let model = cause(solver.get_model(&ModelQuery::for_solver_tests(
            &constraints,
            &Substitution::new(),
        )))
        .unwrap()
        .unwrap();
        assert_eq!(
            model,
            ModelResult::Sat(Substitution::from([(
                x(),
                Term::raw_domain_value(Sort::simple("SortInt"), "7")
            )]))
        );
    }

    #[test]
    fn model_from_an_uninterpreted_function_is_unknown() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let bitwise = term(
            &definition,
            r#"bitwise{}(X:SortInt{}, \dv{SortInt{}}("1"))"#,
        );
        let predicate = Predicate::Equals(
            bitwise.clone(),
            Term::raw_domain_value(Sort::simple("SortInt"), "2"),
        );
        assert_eq!(
            solver.get_model(&ModelQuery::for_solver_tests(
                &[predicate],
                &Substitution::new()
            )),
            Ok(Ok(ModelResult::Unknown(APPROXIMATE_MODEL_REASON.into())))
        );
        assert_eq!(
            solver.get_model(&ModelQuery::for_solver_tests(
                &[],
                &Substitution::from([(x(), bitwise.clone())])
            )),
            Ok(Ok(ModelResult::Unknown(APPROXIMATE_MODEL_REASON.into())))
        );
        assert_eq!(
            solver.get_model(&ModelQuery::for_solver_tests(
                &[
                    Predicate::Equals(
                        bitwise.clone(),
                        Term::raw_domain_value(Sort::simple("SortInt"), "1"),
                    ),
                    Predicate::Equals(
                        bitwise,
                        Term::raw_domain_value(Sort::simple("SortInt"), "2"),
                    ),
                ],
                &Substitution::new(),
            )),
            Ok(Ok(ModelResult::Unsat))
        );
    }

    #[test]
    fn model_with_an_uninterpreted_quantifier_sort_is_unknown() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let variable = Variable::new("A", Sort::simple("SortS"));
        let predicate = Predicate::Forall(
            variable.clone(),
            Arc::new(Predicate::Equals(
                Term::variable(variable.clone()),
                Term::variable(variable),
            )),
        );
        assert_eq!(
            solver.get_model(&ModelQuery::for_solver_tests(
                &[predicate],
                &Substitution::new()
            )),
            Ok(Ok(ModelResult::Unknown(APPROXIMATE_MODEL_REASON.into())))
        );
    }

    #[test]
    fn quantified_abstractions_follow_binder_order_and_shadowing() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let nested = |outer: &str, inner: &str| {
            let outer = Variable::new(outer, Sort::simple("SortInt"));
            let inner = Variable::new(inner, Sort::simple("SortInt"));
            Predicate::Exists(
                outer.clone(),
                Arc::new(Predicate::Forall(
                    inner.clone(),
                    Arc::new(Predicate::In(Term::variable(outer), Term::variable(inner))),
                )),
            )
        };
        assert_eq!(
            solver.check_predicates(
                &[nested("X", "Y")],
                &Substitution::new(),
                &[nested("Y", "X")]
            ),
            Ok(Ok(Validity::Valid))
        );
        let diagonal = Predicate::Forall(
            x(),
            Arc::new(Predicate::In(Term::variable(x()), Term::variable(x()))),
        );
        assert_eq!(
            solver.check_predicates(&[nested("Y", "Y")], &Substitution::new(), &[diagonal]),
            Ok(Ok(Validity::Valid))
        );
    }

    #[test]
    fn proves_and_refutes_predicates_under_a_substitution() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
        ))];

        assert_eq!(
            solver.check_predicates(
                &[],
                &Substitution::from([(x(), term(&definition, r#"\dv{SortInt{}}("5")"#))]),
                &checked,
            ),
            Ok(Ok(Validity::Valid))
        );
        assert_eq!(
            solver.check_predicates(
                &[],
                &Substitution::from([(x(), term(&definition, r#"\dv{SortInt{}}("15")"#))]),
                &checked,
            ),
            Ok(Ok(Validity::Refuted))
        );
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), &checked),
            Ok(Ok(Validity::Contingent))
        );
    }

    #[test]
    fn proves_native_collection_sizes_are_nonnegative() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortKItem{} []
                hooked-sort SortList{}
                    [hook{}("LIST.List"), unit{}(Lbl'Stop'List{}()), element{}(LblListItem{}()),
                     concat{}(Lbl'Unds'List'Unds'{}())]
                hooked-symbol Lbl'Stop'List{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
                hooked-symbol LblListItem{}(SortKItem{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.element")]
                hooked-symbol Lbl'Unds'List'Unds'{}(SortList{}, SortList{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                hooked-symbol abstractSize{}(SortList{}) : SortInt{}
                    [function{}(), total{}(), hook{}("LIST.size")]
                hooked-symbol translatedSize{}(SortList{}) : SortInt{}
                    [function{}(), total{}(), hook{}("LIST.size"), smtlib{}("list-size")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();

        for size in ["abstractSize", "translatedSize"] {
            let checked = [Predicate::Term(term(
                &definition,
                &format!(r#"lt{{}}(\dv{{SortInt{{}}}}("-1"), {size}{{}}(L:SortList{{}}))"#),
            ))];
            assert_eq!(
                solver.check_predicates(&[], &Substitution::new(), &checked),
                Ok(Ok(Validity::Valid)),
                "{size} should be nonnegative"
            );
        }
    }

    #[test]
    fn distinguishes_unsatisfiable_and_inconsistent_constraints() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let x_term = term(&definition, "X:SortInt{}");
        let five = term(&definition, r#"\dv{SortInt{}}("5")"#);
        let six = term(&definition, r#"\dv{SortInt{}}("6")"#);
        let inconsistent = [
            Predicate::Equals(x_term.clone(), five),
            Predicate::Equals(x_term, six),
        ];

        assert_eq!(
            solver.is_sat(&inconsistent, &Substitution::new()),
            Ok(Ok(Satisfiability::Unsat))
        );
        assert_eq!(
            solver.check_predicates(
                &inconsistent,
                &Substitution::new(),
                &[Predicate::Term(term(
                    &definition,
                    r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
                ))],
            ),
            Ok(Ok(Validity::InconsistentGroundTruth))
        );
    }

    #[test]
    fn validity_filters_ground_truth_unrelated_to_the_checked_variables() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
        ))];
        let unrelated = term(&definition, "Z:SortInt{}");
        let contradictory = [
            Predicate::Equals(
                unrelated.clone(),
                term(&definition, r#"\dv{SortInt{}}("1")"#),
            ),
            Predicate::Equals(unrelated, term(&definition, r#"\dv{SortInt{}}("2")"#)),
        ];

        assert_eq!(
            solver.check_predicates(
                &contradictory,
                &Substitution::from([(x(), term(&definition, r#"\dv{SortInt{}}("5")"#))]),
                &checked,
            ),
            Ok(Ok(Validity::Valid))
        );
    }

    #[test]
    fn rejects_an_inconsistent_smt_lemma_prelude() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol f{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), smtlib{}("f")]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(
                            \dv{SortInt{}}("1"),
                            \top{SortInt{}}()
                        )
                    )
                ) [simplification{}(), smt-lemma{}(), label{}("f-is-one")]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(
                            \dv{SortInt{}}("2"),
                            \top{SortInt{}}()
                        )
                    )
                ) [simplification{}(), smt-lemma{}(), label{}("f-is-two")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        let solver = Z3Solver::new(&definition).unwrap();
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 0);
        assert_eq!(
            cause(solver.is_sat(&[], &Substitution::new())),
            Err(INCONSISTENT)
        );
        assert_eq!(solver.prelude_failure(), Some(PreludeFailure::Inconsistent));
        assert_eq!(
            cause(solver.is_sat(&[], &Substitution::new())),
            Err(INCONSISTENT)
        );
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn loads_external_smt_preludes_and_rejects_inconsistent_ones() {
        let definition = definition();
        let consistent = "(declare-const a Int)\n(assert (> a 0))";
        let inconsistent = "(declare-const a Int)\n(assert (> a 0))\n(assert (< a 0))";

        let consistent = Z3Solver::with_prelude(&definition, consistent).unwrap();
        assert_eq!(cause(consistent.check_prelude()), Ok(()));
        let inconsistent = Z3Solver::with_prelude(&definition, inconsistent).unwrap();
        let concurrent_operation = inconsistent.prelude_signal.clone();
        assert_eq!(concurrent_operation.failure(), None);
        assert_eq!(cause(inconsistent.check_prelude()), Err(INCONSISTENT));
        assert_eq!(
            concurrent_operation.failure(),
            Some(&PreludeFailure::Inconsistent)
        );
        let first_validity = Z3Solver::with_prelude(
            &definition,
            "(declare-const a Int)\n(assert (> a 0))\n(assert (< a 0))",
        )
        .unwrap();
        let tautology = Predicate::Equals(
            Term::raw_domain_value(Sort::simple("SortInt"), "1"),
            Term::raw_domain_value(Sort::simple("SortInt"), "1"),
        );
        assert_eq!(
            cause(first_validity.check_predicates(&[], &Substitution::new(), &[tautology])),
            Err(INCONSISTENT)
        );
    }

    #[test]
    fn sat_first_proves_prelude_consistency_without_an_extra_solve() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 0);
        assert_eq!(
            solver.is_sat(&[], &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 1);
        let impossible = Predicate::Equals(
            Term::raw_domain_value(Sort::simple("SortInt"), "1"),
            Term::raw_domain_value(Sort::simple("SortInt"), "2"),
        );
        assert_eq!(
            solver.is_sat(&[impossible], &Substitution::new()),
            Ok(Ok(Satisfiability::Unsat))
        );
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 2);
        assert_eq!(cause(solver.check_prelude()), Ok(()));
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn concurrent_unsat_answers_check_the_prelude_once() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        std::thread::scope(|scope| {
            for _ in 0..8 {
                let solver = solver.clone();
                scope.spawn(move || {
                    assert_eq!(
                        cause(solver.confirm_answer(Satisfiability::Unsat)),
                        Ok(Satisfiability::Unsat)
                    );
                });
            }
        });
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn unknown_query_does_not_assert_prelude_consistency() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        assert_eq!(
            cause(solver.confirm_answer(Satisfiability::Unknown("query timed out".into()))),
            Ok(Satisfiability::Unknown("query timed out".into()))
        );
        assert!(matches!(
            *solver.prelude_state.lock().unwrap(),
            PreludeState::Unchecked
        ));
        assert_eq!(cause(solver.check_prelude()), Ok(()));
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn an_unknown_prelude_failure_is_sticky() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let failure = PreludeFailure::Unknown("prelude timed out".into());
        *solver.prelude_state.lock().unwrap() = PreludeState::Failed(failure.clone());
        assert_eq!(solver.prelude_failure(), Some(failure.clone()));
        let stopped = StopCause::SolverPrelude(failure);
        assert_eq!(
            cause(solver.is_sat(&[], &Substitution::new())),
            Err(stopped.clone())
        );
        assert_eq!(cause(solver.check_prelude()), Err(stopped));
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 0);
    }

    const INCONSISTENT_PRELUDE: &str = "(declare-const a Int)\n(assert (> a 0))\n(assert (< a 0))";

    fn x_is_one() -> [Predicate; 1] {
        [Predicate::Equals(
            Term::variable(x()),
            Term::raw_domain_value(Sort::simple("SortInt"), "1"),
        )]
    }

    /// A named query, reduced to whether it stopped and why.
    type Query = (&'static str, fn(&Z3Solver) -> Result<(), StopCause>);

    /// The three kinds of query.
    fn queries() -> [Query; 3] {
        [
            ("is_sat", |solver| {
                cause(solver.is_sat(&x_is_one(), &Substitution::new())).map(|_| ())
            }),
            ("check_predicates", |solver| {
                cause(solver.check_predicates(&[], &Substitution::new(), &x_is_one())).map(|_| ())
            }),
            ("get_model", |solver| {
                cause(solver.get_model(&ModelQuery::for_solver_tests(
                    &x_is_one(),
                    &Substitution::new(),
                )))
                .map(|_| ())
            }),
        ]
    }

    /// An unsatisfiable prelude makes no answer of the solver mean anything, so whichever kind of
    /// query finds it returns the prelude's stop, and so does every later query of every kind.
    #[test]
    fn an_inconsistent_prelude_stops_the_query_that_finds_it_and_every_later_one() {
        let definition = definition();
        for (first, finds) in queries() {
            let solver = Z3Solver::with_prelude(&definition, INCONSISTENT_PRELUDE).unwrap();
            assert_eq!(
                finds(&solver),
                Err(INCONSISTENT),
                "{first} finds the failure"
            );
            assert_eq!(
                solver.prelude_failure(),
                Some(PreludeFailure::Inconsistent),
                "{first}"
            );
            assert_eq!(
                solver.prelude_signal.failure(),
                Some(&PreludeFailure::Inconsistent),
                "{first}"
            );
            for _ in 0..2 {
                for (later, query) in queries() {
                    assert_eq!(query(&solver), Err(INCONSISTENT), "{later} after {first}");
                }
            }
        }
    }

    /// Scripts Z3 does not read: an undeclared constant, a sort mismatch, an unbalanced
    /// parenthesis, a redeclaration, and a NUL byte, which would end the C string Z3 reads.
    const UNREADABLE_SCRIPTS: [&str; 5] = [
        "(assert (> b 0))",
        "(declare-sort S 0)\n(declare-const a S)\n(assert (> a 0))",
        "(declare-const a Int",
        "(declare-const a Int)\n(declare-const a Int)",
        "(declare-const a Int)\u{0}\n(assert (> a 0))",
    ];

    /// A script Z3 does not read is rejected with a message, never loaded for a check that would
    /// answer about none of its assertions. A rejection leaves nothing behind on the thread's
    /// context: the next script loads and is checked as written.
    #[test]
    fn load_rejects_every_script_z3_does_not_read() {
        for script in UNREADABLE_SCRIPTS {
            match load(&Solver::new(), script) {
                Err(RejectedScript { message }) => assert!(!message.is_empty(), "{script:?}"),
                Ok(()) => panic!("Z3 loaded the unreadable script {script:?}"),
            }
            let solver = Solver::new();
            assert_eq!(
                load(
                    &solver,
                    "(declare-const a Int)\n(assert (> a 0))\n(assert (< a 0))"
                ),
                Ok(()),
                "after {script:?}"
            );
            assert_eq!(solver.check(), SatResult::Unsat, "after {script:?}");
        }
        // Z3 adds none of a rejected script's assertions, so a check of it answers `sat` even
        // when the script asserts `false` before its error: the answer every rejected script
        // got while the error went unread.
        let solver = Solver::new();
        assert!(load(&solver, "(assert false)\n(assert (> b 0))").is_err());
        assert_eq!(solver.check(), SatResult::Sat);
    }

    /// Whether a query stopped on a prelude Z3 rejected.
    fn stopped_on_a_malformed_prelude(stopped: Result<(), StopCause>) -> bool {
        matches!(
            stopped,
            Err(StopCause::SolverPrelude(PreludeFailure::Malformed(message))) if !message.is_empty()
        )
    }

    /// A prelude Z3 does not read states none of its axioms, so no answer under it means
    /// anything: the prelude check fails with Z3's rejection, and every query stops, whether it
    /// is the query that finds the rejection or a later one. A user prelude that redeclares a
    /// function the definition's `smtlib` attribute declares (`bitwise`) is such a prelude.
    #[test]
    fn a_prelude_z3_rejects_stops_the_query_that_finds_it_and_every_later_one() {
        let definition = definition();
        for prelude in UNREADABLE_SCRIPTS
            .into_iter()
            .chain(["(declare-fun bitwise (Int Int) Int)"])
        {
            let checked = Z3Solver::with_prelude(&definition, prelude).unwrap();
            assert!(
                stopped_on_a_malformed_prelude(cause(checked.check_prelude())),
                "{prelude:?}"
            );
            assert!(
                matches!(
                    checked.prelude_signal.failure(),
                    Some(PreludeFailure::Malformed(_))
                ),
                "{prelude:?}"
            );
            for (first, finds) in queries() {
                let solver = Z3Solver::with_prelude(&definition, prelude).unwrap();
                assert!(
                    stopped_on_a_malformed_prelude(finds(&solver)),
                    "{first} finds the rejection of {prelude:?}"
                );
                for (later, query) in queries() {
                    assert!(
                        stopped_on_a_malformed_prelude(query(&solver)),
                        "{later} after {first} under {prelude:?}"
                    );
                    assert!(
                        stopped_on_a_malformed_prelude(query(&checked)),
                        "{later} after the check of {prelude:?}"
                    );
                }
            }
        }
    }

    /// A definition whose `bogus` is hooked to an operator Z3 does not have, so every query that
    /// translates an application of it is a script Z3 rejects, while the prelude loads.
    fn unreadable_hook_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol bogus{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("no-such-operator")]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// A query whose script Z3 rejects is a failure of that query, never an answer: not `Sat`
    /// (which Z3 would give for the empty formula it holds), not a validity, not a model of
    /// default values. The rejection is not cached, and it does not show the prelude consistent:
    /// the prelude is solved on its own before the rejection is blamed on the query.
    #[test]
    fn a_query_z3_rejects_answers_nothing_and_is_not_cached() {
        let definition = unreadable_hook_definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let bogus = [Predicate::Term(term(
            &definition,
            r#"bogus{}(X:SortInt{}, \dv{SortInt{}}("0"))"#,
        ))];
        fn rejected<T>(answer: &Result<Result<T, SmtError>, StopCause>) -> bool {
            matches!(
                answer,
                Ok(Err(SmtError::MalformedScript { message })) if !message.is_empty()
            )
        }

        let first: Result<Result<Satisfiability, SmtError>, StopCause> =
            cause(solver.is_sat(&bogus, &Substitution::new()));
        assert!(rejected(&first), "{first:?}");
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed),
            2,
            "the query and the prelude"
        );
        assert!(matches!(
            *solver.prelude_state.lock().unwrap(),
            PreludeState::Consistent
        ));
        let again = cause(solver.is_sat(&bogus, &Substitution::new()));
        assert!(rejected(&again), "{again:?}");
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 3);

        let validity: Result<Result<Validity, SmtError>, StopCause> =
            cause(solver.check_predicates(&[], &Substitution::new(), &bogus));
        assert!(rejected(&validity), "{validity:?}");
        let model: Result<Result<ModelResult, SmtError>, StopCause> =
            cause(solver.get_model(&ModelQuery::for_solver_tests(&bogus, &Substitution::new())));
        assert!(rejected(&model), "{model:?}");
        // A query the solver reads still answers.
        assert_eq!(
            cause(solver.is_sat(&[], &Substitution::new())),
            Ok(Ok(Satisfiability::Sat))
        );
    }

    /// A model query whose script Z3 rejects is a failure too, and when it is the solver's first
    /// query the prelude is checked before the rejection is blamed on the query.
    #[test]
    fn a_rejected_model_query_checks_the_prelude_first() {
        let definition = unreadable_hook_definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let bogus = [Predicate::Term(term(
            &definition,
            r#"bogus{}(X:SortInt{}, \dv{SortInt{}}("0"))"#,
        ))];
        let model =
            cause(solver.get_model(&ModelQuery::for_solver_tests(&bogus, &Substitution::new())));
        assert!(
            matches!(model, Ok(Err(SmtError::MalformedScript { .. }))),
            "{model:?}"
        );
        assert!(matches!(
            *solver.prelude_state.lock().unwrap(),
            PreludeState::Consistent
        ));
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 1);
    }

    /// Whether each kind of query of `predicates` fails because Z3 rejects its script.
    fn every_query_is_rejected(solver: &Z3Solver, predicates: &[Predicate]) -> bool {
        fn rejected<T>(answer: Result<Result<T, SmtError>, StopCause>) -> bool {
            matches!(answer, Ok(Err(SmtError::MalformedScript { message })) if !message.is_empty())
        }
        rejected(cause(solver.is_sat(predicates, &Substitution::new())))
            && rejected(cause(solver.check_predicates(
                &[],
                &Substitution::new(),
                predicates,
            )))
            && rejected(cause(solver.get_model(&ModelQuery::for_solver_tests(
                predicates,
                &Substitution::new(),
            ))))
    }

    /// A script the translation wrote without any text of the definition or the user, here one
    /// naming a sort the prelude does not declare, is a defect of k-rust when Z3 rejects it: a
    /// debug build panics with Z3's message and the script, and a release build returns the
    /// typed failure.
    #[test]
    #[cfg_attr(
        debug_assertions,
        should_panic(
            expected = "Z3 rejected an SMT-LIB script k-rust's translation wrote by itself"
        )
    )]
    fn a_rejected_script_the_translation_wrote_by_itself_is_a_defect_of_k_rust() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let undeclared = Term::variable(Variable::new("U", Sort::simple("SortUndeclared")));
        assert!(every_query_is_rejected(
            &solver,
            &[Predicate::Equals(undeclared.clone(), undeclared)]
        ));
    }

    /// A rejection that text the translation did not write may cause is the definition's or the
    /// user's, and stays a typed failure in a debug build too: an `smtlib` function whose name
    /// is a name the query writes (the query's fresh `SMT-1` is redeclared), a user prelude
    /// (which declares that name itself), and a domain value whose text is no SMT-LIB literal,
    /// which the translation copies. An `smt-hook` Z3 does not have is the case of
    /// `a_query_z3_rejects_answers_nothing_and_is_not_cached`.
    #[test]
    fn a_rejection_of_text_the_translation_did_not_write_is_a_typed_failure() {
        let clashing = BackendDefinition::internalize(
            &parse_definition(
                r#"[]
                module MAIN
                    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                    symbol c{}() : SortInt{} [function{}(), total{}(), smtlib{}("|SMT-1|")]
                endmodule []"#,
            )
            .expect("definition should parse"),
            "MAIN",
        )
        .expect("definition should internalize");
        let solver = Z3Solver::new(&clashing).unwrap();
        assert!(every_query_is_rejected(&solver, &x_is_one()), "smtlib");

        let definition = definition();
        let solver = Z3Solver::with_prelude(&definition, "(declare-const SMT-1 Int)").unwrap();
        assert!(every_query_is_rejected(&solver, &x_is_one()), "prelude");

        let solver = Z3Solver::new(&definition).unwrap();
        let not_a_literal = [Predicate::Equals(
            Term::variable(x()),
            Term::raw_domain_value(Sort::simple("SortInt"), "one"),
        )];
        assert!(every_query_is_rejected(&solver, &not_a_literal), "literal");
    }

    /// K symbols that name one `smtlib` function with one SMT signature stand for one function,
    /// declared once, so the prelude loads.
    #[test]
    fn symbols_sharing_an_smtlib_function_declare_it_once() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol f{}(SortInt{}) : SortInt{} [function{}(), total{}(), smtlib{}("ff")]
                symbol g{}(SortInt{}) : SortInt{} [function{}(), total{}(), smtlib{}("ff")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        assert_eq!(
            solver
                .prelude
                .declarations()
                .iter()
                .filter(|declaration| declaration.as_str() == "(declare-fun ff (Int) Int)")
                .count(),
            1
        );
        assert_eq!(cause(solver.check_prelude()), Ok(()));
    }

    /// A query posed under a cancelled request stops with the cancellation before it reaches the
    /// cache or Z3, and records nothing about the prelude: it stays unchecked even when it is
    /// inconsistent, and the first check after the cancellation finds that.
    #[test]
    fn a_cancelled_query_stops_with_the_cancellation_and_leaves_the_prelude_unchecked() {
        let definition = definition();
        let solver = Z3Solver::with_prelude(&definition, INCONSISTENT_PRELUDE).unwrap();
        let token = CancellationToken::new();
        token.cancel();
        token.scope(|| {
            for (name, query) in queries() {
                assert_eq!(query(&solver), Err(StopCause::Cancelled), "{name}");
            }
            assert_eq!(cause(solver.check_prelude()), Err(StopCause::Cancelled));
        });
        assert!(matches!(
            *solver.prelude_state.lock().unwrap(),
            PreludeState::Unchecked
        ));
        assert_eq!(solver.prelude_signal.failure(), None);
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 0);
        assert_eq!(cause(solver.check_prelude()), Err(INCONSISTENT));
    }

    /// The step deadline belongs to the step that poses a query, so once it passed no answer can
    /// be used: the query returns the deadline's stop without running, and runs once the step
    /// that armed the deadline has ended.
    #[test]
    fn a_query_posed_after_the_step_deadline_stops_without_running() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let controller = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::ZERO),
            moving_average: false,
        });
        let deadline = Err(StopCause::Deadline(StepTimeoutMode::Manual(Duration::ZERO)));
        {
            let _step = controller.begin_step();
            for (name, query) in queries() {
                assert_eq!(query(&solver), deadline, "{name}");
            }
            assert_eq!(cause(solver.check_prelude()), deadline);
        }
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 0);
        assert!(matches!(
            *solver.prelude_state.lock().unwrap(),
            PreludeState::Unchecked
        ));
        assert_eq!(
            solver.is_sat(&x_is_one(), &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn extracts_arbitrary_precision_integer_and_boolean_models() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let integer = Variable::new("X", Sort::simple("SortInt"));
        let boolean = Variable::new("B", Sort::simple("SortBool"));
        let expected_integer = "-99999999999999999999999999999999999999";
        let predicates = [
            Predicate::Equals(
                Term::variable(integer.clone()),
                Term::raw_domain_value(Sort::simple("SortInt"), expected_integer),
            ),
            Predicate::Equals(
                Term::variable(boolean.clone()),
                Term::raw_domain_value(Sort::simple("SortBool"), "true"),
            ),
        ];

        let ModelResult::Sat(model) = cause(solver.get_model(&ModelQuery::for_solver_tests(
            &predicates,
            &Substitution::new(),
        )))
        .expect("the query should not stop")
        .expect("model should be extracted") else {
            panic!("constraints should be satisfiable")
        };

        assert_eq!(
            model.get(&integer),
            Some(&Term::raw_domain_value(
                Sort::simple("SortInt"),
                expected_integer
            ))
        );
        assert_eq!(
            model.get(&boolean),
            Some(&Term::raw_domain_value(Sort::simple("SortBool"), "true"))
        );
    }

    /// The model reader builds a value with the kind the definition gives its sort: an integer
    /// in canonical decimal (the solver's `(- 5)` is `-5`), the term `Term::int` builds; and at a
    /// `SortInt` the definition declares without domain values, which has no value to build, the
    /// variable is left as it is.
    #[test]
    fn model_values_are_built_with_the_kind_of_their_sort() {
        let integer = Variable::new("X", Sort::simple("SortInt"));
        let boolean = Variable::new("B", Sort::simple("SortBool"));
        let predicates = [
            Predicate::Equals(Term::variable(integer.clone()), Term::int(-5)),
            Predicate::Equals(Term::variable(boolean.clone()), Term::bool(true)),
        ];
        let model = |definition: &BackendDefinition| {
            let solver = Z3Solver::new(definition).unwrap();
            let ModelResult::Sat(model) = cause(solver.get_model(&ModelQuery::for_solver_tests(
                &predicates,
                &Substitution::new(),
            )))
            .expect("the query should not stop")
            .expect("model should be extracted") else {
                panic!("constraints should be satisfiable")
            };
            model
        };

        let hooked = model(&definition());
        assert_eq!(hooked.get(&integer), Some(&Term::int(-5)));
        assert_eq!(hooked.get(&boolean), Some(&Term::bool(true)));

        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} []
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            endmodule []"#,
        )
        .unwrap();
        let without_integers = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let unhooked = model(&without_integers);
        assert_eq!(
            unhooked.get(&integer),
            Some(&Term::variable(integer.clone()))
        );
        assert_eq!(unhooked.get(&boolean), Some(&Term::bool(true)));
    }

    #[test]
    fn model_results_distinguish_empty_unsatisfiable_and_untranslated_inputs() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();

        assert_eq!(
            solver.get_model(&ModelQuery::for_solver_tests(&[], &Substitution::new())),
            Ok(Ok(ModelResult::Sat(Substitution::new())))
        );

        let integer = Variable::new("X", Sort::simple("SortInt"));
        let integer_term = Term::variable(integer);
        assert_eq!(
            solver.get_model(&ModelQuery::for_solver_tests(
                &[
                    Predicate::Equals(
                        integer_term.clone(),
                        Term::raw_domain_value(Sort::simple("SortInt"), "1"),
                    ),
                    Predicate::Equals(
                        integer_term,
                        Term::raw_domain_value(Sort::simple("SortInt"), "2"),
                    ),
                ],
                &Substitution::new(),
            )),
            Ok(Ok(ModelResult::Unsat))
        );

        let opaque = Variable::new("Y", Sort::simple("SortS"));
        let opaque_term = Term::variable(opaque.clone());
        assert_eq!(
            solver.get_model(&ModelQuery::for_solver_tests(
                &[Predicate::Equals(opaque_term.clone(), opaque_term)],
                &Substitution::new(),
            )),
            Ok(Ok(ModelResult::Unknown(APPROXIMATE_MODEL_REASON.into())))
        );
    }

    #[test]
    fn reuses_conclusive_exact_scripts() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);
        let x_term = Term::variable(x());
        let one = Term::raw_domain_value(Sort::simple("SortInt"), "1");
        let two = Term::raw_domain_value(Sort::simple("SortInt"), "2");
        let satisfiable = [Predicate::Equals(x_term.clone(), one.clone())];
        let unsatisfiable = [
            Predicate::Equals(x_term.clone(), one),
            Predicate::Equals(x_term, two),
        ];

        for _ in 0..2 {
            assert_eq!(
                solver.is_sat(&satisfiable, &Substitution::new()),
                Ok(Ok(Satisfiability::Sat))
            );
            assert_eq!(
                solver.is_sat(&unsatisfiable, &Substitution::new()),
                Ok(Ok(Satisfiability::Unsat))
            );
        }

        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed) - baseline,
            2,
            "each distinct complete script should reach Z3 once"
        );
    }

    #[test]
    fn does_not_conflate_distinct_scripts() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);
        let x_term = Term::variable(x());
        let equals = |value| {
            [Predicate::Equals(
                x_term.clone(),
                Term::raw_domain_value(Sort::simple("SortInt"), value),
            )]
        };

        assert_eq!(
            solver.is_sat(&equals("1"), &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        assert_eq!(
            solver.is_sat(&equals("2"), &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        assert_eq!(
            solver.is_sat(&equals("1"), &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed) - baseline,
            2
        );
    }

    #[test]
    fn a_cancelled_query_stops_before_the_cache_and_z3() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let predicates = [Predicate::Equals(
            Term::variable(x()),
            Term::raw_domain_value(Sort::simple("SortInt"), "1"),
        )];
        assert_eq!(
            solver.is_sat(&predicates, &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);
        let token = CancellationToken::new();
        token.cancel();

        assert_eq!(
            cause(token.scope(|| solver.is_sat(&predicates, &Substitution::new()))),
            Err(StopCause::Cancelled)
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed),
            baseline
        );
        assert_eq!(
            solver.is_sat(&predicates, &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed),
            baseline
        );
    }

    #[test]
    fn result_cache_excludes_unknown_and_bounds_keys_by_fifo_order() {
        let mut cache = SolverResultCache::new(2, usize::MAX);
        cache.insert("A", &Satisfiability::Sat);
        cache.insert("B", &Satisfiability::Unsat);
        assert_eq!(cache.get("A"), Some(Satisfiability::Sat));
        cache.insert("C", &Satisfiability::Sat);

        assert_eq!(cache.get("A"), None, "hits must not refresh FIFO order");
        assert_eq!(cache.get("B"), Some(Satisfiability::Unsat));
        assert_eq!(cache.get("C"), Some(Satisfiability::Sat));

        cache.insert("unknown", &Satisfiability::Unknown("timeout".into()));
        assert_eq!(cache.get("unknown"), None);

        let mut byte_bounded = SolverResultCache::new(2, 2);
        byte_bounded.insert("abc", &Satisfiability::Sat);
        assert_eq!(byte_bounded.get("abc"), None);

        let mut cumulative_bytes = SolverResultCache::new(3, 5);
        cumulative_bytes.insert("aa", &Satisfiability::Sat);
        cumulative_bytes.insert("bbb", &Satisfiability::Unsat);
        cumulative_bytes.insert("cc", &Satisfiability::Sat);
        assert_eq!(cumulative_bytes.get("aa"), None);
        assert_eq!(cumulative_bytes.get("bbb"), Some(Satisfiability::Unsat));
        assert_eq!(cumulative_bytes.get("cc"), Some(Satisfiability::Sat));
        assert_eq!(cumulative_bytes.key_bytes, 5);

        cumulative_bytes.insert("dddd", &Satisfiability::Unsat);
        assert_eq!(cumulative_bytes.get("bbb"), None);
        assert_eq!(cumulative_bytes.get("cc"), None);
        assert_eq!(cumulative_bytes.get("dddd"), Some(Satisfiability::Unsat));
        assert_eq!(cumulative_bytes.key_bytes, 4);
    }

    #[test]
    fn clones_share_cached_results_and_remain_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Z3Solver>();

        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let predicates = [Predicate::Equals(
            Term::variable(x()),
            Term::raw_domain_value(Sort::simple("SortInt"), "1"),
        )];
        assert_eq!(
            solver.is_sat(&predicates, &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);
        let clone = solver.clone();

        assert_eq!(
            clone.is_sat(&predicates, &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed),
            baseline
        );
    }

    #[test]
    fn validity_subqueries_reuse_only_exact_scripts() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
        ))];
        for (substitution, expected) in [
            (Substitution::new(), Validity::Contingent),
            (
                Substitution::from([(x(), Term::raw_domain_value(Sort::simple("SortInt"), "5"))]),
                Validity::Valid,
            ),
            (
                Substitution::from([(x(), Term::raw_domain_value(Sort::simple("SortInt"), "15"))]),
                Validity::Refuted,
            ),
        ] {
            assert_eq!(
                solver.check_predicates(&[], &substitution, &checked),
                Ok(Ok(expected.clone()))
            );
            let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);
            assert_eq!(
                solver.check_predicates(&[], &substitution, &checked),
                Ok(Ok(expected))
            );
            assert_eq!(
                solver.uncached_solve_count.load(Ordering::Relaxed),
                baseline
            );
        }
    }

    #[test]
    fn adaptive_validity_has_explicit_27_case_table() {
        #[derive(Clone, Copy, Debug)]
        enum Outcome {
            Sat,
            Unsat,
            Unknown,
        }

        fn satisfiability(outcome: Outcome, reason: &str) -> Satisfiability {
            match outcome {
                Outcome::Sat => Satisfiability::Sat,
                Outcome::Unsat => Satisfiability::Unsat,
                Outcome::Unknown => Satisfiability::Unknown(reason.into()),
            }
        }

        fn legacy(
            base: Satisfiability,
            positive: Satisfiability,
            negative: Satisfiability,
        ) -> Validity {
            match base {
                Satisfiability::Unsat => return Validity::InconsistentGroundTruth,
                Satisfiability::Unknown(reason) => return Validity::Unknown(reason),
                Satisfiability::Sat => {}
            }
            let (positive, negative) = match (positive, negative) {
                (Satisfiability::Unsat, _) => (Satisfiability::Unsat, Satisfiability::Sat),
                (_, Satisfiability::Unsat) => (Satisfiability::Sat, Satisfiability::Unsat),
                results => results,
            };
            match (positive, negative) {
                (Satisfiability::Sat, Satisfiability::Unsat) => Validity::Valid,
                (Satisfiability::Unsat, Satisfiability::Sat) => Validity::Refuted,
                (Satisfiability::Sat, Satisfiability::Sat) => Validity::Contingent,
                (Satisfiability::Unsat, Satisfiability::Unsat) => Validity::InconsistentGroundTruth,
                (Satisfiability::Unknown(reason), _) | (_, Satisfiability::Unknown(reason)) => {
                    Validity::Unknown(reason)
                }
            }
        }

        let outcomes = [Outcome::Sat, Outcome::Unsat, Outcome::Unknown];
        let mut case_id = 0;
        let mut divergent_cases = Vec::new();
        for &base in &outcomes {
            for &positive in &outcomes {
                for &negative in &outcomes {
                    case_id += 1;
                    let fixed = |subquery| match subquery {
                        ValiditySubquery::Base => satisfiability(base, "base unknown"),
                        ValiditySubquery::Positive => satisfiability(positive, "positive unknown"),
                        ValiditySubquery::Negative => satisfiability(negative, "negative unknown"),
                    };
                    let expected = legacy(
                        fixed(ValiditySubquery::Base),
                        fixed(ValiditySubquery::Positive),
                        fixed(ValiditySubquery::Negative),
                    );
                    let mut queried = Vec::new();
                    let actual = decide_validity(|subquery| {
                        queried.push(subquery);
                        Ok(Ok::<_, SmtError>(fixed(subquery)))
                    })
                    .unwrap()
                    .unwrap();

                    if matches!(base, Outcome::Sat) || !matches!(positive, Outcome::Sat) {
                        assert_eq!(actual, expected, "{base:?}, {positive:?}, {negative:?}");
                    } else {
                        let stronger_result = match negative {
                            Outcome::Unsat => Validity::Valid,
                            Outcome::Sat => Validity::Contingent,
                            Outcome::Unknown => Validity::Unknown("negative unknown".into()),
                        };
                        assert_eq!(
                            actual, stronger_result,
                            "a satisfiable positive subquery proves the base satisfiable despite a conflicting or inconclusive base outcome"
                        );
                    }
                    if actual != expected {
                        divergent_cases.push(case_id);
                    }
                    let expected_queries = match (positive, base) {
                        (Outcome::Sat | Outcome::Unsat, _) => vec![
                            ValiditySubquery::Positive,
                            match positive {
                                Outcome::Sat => ValiditySubquery::Negative,
                                Outcome::Unsat => ValiditySubquery::Base,
                                Outcome::Unknown => unreachable!(),
                            },
                        ],
                        (Outcome::Unknown, Outcome::Sat) => vec![
                            ValiditySubquery::Positive,
                            ValiditySubquery::Base,
                            ValiditySubquery::Negative,
                        ],
                        (Outcome::Unknown, Outcome::Unsat | Outcome::Unknown) => {
                            vec![ValiditySubquery::Positive, ValiditySubquery::Base]
                        }
                    };
                    assert_eq!(
                        queried, expected_queries,
                        "{base:?}, {positive:?}, {negative:?}"
                    );
                }
            }
        }
        assert_eq!(divergent_cases, [10, 11, 12, 19, 20, 21]);
    }

    #[test]
    fn contingent_validity_uses_two_uncached_solver_queries() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
        ))];
        let query = solver
            .prelude
            .query(&[], &Substitution::new(), &checked, true)
            .unwrap();
        let checked_smt = query.checked().to_string();
        let positive_script = format!("{}\n(assert {checked_smt})", query.base());
        let negative_script = format!("{}\n(assert (not {checked_smt}))", query.base());
        let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);

        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), &checked),
            Ok(Ok(Validity::Contingent))
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed) - baseline,
            2,
            "a satisfiable positive query proves the base satisfiable"
        );
        let cache = solver
            .result_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        assert_eq!(cache.entries.len(), 2);
        assert!(cache.entries.contains_key(positive_script.as_str()));
        assert!(cache.entries.contains_key(negative_script.as_str()));
        assert!(!cache.entries.contains_key(query.base()));
    }

    #[test]
    fn refuted_validity_uses_positive_then_base() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
        ))];
        let substitution =
            Substitution::from([(x(), Term::raw_domain_value(Sort::simple("SortInt"), "15"))]);
        let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);

        assert_eq!(
            solver.check_predicates(&[], &substitution, &checked),
            Ok(Ok(Validity::Refuted))
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed) - baseline,
            3,
            "the first unsatisfiable query checks the prelude before solving the base"
        );
    }

    #[test]
    fn already_cancelled_validity_does_not_reach_z3_or_cache() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
        ))];
        let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);
        let token = CancellationToken::new();
        token.cancel();

        assert_eq!(
            cause(token.scope(|| solver.check_predicates(&[], &Substitution::new(), &checked))),
            Err(StopCause::Cancelled)
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed),
            baseline
        );
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), &checked),
            Ok(Ok(Validity::Contingent))
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed) - baseline,
            2,
            "the cancelled request must not populate either adaptive script"
        );
    }

    #[test]
    fn cached_satisfiability_does_not_replace_model_check() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let predicates = [Predicate::Equals(
            Term::variable(x()),
            Term::raw_domain_value(Sort::simple("SortInt"), "7"),
        )];
        assert_eq!(
            solver.is_sat(&predicates, &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );

        assert_eq!(
            solver.get_model(&ModelQuery::for_solver_tests(
                &predicates,
                &Substitution::new()
            )),
            Ok(Ok(ModelResult::Sat(Substitution::from([(
                x(),
                Term::raw_domain_value(Sort::simple("SortInt"), "7")
            )]))))
        );
    }

    /// The solver decides nothing about `^Int` or `^%Int` from a value where no integer is the
    /// power (a negative exponent of a base other than 1 and -1), and still decides what holds for
    /// the integer powers.
    #[test]
    fn decides_nothing_from_a_power_where_no_integer_is_its_value() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-symbol pow{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.pow"), smt-hook{}("^")]
                hooked-symbol powmod{}(SortInt{}, SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.powmod"), smt-hook{}("(mod (^ #1 #2) #3)")]
                hooked-symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.lt"), smt-hook{}("<")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let int = |value: &str| Term::raw_domain_value(Sort::simple("SortInt"), value);
        let less = |left: &str, right: &str| {
            Predicate::Term(term(&definition, &format!("lt{{}}({left}, {right})")))
        };
        let b = "B:SortInt{}";
        let dv = |value: i64| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
        let negative = less(b, &dv(0));
        let validity = |known: &[Predicate], checked: Predicate| {
            solver.check_predicates(known, &Substitution::new(), &[checked])
        };

        // For a negative exponent, Z3's power of 3 is a fraction, whose integer part modulo 7 is
        // 0, and its power of 2 is positive; neither is a K value, so neither is valid. Nested in
        // another power, whose template names its base more than once, it is still no value.
        for (known, checked) in [
            (
                vec![negative.clone()],
                Predicate::Equals(
                    term(
                        &definition,
                        &format!("powmod{{}}(pow{{}}({}, {b}), {}, {})", dv(3), dv(1), dv(7)),
                    ),
                    int("0"),
                ),
            ),
            (
                vec![negative.clone()],
                Predicate::Equals(
                    term(
                        &definition,
                        &format!("powmod{{}}({}, {b}, {})", dv(3), dv(7)),
                    ),
                    int("0"),
                ),
            ),
            (
                vec![negative.clone()],
                less(&dv(0), &format!("pow{{}}({}, {b})", dv(2))),
            ),
            (
                Vec::new(),
                Predicate::Equals(
                    term(
                        &definition,
                        &format!("powmod{{}}({}, {}, {})", dv(2), dv(-1), dv(7)),
                    ),
                    int("0"),
                ),
            ),
        ] {
            assert_eq!(
                validity(&known, checked.clone()),
                Ok(Ok(Validity::Contingent)),
                "{checked:?} under {known:?}"
            );
        }
        // Where an integer is the power, the solver still reads it: a nonnegative exponent, and a
        // base of magnitude 1 with any exponent.
        let nonnegative = Predicate::Not(Arc::new(negative));
        for (known, checked) in [
            (
                vec![nonnegative.clone()],
                less(
                    &dv(0),
                    &format!("pow{{}}(pow{{}}({}, {b}), {})", dv(2), dv(2)),
                ),
            ),
            (
                Vec::new(),
                Predicate::Equals(
                    term(
                        &definition,
                        &format!("pow{{}}(pow{{}}({}, {b}), {b})", dv(1)),
                    ),
                    int("1"),
                ),
            ),
            (
                vec![nonnegative],
                less(&dv(0), &format!("pow{{}}({}, {b})", dv(2))),
            ),
            (
                Vec::new(),
                Predicate::Equals(
                    term(&definition, &format!("pow{{}}({}, {})", dv(1), dv(-1))),
                    int("1"),
                ),
            ),
            (
                Vec::new(),
                Predicate::Equals(
                    term(&definition, &format!("pow{{}}({}, {})", dv(-1), dv(-3))),
                    int("-1"),
                ),
            ),
            // `X ^Int 0` is 1 for every integer `X`, 0 included.
            (
                Vec::new(),
                Predicate::Equals(
                    term(&definition, &format!("pow{{}}({b}, {})", dv(0))),
                    int("1"),
                ),
            ),
            (
                Vec::new(),
                Predicate::Equals(
                    term(&definition, &format!("pow{{}}({}, {})", dv(0), dv(0))),
                    int("1"),
                ),
            ),
        ] {
            assert_eq!(
                validity(&known, checked.clone()),
                Ok(Ok(Validity::Valid)),
                "{checked:?} under {known:?}"
            );
        }
    }

    /// A definition whose `Float`, `MInt{8}` and renamed-`Int` operations carry the `smt-hook`s
    /// `domains.md` gives them (and `fg.gt`, which names no SMT-LIB function): the solver
    /// interprets none of these sorts.
    fn uninterpreted_sort_hook_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortFloat{} [hook{}("FLOAT.Float"), hasDomainValues{}()]
                hooked-sort SortMInt{S} [hook{}("MINT.MInt"), hasDomainValues{}()]
                sort Sort8{} []
                hooked-sort SortMyInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol ltInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}(">")]
                symbol isNaN{}(SortFloat{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("fp.isNaN")]
                symbol gtFloat{}(SortFloat{}, SortFloat{}) : SortBool{}
                    [function{}(), smt-hook{}("fg.gt")]
                symbol ultMInt{}(SortMInt{Sort8{}}, SortMInt{Sort8{}}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("bvult")]
                symbol eqMInt{}(SortMInt{Sort8{}}, SortMInt{Sort8{}}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("=")]
                symbol int2MInt{}(SortInt{}) : SortMInt{Sort8{}}
                    [function{}(), total{}(), smt-hook{}("int2bv")]
                symbol mint2Unsigned{}(SortMInt{Sort8{}}) : SortInt{}
                    [function{}(), total{}(), smt-hook{}("bv2int")]
                symbol addMyInt{}(SortMyInt{}, SortMyInt{}) : SortMyInt{}
                    [function{}(), total{}(), smt-hook{}("+")]
                symbol gtMyInt{}(SortMyInt{}, SortMyInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}(">")]
                symbol iteK{S}(SortBool{}, S, S) : S
                    [function{}(), total{}(), smt-hook{}("ite")]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// An atom over a sort the solver does not interpret is an opaque Boolean, so the `Int`
    /// facts beside it stay decidable: `X >Int 5 ∧ X <Int 3` is refuted whatever the atom says,
    /// and `X >Int 5` still implies `X >Int 4` beside it.
    #[test]
    fn hooks_over_uninterpreted_sorts_leave_the_int_facts_decidable() {
        let definition = uninterpreted_sort_hook_definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let fact = |source: &str| Predicate::Term(term(&definition, source));
        let above = |bound: &str| {
            fact(&format!(
                r#"gtInt{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("{bound}"))"#
            ))
        };
        let below_three = fact(r#"ltInt{}(X:SortInt{}, \dv{SortInt{}}("3"))"#);
        for atom in [
            "isNaN{}(F:SortFloat{})",
            "gtFloat{}(F:SortFloat{}, G:SortFloat{})",
            "ultMInt{}(A:SortMInt{Sort8{}}, B:SortMInt{Sort8{}})",
            "eqMInt{}(int2MInt{}(X:SortInt{}), int2MInt{}(Y:SortInt{}))",
            "gtMyInt{}(addMyInt{}(M:SortMyInt{}, N:SortMyInt{}), M:SortMyInt{})",
            r#"eqMInt{}(iteK{SortMInt{Sort8{}}}(C:SortBool{}, A:SortMInt{Sort8{}}, B:SortMInt{Sort8{}}), A:SortMInt{Sort8{}})"#,
        ] {
            let atom = fact(atom);
            assert_eq!(
                cause(solver.is_sat(
                    &[atom.clone(), above("5"), below_three.clone()],
                    &Substitution::new()
                )),
                Ok(Ok(Satisfiability::Unsat)),
                "{atom:?}"
            );
            assert_eq!(
                cause(solver.check_predicates(
                    &[atom.clone(), above("5")],
                    &Substitution::new(),
                    &[above("4")]
                )),
                Ok(Ok(Validity::Valid)),
                "{atom:?}"
            );
            assert_eq!(
                cause(solver.is_sat(std::slice::from_ref(&atom), &Substitution::new())),
                Ok(Ok(Satisfiability::Sat)),
                "{atom:?}"
            );
        }
    }

    /// `MInt2Unsigned(Int2MInt(X)) <Int 0` holds of no 8-bit machine integer, but the solver
    /// does not interpret `MInt`, so it reads the `MInt2Unsigned` value as an unconstrained
    /// integer: the query is `Sat` of an approximate translation, which shows no K valuation, so
    /// no model is returned for it.
    #[test]
    fn an_int_over_a_machine_integer_has_no_model_as_a_k_valuation() {
        let definition = uninterpreted_sort_hook_definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let negative = Predicate::Term(term(
            &definition,
            r#"ltInt{}(mint2Unsigned{}(int2MInt{}(X:SortInt{})), \dv{SortInt{}}("0"))"#,
        ));
        assert_eq!(
            crate::smt::translation_exactness(std::slice::from_ref(&negative)),
            crate::smt::Exactness::Approximate
        );
        assert_eq!(
            cause(solver.is_sat(std::slice::from_ref(&negative), &Substitution::new())),
            Ok(Ok(Satisfiability::Sat))
        );
        assert_eq!(
            cause(solver.get_model(&ModelQuery::for_solver_tests(
                &[negative],
                &Substitution::new()
            ))),
            Ok(Ok(ModelResult::Unknown(APPROXIMATE_MODEL_REASON.into())))
        );
    }

    /// The `requires` `2 ^Int X ==Int 3` of a rule, as the backend writes it for Z3. It is
    /// satisfiable (`X = -1`, with the power outside the integers equal to 3), and Z3 either
    /// decides it in a few thousand resource units or takes a path on which it never decides it;
    /// which path it takes depends on everything the Z3 context it runs in has seen.
    const PATH_SENSITIVE_QUERY: &str = r#"(declare-sort |SortFloat| 0)
(declare-sort |SortGeneratedCounterCell| 0)
(declare-sort |SortGeneratedCounterCellOpt| 0)
(declare-sort |SortGeneratedTopCell| 0)
(declare-sort |SortGeneratedTopCellFragment| 0)
(declare-sort |SortK| 0)
(declare-sort |SortKCell| 0)
(declare-sort |SortKCellOpt| 0)
(declare-sort |SortKConfigVar| 0)
(declare-sort |SortKItem| 0)
(declare-sort |SortList| 0)
(declare-sort |SortMInt| 1)
(declare-sort |SortMap| 0)
(declare-sort |SortPgm| 0)
(declare-sort |SortSet| 0)
(declare-sort |SortString| 0)
(declare-fun |KRUST-POWER-OUTSIDE-THE-INTEGERS| (Int Int) Real)
(declare-fun smt_seq_nil () |SortList|)
(declare-fun notInt (Int) Int)
(declare-fun smt_seq_concat (|SortList| |SortList|) |SortList|)
(declare-fun xorInt (Int Int) Int)
(declare-fun shrInt (Int Int) Int)
(declare-fun shlInt (Int Int) Int)
(declare-fun andInt (Int Int) Int)
(declare-fun orInt (Int Int) Int)
(declare-fun smt_seq_elem (|SortKItem|) |SortList|)
(declare-fun smt_seq_len (|SortList|) Int)
(assert (forall ((KRUST-COLLECTION |SortList|)) (>= (smt_seq_len KRUST-COLLECTION) 0)))
(declare-const SMT-2 Int)
(declare-const SMT-1 Bool)
(assert (and SMT-1 (= (ite (or (>= SMT-2 0) (= 2 1) (= 2 (- 1))) (^ 2 SMT-2) (|KRUST-POWER-OUTSIDE-THE-INTEGERS| 2 SMT-2)) 3)))"#;

    /// A clock-free attempt limit about thirty times what the decided path of
    /// [`PATH_SENSITIVE_QUERY`] consumes (under 1,000 units), so that only the path decides the
    /// answer.
    const PATH_SENSITIVE_OPTIONS: Z3Options = Z3Options {
        timeout_ms: 125,
        retry_limit: 0,
        resource_limit: NonZeroU32::new(20_000),
    };

    /// A nonlinear integer query Z3 does not decide within [`PATH_SENSITIVE_OPTIONS`]: one such
    /// check on a context is enough to change the path Z3 later takes on
    /// [`PATH_SENSITIVE_QUERY`] there.
    const NONLINEAR_QUERY: &str = "(declare-const x Int)\n(declare-const y Int)\n\
        (declare-const z Int)\n(assert (> x 1))\n(assert (> y 1))\n(assert (> z 1))\n\
        (assert (= (+ (* x x x) (* y y y)) (* z z z)))";

    /// The answers of `count` uncached checks of `script` by `solver`, as `S`, `U` or `?`.
    fn answers(solver: &Z3Solver, script: &str, count: usize) -> String {
        (0..count)
            .map(|_| match cause(solver.solve_uncached(script)) {
                Ok(Ok(Satisfiability::Sat)) => 'S',
                Ok(Ok(Satisfiability::Unsat)) => 'U',
                Ok(Ok(Satisfiability::Unknown(_))) => '?',
                other => panic!("{other:?}"),
            })
            .collect()
    }

    /// The answers of `count` checks of `script` on the thread's own Z3 context, by another Z3
    /// user than the backend (checked sort inference, say), as `S`, `U` or `?`, each with the
    /// resource limit of [`PATH_SENSITIVE_OPTIONS`].
    fn thread_context_answers(script: &str, count: usize) -> String {
        (0..count)
            .map(|_| {
                let solver = Solver::new();
                let mut parameters = Params::new();
                parameters.set_u32(
                    "rlimit",
                    PATH_SENSITIVE_OPTIONS.resource_limit.unwrap().get(),
                );
                solver.set_params(&parameters);
                solver.from_string(script);
                match solver.check() {
                    SatResult::Sat => 'S',
                    SatResult::Unsat => 'U',
                    SatResult::Unknown => '?',
                }
            })
            .collect()
    }

    /// A query's answer is a function of the query and the attempt's limit: it is the same on a
    /// fresh thread, after unrelated Z3 work on the thread's own context (checked sort inference
    /// runs there), and on every repetition, so two runs of one request, in one process or in
    /// two, decide it alike.
    #[test]
    fn an_answer_does_not_depend_on_earlier_z3_work_on_the_thread() {
        let run = |unrelated: bool| {
            std::thread::spawn(move || {
                if unrelated {
                    assert_eq!(thread_context_answers(NONLINEAR_QUERY, 1), "?");
                }
                let solver = Z3Solver::with_options(&definition(), PATH_SENSITIVE_OPTIONS).unwrap();
                answers(&solver, PATH_SENSITIVE_QUERY, 10)
            })
            .join()
            .unwrap()
        };
        let fresh = run(false);
        assert_eq!(fresh, "S".repeat(10));
        assert_eq!(run(true), fresh);
    }

    /// The backend's queries leave the thread's own Z3 context as they found it, so another Z3
    /// user on the thread answers as it would had the backend never run.
    #[test]
    fn backend_queries_do_not_change_another_z3_users_answers_on_the_thread() {
        let run = |backend: bool| {
            std::thread::spawn(move || {
                if backend {
                    let solver =
                        Z3Solver::with_options(&definition(), PATH_SENSITIVE_OPTIONS).unwrap();
                    assert_eq!(answers(&solver, NONLINEAR_QUERY, 1), "?");
                }
                thread_context_answers(PATH_SENSITIVE_QUERY, 10)
            })
            .join()
            .unwrap()
        };
        let fresh = run(false);
        assert_eq!(fresh, "S".repeat(10));
        assert_eq!(run(true), fresh);
    }

    /// The feasibility check `H *Int I ==Int 2021027 andBool 1 <Int H andBool H <Int I` of a
    /// rule, as the backend writes it for Z3. It is satisfiable (`2021027 = 1009 * 2003`), and the
    /// path Z3 takes on it from a fresh context does not decide it.
    const FACTORING_QUERY: &str = r#"(declare-sort |SortACell| 0)
(declare-sort |SortACellOpt| 0)
(declare-sort |SortBCell| 0)
(declare-sort |SortBCellOpt| 0)
(declare-sort |SortCCell| 0)
(declare-sort |SortCCellOpt| 0)
(declare-sort |SortDCell| 0)
(declare-sort |SortDCellOpt| 0)
(declare-sort |SortECell| 0)
(declare-sort |SortECellOpt| 0)
(declare-sort |SortFCell| 0)
(declare-sort |SortFCellOpt| 0)
(declare-sort |SortGCell| 0)
(declare-sort |SortGCellOpt| 0)
(declare-sort |SortGeneratedCounterCell| 0)
(declare-sort |SortGeneratedTopCell| 0)
(declare-sort |SortGeneratedTopCellFragment| 0)
(declare-sort |SortHCell| 0)
(declare-sort |SortHCellOpt| 0)
(declare-sort |SortICell| 0)
(declare-sort |SortICellOpt| 0)
(declare-sort |SortK| 0)
(declare-sort |SortKCell| 0)
(declare-sort |SortKCellOpt| 0)
(declare-sort |SortKConfigVar| 0)
(declare-sort |SortKItem| 0)
(declare-sort |SortList| 0)
(declare-sort |SortMInt| 1)
(declare-sort |SortMap| 0)
(declare-sort |SortPgm| 0)
(declare-sort |SortSet| 0)
(declare-fun |KRUST-POWER-OUTSIDE-THE-INTEGERS| (Int Int) Real)
(declare-fun smt_seq_nil () |SortList|)
(declare-fun notInt (Int) Int)
(declare-fun smt_seq_concat (|SortList| |SortList|) |SortList|)
(declare-fun xorInt (Int Int) Int)
(declare-fun shrInt (Int Int) Int)
(declare-fun shlInt (Int Int) Int)
(declare-fun andInt (Int Int) Int)
(declare-fun orInt (Int Int) Int)
(declare-fun smt_seq_elem (|SortKItem|) |SortList|)
(declare-fun smt_seq_len (|SortList|) Int)
(assert (forall ((KRUST-COLLECTION |SortList|)) (>= (smt_seq_len KRUST-COLLECTION) 0)))
(declare-const SMT-1 Int)
(declare-const SMT-2 Int)
(assert (and (= (* SMT-1 SMT-2) 2021027) (< 1 SMT-1) (< SMT-1 SMT-2)))"#;

    /// A query's retries run on the context its earlier attempts left, so a retry takes another
    /// path than theirs. The answer is still the query's own: equal on a fresh thread and after
    /// unrelated Z3 work, on every Z3 version. Which answers those are depends on the version:
    /// with Z3 4.16.0 the factoring check is undecided by one attempt of 1,000,000 units on a
    /// fresh context, and decided within three attempts of 250,000, 500,000 and 1,000,000 (4.12.5
    /// decides it within neither).
    #[test]
    fn a_retry_starts_from_the_querys_earlier_attempts() {
        let options = |resource_limit: u32, retry_limit: u32| Z3Options {
            timeout_ms: 125,
            retry_limit,
            resource_limit: NonZeroU32::new(resource_limit),
        };
        let run = |options: Z3Options, unrelated: bool| {
            std::thread::spawn(move || {
                if unrelated {
                    assert_eq!(thread_context_answers(NONLINEAR_QUERY, 1), "?");
                }
                let solver = Z3Solver::with_options(&definition(), options).unwrap();
                answers(&solver, FACTORING_QUERY, 1)
            })
            .join()
            .unwrap()
        };
        let single = run(options(1_000_000, 0), false);
        let retried = run(options(250_000, 2), false);
        assert_eq!(run(options(1_000_000, 0), true), single);
        assert_eq!(run(options(250_000, 2), true), retried);
        if z3_version().starts_with("Z3 4.16.0") {
            assert_eq!((single.as_str(), retried.as_str()), ("?", "S"));
        }
    }

    /// A panic inside a query reaches its caller, and leaves the thread on the Z3 context it was
    /// on before the query, not on the query's own.
    #[test]
    fn a_panic_inside_a_query_restores_the_threads_context() {
        std::thread::spawn(|| {
            // The address of the thread's context, which the query must not hold.
            let before = z3::Context::thread_local().get_z3_context().as_ptr() as usize;
            let caught = std::panic::catch_unwind(|| {
                on_own_context(|| {
                    let solver = Solver::new();
                    assert_ne!(
                        solver.get_context().get_z3_context().as_ptr() as usize,
                        before
                    );
                    panic!("a query panics");
                })
            });
            let payload = caught.expect_err("the panic reaches the caller");
            assert_eq!(payload.downcast_ref::<&str>(), Some(&"a query panics"));
            assert_eq!(
                z3::Context::thread_local().get_z3_context().as_ptr() as usize,
                before
            );
            assert_eq!(thread_context_answers(PATH_SENSITIVE_QUERY, 1), "S");
        })
        .join()
        .unwrap();
    }
}
