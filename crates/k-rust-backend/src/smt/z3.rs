//! ```toml algorithm
//! id = "backend.smt.cache"
//! name = "bounded decided-answer reuse before preparation and over SMT scripts"
//! sites = ["Z3Solver::solve", "SolverResultCache::get", "SolverResultCache::insert", "Z3Solver::solve_uncached", "SolverResultCache", "Z3Solver::solve_model", "Z3Solver::confirm_answer", "Z3Solver::check_prelude", "Z3Solver::typed_answer", "Z3Solver::remember_typed"]
//! variable = "e = entries evicted; E = cached entries; L = script length in bytes; W = bounded typed-input comparison or admission work; G = retained key-graph charge"
//! counters = ["SmtQueries", "SmtSolverRuns", "SmtRlimitCount", "SmtTypedCacheHits", "SmtTypedCacheMisses", "SmtPreparedQueries"]
//! span = "per call"
//! invariant = "Typed entries belong to one immutable solver/prelude and are compared in full under their query kind and evaluation context. Only decided answers are retained, with FIFO entry and graph-retention limits. The lower script cache retains its independent entry and key-byte limits. Stops, failures, Unknown and models are never typed-cache answers."
//!
//! [[cost]]
//! mode = "script cache hit"
//! bound = "O(L x log E) for the key comparison, after an O(L) copy of the base script in solve_query"
//!
//! [[cost]]
//! mode = "cache insertion"
//! bound = "O(e) evictions for e oldest entries removed to satisfy both limits"
//!
//! [[cost]]
//! mode = "typed-input lookup and admission"
//! bound = "A fixed-size syntactic-prefix fingerprint, then at most E full structural comparisons, each limited to W=32768 work units and visiting shared term pairs once. A miss uses ordinary preparation. Decided-answer insertion walks distinct term nodes, variable supports, payloads and collection-size bounds before cloning; W and a 4-MiB per-entry retention charge bound admission. At most 256 entries and 64 MiB of conservative graph charge are retained; shared graphs between entries are overcharged. Eviction drops e key graphs, whose retained total is bounded by G."
//!
//! [[cost]]
//! mode = "prelude consistency"
//! bound = "zero checks after a sat query; otherwise at most one prelude check, with configured retries, before the first unsat answer or rejected script"
//! ```
//!
//! Decided typed-input answers are reused before preparation; nontrivial model requests translate
//! and solve afresh. The typed cache belongs to the solver's immutable prelude, is shared only
//! by its clones, and separates query kind, evaluation mode and console context. Oversized or
//! foreign-metadata keys decline admission. Cancellation and prelude failure precede hits.
//!
//! In-process Z3 also retains the bounded FIFO script result cache: `Counter::SmtQueries` in,
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
//! name = "bounded sufficient proof attempt and Z3 satisfiability check"
//! sites = ["measured_check", "Z3Solver::solve_uncached", "Z3Solver::solve_model", "Z3Solver::check_predicates_inner", "Z3Solver::prove_with_observation_aliases"]
//! variable = "R = Z3 resource-limit units consumed by one check"
//! counters = ["SmtSolverRuns", "SmtRlimitCount", "SmtOpaqueAtomDomains", "SmtLemmasLeftOut"]
//! span = "per call"
//! invariant = "the rlimit delta is read around each check from the cumulative statistics of its context"
//!
//! [[cost]]
//! mode = "solver check"
//! bound = "O(R) solver work as reported by Z3"
//!
//! [[cost]]
//! mode = "atom domains in the translation"
//! bound = "Each atom's operands carry their domains (GAP K15): a ceil_free operand costs one stored-bit read and adds nothing; any other is read through the per-node domain memo of its predicate's lexical scope, one let per distinct non-ceil_free node per scope, each of size 1 + arity + its own condition (a domain-function application, an opaque atom, or a ceil-equation instance over argument references). An operand stated defined by a sibling ceil conjunct, a known ceil, or as a child within its parent's domain adds nothing. Preparation plans each distinct node once within its 16384-work budget. A quantifier's body has its own scope, which holds the domains and values of the nodes that mention its variable; any other node is named once, in the scope of its own variables, however many binders read it (GAP K23). Decided-domain links to a head's domain function are asserted only when the query reads that function as an undecided domain."
//!
//! [[cost]]
//! mode = "positive map-context sufficient proof"
//! bound = "At most 4096 graph/structural-comparison work units and 32 sufficient goals per attempt. The sufficient conjunction is checked once, then at most 32 independent goals on failure, each using the ordinary typed cache and query preparation/solver path, including both original map domains. Common pure source-owned contexts are removed without entering scalar observations, binders or negative contexts. Residual map goals cannot repeat a removed context plan. Unless the conjunction or every independent goal is Valid, fall back to the original query; no model uses the attempt."
//!
//! [[cost]]
//! mode = "source scalar guard partitions during preparation"
//! bound = "The definition-local catalog shares its 16384-work allowance across at most 128 specializations, 64 rows and depth 64. Reading Boolean DAG guards and taking Shannon cofactors charge each node visit and child handle; guards are not eagerly expanded to DNF. Structural source-atom comparisons and matching/domain-plan costs remain additional work. Exhaustion refuses the summary and retains ordinary conservative translation."
//!
//! [[cost]]
//! mode = "observation aliases after Unknown"
//! bound = "At most 4096 predicate/term discovery and expanded preflight visits, plus the existing observation builder's 16384-work/depth limits and structural comparisons on bounded expanded inputs. At most 16 ordinary validity checks prove both domains and a candidate equality; at most eight equality facts enter a request-local known vector. One fresh check of the unchanged exhausted query must be Valid. Auxiliary, augmented and congruence checks disable alias discovery explicitly, so candidates cannot recreate their own proof attempt. No model or global source catalog uses these facts. Failed trials retain the original Unknown; stops propagate."
//! ```

#![deny(clippy::wildcard_enum_match_arm)]

#[cfg(test)]
mod alias_tests;
#[cfg(test)]
mod fault_tests;
pub mod trace;
mod typed_cache;

use std::num::NonZeroU32;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    ffi::CStr,
    str::FromStr,
    sync::{Arc, Mutex},
    time::{Duration, Instant},
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

/// The resource units `solver`'s context has consumed so far: Z3 counts them per context, across
/// its solvers' checks.
fn rlimit_count(solver: &Solver) -> u64 {
    match solver.get_statistics().value("rlimit count") {
        Some(z3::StatisticsValue::UInt(value)) => u64::from(value),
        _ => 0,
    }
}

/// What one check answered and, when observed, the resource units and the wall time it took.
struct Checked {
    result: SatResult,
    rlimit_used: Option<u64>,
    wall: Option<Duration>,
}

/// Check `solver`, observing the resource units and the time the check takes when `observe` is
/// set or the build measures its work. The observation reads the context's statistics before and
/// after the check: it copies counters out and adds nothing the search reads.
fn measured_check(solver: &Solver, observe: bool) -> Checked {
    let observe = observe || cfg!(feature = "measure");
    let before = observe.then(|| rlimit_count(solver));
    let started = observe.then(Instant::now);
    let result = {
        let _span = measure::algorithm_span(Algorithm::BackendSmtCheck);
        solver.check()
    };
    let wall = started.map(|started| started.elapsed());
    let rlimit_used = before.map(|before| rlimit_count(solver).saturating_sub(before));
    #[cfg(feature = "measure")]
    if let Some(used) = rlimit_used {
        measure::add(Counter::SmtRlimitCount, used);
    }
    Checked {
        result,
        rlimit_used,
        wall,
    }
}

/// An attempt whose check answered: its solver, still on the attempt's context, and the check's
/// answer. With the SMT trace on, the attempt's in-flight script stays on disk until this is
/// dropped, so a caller holds it while Z3 still works on the attempt (reading a model, say).
struct Attempted {
    solver: Solver,
    checked: Checked,
    _traced: Option<trace::Answered>,
}

/// The assertions of a query's script, as its first attempt loaded them into the query's Z3
/// context (`None` before that attempt).
type Loaded = Option<Vec<Bool>>;

/// Run attempt `attempt` of `script`, with `limit`, on the thread's current Z3 context: a fresh
/// solver with the attempt's parameters, holding the script's assertions, checked. With the SMT
/// trace on ([`trace`]), the script is on disk before Z3 reads it and the attempt is recorded
/// after its check; `observe` asks for the check's resource units and time without the trace.
///
/// The first attempt loads the script, and `loaded` keeps the assertions it added; a later one
/// asserts those, the terms of the context the script's parse made. A script's declarations and
/// definitions belong to the context, not to the solver, so a later attempt does not read the
/// script again: Z3 5.3.3 refuses a second `define-fun-rec` of a function its context already
/// defines (`recursive function f already defined`), which would turn every retry of a script
/// with a recursive definition into a rejected script.
fn run_attempt(
    script: &str,
    loaded: &mut Loaded,
    ladder: &Ladder,
    attempt: u32,
    limit: AttemptLimit,
    observe: bool,
) -> Result<Attempted, RejectedScript> {
    let solver = Solver::new();
    solver.set_params(&parameters(limit));
    let traced = trace::Attempt::begin(script, ladder, attempt, limit);
    match loaded {
        Some(assertions) => {
            for assertion in assertions.iter() {
                solver.assert(assertion);
            }
        }
        None => {
            if let Err(rejected) = load(&solver, script) {
                if let Some(traced) = traced {
                    traced.rejected(&rejected);
                }
                return Err(rejected);
            }
            *loaded = Some(solver.get_assertions());
        }
    }
    let checked = measured_check(&solver, observe || traced.is_some());
    let traced = traced.map(|traced| traced.finish(&solver, &checked));
    Ok(Attempted {
        solver,
        checked,
        _traced: traced,
    })
}

/// Why Z3 did not load a script: its own message, or the reason the script never reached it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct RejectedScript {
    message: String,
}

/// Why a script got no answer from Z3: Z3 rejected it, or an attempt met an internal error of
/// Z3 ([`internal_error`]), whose text this is.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Unanswered {
    Rejected(RejectedScript),
    Fault(String),
}

/// Whether `reason`, Z3's reason for an unknown answer, is an internal error of Z3.
///
/// Z3 4.16.0 raises an internal error (an `UNREACHABLE`, `VERIFY` or `NOT_IMPLEMENTED_YET` it
/// reached, or a fatal error) as an exception on a context made through its API
/// (`invoke_exit_action`); the check catches it and answers unknown, with the exception's text,
/// `unreachable`, `internal fatal` or `not implemented yet`, as its reason. Z3 4.12.5 ends the
/// process instead (`UNREACHABLE` with exit status 114), which nothing in the process observes.
/// Both versions raise `formula has not been simplified` (4.16.0 followed by ` : ` and the
/// formula) where the search's internalizer meets a core operator its callers must have
/// rewritten, the same broken precondition as the bit-vector theory's `UNREACHABLE` on a
/// `bvult` (`word::internalized_operators`). The operators differ by version: `=>` only on
/// 4.12.5 (4.16.0 internalizes it), `distinct` on both, and `=` over Bool or `xor` with more
/// than two operands on both.
///
/// Such an answer is no undecided query: an unknown says the solver ran within its bounds, and
/// the retries exist to spend more of them on it; this is a defect of the solver met on the
/// query. So the query's attempts end there, and its failure is the solver's
/// (`SmtError::SolverFault`), which a consumer does not answer with more budget. The answer of a
/// retry would not be unsound for the error: the attempts share the Z3 context's terms and
/// declarations, each on a fresh solver, and the error unwinds the solver it interrupted as an
/// exception, as the cancellation of a check does, and the attempt drops that solver.
///
/// Z3 records the exception's text only when no event cancelled the check: it keeps the reason
/// of the event that did (`timeout` for its timer, `interrupted`) over the exception's
/// (`check_sat_result::set_reason_unknown`). So under a clock, an internal error met after the
/// timer fired reads as a timeout, and is retried as one; under [`Z3Options::resource_limit`]
/// alone, which cancels through no event, it reads as itself.
fn internal_error(reason: &str) -> bool {
    matches!(
        reason,
        "unreachable" | "internal fatal" | "not implemented yet"
    ) || reason.starts_with("formula has not been simplified")
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
/// that never decides the query: of 200 traced queries of a Game Boy CPU specification's proofs,
/// Z3 4.16.0 decided 177 within 310,000 units and 3 retries, 52 of them at an attempt whose limit
/// one attempt from a fresh context does not decide them within. The answer is then a function of
/// the script, the attempts' parameters and the Z3 library only, as it is for the first query a
/// process asks on a thread.
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

/// One attempt's wall-clock timeout (`None`: no clock) and resource limit (0: none).
pub(crate) type AttemptLimit = (Option<u32>, u32);

/// A query's attempt ladder: its options, and whether Z3's clock bounds its attempts.
#[derive(Clone, Copy, Debug)]
struct Ladder {
    options: Z3Options,
    clocked: bool,
}

impl Ladder {
    /// The limits of the attempt numbered `attempt` (0 first) whose clocked timeout is
    /// `timeout`: the timeout and its resource limit, or under [`Z3Options::resource_limit`]
    /// that limit doubled per retry and no timeout.
    fn limit(&self, timeout: u32, attempt: u32) -> AttemptLimit {
        match self.options.resource_limit {
            Some(units) => {
                let scale = 1_u32.checked_shl(attempt).unwrap_or(u32::MAX);
                (None, units.get().saturating_mul(scale))
            }
            None => (self.clocked.then_some(timeout), resource_limit(timeout)),
        }
    }
}

/// The Z3 parameters of an attempt with `limit`.
fn parameters((clock, units): AttemptLimit) -> Params {
    let mut parameters = Params::new();
    parameters.set_u32("rlimit", units);
    if let Some(timeout) = clock {
        parameters.set_u32("timeout", timeout);
    }
    parameters
}

#[derive(Clone, Debug)]
pub struct Z3Solver {
    prelude: SmtPrelude,
    options: Z3Options,
    /// The kinds the definition gives `SortInt` and `SortBool`, with which a model's values of
    /// those sorts are built; a sort the definition gives no kind has no values to build.
    model_kinds: ModelKinds,
    result_cache: Arc<Mutex<SolverResultCache>>,
    typed_cache: Arc<Mutex<typed_cache::Cache>>,
    #[cfg(test)]
    preparation_count: Arc<AtomicUsize>,
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
            typed_cache: Arc::new(Mutex::new(typed_cache::Cache::new(
                typed_cache::ENTRY_LIMIT,
                typed_cache::RETENTION_LIMIT,
            ))),
            #[cfg(test)]
            preparation_count: Arc::new(AtomicUsize::new(0)),
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

    /// This solver's attempt ladder.
    fn ladder(&self) -> Ladder {
        #[cfg(test)]
        let clocked = !self.without_clock;
        #[cfg(not(test))]
        let clocked = true;
        Ladder {
            options: self.options,
            clocked,
        }
    }

    /// The limits of the attempt numbered `attempt` (0 first) with the given timeout
    /// ([`Ladder::limit`]); a test build records them.
    fn attempt_limit(&self, ladder: &Ladder, timeout: u32, attempt: u32) -> AttemptLimit {
        let limit = ladder.limit(timeout, attempt);
        #[cfg(test)]
        {
            self.record_attempt(timeout);
            self.attempt_limits
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .push(limit);
        }
        limit
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
            // Undecided, with Z3's error as the reason. A failed prelude already ends every
            // operation of the solver and names the reason, so the error changes no outcome
            // here; for a query it does (`SmtError::SolverFault`).
            Err(Unanswered::Fault(reason)) => PreludeFailure::Unknown(reason.into()),
            Err(Unanswered::Rejected(rejected)) => {
                PreludeFailure::Malformed(rejected.message.into())
            }
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

    /// Confirm an internal error of Z3 on a query against the prelude, as an unknown answer is:
    /// once the prelude failed, no answer or failure of a query means anything.
    fn confirm_fault(&self, reason: String) -> Stoppable<SmtError> {
        match self.prelude_failure() {
            Some(failure) => Err(self.prelude_stop(failure)),
            None => Ok(SmtError::SolverFault(reason)),
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
        let translation_blamed = self.prelude.blames_the_translation(query, script);
        debug_assert!(
            !translation_blamed,
            "Z3 rejected an SMT-LIB script k-rust's translation wrote by itself ({}):\n{script}",
            rejected.message
        );
        Ok(SmtError::MalformedScript {
            message: rejected.message,
            translation_blamed,
        })
    }

    /// Solve `script` through the result cache. A stop observed before the lookup ends the
    /// query: its answer is not needed, and neither the cache nor Z3 is consulted. Only answers
    /// are cached; a rejected script or an internal error is not, so the cache never answers for
    /// a script Z3 did not read or did not answer.
    fn solve(&self, script: &str) -> Stoppable<Result<Satisfiability, Unanswered>> {
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
    /// rejection does not depend on the timeout. An unknown answer from an internal error of Z3
    /// ends the query's attempts with that error ([`internal_error`]): the query is not undecided
    /// within the solver's bounds, which is what the retries are for.
    fn solve_uncached(&self, script: &str) -> Stoppable<Result<Satisfiability, Unanswered>> {
        measure::bump(Counter::SmtSolverRuns);
        #[cfg(test)]
        self.uncached_solve_count.fetch_add(1, Ordering::Relaxed);

        on_own_context(|| {
            let ladder = self.ladder();
            let mut loaded = None;
            let mut timeout = self.options.timeout_ms;
            for attempt in 0..=self.options.retry_limit {
                stop::check()?;
                let limit = self.attempt_limit(&ladder, timeout, attempt);
                let attempted =
                    match run_attempt(script, &mut loaded, &ladder, attempt, limit, false) {
                        Ok(attempted) => attempted,
                        Err(rejected) => return Ok(Err(Unanswered::Rejected(rejected))),
                    };
                match attempted.checked.result {
                    SatResult::Sat => return Ok(Ok(Satisfiability::Sat)),
                    SatResult::Unsat => return Ok(Ok(Satisfiability::Unsat)),
                    SatResult::Unknown => {
                        let reason = reason_unknown(&attempted.solver);
                        if internal_error(&reason) {
                            return Ok(Err(Unanswered::Fault(reason)));
                        }
                        if attempt == self.options.retry_limit {
                            return Ok(Ok(Satisfiability::Unknown(reason)));
                        }
                        timeout = timeout.saturating_mul(2);
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
            Err(Unanswered::Rejected(rejected)) => {
                self.confirm_rejection(rejected, query, &script).map(Err)
            }
            Err(Unanswered::Fault(reason)) => self.confirm_fault(reason).map(Err),
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
            let ladder = self.ladder();
            let mut loaded = None;
            let mut timeout = self.options.timeout_ms;
            for attempt in 0..=self.options.retry_limit {
                stop::check()?;
                measure::bump(Counter::SmtSolverRuns);
                let limit = self.attempt_limit(&ladder, timeout, attempt);
                // Held until the attempt's model is read: Z3 works on the attempt's context until
                // then.
                let attempted =
                    match run_attempt(query.base(), &mut loaded, &ladder, attempt, limit, false) {
                        Ok(attempted) => attempted,
                        Err(rejected) => return Ok(Err(Unanswered::Rejected(rejected))),
                    };
                let solver = &attempted.solver;
                match attempted.checked.result {
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
                    SatResult::Unknown => {
                        let reason = reason_unknown(solver);
                        if internal_error(&reason) {
                            return Ok(Err(Unanswered::Fault(reason)));
                        }
                        if attempt == self.options.retry_limit {
                            return Ok(Ok(ModelAttempt::Unknown(reason)));
                        }
                        timeout = timeout.saturating_mul(2);
                    }
                }
            }
            unreachable!("the retry loop always returns")
        })?;
        match outcome {
            Err(Unanswered::Rejected(rejected)) => Ok(Err(self.confirm_rejection(
                rejected,
                query,
                query.base(),
            )?)),
            Err(Unanswered::Fault(reason)) => Ok(Err(self.confirm_fault(reason)?)),
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

impl Z3Solver {
    fn typed_answer(
        &self,
        inputs: &typed_cache::Query<'_>,
    ) -> Stoppable<Option<typed_cache::Answer>> {
        stop::check()?;
        let answer = self
            .typed_cache
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .get(inputs)?;
        // A concurrently failed prelude or cancellation still wins over a cached answer.
        stop::check()?;
        if let Some(failure) = self.prelude_failure() {
            return Err(self.prelude_stop(failure));
        }
        measure::bump(if answer.is_some() {
            Counter::SmtTypedCacheHits
        } else {
            Counter::SmtTypedCacheMisses
        });
        Ok(answer)
    }
    fn remember_typed(
        &self,
        inputs: &typed_cache::Query<'_>,
        answer: typed_cache::Answer,
    ) -> Stoppable<()> {
        if let Some(source) = &self.prelude.source {
            self.typed_cache
                .lock()
                .unwrap_or_else(|p| p.into_inner())
                .insert(inputs, answer, source.definition())?;
        }
        Ok(())
    }
}

impl Z3Solver {
    fn check_predicates_inner(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
        allow_observation_aliases: bool,
    ) -> Stoppable<Result<Validity, SmtError>> {
        if let Some(failure) = self.prelude_failure() {
            return Err(self.prelude_stop(failure));
        }
        stop::check()?;
        if checked.is_empty() {
            return Ok(Ok(Validity::Valid));
        }
        let inputs = typed_cache::Query::new(true, known, substitution, checked);
        if let Some(typed_cache::Answer::Validity(answer)) = self.typed_answer(&inputs)? {
            return Ok(Ok(answer));
        }
        if let Some(goals) = super::congruence::sufficient(&self.prelude, checked)? {
            // Preparing the sufficient conjunction together can demand useful source/domain
            // links shared by its conditions. If that does not prove it, try independently:
            // smaller queries and cached field checks can avoid the larger solver search.
            let mut valid = matches!(
                self.check_predicates_inner(known, substitution, &goals, false)?,
                Ok(Validity::Valid)
            );
            if !valid {
                valid = true;
                for goal in goals {
                    match self.check_predicates_inner(
                        known,
                        substitution,
                        std::slice::from_ref(&goal),
                        false,
                    )? {
                        Ok(Validity::Valid) => {}
                        // These are sufficient conditions, not equivalent obligations. No failure,
                        // refutation, contingency or Unknown of this attempt refutes the original.
                        Ok(
                            Validity::Refuted
                            | Validity::InconsistentGroundTruth
                            | Validity::Contingent
                            | Validity::Unknown(_),
                        )
                        | Err(_) => {
                            valid = false;
                            break;
                        }
                    }
                }
            }
            if valid {
                self.check_prelude()?;
                stop::check()?;
                self.remember_typed(&inputs, typed_cache::Answer::Validity(Validity::Valid))?;
                return Ok(Ok(Validity::Valid));
            }
        }
        #[cfg(test)]
        self.preparation_count.fetch_add(1, Ordering::Relaxed);
        let query = match self.prelude.query(known, substitution, checked, true)? {
            Ok(query) => query,
            Err(error) => return Ok(Err(error.into())),
        };
        let checked_text = query.checked().to_string();
        let mut answer = decide_validity(|subquery| match subquery {
            ValiditySubquery::Base => self.solve_query(&query, None),
            ValiditySubquery::Positive => self.solve_query(&query, Some(&checked_text)),
            ValiditySubquery::Negative => {
                self.solve_query(&query, Some(&format!("(not {checked_text})")))
            }
        })?;
        if allow_observation_aliases
            && matches!(&answer, Ok(Validity::Unknown(_)))
            && self.prove_with_observation_aliases(known, substitution, checked)?
        {
            self.check_prelude()?;
            stop::check()?;
            answer = Ok(Validity::Valid);
        }
        if let Ok(answer) = &answer {
            self.remember_typed(&inputs, typed_cache::Answer::Validity(answer.clone()))?;
        }
        Ok(answer)
    }

    /// Learn only independently proved source observation aliases, then recheck the original
    /// checked predicates unchanged. Auxiliary checks disable this attempt explicitly.
    fn prove_with_observation_aliases(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<bool> {
        let Some(candidates) = super::aliases::discover(&self.prelude, checked)? else {
            return Ok(false);
        };
        let mut facts = Vec::new();
        let mut trials = 0;
        for candidate in candidates {
            for leaf in candidate.leaves {
                stop::check()?;
                if trials >= super::aliases::TRIALS {
                    break;
                }
                trials += 1;
                let equality = Predicate::Equals(candidate.original.clone(), leaf.clone());
                let conditions = [
                    Predicate::Ceil(candidate.original.clone()),
                    Predicate::Ceil(leaf),
                    equality.clone(),
                ];
                if matches!(
                    self.check_predicates_inner(known, substitution, &conditions, false)?,
                    Ok(Validity::Valid)
                ) {
                    facts.push(equality);
                    break;
                }
            }
            if trials >= super::aliases::TRIALS || facts.len() >= super::aliases::FACTS {
                break;
            }
        }
        if facts.is_empty() {
            return Ok(false);
        }
        let mut augmented = known.to_vec();
        augmented.extend(facts);
        Ok(matches!(
            self.check_predicates_inner(&augmented, substitution, checked, false)?,
            Ok(Validity::Valid)
        ))
    }
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
        let inputs = typed_cache::Query::new(false, predicates, substitution, &[]);
        if let Some(typed_cache::Answer::Sat(answer)) = self.typed_answer(&inputs)? {
            return Ok(Ok(answer));
        }
        #[cfg(test)]
        self.preparation_count.fetch_add(1, Ordering::Relaxed);
        let query = match self.prelude.query(predicates, substitution, &[], false)? {
            Ok(query) => query,
            Err(error) => return Ok(Err(error.into())),
        };
        let answer = self.solve_query(&query, None)?;
        if let Ok(answer) = &answer {
            self.remember_typed(&inputs, typed_cache::Answer::Sat(answer.clone()))?;
        }
        Ok(answer)
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        self.check_predicates_inner(known, substitution, checked, true)
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
        let query = match self.prelude.query(predicates, substitution, &[], false)? {
            Ok(query) => query,
            Err(error) => return Ok(Err(error.into())),
        };
        self.solve_model(&query, &variables)
    }

    fn prelude_signal(&self) -> Option<&PreludeSignal> {
        Some(&self.prelude_signal)
    }

    /// Under [`Z3Options::resource_limit`] no attempt carries a wall-clock timeout, and an
    /// `Unknown` is a function of the query, the options and the Z3 version.
    fn undecided_answers_reproducible(&self) -> bool {
        self.options.resource_limit.is_some()
    }
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

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

    pub(super) fn definition() -> BackendDefinition {
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

    pub(super) fn term(definition: &BackendDefinition, source: &str) -> crate::term::Term {
        definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize")
    }

    fn x() -> Variable {
        Variable::new("X", crate::term::Sort::simple("SortInt"))
    }

    /// An API hit must skip preparation even when the lower script cache has evicted its answer.
    #[test]
    fn typed_reuse_precedes_preparation_and_survives_script_eviction() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let s = Substitution::new();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{},\dv{SortInt{}}("10"))"#,
        ))];
        assert_eq!(
            solver.check_predicates(&[], &s, &checked),
            Ok(Ok(Validity::Contingent))
        );
        let prepared = solver.preparation_count.load(Ordering::Relaxed);
        let runs = solver.uncached_solve_count.load(Ordering::Relaxed);
        *solver.result_cache.lock().unwrap() = SolverResultCache::new(0, 0);
        assert_eq!(
            solver.clone().check_predicates(&[], &s, &checked),
            Ok(Ok(Validity::Contingent))
        );
        assert_eq!(solver.preparation_count.load(Ordering::Relaxed), prepared);
        assert_eq!(solver.uncached_solve_count.load(Ordering::Relaxed), runs);
        let changed = Substitution::from([(x(), Term::int(20))]);
        assert_eq!(
            solver.check_predicates(&[], &changed, &checked),
            Ok(Ok(Validity::Refuted))
        );
        assert!(solver.preparation_count.load(Ordering::Relaxed) > prepared);
        let known = [Predicate::Equals(Term::variable(x()), Term::int(5))];
        assert_eq!(
            solver.check_predicates(&known, &s, &checked),
            Ok(Ok(Validity::Valid))
        );
        let opposite = [Predicate::Not(Arc::new(checked[0].clone()))];
        assert_eq!(
            solver.check_predicates(&known, &s, &opposite),
            Ok(Ok(Validity::Refuted))
        );
    }
    #[test]
    fn cached_typed_answers_still_observe_cancellation_and_prelude_failure() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let s = Substitution::new();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{},\dv{SortInt{}}("10"))"#,
        ))];
        assert_eq!(
            solver.check_predicates(&[], &s, &checked),
            Ok(Ok(Validity::Contingent))
        );
        let token = CancellationToken::new();
        token.cancel();
        assert_eq!(
            token.scope(|| cause(solver.check_predicates(&[], &s, &checked))),
            Err(StopCause::Cancelled)
        );
        *solver.prelude_state.lock().unwrap() = PreludeState::Failed(PreludeFailure::Inconsistent);
        assert_eq!(
            cause(solver.check_predicates(&[], &s, &checked)),
            Err(INCONSISTENT)
        );
    }
    #[test]
    fn typed_cache_is_private_to_its_definition_and_evaluation_context() {
        use crate::evaluation::{EvaluationMode, with_evaluation};
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let s = Substitution::new();
        let q = [Predicate::Equals(Term::variable(x()), Term::int(5))];
        assert_eq!(solver.is_sat(&q, &s), Ok(Ok(Satisfiability::Sat)));
        let prepared = solver.preparation_count.load(Ordering::Relaxed);
        with_evaluation(EvaluationMode::Execution, || {
            assert_eq!(solver.is_sat(&q, &s), Ok(Ok(Satisfiability::Sat)))
        });
        assert_eq!(
            solver.preparation_count.load(Ordering::Relaxed),
            prepared + 1
        );
        assert_eq!(solver.is_sat(&q, &s), Ok(Ok(Satisfiability::Sat)));
        assert_eq!(
            solver.preparation_count.load(Ordering::Relaxed),
            prepared + 1
        );
        {
            let _scope =
                crate::evaluation::EvaluationScope::enter_run(EvaluationMode::Execution, true);
            assert_eq!(solver.is_sat(&q, &s), Ok(Ok(Satisfiability::Sat)));
        }
        assert_eq!(
            solver.preparation_count.load(Ordering::Relaxed),
            prepared + 2
        );
        let other = Z3Solver::with_prelude(&definition, "(assert false)").unwrap();
        assert_eq!(cause(other.is_sat(&q, &s)), Err(INCONSISTENT));
    }

    #[test]
    fn structurally_equal_query_terms_do_not_reuse_another_definitions_axioms() {
        let source = r#"[] module MAIN
          hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
          symbol f{}(SortInt{}) : SortInt{} [function{}(),total{}(),smtlib{}("f")]
          axiom{R} \implies{R}(\top{R}(),\equals{SortInt{},R}(
            f{}(X:SortInt{}),\and{SortInt{}}(\dv{SortInt{}}("1"),\top{SortInt{}}())))
            [simplification{}(),smt-lemma{}(),label{}("value")]
          endmodule []"#;
        let first =
            BackendDefinition::internalize(&parse_definition(source).unwrap(), "MAIN").unwrap();
        let second = BackendDefinition::internalize(
            &parse_definition(&source.replace("\"1\"", "\"2\"")).unwrap(),
            "MAIN",
        )
        .unwrap();
        let checked = [Predicate::Equals(
            term(&first, r#"f{}(\dv{SortInt{}}("0"))"#),
            Term::int(1),
        )];
        let s = Substitution::new();
        let first = Z3Solver::new(&first).unwrap();
        let second = Z3Solver::new(&second).unwrap();
        assert_eq!(
            first.check_predicates(&[], &s, &checked),
            Ok(Ok(Validity::Valid))
        );
        assert_eq!(
            second.check_predicates(&[], &s, &checked),
            Ok(Ok(Validity::Refuted))
        );
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
                Ok(Err(SmtError::MalformedScript { message, translation_blamed: false })) if !message.is_empty()
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
            matches!(answer, Ok(Err(SmtError::MalformedScript { message, translation_blamed: false })) if !message.is_empty())
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
            .unwrap()
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

        let runs = measure::snapshot().get(Counter::SmtSolverRuns);
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
        assert_eq!(measure::snapshot().get(Counter::SmtSolverRuns), runs + 1);
        assert!(matches!(
            solver.get_model(&ModelQuery::for_solver_tests(
                &predicates,
                &Substitution::new()
            )),
            Ok(Ok(ModelResult::Sat(_)))
        ));
        assert_eq!(measure::snapshot().get(Counter::SmtSolverRuns), runs + 2);
    }

    /// The solver decides nothing about `^Int` or `^%Int` from a value where no integer is the
    /// power (a negative exponent of a base other than 1 and -1), and still decides what holds for
    /// the integer powers.
    ///
    /// GAP K15 re-pinned it. The definition now states AM-12's domains of `^Int` and `^%Int`
    /// (`INT-SYMBOLIC-KORE`, docs/amendments.md); without them `\ceil(pow(2, B))` is unknown for
    /// every `B`, and `0 <Int pow(pow(2, B), 2)` was valid only through the total reading of a
    /// term that may denote nothing. With them, each power the first loop reads is undefined
    /// under its known predicates (a negative exponent of 2 or 3, or of 2 at -1), so each atom
    /// over it is `\bottom = v`, false in every K valuation: `Refuted`, which the solver now
    /// answers through the domain, never through the fractional value of `^`. Before, it
    /// answered `Contingent`, which no K valuation supports: none satisfies the atom.
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
                hooked-symbol le{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.le"), smt-hook{}("<=")]
                hooked-symbol eq{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
                hooked-symbol ne{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.ne"), smt-hook{}("distinct")]
                hooked-symbol bor{}(SortBool{}, SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.or"), smt-hook{}("or")]
                hooked-symbol plus{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
                hooked-symbol mul{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.mul"), smt-hook{}("*")]
                axiom{Q} \implies{Q}(\top{Q}(), \equals{Q, Q}(
                    \ceil{SortInt{}, Q}(pow{}(I1:SortInt{}, I2:SortInt{})),
                    \and{Q}(\equals{SortBool{}, Q}(
                        bor{}(le{}(\dv{SortInt{}}("0"), I2:SortInt{}),
                          bor{}(eq{}(I1:SortInt{}, \dv{SortInt{}}("1")),
                            eq{}(I1:SortInt{}, \dv{SortInt{}}("-1")))),
                        \dv{SortBool{}}("true")), \top{Q}()))) [simplification{}()]
                axiom{Q} \implies{Q}(\top{Q}(), \equals{Q, Q}(
                    \ceil{SortInt{}, Q}(powmod{}(I1:SortInt{}, I2:SortInt{}, I3:SortInt{})),
                    \and{Q}(\equals{SortBool{}, Q}(
                        ne{}(I3:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")),
                      \and{Q}(\equals{SortBool{}, Q}(
                        bor{}(le{}(\dv{SortInt{}}("0"), I2:SortInt{}),
                          bor{}(eq{}(I1:SortInt{}, \dv{SortInt{}}("1")),
                            eq{}(I1:SortInt{}, \dv{SortInt{}}("-1")))),
                        \dv{SortBool{}}("true")), \top{Q}())))) [simplification{}()]
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
                Ok(Ok(Validity::Refuted)),
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
        // GAP K16: `X ^Int 0` is 1 for every `X`, 0 included, so wherever the exponent is 0 the
        // power is 1 in every reading of the query, whether the exponent is the numeral 0 or a
        // term the query makes 0, as `Y *Int Y = 0` does. Before, the reading of a symbolic
        // exponent was Z3's `(^ a b)`, and Z3 leaves `(^ 0 0)` uninterpreted: both were
        // `Contingent`.
        let y_is_zero = Predicate::Term(term(&definition, &format!("eq{{}}({b}, {})", dv(0))));
        let square_is_zero =
            Predicate::Equals(term(&definition, &format!("mul{{}}({b}, {b})")), int("0"));
        for (known, checked) in [
            (
                vec![y_is_zero],
                Predicate::Equals(
                    term(&definition, &format!("pow{{}}({}, {b})", dv(0))),
                    int("1"),
                ),
            ),
            (
                vec![square_is_zero],
                Predicate::Equals(
                    term(&definition, &format!("pow{{}}(X:SortInt{{}}, {b})")),
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
        // GAP K32: a power with a symbolic exponent is no longer Z3's power, whose evaluation at
        // model values nothing stops; what the solver decided through it, it decides from the
        // value's cases and the power's facts (`power_value`, `record_power`): a 256-bit word's
        // power of 2 at a bounded exponent, a lower bound, a value at fixed operands, and the
        // quotient of two powers of one base, by one step and by a byte.
        let at_most = |left: &str, right: &str| {
            Predicate::Term(term(&definition, &format!("le{{}}({left}, {right})")))
        };
        let word = BigInt::from(2).pow(256).to_string();
        for (known, checked) in [
            (
                vec![at_most(&dv(0), b), at_most(b, &dv(32))],
                at_most(
                    &format!("pow{{}}({}, mul{{}}({}, {b}))", dv(2), dv(8)),
                    &format!(r#"\dv{{SortInt{{}}}}("{word}")"#),
                ),
            ),
            (
                vec![at_most(&dv(3), b)],
                at_most(&dv(8), &format!("pow{{}}({}, {b})", dv(2))),
            ),
            (
                vec![Predicate::Equals(term(&definition, b), int("3"))],
                Predicate::Equals(term(&definition, &format!("pow{{}}({b}, {b})")), int("27")),
            ),
            (
                vec![at_most(&dv(0), b)],
                Predicate::Equals(
                    term(
                        &definition,
                        &format!("pow{{}}({}, plus{{}}({b}, {}))", dv(2), dv(1)),
                    ),
                    term(
                        &definition,
                        &format!("mul{{}}({}, pow{{}}({}, {b}))", dv(2), dv(2)),
                    ),
                ),
            ),
            (
                vec![at_most(&dv(0), b)],
                Predicate::Equals(
                    term(
                        &definition,
                        &format!(
                            "pow{{}}({}, mul{{}}({}, plus{{}}({b}, {})))",
                            dv(2),
                            dv(8),
                            dv(1)
                        ),
                    ),
                    term(
                        &definition,
                        &format!(
                            "mul{{}}({}, pow{{}}({}, mul{{}}({}, {b})))",
                            dv(256),
                            dv(2),
                            dv(8)
                        ),
                    ),
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

    /// GAP K16 (the K15 review's pin of the power's answer where its domain is open): without
    /// AM-12's ceil equation, `^Int`'s domain is an uninterpreted domain function. Where no integer
    /// is the power (`2 ^Int B` with `B <Int 0`), `0 <Int 2 ^Int B` is not valid: the atom carries
    /// the open domain, and the reading gives the power no value there (`KRUST-POWER` and the
    /// function outside the integers are both unconstrained at a negative exponent). Where the
    /// exponent is nonnegative and the power is stated defined, the integer power is read and the
    /// atom is valid.
    ///
    /// The open domain alone keeps the first atom from being valid, whatever the power's reading,
    /// so the pin also states the power defined at `B <Int 0` (`\ceil`), a known part K makes
    /// unsatisfiable but SMT does not, since the domain function is open: there the answer is the
    /// reading's alone. `0 ^Int B ==Int 0` is then not valid only through `guard_powers`' guard
    /// (without it the in-integers value of base 0, 0 at every exponent but 0, is read at
    /// `B < 0`), and `0 <Int 2 ^Int B` only through the reading's not being Z3's power (whose
    /// real value `2^B` is positive). Each answer fails under that mutation (GAP K32 review, the
    /// fix round's report).
    #[test]
    fn reads_no_power_value_where_no_integer_is_the_power_and_the_domain_is_open() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-symbol pow{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.pow"), smt-hook{}("^")]
                hooked-symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.lt"), smt-hook{}("<")]
                hooked-symbol le{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.le"), smt-hook{}("<=")]
                hooked-symbol eq{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let atom = |source: &str| Predicate::Term(term(&definition, source));
        let two = r#"\dv{SortInt{}}("2")"#;
        let zero = r#"\dv{SortInt{}}("0")"#;
        let power = format!("pow{{}}({two}, B:SortInt{{}})");
        let positive = atom(&format!("lt{{}}({zero}, {power})"));
        let validity = |known: &[Predicate]| {
            solver.check_predicates(known, &Substitution::new(), std::slice::from_ref(&positive))
        };
        assert_ne!(
            validity(&[atom(&format!("lt{{}}(B:SortInt{{}}, {zero})"))]),
            Ok(Ok(Validity::Valid))
        );
        assert_eq!(
            validity(&[
                atom(&format!("le{{}}({zero}, B:SortInt{{}})")),
                Predicate::Ceil(term(&definition, &power)),
            ]),
            Ok(Ok(Validity::Valid))
        );
        // The power stated defined where K has no value for it: only the reading decides.
        let negative = atom(&format!("lt{{}}(B:SortInt{{}}, {zero})"));
        let power_of_zero = format!("pow{{}}({zero}, B:SortInt{{}})");
        let decided = [
            (
                "0 ^Int B ==Int 0",
                power_of_zero.clone(),
                atom(&format!("eq{{}}({power_of_zero}, {zero})")),
            ),
            ("0 <Int 2 ^Int B", power.clone(), positive.clone()),
        ]
        .into_iter()
        .filter(|(_, power, checked)| {
            let known = [negative.clone(), Predicate::Ceil(term(&definition, power))];
            solver.check_predicates(&known, &Substitution::new(), std::slice::from_ref(checked))
                == Ok(Ok(Validity::Valid))
        })
        .map(|(name, _, _)| name)
        .collect::<Vec<_>>();
        assert!(
            decided.is_empty(),
            "valid under B <Int 0 with the power stated defined: {decided:?}"
        );
    }

    /// A definition with `^Int` (no domain equation), `+Int` and `==Int`, for the power tests.
    fn power_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-symbol pow{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.pow"), smt-hook{}("^")]
                hooked-symbol plus{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
                hooked-symbol eq{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// GAP K32 review: the facts `record_power` states are true of the integer power at the
    /// boundary of a literal base's window of numerals (`W` = 256 for 2, 3 and -2, 7 for `2^64`)
    /// and past it, so the power's true value is never excluded: a query that fixes the exponents
    /// and states the powers' true values is satisfiable. Pairs of powers of one base whose
    /// exponents differ by a constant at the window's last exponent and past it (where the
    /// quotient's factor is a numeral, and where it is not stated), and by no constant.
    #[test]
    fn states_power_facts_the_integer_power_satisfies_at_the_window_boundary() {
        let definition = power_definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let dv = |value: &BigInt| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
        let equals = |left: &str, right: &str| {
            Predicate::Equals(term(&definition, left), term(&definition, right))
        };
        let power = |base: &BigInt, exponent: &str| format!("pow{{}}({}, {exponent})", dv(base));
        let fixed = |exponent: &str, value: i64| equals(exponent, &dv(&BigInt::from(value)));
        let truly = |base: &BigInt, exponent: &str, value: u32| {
            equals(&power(base, exponent), &dv(&base.pow(value)))
        };
        let (b, c) = ("B:SortInt{}", "C:SortInt{}");
        let wide = BigInt::from(2).pow(64);
        let mut queries = Vec::new();
        for (base, exponents) in [
            (BigInt::from(2), vec![255, 256, 257, 300]),
            (BigInt::from(3), vec![255, 256, 257, 300]),
            (BigInt::from(-2), vec![255, 256, 257, 300]),
            (wide.clone(), vec![6, 7, 8, 20]),
        ] {
            for exponent in exponents {
                queries.push(vec![
                    fixed(b, i64::from(exponent)),
                    truly(&base, b, exponent),
                ]);
            }
            let window = if base == wide { 7 } else { 256 };
            for (low, offset) in [(8, window), (8, window + 1), (0, window), (1, 2)] {
                let shifted = format!("plus{{}}({b}, {})", dv(&BigInt::from(offset)));
                queries.push(vec![
                    fixed(b, i64::from(low)),
                    truly(&base, b, low),
                    truly(&base, &shifted, low + offset),
                ]);
            }
            queries.push(vec![
                fixed(b, 8),
                fixed(c, i64::from(8 + window)),
                truly(&base, b, 8),
                truly(&base, c, 8 + window),
            ]);
        }
        for query in queries {
            assert_eq!(
                solver.is_sat(&query, &Substitution::new()),
                Ok(Ok(Satisfiability::Sat)),
                "{query:?}"
            );
        }
    }

    /// GAP K32 review: a power whose exponent a quantifier binds gets no fact, also where the
    /// exponent reaches the bound variable only through a `let` of the query's shared values
    /// (here `B +Int 1`, named once): the facts are closed with those `let`s before their
    /// variables are compared with the bound ones. A closed power of the same shape gets them.
    /// A fact that escaped its binder would name an undeclared constant, and Z3 would reject the
    /// script.
    #[test]
    fn states_no_power_fact_under_a_binder_through_a_shared_let() {
        let definition = power_definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let two = r#"\dv{SortInt{}}("2")"#;
        let one = r#"\dv{SortInt{}}("1")"#;
        let four = r#"\dv{SortInt{}}("4")"#;
        let equation = |exponent: &str| {
            let power = format!("pow{{}}({two}, plus{{}}({exponent}, {one}))");
            Predicate::Equals(
                term(&definition, &format!("plus{{}}({power}, {power})")),
                term(&definition, &format!("plus{{}}({four}, {four})")),
            )
        };
        let b = crate::term::Variable::new("B", Sort::simple("SortInt"));
        let bound = Predicate::Exists(b, Arc::new(equation("B:SortInt{}")));
        let base = |predicate: &Predicate| {
            solver
                .prelude
                .query(
                    std::slice::from_ref(predicate),
                    &Substitution::new(),
                    &[],
                    false,
                )
                .unwrap()
                .unwrap()
                .base()
                .to_owned()
        };
        // The fact past the window, `e > 256 => V > 2^256`, names the window's last exponent.
        let facts = |script: &str| script.contains(" 256) (> SMT-");
        let open = base(&equation("C:SortInt{}"));
        let closed = base(&bound);
        assert!(facts(&open), "{open}");
        assert!(!facts(&closed), "{closed}");
        assert_eq!(
            solver.is_sat(&[bound], &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
    }

    /// GAP K15: the solver's domain of a partial hooked application that no ceil equation states
    /// reads what the hook decides, as the simplifier does (`builtin::hook_domain`): `bn128valid`
    /// is a `Bool` for every point term and a raw digest has a value for every byte string, so
    /// both are defined wherever their arguments are; on literal arguments the evaluator's value
    /// shows `2 ^Int 3` defined and its stated `\bottom` shows `2 ^Int -1` undefined. Before, each
    /// domain was its head's opaque domain function, and the solver decided none of them.
    #[test]
    fn a_domain_reads_the_definedness_its_hook_decides() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortBytes{} [hook{}("BYTES.Bytes"), hasDomainValues{}()]
                sort SortG1{} []
                hooked-symbol valid{}(SortG1{}) : SortBool{}
                    [function{}(), hook{}("KRYPTO.bn128valid")]
                hooked-symbol digest{}(SortBytes{}) : SortBytes{}
                    [function{}(), hook{}("KRYPTO.keccak256raw")]
                hooked-symbol pow{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.pow"), smt-hook{}("^")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let ceil = |source: &str| Predicate::Ceil(term(&definition, source));
        let dv = |value: i64| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
        for (checked, expected) in [
            (ceil("valid{}(P:SortG1{})"), Validity::Valid),
            (ceil("digest{}(B:SortBytes{})"), Validity::Valid),
            (
                ceil(&format!("pow{{}}({}, {})", dv(2), dv(3))),
                Validity::Valid,
            ),
            (
                ceil(&format!("pow{{}}({}, {})", dv(2), dv(-1))),
                Validity::Refuted,
            ),
        ] {
            assert_eq!(
                solver.check_predicates(&[], &Substitution::new(), std::slice::from_ref(&checked)),
                Ok(Ok(expected)),
                "{checked:?}"
            );
        }
    }

    /// GAP K15: the solver reads an atom over a partial term as K does wherever the term is
    /// undefined too. `half` is partial, with the `smt-hook` SMT-LIB's `div`, which has a value
    /// at 1 where the definition leaves `half(1)` open. `half(1) = 0` is `\bottom` where
    /// `half(1)` is undefined, so it is not valid (Z3 read it as `div 1 2 = 0` and found it
    /// valid), its negation is not refuted, and it contradicts `\not \ceil(half(1))`; two
    /// undefined terms are equal, `\bottom = \bottom` being `\top`.
    #[test]
    fn an_atom_over_a_partial_term_is_decided_only_where_the_term_is_defined() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol half{}(SortInt{}) : SortInt{} [function{}(), smt-hook{}("(div #1 2)")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let half = |argument: &str| term(&definition, &format!("half{{}}({argument})"));
        let one = r#"\dv{SortInt{}}("1")"#;
        let zero = term(&definition, r#"\dv{SortInt{}}("0")"#);
        let equality = Predicate::Equals(half(one), zero);
        let undefined =
            |argument: &str| Predicate::Not(std::sync::Arc::new(Predicate::Ceil(half(argument))));
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), std::slice::from_ref(&equality)),
            Ok(Ok(Validity::Contingent))
        );
        assert_eq!(
            solver.check_predicates(
                &[],
                &Substitution::new(),
                &[Predicate::Not(std::sync::Arc::new(equality.clone()))]
            ),
            Ok(Ok(Validity::Contingent))
        );
        assert_eq!(
            solver.is_sat(&[equality, undefined(one)], &Substitution::new()),
            Ok(Ok(Satisfiability::Unsat))
        );
        assert_eq!(
            solver.check_predicates(
                &[undefined("X:SortInt{}"), undefined("Y:SortInt{}")],
                &Substitution::new(),
                &[Predicate::Equals(half("X:SortInt{}"), half("Y:SortInt{}"))]
            ),
            Ok(Ok(Validity::Valid))
        );
    }

    /// GAP K29: a query over a partial symbol whose domain the definition states as a closed
    /// formula is exact, so its model is a K valuation. `half(X) = 3` is read as
    /// `D(half(X)) ∧ div(X, 2) = 3` with `D(half(X))` the ceil equation's `even(X) = true`, so
    /// every model has `X = 6`: `X = 7`, where `div` is 3 too, is refuted by the domain, and
    /// `get-model` gives `X = 6`. Without a ceil equation the domain is a domain function a model
    /// may set true where `half2(X)` is undefined, and the query stays approximate.
    #[test]
    fn a_query_whose_partial_symbols_have_closed_domains_is_exact() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol even{}(SortInt{}) : SortBool{} [function{}(), total{}(), smt-hook{}("(= (mod #1 2) 0)")]
                symbol half{}(SortInt{}) : SortInt{} [function{}(), smt-hook{}("(div #1 2)")]
                symbol half2{}(SortInt{}) : SortInt{} [function{}(), smt-hook{}("(div #1 2)")]
                axiom{Q} \implies{Q}(\top{Q}(), \equals{Q, Q}(
                    \ceil{SortInt{}, Q}(half{}(X:SortInt{})),
                    \and{Q}(\equals{SortBool{}, Q}(even{}(X:SortInt{}), \dv{SortBool{}}("true")), \top{Q}())))
                    [simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let int = |value: &str| crate::term::Term::raw_domain_value(Sort::simple("SortInt"), value);
        let three = Predicate::Equals(term(&definition, "half{}(X:SortInt{})"), int("3"));
        assert_eq!(
            solver.is_sat(std::slice::from_ref(&three), &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        let not_six = Predicate::Not(std::sync::Arc::new(Predicate::Equals(
            crate::term::Term::variable(x()),
            int("6"),
        )));
        assert_eq!(
            solver.is_sat(&[three.clone(), not_six], &Substitution::new()),
            Ok(Ok(Satisfiability::Unsat))
        );
        assert_eq!(
            solver.get_model(&ModelQuery::for_solver_tests(
                std::slice::from_ref(&three),
                &Substitution::new()
            )),
            Ok(Ok(ModelResult::Sat(Substitution::from([(x(), int("6"))]))))
        );
        let opaque = Predicate::Equals(term(&definition, "half2{}(X:SortInt{})"), int("3"));
        assert_eq!(
            solver.get_model(&ModelQuery::for_solver_tests(
                &[opaque],
                &Substitution::new()
            )),
            Ok(Ok(ModelResult::Unknown(APPROXIMATE_MODEL_REASON.into())))
        );
    }

    /// GAP K35: a term-level `\and` denotes the common value of its sides where both denote it,
    /// and nothing elsewhere, so the solver reads it as a partial operation: defined exactly
    /// where `D(l) ∧ D(r) ∧ l = r`, with the value of `l` there. `eqb(B ∧ true, true)` then holds
    /// exactly where `B` is `true`, and its negation exactly where `B` is `false` (the
    /// conjunction is `\bottom` there), so "¬atom ⇒ B = false" is valid; the domain is a closed
    /// formula, so the query is exact and its model a K valuation.
    #[test]
    fn a_boolean_term_conjunction_is_defined_where_its_sides_are_equal() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol eqb{}(SortBool{}, SortBool{}) : SortBool{} [function{}(), total{}(), smt-hook{}("=")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let boolean =
            |value: &str| crate::term::Term::raw_domain_value(Sort::simple("SortBool"), value);
        let b = Variable::new("B", Sort::simple("SortBool"));
        let atom = Predicate::Term(term(
            &definition,
            r#"eqb{}(\and{SortBool{}}(B:SortBool{}, \dv{SortBool{}}("true")), \dv{SortBool{}}("true"))"#,
        ));
        let not = |predicate: &Predicate| Predicate::Not(std::sync::Arc::new(predicate.clone()));
        let is =
            |value: &str| Predicate::Equals(crate::term::Term::variable(b.clone()), boolean(value));
        let s = Substitution::new();
        for (known, checked, expected) in [
            (not(&atom), is("false"), Validity::Valid),
            (atom.clone(), is("true"), Validity::Valid),
            (is("true"), atom.clone(), Validity::Valid),
            (is("false"), not(&atom), Validity::Valid),
            (is("false"), atom.clone(), Validity::Refuted),
        ] {
            assert_eq!(
                solver.check_predicates(
                    std::slice::from_ref(&known),
                    &s,
                    std::slice::from_ref(&checked)
                ),
                Ok(Ok(expected)),
                "{known:?} => {checked:?}"
            );
        }
        for (query, value) in [(not(&atom), "false"), (atom.clone(), "true")] {
            assert_eq!(
                solver.get_model(&ModelQuery::for_solver_tests(
                    std::slice::from_ref(&query),
                    &s
                )),
                Ok(Ok(ModelResult::Sat(Substitution::from([(
                    b.clone(),
                    boolean(value)
                )])))),
                "{query:?}"
            );
        }
    }

    /// GAP K36: an `\and` of any sort is read as the Boolean one is (GAP K35): defined where its
    /// sides are defined and equal, with their common value. So `X ∧ Y = 4` holds exactly where
    /// both are 4 and has that model, `\not(X ∧ 3 = 3)` holds exactly where `X` is not 3, and
    /// `\ceil(X ∧ Y)` is `X = Y`.
    #[test]
    fn an_integer_term_conjunction_is_defined_where_its_sides_are_equal() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let int = |value: &str| crate::term::Term::raw_domain_value(Sort::simple("SortInt"), value);
        let variable =
            |name: &str| crate::term::Term::variable(Variable::new(name, Sort::simple("SortInt")));
        let and =
            |left: crate::term::Term, right: crate::term::Term| crate::term::Term::and(left, right);
        let not = |predicate: Predicate| Predicate::Not(std::sync::Arc::new(predicate));
        let s = Substitution::new();
        let four = Predicate::Equals(and(variable("X"), variable("Y")), int("4"));
        assert_eq!(
            solver.is_sat(
                &[
                    four.clone(),
                    not(Predicate::Equals(variable("Y"), int("4")))
                ],
                &s
            ),
            Ok(Ok(Satisfiability::Unsat))
        );
        assert_eq!(
            solver.get_model(&ModelQuery::for_solver_tests(
                std::slice::from_ref(&four),
                &s
            )),
            Ok(Ok(ModelResult::Sat(Substitution::from([
                (x(), int("4")),
                (Variable::new("Y", Sort::simple("SortInt")), int("4")),
            ]))))
        );
        let three = Predicate::Equals(and(variable("X"), int("3")), int("3"));
        assert_eq!(
            solver.check_predicates(
                &[not(three.clone())],
                &s,
                &[not(Predicate::Equals(variable("X"), int("3")))]
            ),
            Ok(Ok(Validity::Valid))
        );
        assert_eq!(
            solver.check_predicates(&[], &s, &[Predicate::Equals(variable("X"), int("3"))]),
            Ok(Ok(Validity::Contingent))
        );
        let defined = Predicate::Ceil(and(variable("X"), variable("Y")));
        assert_eq!(
            solver.check_predicates(&[], &s, std::slice::from_ref(&defined)),
            Ok(Ok(Validity::Contingent))
        );
        assert_eq!(
            solver.check_predicates(
                &[Predicate::Equals(variable("X"), variable("Y"))],
                &s,
                std::slice::from_ref(&defined)
            ),
            Ok(Ok(Validity::Valid))
        );
        assert_eq!(
            solver.check_predicates(
                &[defined],
                &s,
                &[Predicate::Equals(variable("X"), variable("Y"))]
            ),
            Ok(Ok(Validity::Valid))
        );
    }

    /// GAP K36 at an uninterpreted sort: `F ∧ G` over a user sort is defined exactly where
    /// `F = G`, the plan's equality being SMT `=` over the sort's uninterpreted values, which
    /// every K model satisfies with the sort read as K's carrier. So `\ceil(F ∧ G)` is `F = G`
    /// both ways, and an atom `isA(F ∧ G)` holds only there: with `F ≠ G` it is refuted, while
    /// its negation is satisfiable (the conjunction is `\bottom` there). `isA` and the sort are
    /// uninterpreted, so a query over the atom is approximate and offers no model.
    #[test]
    fn a_term_conjunction_at_an_uninterpreted_sort_is_defined_where_its_sides_are_equal() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortFoo{} []
                symbol isA{}(SortFoo{}) : SortBool{} [function{}(), total{}(), smtlib{}("isA")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let foo =
            |name: &str| crate::term::Term::variable(Variable::new(name, Sort::simple("SortFoo")));
        let not = |predicate: Predicate| Predicate::Not(std::sync::Arc::new(predicate));
        let s = Substitution::new();
        let same = Predicate::Equals(foo("F"), foo("G"));
        let defined = Predicate::Ceil(crate::term::Term::and(foo("F"), foo("G")));
        assert_eq!(
            solver.check_predicates(&[], &s, std::slice::from_ref(&defined)),
            Ok(Ok(Validity::Contingent))
        );
        assert_eq!(
            solver.check_predicates(
                std::slice::from_ref(&same),
                &s,
                std::slice::from_ref(&defined)
            ),
            Ok(Ok(Validity::Valid))
        );
        assert_eq!(
            solver.check_predicates(
                std::slice::from_ref(&defined),
                &s,
                std::slice::from_ref(&same)
            ),
            Ok(Ok(Validity::Valid))
        );
        let atom = Predicate::Term(term(
            &definition,
            r#"isA{}(\and{SortFoo{}}(F:SortFoo{}, G:SortFoo{}))"#,
        ));
        assert_eq!(
            solver.is_sat(&[atom.clone(), not(same.clone())], &s),
            Ok(Ok(Satisfiability::Unsat))
        );
        assert_eq!(
            solver.check_predicates(std::slice::from_ref(&atom), &s, std::slice::from_ref(&same)),
            Ok(Ok(Validity::Valid))
        );
        let apart = [not(atom.clone()), not(same)];
        assert_eq!(solver.is_sat(&apart, &s), Ok(Ok(Satisfiability::Sat)));
        for query in [&[atom][..], &apart[..]] {
            assert_eq!(
                solver.get_model(&ModelQuery::for_solver_tests(query, &s)),
                Ok(Ok(ModelResult::Unknown(APPROXIMATE_MODEL_REASON.into())))
            );
        }
    }

    /// A term-level `\and` denotes the intersection of what its sides denote. A side with no set
    /// variable denotes at most one element, so a conjunction with such a side does too, and the
    /// solver may read it as one value (gated by its domain). When both sides hold set
    /// variables the intersection may have several elements, and no single value reads it: with
    /// `S = T = {-1, 0}`, `st = @S ∧ @T` is `{-1, 0}`, so `g = st + 1 > 0` and `n = st + 1 <= 0`
    /// are both `{false, true}`: both are defined and neither is `{true}`. So `⌈g⌉ ∧ ⌈n⌉ ∧ ¬(g =
    /// true)` does not imply `n = true`, which a reading of `st` as one SMT constant makes valid.
    /// The Boolean `@P ∧ @Q` is `{false, true}` when both are: defined, neither `true` nor
    /// `false`. Such a conjunction is refused (`MayDenoteSeveral`), and its atom is not posed. With
    /// one side an element variable, `@S ∧ X` is at most `{X}`, and the implication is valid.
    #[test]
    fn a_term_conjunction_of_two_sides_with_set_variables_is_not_read_as_one_value() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol plus{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}(), smt-hook{}("+")]
                symbol gt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), smt-hook{}(">")]
                symbol le{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), smt-hook{}("<=")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let boolean =
            |value: &str| crate::term::Term::raw_domain_value(Sort::simple("SortBool"), value);
        let not = |predicate: Predicate| Predicate::Not(std::sync::Arc::new(predicate));
        let s = Substitution::new();
        let shapes = |st: &str| {
            let atom = |symbol: &str| {
                term(
                    &definition,
                    &format!(
                        r#"{symbol}{{}}(plus{{}}({st}, \dv{{SortInt{{}}}}("1")), \dv{{SortInt{{}}}}("0"))"#
                    ),
                )
            };
            let (g, n) = (atom("gt"), atom("le"));
            (
                vec![
                    Predicate::Ceil(g.clone()),
                    Predicate::Ceil(n.clone()),
                    not(Predicate::Equals(boolean("true"), g)),
                ],
                Predicate::Equals(boolean("true"), n),
            )
        };
        fn refused<T>(result: &Result<T, SmtError>) -> bool {
            matches!(
                result,
                Err(SmtError::Translation(
                    crate::smt::TranslationError::MayDenoteSeveral(_)
                ))
            )
        }
        let two = r#"\and{SortInt{}}(@S:SortInt{}, @T:SortInt{})"#;
        let (known, checked) = shapes(two);
        let answer = solver
            .check_predicates(&known, &s, std::slice::from_ref(&checked))
            .unwrap();
        assert!(refused(&answer), "{answer:?}");
        let (mut both, n) = shapes(two);
        both.push(not(n));
        let answer = solver.is_sat(&both, &s).unwrap();
        assert!(refused(&answer), "{answer:?}");
        let answer = solver
            .get_model(&ModelQuery::for_solver_tests(&both, &s))
            .unwrap();
        assert!(refused(&answer), "{answer:?}");
        let (known, checked) = shapes(r#"\and{SortInt{}}(@S:SortInt{}, X:SortInt{})"#);
        assert_eq!(
            solver.check_predicates(&known, &s, std::slice::from_ref(&checked)),
            Ok(Ok(Validity::Valid))
        );
        let c = term(
            &definition,
            r#"\and{SortBool{}}(@P:SortBool{}, @Q:SortBool{})"#,
        );
        let known = [
            Predicate::Ceil(c.clone()),
            not(Predicate::Equals(c.clone(), boolean("true"))),
        ];
        let answer = solver
            .check_predicates(
                &known,
                &s,
                &[Predicate::Equals(c.clone(), boolean("false"))],
            )
            .unwrap();
        assert!(refused(&answer), "{answer:?}");
        let both = [
            Predicate::Ceil(c.clone()),
            not(Predicate::Equals(c.clone(), boolean("true"))),
            not(Predicate::Equals(c.clone(), boolean("false"))),
        ];
        let answer = solver.is_sat(&both, &s).unwrap();
        assert!(refused(&answer), "{answer:?}");
        let answer = solver
            .get_model(&ModelQuery::for_solver_tests(&both, &s))
            .unwrap();
        assert!(refused(&answer), "{answer:?}");
    }

    /// GAP K40: a set variable may denote several elements, so the solver reads no term holding
    /// one as one value, and a library caller's query over one is refused, not answered.
    /// With `S = {-1, 0}`, `g = (S + 1 > 0)` and `n = (S + 1 <= 0)` are both `{false, true}`:
    /// defined, and neither is `true`. So `⌈g⌉ ∧ ⌈n⌉ ∧ ¬(true = g) ⇒ true = n` is not
    /// entailed, though it is valid for every one value of `S`. The same holds below an
    /// application the solver reads as an opaque value (`opaque(@S) + 1`, no `smt` attribute),
    /// which reaches no variable arm. A term-level `\and` with a side that holds no set
    /// variable denotes at most one element and is still read (the K35 test above).
    #[test]
    fn a_set_variable_is_not_read_as_one_value() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol plus{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}(), smt-hook{}("+")]
                symbol gt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), smt-hook{}(">")]
                symbol le{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), smt-hook{}("<=")]
                symbol opaque{}(SortInt{}) : SortInt{} [function{}(), total{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let boolean =
            |value: &str| crate::term::Term::raw_domain_value(Sort::simple("SortBool"), value);
        let not = |predicate: Predicate| Predicate::Not(std::sync::Arc::new(predicate));
        let s = Substitution::new();
        let shapes = |st: &str| {
            let atom = |symbol: &str| {
                term(
                    &definition,
                    &format!(
                        r#"{symbol}{{}}(plus{{}}({st}, \dv{{SortInt{{}}}}("1")), \dv{{SortInt{{}}}}("0"))"#
                    ),
                )
            };
            let (g, n) = (atom("gt"), atom("le"));
            (
                vec![
                    Predicate::Ceil(g.clone()),
                    Predicate::Ceil(n.clone()),
                    not(Predicate::Equals(boolean("true"), g)),
                ],
                Predicate::Equals(boolean("true"), n),
            )
        };
        fn refused<T>(result: &Result<T, SmtError>) -> bool {
            matches!(
                result,
                Err(SmtError::Translation(
                    crate::smt::TranslationError::MayDenoteSeveral(_)
                ))
            )
        }
        for st in ["@S:SortInt{}", "opaque{}(@S:SortInt{})"] {
            let (known, checked) = shapes(st);
            let answer = solver
                .check_predicates(&known, &s, std::slice::from_ref(&checked))
                .unwrap();
            assert!(refused(&answer), "{st}: {answer:?}");
            let (mut both, n) = shapes(st);
            both.push(not(n));
            let answer = solver.is_sat(&both, &s).unwrap();
            assert!(refused(&answer), "{st}: {answer:?}");
            let answer = solver
                .get_model(&ModelQuery::for_solver_tests(&both, &s))
                .unwrap();
            assert!(refused(&answer), "{st}: {answer:?}");
        }
        for st in ["X:SortInt{}", "opaque{}(X:SortInt{})"] {
            let (known, checked) = shapes(st);
            assert_eq!(
                solver.check_predicates(&known, &s, std::slice::from_ref(&checked)),
                Ok(Ok(Validity::Valid)),
                "{st}"
            );
        }
    }

    /// GAP K23: a node is named in a scope outside a binder only when the binder binds none of
    /// its variables. In `\exists Y. (half(X) = Y /\ \forall X. half(X) = Y)` the inner
    /// `half(X)` reads the `X` the `\forall` binds, not the free `X` of the first conjunct, so
    /// it is not the outer node's value: the formula says that `half` is defined everywhere and
    /// constant, which its `smt-hook` (`div`) is not, so it is unsatisfiable. Reading the
    /// inner `half(X)` as the outer one's `let` would make the `\forall` hold of every `Y` equal
    /// to `half(X)`, a satisfiable formula.
    #[test]
    fn a_node_under_a_binder_that_rebinds_its_variable_is_not_the_outer_node() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol half{}(SortInt{}) : SortInt{} [function{}(), smt-hook{}("(div #1 2)")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let int = crate::term::Sort::simple("SortInt");
        let x = crate::term::Variable::new("X", int);
        let y = crate::term::Variable::new("Y", int);
        let half = term(&definition, "half{}(X:SortInt{})");
        let y_term = crate::term::Term::variable(y.clone());
        let formula = Predicate::Exists(
            y,
            std::sync::Arc::new(Predicate::And(
                vec![
                    Predicate::Equals(half.clone(), y_term.clone()),
                    Predicate::Forall(x, std::sync::Arc::new(Predicate::Equals(half, y_term))),
                ]
                .into(),
            )),
        );
        assert_eq!(
            solver.is_sat(&[formula], &Substitution::new()),
            Ok(Ok(Satisfiability::Unsat))
        );
    }

    /// GAP K23 review: a hoisted `let` keeps the meaning of its node across every binder. Each
    /// case is a formula whose satisfiability does not depend on `let` placement, decided by
    /// what `half` (`div` by 2, total) and `sdiv` (`div`, defined at a nonzero divisor by its
    /// `\ceil` equation) denote. The cases bind the same variable twice on one path (`p1`,
    /// `p1b`, `p2`, `p4`, `p6`, `p7`): a node made under the outer binder and read again under
    /// the inner one denotes another value there, so it may reuse only a `let` from a scope at
    /// or inside the innermost binder of its variables. Reusing one from the outer binder's
    /// scope (the outermost binder, not the innermost) reads `\forall X. half(X) = 1` as
    /// `half(X) = 1` of the outer `X`: `p1`, `p2`, `p6`, `p7` become Sat and `p1b` Unsat.
    /// `p3`, `p3b` rebind a free variable, a domain read through the `\ceil` equation; `p5`
    /// hoists a node across a binder of another variable (sound: `N` does not occur in it);
    /// `p7` puts an unrelated binder between the two binders of `X`. Both directions are
    /// pinned: a capture turns a Sat case Unsat (`p1b`, `p3b`) as well as an Unsat one Sat.
    #[test]
    fn hoisted_lets_keep_their_meaning_under_binders_that_rebind_their_variables() {
        use std::sync::Arc;
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol half{}(SortInt{}) : SortInt{} [function{}(), smt-hook{}("(div #1 2)")]
                hooked-symbol sdiv{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
                hooked-symbol neInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.ne"), smt-hook{}("distinct")]
                axiom{Q} \implies{Q}(\top{Q}(), \equals{Q, Q}(
                    \ceil{SortInt{}, Q}(sdiv{}(I:SortInt{}, J:SortInt{})),
                    \and{Q}(\equals{SortBool{}, Q}(neInt{}(J:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")),
                      \top{Q}()))) [simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let int = crate::term::Sort::simple("SortInt");
        let v = |name: &str| crate::term::Variable::new(name, int);
        let t = |source: &str| term(&definition, source);
        let lit = |n: &str| t(&format!("\\dv{{SortInt{{}}}}(\"{n}\")"));
        let n = t("N:SortInt{}");
        let and = |ps: Vec<Predicate>| Predicate::And(ps.into());
        let ex = |name: &str, p: Predicate| Predicate::Exists(v(name), Arc::new(p));
        let all = |name: &str, p: Predicate| Predicate::Forall(v(name), Arc::new(p));
        let not = |p: Predicate| Predicate::Not(Arc::new(p));
        let eq =
            |a: &crate::term::Term, b: &crate::term::Term| Predicate::Equals(a.clone(), b.clone());
        let ceil = |a: &crate::term::Term| Predicate::Ceil(a.clone());
        let half_x = t("half{}(X:SortInt{})");
        let div_1y = t("sdiv{}(\\dv{SortInt{}}(\"1\"), Y:SortInt{})");
        let div_xy = t("sdiv{}(X:SortInt{}, Y:SortInt{})");
        let cases: Vec<(&str, Predicate, Satisfiability)> = vec![
            // A value, X bound twice: \exists X. (half(X) = 1 /\ \forall X. half(X) = 1).
            (
                "p1",
                ex(
                    "X",
                    and(vec![
                        eq(&half_x, &lit("1")),
                        all("X", eq(&half_x, &lit("1"))),
                    ]),
                ),
                Satisfiability::Unsat,
            ),
            // The other direction: \exists X. (half(X) = 1 /\ \exists X. half(X) = 2).
            (
                "p1b",
                ex(
                    "X",
                    and(vec![
                        eq(&half_x, &lit("1")),
                        ex("X", eq(&half_x, &lit("2"))),
                    ]),
                ),
                Satisfiability::Sat,
            ),
            // A domain, Y bound twice: \exists Y. (\ceil(1 sdiv Y) /\ \forall Y. \ceil(1 sdiv Y)).
            (
                "p2",
                ex("Y", and(vec![ceil(&div_1y), all("Y", ceil(&div_1y))])),
                Satisfiability::Unsat,
            ),
            // A domain, Y free outside: \ceil(1 sdiv Y) /\ \forall Y. \ceil(1 sdiv Y).
            (
                "p3",
                and(vec![ceil(&div_1y), all("Y", ceil(&div_1y))]),
                Satisfiability::Unsat,
            ),
            // The other direction: \not\ceil(1 sdiv Y) /\ \exists Y. \ceil(1 sdiv Y).
            (
                "p3b",
                and(vec![not(ceil(&div_1y)), ex("Y", ceil(&div_1y))]),
                Satisfiability::Sat,
            ),
            // An atom's operand domain, Y bound twice:
            // \exists Y. (1 sdiv Y = 1 /\ \forall Y. \not(1 sdiv Y = 1)).
            (
                "p4",
                ex(
                    "Y",
                    and(vec![
                        eq(&div_1y, &lit("1")),
                        all("Y", not(eq(&div_1y, &lit("1")))),
                    ]),
                ),
                Satisfiability::Unsat,
            ),
            // Hoisted across a binder of another variable:
            // \ceil(X sdiv Y) /\ \forall N. \not(X sdiv Y = N).
            (
                "p5",
                and(vec![ceil(&div_xy), all("N", not(eq(&div_xy, &n)))]),
                Satisfiability::Unsat,
            ),
            // Two variables, one rebound: \exists Y. (X sdiv Y = half(X) /\ \forall X. X sdiv Y = 0).
            (
                "p6",
                ex(
                    "Y",
                    and(vec![eq(&div_xy, &half_x), all("X", eq(&div_xy, &lit("0")))]),
                ),
                Satisfiability::Unsat,
            ),
            // Three levels, the middle binder unrelated:
            // \exists X. (half(X) = 1 /\ \exists N. (N = half(X) /\ \forall X. half(X) = N)).
            (
                "p7",
                ex(
                    "X",
                    and(vec![
                        eq(&half_x, &lit("1")),
                        ex("N", and(vec![eq(&n, &half_x), all("X", eq(&half_x, &n))])),
                    ]),
                ),
                Satisfiability::Unsat,
            ),
        ];
        let failures: Vec<String> = cases
            .into_iter()
            .filter_map(|(name, formula, expected)| {
                let got = solver.is_sat(&[formula], &Substitution::new());
                (got != Ok(Ok(expected.clone())))
                    .then(|| format!("{name}: expected {expected:?}, got {got:?}"))
            })
            .collect();
        assert!(failures.is_empty(), "{failures:#?}");
    }

    /// GAP K22 step 0 (K15's C1b acceptance): a deferred operand that builtin hooks alone show
    /// defined is read as defined. `#if C #then 1 #else 2 /Int 2 #fi` is defined at every `C`,
    /// each branch being an integer (`/Int` is defined at a nonzero divisor, and the hook decides
    /// that on the literals), and denotes 1 at both, so an atom true of 1 is valid with `C`
    /// symbolic. An atom true of one branch only is not valid. The conditional is an application,
    /// strict in every argument, so one whose other branch is undefined (`2 /Int 0`) is `\bottom`
    /// whatever `C` is, and an atom over it is refuted, also where `C` is known.
    #[test]
    fn an_atom_over_a_conditional_with_hook_defined_branches_is_decided_at_both_branches() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-symbol ite{}(SortBool{}, SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("KEQUAL.ite"), smt-hook{}("ite")]
                hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let dv = |value: i64| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
        let conditional = |dividend: i64, divisor: i64| {
            term(
                &definition,
                &format!(
                    "ite{{}}(C:SortBool{{}}, {}, divInt{{}}({}, {}))",
                    dv(1),
                    dv(dividend),
                    dv(divisor)
                ),
            )
        };
        let one = term(&definition, &dv(1));
        let condition = Predicate::Term(term(&definition, "C:SortBool{}"));
        for (known, checked, expected) in [
            (
                vec![],
                Predicate::Equals(conditional(2, 2), one.clone()),
                Validity::Valid,
            ),
            (vec![], Predicate::Ceil(conditional(2, 2)), Validity::Valid),
            (
                vec![],
                Predicate::Equals(conditional(4, 2), one.clone()),
                Validity::Contingent,
            ),
            (
                vec![],
                Predicate::Equals(conditional(2, 0), one.clone()),
                Validity::Refuted,
            ),
            (
                vec![],
                Predicate::Ceil(conditional(2, 0)),
                Validity::Refuted,
            ),
            (
                vec![condition],
                Predicate::Equals(conditional(2, 0), one.clone()),
                Validity::Refuted,
            ),
        ] {
            assert_eq!(
                solver.check_predicates(
                    &known,
                    &Substitution::new(),
                    std::slice::from_ref(&checked)
                ),
                Ok(Ok(expected)),
                "{known:?} => {checked:?}"
            );
        }
    }

    /// GAP K15: a conditional ceil equation `\ceil(I divInt J) = \top requires J =/=Int 0` is an
    /// axiom, not the domain of `divInt` (which stays its domain function); the solver states its
    /// instance beside that domain, so `\ceil(I divInt J)` is valid where `J =/=Int 0` is known,
    /// as the simplifier decides by the same equation, and not valid without it. GAP K18: the
    /// instance holds only where the terms it binds are defined.
    #[test]
    fn a_conditional_ceil_equation_is_a_fact_beside_the_domain() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-symbol neInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.ne"), smt-hook{}("distinct")]
                hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.ediv"), smt-hook{}("div")]
                axiom{R, Q} \implies{R}(
                    \equals{SortBool{}, R}(
                        neInt{}(J:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    ),
                    \equals{Q, R}(
                        \ceil{SortInt{}, Q}(divInt{}(I:SortInt{}, J:SortInt{})),
                        \and{Q}(\top{Q}(), \top{Q}())
                    )
                ) [label{}("div-defined"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();
        let defined = Predicate::Ceil(term(&definition, "divInt{}(X:SortInt{}, Y:SortInt{})"));
        let nonzero = Predicate::Term(term(
            &definition,
            r#"neInt{}(Y:SortInt{}, \dv{SortInt{}}("0"))"#,
        ));
        assert_eq!(
            solver.check_predicates(
                std::slice::from_ref(&nonzero),
                &Substitution::new(),
                std::slice::from_ref(&defined)
            ),
            Ok(Ok(Validity::Valid))
        );
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), std::slice::from_ref(&defined)),
            Ok(Ok(Validity::Contingent))
        );
        // The equation's variables range over elements, so its instance at `I := X divInt Y`
        // says nothing where `X divInt Y` is undefined: `\ceil((X divInt Y) divInt 2)` is not
        // valid (the definition leaves `X divInt 0` open), and an undefined `X divInt Y` beside
        // any statement about the outer quotient is satisfiable.
        let nested = term(
            &definition,
            r#"divInt{}(divInt{}(X:SortInt{}, Y:SortInt{}), \dv{SortInt{}}("2"))"#,
        );
        assert_eq!(
            solver.is_sat(
                &[
                    Predicate::Not(std::sync::Arc::new(defined)),
                    Predicate::Not(std::sync::Arc::new(Predicate::Equals(
                        nested.clone(),
                        term(&definition, r#"\dv{SortInt{}}("7")"#),
                    ))),
                ],
                &Substitution::new()
            ),
            Ok(Ok(Satisfiability::Sat))
        );
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), &[Predicate::Ceil(nested)]),
            Ok(Ok(Validity::Contingent))
        );
    }

    /// The definition of `an_smt_lemma_over_a_partial_operand_states_its_domain_or_is_left_out`:
    /// the lemma `f-zero` over `X divInt 2`, whose domain a ceil equation states, and the lemmas
    /// `g-zero` over `half(X)`, with no ceil equation, and `h-zero` over `X sdiv 2`, whose ceil
    /// equation's condition `nz(2)` has no SMT reading.
    fn partial_operand_lemma_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-symbol neInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.ne"), smt-hook{}("distinct")]
                hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
                hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.ediv"), smt-hook{}("div")]
                symbol half{}(SortInt{}) : SortInt{} [function{}(), smt-hook{}("(div #1 2)")]
                symbol f{}(SortInt{}) : SortInt{} [function{}(), total{}(), smtlib{}("f")]
                symbol g{}(SortInt{}) : SortInt{} [function{}(), total{}(), smtlib{}("g")]
                axiom{Q} \implies{Q}(\top{Q}(), \equals{Q, Q}(
                    \ceil{SortInt{}, Q}(divInt{}(I:SortInt{}, J:SortInt{})),
                    \and{Q}(\equals{SortBool{}, Q}(
                        neInt{}(J:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")),
                      \top{Q}()))) [simplification{}()]
                axiom{R} \implies{R}(
                    \equals{SortBool{}, R}(
                        gtInt{}(divInt{}(X:SortInt{}, \dv{SortInt{}}("2")), \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")),
                    \equals{SortInt{}, R}(f{}(X:SortInt{}),
                        \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}())))
                    [simplification{}(), smt-lemma{}(), label{}("f-zero")]
                axiom{R} \implies{R}(
                    \equals{SortBool{}, R}(
                        gtInt{}(half{}(X:SortInt{}), \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")),
                    \equals{SortInt{}, R}(g{}(X:SortInt{}),
                        \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}())))
                    [simplification{}(), smt-lemma{}(), label{}("g-zero")]
                hooked-symbol sdiv{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
                symbol nz{}(SortInt{}) : SortBool{} [function{}(), total{}()]
                symbol h{}(SortInt{}) : SortInt{} [function{}(), total{}(), smtlib{}("h")]
                axiom{Q} \implies{Q}(\top{Q}(), \equals{Q, Q}(
                    \ceil{SortInt{}, Q}(sdiv{}(I:SortInt{}, J:SortInt{})),
                    \and{Q}(\equals{SortBool{}, Q}(nz{}(J:SortInt{}), \dv{SortBool{}}("true")),
                      \top{Q}()))) [simplification{}()]
                axiom{R} \implies{R}(
                    \equals{SortBool{}, R}(
                        gtInt{}(sdiv{}(X:SortInt{}, \dv{SortInt{}}("2")), \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")),
                    \equals{SortInt{}, R}(h{}(X:SortInt{}),
                        \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}())))
                    [simplification{}(), smt-lemma{}(), label{}("h-zero")]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// GAP K21: the lemmas a prelude states are a function of the definition alone. A prelude
    /// is built lazily, at the first operation that needs the solver, which for an RPC session's
    /// other modules runs inside a request; its lemmas' domains are prepared detached from that
    /// request (`stop::detached`), so a prelude built under an already cancelled token states
    /// what one built outside it states. Before, the cancelled build left `f-zero`'s domain
    /// unprepared and dropped the lemma.
    #[test]
    fn a_cancelled_request_does_not_change_the_lemmas_a_prelude_states() {
        let definition = partial_operand_lemma_definition();
        let outside = SmtPrelude::from_definition(&definition).expect("the prelude is built");
        let token = CancellationToken::new();
        token.cancel();
        let inside = token
            .scope(|| SmtPrelude::from_definition(&definition))
            .expect("the prelude is built");
        assert_eq!(inside.dropped_lemmas(), outside.dropped_lemmas());
        assert_eq!(inside.declarations(), outside.declarations());
    }

    /// GAP K21: the report of the lemmas a prelude leaves out (`dropped_smt_lemmas`) is the
    /// prelude's own list, with the innermost operand whose domain no closed formula states and
    /// why: `half(X)`'s domain is an opaque `\ceil` (no ceil equation states it), and `X sdiv 2`'s
    /// ceil condition `nz(2)` has no SMT reading. Building the prelude counts them (`smt.lemmas_left_out`);
    /// reporting them counts nothing.
    #[test]
    fn a_left_out_lemma_is_reported_with_its_operand_and_reason() {
        use crate::smt::{LeftOutReason, dropped_smt_lemmas};
        use k_rust_kore::measure::{Counter, snapshot};
        let definition = partial_operand_lemma_definition();
        let before = snapshot();
        let prelude = SmtPrelude::from_definition(&definition).expect("the prelude is built");
        let built = snapshot();
        let dropped = dropped_smt_lemmas(&definition);
        let reported = snapshot();
        assert_eq!(
            dropped
                .iter()
                .map(|lemma| lemma.rule.attributes.unique_id.clone())
                .collect::<Vec<_>>(),
            prelude.dropped_lemmas()
        );
        // The operand by its head and arguments' shapes: the lemma's variables are renamed
        // where it is internalized.
        let operand = |lemma: &crate::smt::DroppedLemma<'_>| {
            let operand = lemma.operand.as_ref().expect("an operand");
            let crate::term::TermKind::Application {
                symbol, arguments, ..
            } = operand.kind()
            else {
                panic!("an application: {operand:?}");
            };
            let arguments = arguments
                .iter()
                .map(|argument| match argument.kind() {
                    crate::term::TermKind::Variable(_) => "X".to_owned(),
                    crate::term::TermKind::DomainValue { value, .. } => {
                        value.as_utf8().expect("UTF-8").to_owned()
                    }
                    _ => panic!("a variable or a domain value: {argument:?}"),
                })
                .collect::<Vec<_>>();
            format!("{}({})", symbol.name, arguments.join(", "))
        };
        let mut found = dropped
            .iter()
            .map(|lemma| {
                (
                    lemma.rule.attributes.label.clone().expect("a label"),
                    operand(lemma),
                    lemma.reason,
                )
            })
            .collect::<Vec<_>>();
        found.sort_by(|left, right| left.0.cmp(&right.0));
        assert_eq!(
            found,
            [
                (
                    "g-zero".to_owned(),
                    "half(X)".to_owned(),
                    LeftOutReason::OpaqueAtom
                ),
                (
                    "h-zero".to_owned(),
                    "sdiv(X, 2)".to_owned(),
                    LeftOutReason::AbstractedTerm
                ),
            ]
        );
        assert_eq!(built.delta(&before).get(Counter::SmtLemmasLeftOut), 2);
        // Building the prelude counts what its one translation of each lemma counted before
        // GAP K21: one operand domain read as an opaque `\ceil`, `g-zero`'s `half(X)`. Naming a
        // left-out lemma's operand, and the report, translate again for a reader, not for the
        // solver, and move no counter.
        assert_eq!(built.delta(&before).get(Counter::SmtOpaqueAtomDomains), 1);
        let moved = reported
            .delta(&built)
            .iter()
            .filter(|(_, value)| *value != 0)
            .collect::<Vec<_>>();
        assert!(moved.is_empty(), "the report moved {moved:?}");
    }

    /// GAP K18: an `smt-lemma` whose `requires` reads a partial operand is stated with the
    /// operand's domain, as a query's atom is, so it holds only where K's condition holds. With
    /// `\ceil(I divInt J) = (J =/=Int 0)` the domain of `X divInt 2` is a formula over the bound
    /// `X`, and `f(X) = 0 requires X divInt 2 >Int 0` decides `f(4) = 0`. A lemma whose operand's
    /// domain is an opaque `\ceil` (`half`, no ceil equation), a name of one query's
    /// translation, is left out, and the solver still starts. Before, either lemma made the
    /// prelude fail (`SmtLemmaSurplusPredicates`), and with it every query of the definition.
    /// So is `h(X) = 0 requires X sdiv 2 >Int 0`, whose domain plan, from the ceil equation
    /// `\ceil(I sdiv J) = nz(J)`, holds `nz(2)`, a term of no SMT reading that only one
    /// translation can name: before, it failed the prelude (`SmtLemmaSurplusMappings`).
    #[test]
    fn an_smt_lemma_over_a_partial_operand_states_its_domain_or_is_left_out() {
        let definition = partial_operand_lemma_definition();
        let prelude = SmtPrelude::from_definition(&definition).expect("the prelude is built");
        let id = |label: &str| {
            [
                definition.function_theory(),
                definition.simplification_theory(),
            ]
            .into_iter()
            .flat_map(|theory| theory.values())
            .flat_map(|groups| groups.values())
            .flatten()
            .find(|rule| rule.attributes.label.as_deref() == Some(label))
            .expect("the lemma")
            .attributes
            .unique_id
            .clone()
        };
        let mut dropped = prelude.dropped_lemmas().to_vec();
        dropped.sort();
        let mut expected = vec![id("g-zero"), id("h-zero")];
        expected.sort();
        assert_eq!(dropped, expected);
        let solver = Z3Solver::new(&definition).expect("Z3 should start");
        let zero = term(&definition, r#"\dv{SortInt{}}("0")"#);
        let at = |symbol: &str, argument: &str| {
            Predicate::Equals(
                term(
                    &definition,
                    &format!(r#"{symbol}{{}}(\dv{{SortInt{{}}}}("{argument}"))"#),
                ),
                zero.clone(),
            )
        };
        for (checked, expected) in [
            (at("f", "4"), Validity::Valid),
            (at("f", "1"), Validity::Contingent),
            (at("g", "4"), Validity::Contingent),
            (at("h", "4"), Validity::Contingent),
        ] {
            assert_eq!(
                solver.check_predicates(&[], &Substitution::new(), std::slice::from_ref(&checked)),
                Ok(Ok(expected)),
                "{checked:?}"
            );
        }
    }

    /// GAP K18: a term of an `smt-lemma`'s own text that has no SMT reading is the author's: the
    /// prelude cannot state the lemma, and says so (`SmtLemmaSurplusMappings`), as it did before
    /// domains were read. Only a term a domain plan brings in leaves the lemma out.
    #[test]
    fn an_smt_lemma_whose_own_term_has_no_smt_reading_is_refused() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol nz{}(SortInt{}) : SortBool{} [function{}(), total{}()]
                symbol h{}(SortInt{}) : SortInt{} [function{}(), total{}(), smtlib{}("h")]
                axiom{R} \implies{R}(
                    \equals{SortBool{}, R}(nz{}(\dv{SortInt{}}("2")), \dv{SortBool{}}("true")),
                    \equals{SortInt{}, R}(h{}(X:SortInt{}),
                        \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}())))
                    [simplification{}(), smt-lemma{}(), label{}("h-zero")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        assert!(
            matches!(
                SmtPrelude::from_definition(&definition),
                Err(crate::smt::TranslationError::SmtLemmaSurplusMappings { .. })
            ),
            "{:?}",
            SmtPrelude::from_definition(&definition).map(|prelude| prelude.declarations().to_vec())
        );
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

    /// The `requires` `2 ^Int X ==Int 3` of a rule, as the backend wrote it for Z3 before GAP K32
    /// read a power with a symbolic exponent without Z3's own power (`guard_powers`). It is
    /// satisfiable (`X = -1`, with the power outside the integers equal to 3), and Z3 either
    /// decides it in a few thousand resource units or takes a path on which it never decides it;
    /// which path it takes depends on everything the Z3 context it runs in has seen.
    pub(super) const PATH_SENSITIVE_QUERY: &str = r#"(declare-sort |SortFloat| 0)
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
    pub(super) const NONLINEAR_QUERY: &str = "(declare-const x Int)\n(declare-const y Int)\n\
        (declare-const z Int)\n(assert (> x 1))\n(assert (> y 1))\n(assert (> z 1))\n\
        (assert (= (+ (* x x x) (* y y y)) (* z z z)))";

    /// The answers of `count` uncached checks of `script` by `solver`, as `S`, `U` or `?`.
    pub(super) fn answers(solver: &Z3Solver, script: &str, count: usize) -> String {
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
    /// rule, as the backend wrote it for Z3 before GAP K32 read a power with a symbolic exponent
    /// without Z3's own power (its prelude declares the Real-valued function outside the
    /// integers, and not `KRUST-POWER` or `KRUST-POWER-VALUE`). It is satisfiable
    /// (`2021027 = 1009 * 2003`), and the path Z3 takes on it from a fresh context does not
    /// decide it. The text is kept: with the current prelude's power declarations, which the
    /// check does not use, Z3 4.16.0 takes another path and one attempt of 1,000,000 units
    /// decides it, so the script would no longer show a retry's path.
    pub(super) const FACTORING_QUERY: &str = r#"(declare-sort |SortACell| 0)
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
    /// fresh context, and by three attempts of 250,000, 500,000 and 1,000,000 (when each attempt
    /// read the script again, the third decided it; 4.12.5 decides it within neither).
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
            assert_eq!((single.as_str(), retried.as_str()), ("?", "?"));
        }
    }

    /// A retry checks the assertions the first attempt loaded, never the script read again: a
    /// recursive definition is a declaration of the query's context, which Z3 5.3.3 refuses to
    /// read twice, so a reloaded script with one would be rejected at its first retry.
    #[test]
    fn a_retry_of_a_script_with_a_recursive_definition_is_checked_again() {
        const RECURSIVE: &str = "(declare-fun g (Int) Int)\n\
            (define-fun-rec f ((x Int)) Int (ite (<= x 0) 0 (f (- x 1))))\n\
            (assert (= (f (g 7)) 1))\n(assert (> (g 7) 100000))";
        let solver = Z3Solver::with_options(
            &definition(),
            Z3Options {
                timeout_ms: 125,
                retry_limit: 2,
                resource_limit: NonZeroU32::new(100),
            },
        )
        .unwrap();
        assert_eq!(answers(&solver, RECURSIVE, 1), "?");
        assert_eq!(solver.attempt_limits().len(), 3);
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
