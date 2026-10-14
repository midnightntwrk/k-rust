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
//! bound = "zero checks after a sat query; otherwise at most one prelude check, with configured retries, before the first unsat answer"
//! ```
//!
//! In-process Z3 behind a bounded FIFO result cache: `Counter::SmtQueries` in,
//! `Counter::SmtSolverRuns` out (the lazy prelude check and the model path count solver
//! runs without a query), O(L x log E) per hit for a script of L bytes among E cached entries,
//! eviction pops the oldest entry until the entry and key-byte limits admit the new key. A solver
//! is constructed per uncached query. Construction does not create a Z3 context; a satisfiable
//! query establishes prelude consistency, while the first unsatisfiable answer requires one
//! explicit prelude check.
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

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
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
    ModelResult, Satisfiability, SmtError, SmtPrelude, SmtSolver, TranslatedQuery, Validity,
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Z3Options {
    pub timeout_ms: u32,
    pub retry_limit: u32,
}

impl Default for Z3Options {
    fn default() -> Self {
        Self {
            timeout_ms: 125,
            retry_limit: 3,
        }
    }
}

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
const APPROXIMATE_MODEL_REASON: &str =
    "the query abstracts symbols or sorts; a solver model is not a model of the predicate";

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

    /// The parameters of one attempt with the given timeout: the timeout and its resource limit.
    fn attempt_parameters(&self, timeout: u32) -> Params {
        let mut parameters = Params::new();
        parameters.set_u32("rlimit", resource_limit(timeout));
        #[cfg(test)]
        let clocked = !self.without_clock;
        #[cfg(not(test))]
        let clocked = true;
        if clocked {
            parameters.set_u32("timeout", timeout);
        }
        parameters
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

    /// Check that the prelude (the definition's axioms and the user prelude) is satisfiable.
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
            Satisfiability::Sat => {
                *state = PreludeState::Consistent;
                return Ok(());
            }
            Satisfiability::Unsat => PreludeFailure::Inconsistent,
            Satisfiability::Unknown(reason) => PreludeFailure::Unknown(reason.into()),
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

    /// Solve `script` through the result cache. A stop observed before the lookup ends the
    /// query: its answer is not needed, and neither the cache nor Z3 is consulted.
    fn solve(&self, script: &str) -> Stoppable<Satisfiability> {
        let _span = measure::algorithm_span(Algorithm::BackendSmtCache);
        stop::check()?;
        measure::bump(Counter::SmtQueries);
        if let Some(result) = self
            .result_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get(script)
        {
            return Ok(result);
        }

        let result = self.solve_uncached(script)?;
        self.result_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .insert(script, &result);
        Ok(result)
    }

    /// Solve `script` with Z3, doubling the timeout on each retry of an unknown answer. Each
    /// attempt is preceded by a poll, so a stop raised meanwhile ends the query instead of
    /// starting another attempt.
    fn solve_uncached(&self, script: &str) -> Stoppable<Satisfiability> {
        measure::bump(Counter::SmtSolverRuns);
        #[cfg(test)]
        self.uncached_solve_count.fetch_add(1, Ordering::Relaxed);

        let mut timeout = self.options.timeout_ms;
        for attempt in 0..=self.options.retry_limit {
            stop::check()?;
            let solver = Solver::new();
            solver.set_params(&self.attempt_parameters(timeout));
            #[cfg(test)]
            self.record_attempt(timeout);
            solver.from_string(script);
            match measured_check(&solver) {
                SatResult::Sat => return Ok(Satisfiability::Sat),
                SatResult::Unsat => return Ok(Satisfiability::Unsat),
                SatResult::Unknown if attempt < self.options.retry_limit => {
                    timeout = timeout.saturating_mul(2);
                }
                SatResult::Unknown => {
                    return Ok(Satisfiability::Unknown(
                        solver
                            .get_reason_unknown()
                            .unwrap_or_else(|| "Z3 returned unknown".into()),
                    ));
                }
            }
        }
        unreachable!("the retry loop always returns")
    }

    fn solve_query(
        &self,
        query: &TranslatedQuery,
        assertion: Option<&str>,
    ) -> Stoppable<Satisfiability> {
        let mut script = query.base().to_owned();
        if let Some(assertion) = assertion {
            script.push_str("\n(assert ");
            script.push_str(assertion);
            script.push(')');
        }
        if let Some(failure) = self.prelude_failure() {
            return Err(self.prelude_stop(failure));
        }
        self.confirm_answer(self.solve(&script)?)
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
        let mut timeout = self.options.timeout_ms;
        for attempt in 0..=self.options.retry_limit {
            stop::check()?;
            measure::bump(Counter::SmtSolverRuns);
            let solver = Solver::new();
            solver.set_params(&self.attempt_parameters(timeout));
            #[cfg(test)]
            self.record_attempt(timeout);
            solver.from_string(query.base());
            match measured_check(&solver) {
                SatResult::Sat => {
                    // confirm_answer returns its argument unchanged; only the prelude check matters
                    // here.
                    let _: Satisfiability = self.confirm_answer(Satisfiability::Sat)?;
                    let Some(mappings) = query.model_mappings() else {
                        return Ok(Ok(ModelResult::Unknown(APPROXIMATE_MODEL_REASON.into())));
                    };
                    let Some(model) = solver.get_model() else {
                        return Ok(Err(SmtError::MissingModel));
                    };
                    return Ok(self.extract_model(&model, mappings, variables));
                }
                SatResult::Unsat => {
                    let _: Satisfiability = self.confirm_answer(Satisfiability::Unsat)?;
                    return Ok(Ok(ModelResult::Unsat));
                }
                SatResult::Unknown if attempt < self.options.retry_limit => {
                    timeout = timeout.saturating_mul(2);
                }
                SatResult::Unknown => {
                    let reason = solver
                        .get_reason_unknown()
                        .unwrap_or_else(|| "Z3 returned unknown".into());
                    let _: Satisfiability =
                        self.confirm_answer(Satisfiability::Unknown(reason.clone()))?;
                    return Ok(Ok(ModelResult::Unknown(reason)));
                }
            }
        }
        unreachable!("the retry loop always returns")
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
                    Term::domain_value_of(DomainKind::Int, variable.sort.clone(), rendered)
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
                    Term::domain_value_of(
                        DomainKind::Bool,
                        variable.sort.clone(),
                        value.to_string(),
                    )
                }
                _ => term,
            };
            substitution.insert(variable.clone(), value);
        }
        Ok(ModelResult::Sat(substitution))
    }
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

fn decide_validity(
    mut solve: impl FnMut(ValiditySubquery) -> Stoppable<Satisfiability>,
) -> Stoppable<Validity> {
    Ok(match solve(ValiditySubquery::Positive)? {
        Satisfiability::Sat => match solve(ValiditySubquery::Negative)? {
            Satisfiability::Unsat => Validity::Valid,
            Satisfiability::Sat => Validity::Contingent,
            Satisfiability::Unknown(reason) => Validity::Unknown(reason),
        },
        Satisfiability::Unsat => match solve(ValiditySubquery::Base)? {
            Satisfiability::Unsat => Validity::InconsistentGroundTruth,
            Satisfiability::Sat => Validity::Refuted,
            Satisfiability::Unknown(reason) => Validity::Unknown(reason),
        },
        Satisfiability::Unknown(positive_reason) => match solve(ValiditySubquery::Base)? {
            Satisfiability::Unsat => Validity::InconsistentGroundTruth,
            Satisfiability::Unknown(reason) => Validity::Unknown(reason),
            Satisfiability::Sat => match solve(ValiditySubquery::Negative)? {
                Satisfiability::Unsat => Validity::Valid,
                Satisfiability::Sat | Satisfiability::Unknown(_) => {
                    Validity::Unknown(positive_reason)
                }
            },
        },
    })
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
        self.solve_query(&query, None).map(Ok)
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
        .map(Ok)
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
        let no_fixed_point = Predicate::Not(Box::new(Predicate::Exists(
            x(),
            Box::new(Predicate::Equals(
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
                Box::new(Predicate::Ceil(term(&definition, "opaque{}(X:SortInt{})"))),
            );
            let some_undefined = Predicate::Exists(
                Variable::new(name, Sort::simple("SortInt")),
                Box::new(Predicate::Not(Box::new(Predicate::Ceil(term(
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
                Box::new(Predicate::In(
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
                Box::new(Predicate::And(vec![
                    equals("1"),
                    Predicate::Exists(x(), Box::new(equals("2"))),
                    equals("1"),
                ])),
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
            Box::new(Predicate::Equals(
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
                Box::new(Predicate::Forall(
                    inner.clone(),
                    Box::new(Predicate::In(Term::variable(outer), Term::variable(inner))),
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
            Box::new(Predicate::In(Term::variable(x()), Term::variable(x()))),
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
                sort SortList{} []
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
                        Ok(fixed(subquery))
                    })
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
        let nonnegative = Predicate::Not(Box::new(negative));
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
}
