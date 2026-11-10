//! ```toml algorithm-site
//! id = "backend.rewrite.execute"
//! role = "part"
//! sites = ["Backend::execute_using"]
//! ```
//!
//! One orchestration path for the CLI, RPC server, and JavaScript hosts: a session, one solver per module, and execution, search, simplification, implication, and proving operations. `wire` contains the JavaScript JSON contracts.
//!
//! This module is the supported surface for embedding k-rust in a Rust host.
//! Besides its own items, it re-exports by name the backend items a host needs to bound an
//! operation and to match or construct the cause of a stop ([`CancellationToken`],
//! [`StopCause`], [`StopScope`], [`StackLimit`], [`SegmentRefused`], [`PreludeFailure`],
//! [`StepTimeoutMode`]) and the [`VARIABLE_IDENTITY`] contract version beside
//! [`BACKEND_SCHEMA_VERSION`].
//! The backend types that [`Backend::with_solver`] and the internalizing constructors carry are
//! named through [`crate::k_rust_backend`], which makes no stability promise of its own.
//!
//! # Bounding an operation
//!
//! A host bounds a request with a [`CancellationToken`]: it runs the request inside the token's
//! scope on the thread that performs it (`token.scope(|| backend.execute_kore(request))`) and
//! calls [`CancellationToken::cancel`] from any thread.
//! An operation that stops does so for a [`StopCause`], and an error it returns for a stop names
//! that cause ([`BackendError::stop_cause`]).
//!
//! 1. The operations that link to this section ([`Backend::execute_kore`],
//!    [`Backend::search_kore`] and their variants, [`Backend::prove_kore`], the `_json` form of
//!    each, [`Backend::simplify_json`], [`Backend::implies_json`] and
//!    [`Backend::get_model_json`]), [`Backend::match_patterns`] and any operation run through
//!    [`Backend::with_solver`] run inside one operation boundary, in both builds. A request
//!    cancelled before its operation starts does not run: the operation returns `Err(e)` with
//!    `e.stop_cause() == Some(&StopCause::Cancelled)`. Constructing a [`Backend`] inside the
//!    token's scope fails the same way. An error the request has before the boundary is reported
//!    instead: an unsupported schema version, an operation this build does not provide
//!    ([`Backend::get_model_json`] without the `z3-inference` feature, step timeouts on wasm32),
//!    an unknown module or a module that fails to load, and a state too deep for the backend.
//!    [`Backend::add_module`], [`Backend::rule_catalog`], [`Backend::select_definition`] and the
//!    internalizing constructors ([`Backend::internalize_definition`],
//!    [`Backend::internalize_source_definition`]) have no boundary and never answer `Cancelled`;
//!    those that load a definition (`select_definition`, the internalizing constructors) do not
//!    read the token, as point 6 says.
//! 2. A cancellation observed while [`Backend::execute_kore`] or a search
//!    ([`Backend::search_kore`] and its path and pattern variants) explores ends the whole run, and
//!    the run reports it in its result. An execution returns `Ok` with the leaves completed before
//!    the cancellation and the stopped state as a `cancelled` leaf
//!    ([`HaltReasonOutput::Cancelled`]); it does not list the states still pending. A search
//!    returns `Ok` with a `cancelled` incomplete entry ([`IncompleteSearchOutput::Cancelled`]) for
//!    the stopped state. Such a result is incomplete and makes no coverage claim. An execution
//!    whose request sets [`ExecuteRequest::cancelled_result`] to `error` answers such a
//!    cancellation as `Err(e)` with `e.stop_cause() == Some(&StopCause::Cancelled)` instead,
//!    whichever phase observed it (the exploration, the passes after it, or the conversion of the
//!    leaves), and builds no leaf beyond the stopped state's own, which the observing poll builds
//!    and the run discards; point 3's rule then holds for that execution too.
//! 3. The simplification, implication and model operations ([`Backend::simplify_json`],
//!    [`Backend::implies_json`], [`Backend::get_model_json`] and their pattern forms
//!    [`Backend::simplify_kore`], [`Backend::implies_kore`] and `Backend::model_for`) report a
//!    cancellation observed at any point, including one a refinement observed and set aside, as
//!    `Err(e)` with `e.stop_cause() == Some(&StopCause::Cancelled)`: each polls once more after its
//!    work returns. [`Backend::prove_kore`] reports a cancellation as that `Err` unless the proof's
//!    verdict no longer depends on the work the cancellation prevented (`ProofResult::settled`):
//!    it keeps `Ok` when it found a certified refutation (`disproved`), or when no state it left
//!    unexplored could add a leaf at most as deep as the proof's horizon, the depth of its
//!    `max_counterexamples`-th shallowest leaf that is not proven (any state, before it has that
//!    many), and no refinement of a leaf set the cancellation aside. Any other cancelled proof
//!    could change status if it went on, so it is the `Err`. A failed solver prelude is always an `Err`. So a cancelled
//!    operation answers `Err` with the `Cancelled` cause, except a cancellation observed during an
//!    execution (under the default `cancelledResult: partial`) or search run, which is a
//!    `cancelled` leaf or entry, and a proof whose verdict it could not change.
//! 4. A cancellation that lands after the boundary's entry poll and before the run's first poll
//!    still gives, under `cancelledResult: partial` (the default), `Ok` with a depth-0 `cancelled`
//!    leaf (a search: a `cancelled` entry for its initial state), in both builds; under `error` the
//!    same timing answers the `Err`. Which shape a host gets depends only on timing, so a host
//!    treats both `Err` with the `Cancelled` cause and a `cancelled` leaf or entry as a
//!    cancellation; point 1 does not mean that a depth-0 `cancelled` leaf cannot occur.
//! 5. The step deadline of a request ([`ExecuteRequest::step_timeout_ms`],
//!    [`ProveRequest::step_timeout_ms`]) is not a cancellation: a step that passes it ends its own
//!    state as a `timeout` leaf, and execution goes on with the other states while a proof ends.
//! 6. Loading a module's definition (on construction, or on a module's first use) happens before
//!    the boundary and is not cancellable: a cancellation does not interrupt it, and a
//!    [`Backend`] constructed inside a cancelled scope loads its default module and then fails at
//!    the boundary as in point 1. A load is detached from the request's token: neither the
//!    load-time critical-pair check nor the discharge of rewrite rules' definedness obligations
//!    reads it, so a definition loaded or cached inside a cancelled request (a module first used
//!    by a cancelled request, or one an internalizing constructor returns inside a cancelled
//!    scope) equals one loaded outside any token's scope
//!    (`crates/k-rust/tests/load_cancellation.rs`). Both are bounded by a budget of polls
//!    instead, so a load ends however its definition's conditions evaluate
//!    (`docs/backend-port.md`, the critical-pair check).
//! 7. The work budget of an execution ([`ExecuteRequest::max_work`]) is not a cancellation and
//!    never an `Err`: a run that reaches it returns `Ok`, and like a cancelled run it reports the
//!    leaves completed before the stop and the state it did not visit as one leaf, a
//!    `work-bound` one ([`HaltReasonOutput::WorkBound`]), and drops the states still pending.
//!    Unlike a cancellation it is deterministic: the run stops at the same state wherever its
//!    result is the same (docs/compatibility.md, "Work budget").
//! 8. The bound of polls of an execution ([`ExecuteRequest::max_polls`]) bounds all of its work,
//!    inside its steps included, and is not a cancellation either: a run that reaches it returns
//!    `Ok` under either `cancelledResult`, with the leaves completed before the stop and the
//!    state it was expanding as one `poll-bound` leaf ([`HaltReasonOutput::PollBound`]). Every
//!    result reports the polls it counted ([`ExecutionResult::polls`]), the same on a fresh and
//!    on a reused `Backend` (docs/compatibility.md, "Poll budget").
//!
//! With the `z3-inference` feature, a solver whose prelude failed stops every operation that uses
//! it, as `Err(e)` with a `SolverPrelude` cause, at the boundary or during the run. A prelude
//! whose check timed out (`PreludeFailure::Unknown`; the check runs under the solver's timeout
//! the first time a query answers `unsat`) fails for a reason of time, not of the definition: the
//! error is not a fact to cache, and since the `Backend` keeps the failure, a host rebuilds it.
//! An execution's [`ExecutionResult::smt_unknowns`] counts the undecided solver answers (a
//! timeout among them) the run took decisions from; a run that reports none gives the same
//! result on a fresh and on a reused `Backend` (docs/compatibility.md, "Determinism and
//! concurrency").
//!
//! Every operation, an execution's result aside, can also be read as a whole by a host that must
//! know whether its outcome is a function of its inputs: run inside
//! [`k_rust_backend::stop::with_operation_record`], the operation's record counts the `Unknown`
//! answers of the solver it received (a condition so answered stays undecided, while one left
//! undecided on decided answers alone counts nothing) and the stops for lack of native stack it
//! met, a dismissed one included, whatever poll budget or record encloses the call.
//!
//! An execution cancelled by a watchdog thread, with names from `k_rust` alone:
//!
//! ```
//! use std::{thread, time::Duration};
//!
//! use k_rust::backend::{
//!     Backend, BackendOptions, CancellationToken, ExecuteRequest, HaltReasonOutput, StopCause,
//! };
//! use k_rust::kore::parser::parse_pattern;
//!
//! // `count(I) => count(I +Int 1)`: a run that never ends by itself.
//! let definition = r#"[]
//! module LOOP
//!   hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
//!   sort SortS{} []
//!   symbol count{}(SortInt{}) : SortS{} [constructor{}(), functional{}()]
//!   hooked-symbol add{}(SortInt{}, SortInt{}) : SortInt{}
//!     [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
//!   axiom{} \rewrites{SortS{}}(
//!     \and{SortS{}}(count{}(I:SortInt{}), \top{SortS{}}()),
//!     \and{SortS{}}(count{}(add{}(I:SortInt{}, \dv{SortInt{}}("1"))), \top{SortS{}}())
//!   ) [label{}("count")]
//! endmodule []"#;
//! let mut backend = Backend::new(definition, "LOOP", BackendOptions::default())?;
//! let start = parse_pattern(r#"count{}(\dv{SortInt{}}("0"))"#)?;
//!
//! let token = CancellationToken::new();
//! let watchdog = {
//!     let token = token.clone();
//!     thread::spawn(move || {
//!         thread::sleep(Duration::from_millis(100));
//!         token.cancel();
//!     })
//! };
//! let outcome = token.scope(|| backend.execute_kore(ExecuteRequest::new(start)));
//! watchdog.join().unwrap();
//!
//! // Both shapes are a cancellation (points 1, 2 and 4): which one a run gives depends on when
//! // the cancellation lands.
//! let cancelled = match outcome {
//!     Err(error) => error.stop_cause() == Some(&StopCause::Cancelled),
//!     Ok(result) => result
//!         .leaves
//!         .iter()
//!         .any(|leaf| matches!(leaf.reason, HaltReasonOutput::Cancelled)),
//! };
//! assert!(cancelled);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::Arc,
    time::Duration,
};

#[cfg(not(feature = "z3-inference"))]
use k_rust_backend::smt::NoSolver;
#[cfg(feature = "z3-inference")]
use k_rust_backend::smt::{ModelResult, Z3Options, Z3Solver};
use k_rust_backend::stop;
#[cfg(feature = "z3-inference")]
use k_rust_backend::substitution::Substitution;
use k_rust_backend::{
    definition::{Admission, Admitted, BackendDefinition, DefinitionError},
    evaluation::{EvaluationMode, EvaluationScope},
    externalize,
    fresh::RequestNames,
    implication::{ImplicationFailure, ImplicationStatus},
    proof::{ProofError, ProofLeafOutcome, ProofOptions, ProofSearchOrder, ProofStatus},
    rewrite::{
        ChainOptions, ChainStep, CheckedChain, ExecutionBranchMode, ExecutionMode,
        ExecutionOptions, HaltReason, StateMatchOptions, TraceKind, UnlessPart, execute_in_process,
        execute_observed_with_solver, execute_with_solver,
    },
    rule::ClassifiedAxiom,
    search::{
        SearchOptions, SearchType, search_graph_observed_with_solver, search_graph_with_solver,
        search_paths_observed_with_solver, search_paths_with_solver,
        search_pattern_observed_with_solver, search_pattern_paths_observed_with_solver,
        search_pattern_paths_with_solver, search_pattern_with_solver,
    },
    session::{BackendSession, SessionError},
    simplify::{DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError},
    smt::SmtSolver,
    term::{Name, Sort},
    transition::ObservationOptions,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, value::RawValue};

#[cfg(test)]
use k_rust_backend::rule::Predicate;

use crate::kore::{
    ast::Pattern as KorePattern,
    ast::Variable as KoreVariable,
    codec as kore_codec,
    parser::{parse_definition, parse_module},
};

pub mod execution;
pub mod implication;
pub mod proving;
pub mod search;
pub mod simplification;
mod wire;
pub use wire::*;

pub use k_rust_backend::definition::{
    EXECUTION_DIGEST_VERSION, ExecutionDigest, ExecutionDigestError, ExecutionRole,
    ParseExecutionDigestError, UnstatedDefinedness, execution_digest, execution_role,
};
pub use k_rust_backend::nesting::SegmentRefused;
pub use k_rust_backend::rewrite::{
    CellHandle, InProcess, Probe, ProbeArrival, ProbeCycle, ProbeDecision, ProbeLeaf, ProbePath,
    ProbeRules, ProbeState, StopArrival, StopCondition, StopConditionRefusal, StopDecision,
    StopSide, SuccessorCandidate, SuccessorReading,
};
pub use k_rust_backend::stop::{
    CancellationToken, PreludeFailure, StackLimit, StopCause, StopScope,
};
pub use k_rust_backend::term::names::VARIABLE_IDENTITY;
pub use k_rust_backend::timeout::StepTimeoutMode;

/// The solver options of a [`Backend`]: how each Z3 check is bounded and how often an unknown
/// answer is retried. A build without Z3 reads none of them.
///
/// The default bounds every attempt by Z3's own resource units ([`SmtBudget::DEFAULT`]), so
/// whether a query is decided is a function of the query, these options and the Z3 build, never
/// of the machine's speed or load (docs/compatibility.md, "Determinism and concurrency"). A
/// clock is only ever asked for: by [`SmtBudget::clock`], or on the wire by `smtTimeoutMs`.
///
/// On the wire (camelCase) the budget is `smtResourceLimit` (units, positive) or `smtTimeoutMs`
/// (the clock), never both; with neither it is the default units. `smtRetryLimit` defaults to 3.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(try_from = "WireBackendOptions")]
pub struct BackendOptions {
    /// The first attempt's bound, doubled on each retry.
    pub smt_budget: SmtBudget,
    /// The retries of an unknown answer.
    pub smt_retry_limit: u32,
}

/// The wire form of [`BackendOptions`].
#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
struct WireBackendOptions {
    #[serde(default)]
    smt_timeout_ms: Option<u32>,
    #[serde(default)]
    smt_retry_limit: Option<u32>,
    #[serde(default)]
    smt_resource_limit: Option<std::num::NonZeroU32>,
}

impl TryFrom<WireBackendOptions> for BackendOptions {
    type Error = k_rust_backend::smt::BudgetConflict;

    fn try_from(wire: WireBackendOptions) -> Result<Self, Self::Error> {
        #[expect(
            clippy::disallowed_methods,
            reason = "an explicit `smtTimeoutMs` on the wire asks for the clock"
        )]
        let smt_budget = SmtBudget::requested(wire.smt_timeout_ms, wire.smt_resource_limit)?;
        Ok(Self {
            smt_budget,
            smt_retry_limit: wire
                .smt_retry_limit
                .unwrap_or(Self::DEFAULT.smt_retry_limit),
        })
    }
}

impl Default for BackendOptions {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// The Z3 resource units of the first attempt of the default options; its calibration is
/// documented where the backend defines it.
pub use k_rust_backend::smt::DEFAULT_SMT_RESOURCE_LIMIT;
pub use k_rust_backend::smt::{BudgetConflict, SmtBudget, SmtClock};

impl BackendOptions {
    /// The default options: [`SmtBudget::DEFAULT`] (each attempt bounded by Z3 resource units
    /// only, [`DEFAULT_SMT_RESOURCE_LIMIT`] for the first and twice the previous for each retry)
    /// and 3 retries.
    pub const DEFAULT: Self = Self {
        smt_budget: SmtBudget::DEFAULT,
        smt_retry_limit: 3,
    };

    /// The options a binding's fields ask for (`smtTimeoutMs`, `smtResourceLimit`,
    /// `smtRetryLimit`), read as the wire reads them: units unless only `smtTimeoutMs` is given,
    /// which asks for the clock. A binding states in an
    /// `#[expect(clippy::disallowed_methods, reason = ...)]` that its field asks for the clock.
    ///
    /// # Errors
    ///
    /// Both bounds given, or `smtResourceLimit` 0.
    pub fn requested(
        smt_timeout_ms: Option<u32>,
        smt_resource_limit: Option<u32>,
        smt_retry_limit: Option<u32>,
    ) -> Result<Self, String> {
        let smt_resource_limit = smt_resource_limit
            .map(|units| {
                std::num::NonZeroU32::new(units)
                    .ok_or_else(|| "smtResourceLimit must be positive".to_owned())
            })
            .transpose()?;
        Self::try_from(WireBackendOptions {
            smt_timeout_ms,
            smt_retry_limit,
            smt_resource_limit,
        })
        .map_err(|conflict| format!("smtTimeoutMs and smtResourceLimit: {conflict}"))
    }
}

/// The KORE symbol of a compiled configuration's top cell.
const GENERATED_TOP: &str = "Lbl'-LT-'generatedTop'-GT-'";
/// The KORE symbol of the cell compilation adds to a configuration to number fresh values.
const GENERATED_COUNTER: &str = "Lbl'-LT-'generatedCounter'-GT-'";

/// `pattern`, a configuration, with the content of its `<generatedCounter>` cell erased: when
/// `pattern` is a `<generatedTop>` application whose last argument is a `<generatedCounter>`
/// application of one argument, `pattern` with that argument replaced by `\dv{SortInt{}}("0")`;
/// otherwise `pattern` unchanged. Two configurations have equal erasures exactly when they are
/// equal outside the counter's content.
///
/// The counter is how compilation encodes a rule's `!` variables (`docs/compatibility.md`,
/// "Compiler-resolved fresh constants"): it holds the first value not yet minted, so that a
/// later step mints none of the values minted before. The definition's author does not declare
/// it, and at a final configuration, from which no step follows, it constrains nothing: two final
/// configurations that differ only in the counter have the same declared content and the same
/// (empty) future. How many values a run minted shows only through the cells the minted values
/// reach, which the erasure keeps. A client that compares the final configurations of two
/// definitions (the fuzz's differential target, kink's whole-term projection) compares their
/// erasures, through this one function.
#[must_use]
pub fn counter_erased(pattern: &KorePattern) -> std::borrow::Cow<'_, KorePattern> {
    use std::borrow::Cow;
    let KorePattern::Application { symbol, arguments } = pattern else {
        return Cow::Borrowed(pattern);
    };
    let Some(KorePattern::Application {
        symbol: counter,
        arguments: content,
    }) = arguments.last()
    else {
        return Cow::Borrowed(pattern);
    };
    if symbol.name != GENERATED_TOP || counter.name != GENERATED_COUNTER || content.len() != 1 {
        return Cow::Borrowed(pattern);
    }
    let erased = KorePattern::DomainValue {
        sort: crate::kore::ast::Sort::Application {
            name: "SortInt".to_owned(),
            arguments: Vec::new(),
        },
        value: "0".into(),
    };
    if content[0] == erased {
        return Cow::Borrowed(pattern);
    }
    let mut arguments = arguments.clone();
    if let Some(KorePattern::Application { arguments, .. }) = arguments.last_mut() {
        arguments[0] = erased;
    }
    Cow::Owned(KorePattern::Application {
        symbol: symbol.clone(),
        arguments,
    })
}

/// The version of the Z3 library this build links, as Z3 reports it, which counts the resource
/// units of [`SmtBudget::Units`]; `None` in a build without Z3.
#[must_use]
pub fn z3_version() -> Option<&'static str> {
    #[cfg(feature = "z3-inference")]
    {
        Some(k_rust_backend::smt::z3_version())
    }
    #[cfg(not(feature = "z3-inference"))]
    {
        None
    }
}

/// The Z3 build this process runs: Z3's version string ([`z3_version`]) and the SHA-256 of the
/// library file Z3's code comes from.
///
/// Z3 counts the resource units of [`SmtBudget::Units`] in its own search, so
/// how many units a query takes is a function of the machine code that searches: two builds of
/// one version (another compiler, other flags, another architecture) can count differently, and
/// a version string names no build. The library file names that code, and nothing else: the
/// shared library when Z3 is linked dynamically, and when it is linked statically the archive
/// (`libz3.a`) the link took it from. A static link's code sits in the executable among the
/// program around it, so the executable's digest would change with every change to that program
/// while Z3 stays the same; the archive's does not.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Z3Build {
    /// Z3's version string (`Z3_get_full_version`).
    pub version: &'static str,
    /// The lowercase hexadecimal SHA-256 of the library file Z3's code comes from. Under a
    /// dynamic link it is the shared library this process maps, read when first asked. Under a
    /// static link it is the archive k-rust's build script recorded (`build/z3_archive.rs`): the
    /// published release asset's `libz3.a` when the build downloads it, or the archive found in
    /// the linker's search path. `None` when it cannot be named: a shared library replaced since
    /// it was mapped, a static link whose archive the build could not name (or whose recorded
    /// archive holds another release than the linked Z3 reports), or a platform without
    /// `/proc/self/maps` and no recorded archive; this process then cannot say which build
    /// answers.
    pub library_sha256: Option<String>,
}

/// The SHA-256 of the archive k-rust's build script found a static link takes Z3 from, empty
/// when it found none.
const Z3_ARCHIVE_SHA256: &str = env!("K_RUST_Z3_ARCHIVE_SHA256");
/// The Z3 release that archive holds (`5.3.3`), empty when it found none.
const Z3_ARCHIVE_RELEASE: &str = env!("K_RUST_Z3_ARCHIVE_RELEASE");

/// The Z3 build this process links ([`Z3Build`]), computed once per process; `None` in a build
/// without Z3.
#[must_use]
pub fn z3_build() -> Option<&'static Z3Build> {
    static BUILD: std::sync::OnceLock<Option<Z3Build>> = std::sync::OnceLock::new();
    BUILD
        .get_or_init(|| {
            let version = z3_version()?;
            // Z3's version string is a constant of Z3's own image and this function is code of
            // k-rust's, so the two lie in mappings of one file exactly when Z3 is linked into the
            // same image as k-rust, statically.
            let z3_image = mapped_file(version.as_ptr() as usize);
            let own_image = mapped_file(z3_build as fn() -> Option<&'static Z3Build> as usize);
            // The recorded archive names this build only if it holds the release Z3 reports.
            let archive = (!Z3_ARCHIVE_SHA256.is_empty()
                && names_release(version, Z3_ARCHIVE_RELEASE))
            .then(|| Z3_ARCHIVE_SHA256.to_owned());
            let library_sha256 = match (z3_image, own_image) {
                (Some(z3_image), Some(own_image)) if z3_image != own_image => {
                    // Dynamic: the shared library, unless it was replaced since it was mapped.
                    z3_image
                        .strip_suffix(" (deleted)")
                        .is_none()
                        .then(|| file_sha256(std::path::Path::new(&z3_image)))
                        .flatten()
                }
                // Static, or no `/proc` to tell: the archive the build recorded for its static
                // link, if any.
                _ => archive,
            };
            Some(Z3Build {
                version,
                library_sha256,
            })
        })
        .as_ref()
}

/// The solver an output's answers were decided with: whether each Z3 attempt is bounded by Z3
/// resource units or by the clock, the first attempt's bound, the retries, each at twice the
/// previous bound, and the Z3 build ([`SolverBuild`]). Under resource units an answer is a
/// function of the question, these options and the Z3 build; under the clock it also depends
/// on the host's speed and load. Every output of krust, krs and kink whose content depends on a
/// solver answer carries it (or, in kink's stores, the same facts as a key).
///
/// The members are in the order of their names, as every krs JSON document has its keys.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SolverReport {
    /// The first attempt's wall-clock timeout in milliseconds, in mode `clock`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub clock_ms: Option<u32>,
    /// `resource` or `clock`.
    pub mode: String,
    /// The retries of an undecided answer.
    pub retries: u32,
    /// The first attempt's Z3 resource units, in mode `resource`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub units: Option<u32>,
    /// The Z3 build the process linked, absent in a build without Z3.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub z3: Option<SolverBuild>,
}

/// The Z3 build that counted an output's resource units ([`z3_build`]): Z3's version string,
/// and the SHA-256 of the library file Z3's code comes from (the shared library when Z3 is
/// linked dynamically, the archive the build linked when statically). Two builds of one version
/// can count the units of one query differently, so the version alone does not name the solver
/// an answer depends on; the library's digest does.
///
/// The members are in the order of their names.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SolverBuild {
    /// The lowercase hexadecimal SHA-256 of the library file Z3's code comes from; null when it
    /// cannot be named (a shared library replaced since it was mapped, or a static link whose
    /// archive the build could not name), and then the output does not say which build
    /// counted.
    pub library_sha256: Option<String>,
    /// Z3's version string (`Z3_get_full_version`).
    pub version: String,
}

impl SolverReport {
    /// The record of the solver options `options` in this process.
    #[must_use]
    pub fn of(options: BackendOptions) -> Self {
        let (mode, units, clock_ms) = match options.smt_budget {
            SmtBudget::Units(units) => ("resource", Some(units.get()), None),
            SmtBudget::Clock(clock) => ("clock", None, Some(clock.timeout_ms())),
        };
        Self {
            clock_ms,
            mode: mode.to_owned(),
            retries: options.smt_retry_limit,
            units,
            z3: SolverBuild::of_process(),
        }
    }
}

impl SolverBuild {
    /// The Z3 build this process links ([`z3_build`]); `None` in a build without Z3.
    #[must_use]
    pub fn of_process() -> Option<Self> {
        z3_build().map(|build| Self {
            library_sha256: build.library_sha256.clone(),
            version: build.version.to_owned(),
        })
    }
}

/// Whether `version`, a `Z3_get_full_version` text, is of the release `release` (`5.3.3`):
/// builds spell it with or without a `Z3 ` prefix, and with a component after the patch number,
/// which Z3's `CMake` build follows with the commit (`Z3 4.16.0.0`, `4.12.5.0`,
/// `5.3.3.0 430d19e6… 430d19e`).
fn names_release(version: &str, release: &str) -> bool {
    !release.is_empty()
        && version
            .strip_prefix("Z3 ")
            .unwrap_or(version)
            .strip_prefix(release)
            .is_some_and(|rest| rest.is_empty() || rest.starts_with('.'))
}

/// The pathname of the file mapped at `address` in this process, from `/proc/self/maps`, with
/// the ` (deleted)` the kernel appends to a file deleted or replaced since it was mapped; `None`
/// on a platform without it and for an anonymous mapping.
fn mapped_file(address: usize) -> Option<String> {
    let maps = std::fs::read_to_string("/proc/self/maps").ok()?;
    maps.lines().find_map(|line| {
        // `start-end perms offset dev inode pathname`, the pathname padded with spaces.
        let mut fields = line.splitn(6, ' ');
        let (start, end) = fields.next()?.split_once('-')?;
        let start = usize::from_str_radix(start, 16).ok()?;
        let end = usize::from_str_radix(end, 16).ok()?;
        if !(start..end).contains(&address) {
            return None;
        }
        let path = fields.nth(4)?.trim_start();
        path.starts_with('/').then(|| path.to_owned())
    })
}

/// The lowercase hexadecimal SHA-256 of the file at `path`, read in pieces.
fn file_sha256(path: &std::path::Path) -> Option<String> {
    use sha2::{Digest, Sha256};
    use std::io::Read;
    let mut file = std::fs::File::open(path).ok()?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0; 1 << 20];
    loop {
        let read = file.read(&mut buffer).ok()?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Some(
        hasher
            .finalize()
            .iter()
            .fold(String::with_capacity(64), |mut hex, byte| {
                use std::fmt::Write;
                let _ = write!(hex, "{byte:02x}");
                hex
            }),
    )
}

/// What this build of the backend supports. An execution below is [`Backend::execute_kore`] or
/// [`Backend::execute_observed_kore`], or a form that writes the same result as text (their
/// `_json` forms and [`Backend::execute_observed_to_writer`]).
#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct BackendCapabilities {
    pub execution: bool,
    pub simplification: bool,
    pub implication: bool,
    pub model_generation: bool,
    pub proving: bool,
    pub module_addition: bool,
    pub smt: bool,
    pub step_timeouts: bool,
    pub search: bool,
    pub observation: bool,
    /// An execution reports the run's coverage when the request sets `collect_coverage`
    /// ([`ExecuteRequest::collect_coverage`]).
    pub coverage: bool,
    /// An execution also reports the offered level of the run's coverage
    /// ([`RunCoverageOutput::offered`]) when the request sets `collect_offered` beside
    /// `collect_coverage` ([`ExecuteRequest::collect_offered`]).
    pub coverage_offered: bool,
    /// An execution also reports how many times the run applied each rule and equation of
    /// `applied` ([`RunCoverageOutput::applied_counts`]) when the request sets `collect_counts`
    /// beside `collect_coverage` ([`ExecuteRequest::collect_counts`]).
    pub coverage_counts: bool,
    /// An execution also reports the condition records of the run's coverage
    /// ([`RunCoverageOutput::conditions`]) when the request sets `collect_conditions` beside
    /// `collect_coverage` ([`ExecuteRequest::collect_conditions`]).
    pub coverage_conditions: bool,
    /// An execution also reports the guard outcomes of the run's coverage
    /// ([`RunCoverageOutput::guards`]) when the request sets `collect_guards` beside
    /// `collect_coverage` ([`ExecuteRequest::collect_guards`]).
    pub coverage_guards: bool,
    /// The guard outcomes are order free within a priority group: every function application
    /// gives an entry of each equation of the group that applied whose left-hand side matches,
    /// and every rewrite step one of each rule of its deciding group whose left-hand side
    /// matches, tried or not, an untried entry left open being `undecided-untried`
    /// ([`GuardOutcomeOutput::UndecidedUntried`]).
    pub coverage_guards_untried: bool,
    /// An execution also reports the bindings of the run's fired instances
    /// ([`RunCoverageOutput::bindings`]) when the request sets `collect_bindings` beside
    /// `collect_coverage` ([`ExecuteRequest::collect_bindings`]).
    pub coverage_bindings: bool,
    /// An execution accepts `collect_committed` beside `collect_coverage`
    /// ([`RunCoverageOutput::committed`]).
    pub coverage_committed: bool,
    /// An execution accepts `collect_windows` beside `collect_coverage`
    /// ([`RunCoverageOutput::windows`]).
    pub coverage_windows: bool,
    /// An execution's `collect_bindings` accepts a `depth`, and its bindings then report the
    /// syntax paths of its fired instances ([`BindingsOutput::paths`]).
    pub coverage_binding_paths: bool,
    /// An execution accepts `match_states` ([`ExecuteRequest::match_states`]) and reports
    /// [`ExecutionResult::state_matches`].
    pub state_matches: bool,
    /// An execution reports the stack stops the run met ([`ExecutionResult::stack_stops`]).
    pub stack_stops: bool,
    /// An execution reports the undecided solver answers the run's decisions were taken from
    /// ([`ExecutionResult::smt_unknowns`]); in a build without a solver the count is always zero.
    pub smt_unknowns: bool,
    /// An execution accepts `max_polls` ([`ExecuteRequest::max_polls`]) and reports the polls
    /// the run counted ([`ExecutionResult::polls`]).
    pub poll_bound: bool,
    /// An execution marks each leaf whose path read a value the definition leaves open
    /// (`BackendDiagnosticOutput::ImplementationChosenValue`) and lists every such value the run
    /// read ([`ExecutionResult::implementation_chosen_values`]); a search marks its states,
    /// witnesses and matches alike and lists every such value it read
    /// (`SearchResponse::implementation_chosen_values` and the other search responses').
    pub implementation_chosen_values: bool,
    /// An execution marks each leaf whose path's decisions rest on a contradicted claim the run
    /// observed (`BackendDiagnosticOutput::ContradictedClaim`), a `total` attribute or a rule's
    /// `preserves-definedness`, and lists every such record the run and its definition's load
    /// observed ([`ExecutionResult::contradicted_claims`]); every search marks its states,
    /// witnesses and matches alike and lists the records (`SearchResponse::contradicted_claims`
    /// and the other search responses'). Proofs name a contradicted total on their empty leaves
    /// only (docs/compatibility.md, "A contradicted `preserves-definedness` attribute is named,
    /// not repaired").
    pub contradicted_claims: bool,
    /// An execution and every search list every `Bytes` result the memory allowance refused
    /// ([`ExecutionResult::allowance_refusals`]), whatever became of the work that met it.
    pub allowance_refusals: bool,
    /// An execution and every search list every application left unevaluated as an unsupported
    /// hook ([`ExecutionResult::unsupported_hooks`]), whatever became of the work that met it.
    pub unsupported_hooks: bool,
    /// An execution and every search list every place where the run used the strict definedness
    /// of an operand a short-circuiting reading skips and did not find it defined
    /// ([`ExecutionResult::short_circuit_readings`]), whatever became of the work.
    pub short_circuit_readings: bool,
    /// An execution lists every selected cut-point or terminal rule it went on past at a step
    /// where the rule was not its state's one successor ([`ExecutionResult::passed_stops`]).
    pub passed_stops: bool,
    /// An execution ends a path at the arrival at a stop [`ExecuteRequest::stop_count`] names and
    /// reports each leaf's count ([`ExecutionLeaf::stops`]).
    pub stop_count: bool,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct ExecuteRequest {
    /// A KORE JSON envelope on the wire ([`deserialize_kore_pattern`]).
    #[serde(deserialize_with = "deserialize_kore_pattern")]
    pub state: KorePattern,
    #[serde(default)]
    pub module_name: Option<String>,
    #[serde(default)]
    pub max_depth: Option<u64>,
    #[serde(default)]
    pub max_breadth: Option<usize>,
    /// Maximum simplifier iterations per rewrite step.
    ///
    /// The bound counts simplification-rule, builtin, and symbolic rewriting. Determined ground
    /// function evaluation (a function equation on a variable-free redex with no residual
    /// condition) runs to its value, bounded only by the step deadline or cancellation and by
    /// the thread's stack, whose exhaustion is a typed error.
    /// Execution keeps a partially simplified term or the original constraints after exhaustion
    /// and records a backend diagnostic before continuing.
    #[serde(default = "wire::default_max_simplification_iterations")]
    pub max_simplification_iterations: usize,
    #[serde(default)]
    pub strategy: ExecutionStrategy,
    #[serde(default)]
    pub stop_at_branch: bool,
    #[serde(default)]
    pub cut_point_rules: Vec<String>,
    #[serde(default)]
    pub terminal_rules: Vec<String>,
    /// The arrival at a stop of [`Self::cut_point_rules`] or [`Self::terminal_rules`] at which a
    /// path ends (wire `stopCount`; absent: its first). An arrival is a step by a selected rule
    /// that is its state's one successor, with a defined successor; a path ends at its
    /// `stopCount`th, before or after the rule's step as at a first arrival, and takes each
    /// earlier one as any other step, so a run to the Nth arrival is one path with the steps of
    /// the run without stop rules up to it. With it, each leaf reports the arrivals its path
    /// counted ([`ExecutionLeaf::stops`]); under `state-set` a state merges only into one of the
    /// same count (docs/compatibility.md, "Stop count").
    #[serde(default)]
    pub stop_count: Option<std::num::NonZeroU64>,
    /// The deadline of each step, in milliseconds (module documentation, point 5). Condition
    /// records ([`Self::collect_conditions`]) run off this clock, so a recorded run is not
    /// bounded in wall time by it alone ([`ConditionCollection::record_polls`]).
    #[serde(default)]
    pub step_timeout_ms: Option<u64>,
    #[serde(default)]
    pub moving_average_timeout: bool,
    /// Assume the initial state's definedness instead of adding it to the path predicate.
    /// Other path obligations still apply: an execution leaf's predicate implies the
    /// definedness of every partial term relied on by its conditions, right-hand sides, and
    /// simplified states in either solver profile. The leaf contract of [`ExecutionLeaf`] then
    /// holds relative to the assumed definedness of the initial term.
    #[serde(default)]
    pub assume_state_defined: bool,
    /// `state-set` (the default) merges structurally equal final configurations into one leaf,
    /// which carries the diagnostics of every path merged into it, and expands each distinct
    /// state of a depth once, so paths that converge on one state at one depth (such as the
    /// evaluation orders of a `strict` production) are explored once;
    /// `path-set` returns one leaf per explored path, so converging paths keep their own trace,
    /// branch identity, and observations. The result reports the modality it was produced under.
    #[serde(default = "default_result_modality")]
    pub result_modality: ResultModalityOutput,
    /// Report the run's coverage as [`ExecutionResult::coverage`]: the rules and equations the
    /// run applied, and those whose condition it began to decide for a matched instance
    /// ([`RunCoverageOutput`]). Off by default; collecting changes no other field of the result.
    #[serde(default)]
    pub collect_coverage: bool,
    /// With [`Self::collect_coverage`], also report [`RunCoverageOutput::offered`] (wire
    /// `collectOffered`): the rules and equations whose left-hand side matched a subject the run
    /// selected them as candidates for, tried there or not. Off by default; a request that sets
    /// it without `collect_coverage` is refused. Asking changes no other field of the result. A
    /// candidate a site never tried costs one left-hand-side match at every visit of the site
    /// while it has not matched, so the cost grows with the visits times the skipped candidates
    /// (docs/compatibility.md, "Run coverage").
    #[serde(default)]
    pub collect_offered: bool,
    /// With [`Self::collect_coverage`], also report [`RunCoverageOutput::applied_counts`] (wire
    /// `collectCounts`): how many times the run applied each rule and equation of `applied`.
    /// Off by default; a request that sets it without `collect_coverage` is refused. Asking
    /// changes no other field of the result and costs only the map: the run counts at the
    /// cost of the set's own lookup (docs/compatibility.md, "Run coverage").
    #[serde(default)]
    pub collect_counts: bool,
    /// With [`Self::collect_coverage`], also report [`RunCoverageOutput::conditions`] (wire
    /// `collectConditions`): for each rewrite rule it names whose `requires` the run began to
    /// decide for a matched instance, the bindings of the variables the condition reads, the
    /// condition with every node's truth and its atoms' operands evaluated under the instance, and
    /// the attempt's verdict, up to its caps ([`ConditionCollection`]). Off by default; a request
    /// that sets it without `collect_coverage` is refused. Asking changes no other field of the
    /// result, also under a step timeout: the records are evaluated off the run's clock, each
    /// bounded by its own budget of polls, and cost about one more evaluation of the condition
    /// per new entry, in wall time (docs/compatibility.md, "Run coverage").
    #[serde(default)]
    pub collect_conditions: Option<ConditionCollection>,
    /// With [`Self::collect_coverage`], also report [`RunCoverageOutput::guards`] (wire
    /// `collectGuards`): for each rule and equation it names whose `requires` the run entered,
    /// the outcomes each node of the written `requires` took on the entries where it was
    /// reached, the entries' guard outcomes and their valuation combinations, within its bounds
    /// ([`GuardCollection`]). Off by default; a request that sets it without `collect_coverage`
    /// is refused. Asking changes no other field of the result: each entry is evaluated off the
    /// run's clock, isolated and without a solver, bounded by its own budget of polls, and an
    /// entry the bounded cache recognizes costs a lookup (docs/compatibility.md, "Run
    /// coverage").
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub collect_guards: Option<GuardCollection>,
    /// With [`Self::collect_coverage`], also report [`RunCoverageOutput::bindings`] (wire
    /// `collectBindings`): per rule and equation, the symbols it names that were the head of an
    /// operand of a fired instance (a committed rewrite step, an equation instance that gave a
    /// result), and the values of the template binders it selects, capped
    /// ([`BindingCollection`]). Off by default; a request that sets it without
    /// `collect_coverage`, or that selects one binder twice (under one name, or under its
    /// axiom's `UNIQUE_ID` and its label), is refused. Asking changes no other
    /// field of the result and evaluates nothing: each fired instance costs one pass over the
    /// substitution its match produced (docs/compatibility.md, "Run coverage").
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub collect_bindings: Option<BindingCollection>,
    /// The most states the run may visit across all its paths (wire `maxWork`; absent: no
    /// bound). A state is visited when the run takes it from its worklist, whatever becomes of
    /// it; [`ExecutionResult::work`] reports the count. The run takes states in a fixed order, so
    /// it stops at the same state, with the same leaves finished before it, wherever its result
    /// is the same: within the execution determinism contract and its exclusions
    /// (docs/compatibility.md, "Determinism and concurrency", "Execute"), which leave out, among
    /// others, in a build with Z3, a run whose result reports a nonzero
    /// [`ExecutionResult::smt_unknowns`] (wire `smtUnknowns`; docs/compatibility.md, "Work
    /// budget"). When a state remains after `max_work` states, it becomes the one
    /// `work-bound` leaf ([`HaltReasonOutput::WorkBound`]), the last of the result, and the other
    /// pending states are not explored or reported; a budget at least the unbounded run's `work`
    /// leaves every leaf's configuration, halt and order, the counts and the result's lists
    /// unchanged, and its only change is that every leaf's diagnostics gain the run's path facts
    /// (below); a budget of 0 makes the first initial state, as the request gave it, that leaf.
    ///
    /// It bounds the states, the leaves and the pending states; it does not bound the work of one
    /// state's step (a ground function evaluation runs to its value), the size of values, or the
    /// length of traces, so a host keeps its own time and memory limits. Under `state-set` a leaf
    /// finished before the stop carries the diagnostics of the paths merged into it before the
    /// stop only, so they may differ from the same leaf's in a run with a larger budget. In a run
    /// with `maxWork` or `maxBreadth` set, every leaf carries every path fact the run noted so far
    /// (each mark of [`ExecutionResult::implementation_chosen_values`] and each record of
    /// [`ExecutionResult::contradicted_claims`] the run observed), since whether a bound fires
    /// rests on the exploration of every path, in every model.
    ///
    /// Every leaf finished before the `work-bound` leaf is a leaf of every run of the same
    /// request with a larger budget or none, at the same position: the result without its
    /// `work-bound` leaf is a prefix of theirs. Under `path-set` the leaf is the same in every
    /// field but its path facts, which are among the larger run's; under `state-set` it is the
    /// same in every field but its diagnostics, which are among the larger run's (a later path
    /// merged into it adds its own). This holds within the determinism contract above
    /// (docs/compatibility.md, "Work budget").
    #[serde(default)]
    pub max_work: Option<u64>,
    /// The most polls the run may count (wire `maxPolls`; absent: no bound), the unit
    /// [`ExecutionResult::polls`] reports: the backend's interruption point, taken at every
    /// round of the simplifier, at every phase of a state's step and inside the hook loops, with
    /// each walk over a term the simplifier charges counted by its nodes, and each solver query
    /// counted once. Unlike `max_work` it bounds the work inside a step too: a ground function
    /// evaluation whose equation applies itself forever is stopped by it, not by a clock.
    ///
    /// When the bound is reached the run ends: the state being expanded becomes a `poll-bound`
    /// leaf ([`HaltReasonOutput::PollBound`]) at the state as it stood when the bound stopped
    /// it, the last leaf of the result, and the states still pending are dropped. It is not a
    /// cancellation and never an `Err`, under either `cancelledResult`; the result is
    /// incomplete, and the leaf's configuration is no result. The count, and so the point where
    /// the bound stops the run, is a function of the request and the definition wherever the
    /// result is: the same on a fresh `Backend` and on one that served other requests first,
    /// and with or without coverage, `matchStates`, a probe, a stop condition or an observer
    /// (docs/compatibility.md, "Poll budget").
    #[serde(default)]
    pub max_polls: Option<u64>,
    /// Whether each leaf carries its path's trace ([`ExecutionLeaf::trace`]), O(depth) entries
    /// per leaf; `true` when omitted. A caller that does not read traces sets `false`: every
    /// leaf's `trace` is then empty and every other field of the result is unchanged, so the
    /// traces no longer grow with the total path length. An observed run's `branch` and
    /// `observations` stay O(depth) per leaf, so only an unobserved branching run's output is
    /// then linear in its leaves (state sizes aside).
    #[serde(default = "default_trace")]
    pub trace: bool,
    /// What the request answers when a cancellation ends its run (wire `cancelledResult`):
    /// `partial` (the default) returns `Ok` with the leaves finished before the cancellation and
    /// the stopped state as a `cancelled` leaf; `error` returns `Err(e)` with
    /// `e.stop_cause() == Some(&StopCause::Cancelled)`, whichever phase observed the cancellation
    /// (the exploration, the passes after it, or the conversion of the leaves), and builds no leaf
    /// beyond the stopped state's own (built by the observing poll, then discarded), for a host
    /// that will not read a cancelled run's leaves. A failed
    /// solver prelude answers its error either way. The text forms
    /// ([`Backend::execute_json`] and the other `*_json` and `*_to_writer` variants) serialize a
    /// converted result without polling: their serialization is linear in the output.
    /// [Bounding an operation](crate::backend#bounding-an-operation), point 2.
    #[serde(default)]
    pub cancelled_result: CancelledResultOutput,
    /// Match every state the run reaches against a pattern, and report a summary of the verdicts
    /// as [`ExecutionResult::state_matches`] (wire `matchStates`; absent by default: nothing is
    /// matched and the result has no `stateMatches` key). Leaves, coverage, work and the run's
    /// lists are those of the same request without it, within the execution determinism
    /// contract, with these exceptions (docs/compatibility.md, "State matches"): a solver prelude
    /// a match's query finds inconsistent ends the run, since it makes every solver answer of the
    /// run meaningless; the pattern's depth enters the operation's stack measurement, which can
    /// change `stackStops` or refuse a request for lack of stack; matching runs on the step
    /// clock, so under a step timeout its time counts against the step's deadline; and under a
    /// [`StateMatchRequest::chain`] a `state-set` run merges two states only when their chain
    /// progresses agree, so it may expand states, and spend work, that it would merge without the
    /// chain, and a work budget may then end it sooner (docs/compatibility.md, "Chains").
    #[serde(default)]
    pub match_states: Option<StateMatchRequest>,
    /// With [`Self::collect_coverage`], also report [`RunCoverageOutput::committed`] (wire
    /// `collectCommitted`): the rewrite rules whose successor the run committed to. Off by
    /// default; a request that sets it without `collect_coverage` is refused. Asking changes no
    /// other field of the result and costs one set insert per normalized successor
    /// (docs/compatibility.md, "Committed transitions").
    #[serde(default)]
    pub collect_committed: bool,
    /// With [`Self::collect_coverage`], also report [`RunCoverageOutput::windows`] up to this
    /// length `d` (wire `collectWindows`, a positive integer): every sequence of at most `d`
    /// rewrite rules some path committed to as consecutive steps. Absent by default; a request
    /// that sets it without `collect_coverage` is refused. Asking changes no other field of the
    /// result; each committed step costs `O(d)` and, under `state-set`, `O(d^2)` more, and each
    /// merged arrival `O(d^2)` per rule sequence shorter than `d` from the state it merges into
    /// (docs/compatibility.md, "Rule windows").
    #[serde(default)]
    pub collect_windows: Option<std::num::NonZeroUsize>,
    #[serde(default = "default_backend_schema_version")]
    pub schema_version: u32,
}

/// The pattern an execute request matches every reached state against
/// ([`ExecuteRequest::match_states`], wire `matchStates`).
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct StateMatchRequest {
    /// The target, internalized as `searchPattern` internalizes its pattern; it may carry
    /// constraints (a `requires`). A KORE JSON envelope on the wire.
    #[serde(deserialize_with = "deserialize_kore_pattern")]
    pub pattern: KorePattern,
    /// Whether a verdict must also hold in proof mode, where a value the definition leaves to
    /// the implementation stays unevaluated (wire `proofAgreement`, default `false`): a state
    /// then reaches only when both modes match it, and is refuted only when both refute it. A
    /// target that evaluates nothing (no constraint, every application a free constructor) has
    /// the same verdict in every mode and needs no agreement.
    #[serde(default)]
    pub proof_agreement: bool,
    /// A chain of patterns the run also matches its states against (wire `chain`; absent by
    /// default), reported as [`StateMatchesOutput::chain`]; `pattern` is matched and reported as
    /// without it (docs/compatibility.md, "Chains"). Proof agreement applies to every part.
    #[serde(default)]
    pub chain: Option<ChainRequest>,
}

impl StateMatchRequest {
    /// A request for `pattern` without proof agreement.
    pub fn new(pattern: KorePattern) -> Self {
        Self {
            pattern,
            proof_agreement: false,
            chain: None,
        }
    }

    /// The patterns of the request: `pattern`, then each chain step's and its unless's.
    fn patterns_mut(&mut self) -> impl Iterator<Item = &mut KorePattern> {
        std::iter::once(&mut self.pattern).chain(self.chain.iter_mut().flat_map(|chain| {
            chain.steps.iter_mut().flat_map(|step| {
                std::iter::once(&mut step.pattern)
                    .chain(step.unless.iter_mut().map(|unless| &mut unless.pattern))
            })
        }))
    }

    fn patterns(&self) -> impl Iterator<Item = &KorePattern> {
        std::iter::once(&self.pattern).chain(self.chain.iter().flat_map(|chain| {
            chain.steps.iter().flat_map(|step| {
                std::iter::once(&step.pattern)
                    .chain(step.unless.iter().map(|unless| &unless.pattern))
            })
        }))
    }
}

/// A chain of patterns ([`StateMatchRequest::chain`], wire `chain`): steps `P1, [U2] P2, …,
/// [Un] Pn`. It holds on a path of the run when the path has states `s1`, …, `sn`, each at or
/// after the previous one, that match the steps under one assignment of the variables the steps
/// share, with no state strictly between `s(i-1)` and `si` matching `Ui`
/// (docs/compatibility.md, "Chains").
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct ChainRequest {
    /// The steps, in order; step 1 has no `unless` and no import. A request whose imports and
    /// exports do not classify the steps' variables consistently is refused.
    pub steps: Vec<ChainStepRequest>,
    /// The most partial occurrences one path keeps (wire `partialCap`): beyond it the largest are
    /// evicted, and the path is reported overflowed (`overflowedPaths`). A count, never a clock.
    pub partial_cap: usize,
}

/// One step of a chain.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct ChainStepRequest {
    /// The step's target, internalized as [`StateMatchRequest::pattern`] is; it may carry a
    /// `requires`, which may name an imported variable. A KORE JSON envelope on the wire.
    #[serde(deserialize_with = "deserialize_kore_pattern")]
    pub pattern: KorePattern,
    /// The element variables of `pattern` an earlier step binds, whose values are substituted
    /// into it before it is matched, each a KORE JSON envelope of the variable (absent: none).
    #[serde(default, deserialize_with = "deserialize_kore_variables")]
    pub imports: Vec<KoreVariable>,
    /// The element variables `pattern`'s term binds that a later step or unless names, each a
    /// KORE JSON envelope of the variable (absent: none).
    #[serde(default, deserialize_with = "deserialize_kore_variables")]
    pub exports: Vec<KoreVariable>,
    /// What no state strictly between the previous step's state and this step's may match.
    #[serde(default)]
    pub unless: Option<UnlessRequest>,
}

/// The `unless` of a chain step: a pattern whose variables other than its imports are
/// existential.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct UnlessRequest {
    #[serde(deserialize_with = "deserialize_kore_pattern")]
    pub pattern: KorePattern,
    #[serde(default, deserialize_with = "deserialize_kore_variables")]
    pub imports: Vec<KoreVariable>,
}

impl ExecuteRequest {
    /// A request from `state` with every other field at its wire default.
    pub fn new(state: KorePattern) -> Self {
        Self {
            state,
            module_name: None,
            max_depth: None,
            max_breadth: None,
            max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            strategy: ExecutionStrategy::All,
            stop_at_branch: false,
            cut_point_rules: Vec::new(),
            terminal_rules: Vec::new(),
            stop_count: None,
            step_timeout_ms: None,
            moving_average_timeout: false,
            assume_state_defined: false,
            result_modality: ResultModalityOutput::StateSet,
            collect_coverage: false,
            collect_offered: false,
            collect_counts: false,
            collect_conditions: None,
            collect_guards: None,
            collect_bindings: None,
            max_work: None,
            max_polls: None,
            trace: true,
            cancelled_result: CancelledResultOutput::Partial,
            match_states: None,
            collect_committed: false,
            collect_windows: None,
            schema_version: BACKEND_SCHEMA_VERSION,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ExecutionStrategy {
    #[default]
    All,
    Any,
}

/// An execution result whose KORE is held as patterns ([`Backend::execute_kore`]).
pub type KoreExecutionResult = ExecutionResult<KorePattern>;
/// A leaf of a [`KoreExecutionResult`].
pub type KoreExecutionLeaf = ExecutionLeaf<KorePattern>;
/// A search response whose KORE is held as patterns ([`Backend::search_kore`]).
pub type KoreSearchResponse = SearchResponse<KorePattern>;
/// A path search response whose KORE is held as patterns ([`Backend::search_paths_kore`]).
pub type KorePathSearchResponse = PathSearchResponse<KorePattern>;
/// A pattern search response whose KORE is held as patterns ([`Backend::search_pattern_kore`]).
pub type KorePatternSearchResponse = PatternSearchResponse<KorePattern>;
/// A pattern path search response whose KORE is held as patterns
/// ([`Backend::search_pattern_paths_kore`]).
pub type KorePathPatternSearchResponse = PathPatternSearchResponse<KorePattern>;
/// A proof result whose leaves' KORE is held as patterns ([`Backend::prove_kore`]).
pub type KoreProofResult = ProofResultOutput<KorePattern>;

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ExecutionResult<K> {
    /// Whether `leaves` is a state set (equal configurations merged) or a path set (one leaf
    /// per explored path), as selected by `ExecuteRequest::result_modality`.
    pub modality: ResultModalityOutput,
    pub leaves: Vec<ExecutionLeaf<K>>,
    /// Compatibility copy of the committed effects when execution retains exactly one leaf.
    /// Multi-leaf executions carry their transcripts on the individual leaves.
    pub effects: Vec<EffectOutput>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub discarded: Vec<ObservationEventOutput<K>>,
    /// The run's coverage, present exactly when the request set `collect_coverage`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub coverage: Option<RunCoverageOutput<K>>,
    /// The states the run visited across all its paths, the unit
    /// [`ExecuteRequest::max_work`] bounds; reported whether or not a budget was set.
    pub work: u64,
    /// The polls the run counted, the unit [`ExecuteRequest::max_polls`] bounds; reported
    /// whether or not a bound was set, so a host measures a run's work in the unit it bounds
    /// another's by. A poll the bound refused is not counted. It is a function of the request
    /// and the definition wherever the result is: the same on a fresh `Backend` and on a reused
    /// one, and with or without the work that only describes the run (docs/compatibility.md,
    /// "Poll budget"). Portable and Z3 builds count differently.
    pub polls: u64,
    /// The visited states whose rewrite step ran and answered, whatever the answer (successors,
    /// a branch or cut-point report, or a verdict that ends the state); at most `work`. A state
    /// the step's guards answer without matching a rule (constraints that are `\bottom`, a
    /// surviving macro or alias) is expanded too. A visited state whose step does not run (the
    /// run ended it before the step, or it is a remainder, decided by its parent's step) or does
    /// not answer (a stop interrupted it) is not expanded (docs/compatibility.md, "Work budget").
    /// Reported whether or not a budget was set, and deterministic exactly where `work` is.
    pub expanded: u64,
    /// The stops for lack of native stack the run met, including those met while a result was
    /// only refined and dismissed there (`k_rust_backend::rewrite::ExecutionResult::stack_stops`);
    /// absent when zero. A run whose count is nonzero is outside the determinism contract
    /// (docs/compatibility.md, "Determinism and concurrency").
    #[serde(skip_serializing_if = "is_zero")]
    pub stack_stops: usize,
    /// The undecided answers the solver delivered to the run's decisions (wire `smtUnknowns`):
    /// each `unknown` of a satisfiability or validity query (a timeout, by default after 125 ms
    /// with retries, the solver's resource limit, or its incompleteness), counted once after
    /// retries (`k_rust_backend::rewrite::ExecutionResult::smt_unknowns`); absent when zero. A
    /// run whose count is zero took every decision from a decided answer, which is a fact about
    /// the query, and the solver's cache holds only decided answers, so within the execution
    /// determinism contract it gives one result on a fresh `Backend` and on a reused one; a run
    /// whose count is nonzero may differ (docs/compatibility.md, "Determinism and concurrency").
    /// A build without a solver always reports zero.
    #[serde(skip_serializing_if = "is_zero")]
    pub smt_unknowns: usize,
    /// Every distinct value the definition leaves open that the run read (wire
    /// `implementationChosenValues`), in the order the run first read it; absent when empty
    /// (docs/compatibility.md, "Implementation-chosen hook values"). It holds the marks of the
    /// leaves' paths (`BackendDiagnosticOutput::ImplementationChosenValue`) and those of work
    /// that ended on no reported leaf: a candidate that vanished, a state a `state-set` merge
    /// absorbed, a state whose successors were all absorbed. When it is empty, every model of the
    /// definition that agrees with the request's inputs and k-rust's order of console effects gives
    /// the run the same leaves. In a run that sets `maxWork` or `maxBreadth` every leaf carries
    /// every mark of this list, since where those bounds cut the run rests on the work of every
    /// path.
    /// Under `state-set` so does every leaf a leaf of another halt class may stand for in the
    /// final merge (a `depth-bound` or other unexplored or undecided leaf, and with
    /// `terminalRules` a `stuck` or `terminal` one), since the leaf it is merged into may come
    /// from a path of another model; an unmarked `state-set` leaf's configuration and halt are
    /// in every such model, its depth and trace may not be.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub implementation_chosen_values: Vec<ChosenValueOutput>,
    /// Every distinct contradicted claim the run observed (wire `contradictedClaims`), and those
    /// the load of its definition observed, in first-observed order; absent when empty
    /// (docs/compatibility.md, "A contradicted total attribute is named, not repaired" and "A
    /// contradicted `preserves-definedness` attribute is named, not repaired"). It holds the
    /// records of the leaves' paths (`BackendDiagnosticOutput::ContradictedClaim`) and those of
    /// work that ended on no reported leaf: a candidate a defined sibling covered, a state a
    /// `state-set` merge absorbed. It is complete for the `total` contradictions evaluation finds
    /// on ground arguments, and for the `preserves-definedness` contradictions a successor's
    /// normalization finds: a declared rule's result term found `\bottom`, by any route (for a
    /// disjunctive right-hand side, every alternative's; a `#Bottom` right-hand side). A symbolic
    /// state trusts the claims, so an empty list says nothing about a non-ground run. Each record
    /// says who observed it (`observedIn`): the load's records are
    /// facts about the definition, on this list and on no leaf, and a contradiction the load and
    /// the run both observed is listed once for each.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub contradicted_claims: Vec<wire::ContradictedClaimOutput<K>>,
    /// Every distinct `Bytes` result the memory allowance refused in the run or in the load of
    /// its definition (wire `allowanceRefusals`), in first-met order, including a refusal inside
    /// an attempt that was undone or passed over, which leaves no diagnostic; absent when empty.
    /// A result without it is the result under every allowance of at least as many bytes
    /// (docs/compatibility.md, "Resource bounds").
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub allowance_refusals: Vec<UnevaluatedHookOutput>,
    /// Every distinct application left unevaluated as an unsupported hook, other than an
    /// allowance refusal, in the run or in the load of its definition (wire `unsupportedHooks`),
    /// in first-met order, whatever became of the work that met it; absent when empty.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub unsupported_hooks: Vec<UnevaluatedHookOutput>,
    /// Every distinct place where the run, or the load of its definition, used the strict
    /// definedness of an operand that a short-circuiting reading skips and did not find it
    /// defined (wire `shortCircuitReadings`), in first-observed order, whatever became of the
    /// work; absent when empty (docs/compatibility.md, "Short-circuit readings"). A fact of the
    /// run only, on no leaf; the load lists its undefined readings only. When it is absent and
    /// the run completed, a backend that evaluates the deciding operand of `#if`, `andThenBool`,
    /// `orElseBool`, `andBool`, `orBool` and `impliesBool` and skips the operand after it once
    /// that operand decides the value gives the run the same states, leaves and lists; an entry
    /// is no evidence that it does not. A result recorded by a backend without the capability
    /// ([`BackendCapabilities::short_circuit_readings`]) has no field either, and reads back as
    /// an empty list: a reader of stored results must tell the two apart by the capability of
    /// the backend that recorded them, since the absence is only then a run that listed nothing.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub short_circuit_readings: Vec<wire::ShortCircuitReadingOutput<K>>,
    /// Each rule that [`ExecuteRequest::cut_point_rules`] or [`ExecuteRequest::terminal_rules`]
    /// selects and that the run went on past at a step where it was not its state's one
    /// successor, with the shallowest depth at which it did (wire `passedStops`), in order of
    /// depth and then of name; one entry per rule, absent when empty (docs/compatibility.md,
    /// "Passed stops"). A stop rule stops a run only as its state's one successor, so where this
    /// lists a rule the run went on past a step at which a system that ends at every step of a
    /// selected rule would end, and its leaves need not be that system's final configurations.
    /// Always absent without stop rules and under `stop_at_branch`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub passed_stops: Vec<PassedStopOutput>,
    /// The summary of the run's state matches, present exactly when the request set
    /// [`ExecuteRequest::match_states`] (wire `stateMatches`; docs/compatibility.md, "State
    /// matches").
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub state_matches: Option<StateMatchesOutput<K>>,
}

/// A selected stop rule the run went on past ([`ExecutionResult::passed_stops`]): at some step
/// the rule had a candidate that the step's normalization did not show undefined, and the step
/// had another successor (another such candidate or a remainder), so the run went on through
/// every successor.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct PassedStopOutput {
    /// The name the request selected the rule by, as [`ExecuteRequest::cut_point_rules`] or
    /// [`ExecuteRequest::terminal_rules`] gives it: a label or a `UNIQUE_ID`.
    pub rule: String,
    /// The depth of the state of the shallowest such step.
    pub depth: u64,
}

/// The summary of an execution's state matches ([`ExecutionResult::state_matches`]), in the
/// run's depth-first order (docs/compatibility.md, "State matches").
///
/// The states matched are every state the run reached in normal form and did not merge into a
/// recorded state of its depth: the initial configuration, every state it stepped or the depth
/// bound stopped, and every successor a terminal rule ended. A state *reaches* when it is decided
/// (no constraint, no variable), ceil-free and matched with empty constraints, in execution mode
/// and also in proof mode under [`StateMatchRequest::proof_agreement`]; it is *refuted* when
/// every required mode refutes it; otherwise it is undecided with a reason. A reach is *clean*
/// when the diagnostics of its path up to the state carry no `implementation-chosen-value`,
/// `contradicted-claim`, `simplification-budget-exhausted`, `rule-condition-unsimplified`,
/// `rule-condition-failed` or `undefined-initial-instances`. Matching stops after the first
/// clean reach whose term holds no term-level `\and`. The summary holds at most five states,
/// each with a copy of its path's diagnostics up to it.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct StateMatchesOutput<K = Value> {
    /// The first state that reaches the pattern on a clean prefix and whose term holds no
    /// term-level `\and`, where one exists, and otherwise the first clean reach; absent when none
    /// did. A state merged into a recorded reaching state whose own prefix was not clean is
    /// reported with its own clean prefix, since equal states have one verdict.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_clean_reach: Option<StateMatchOutput<K>>,
    /// The first state that reaches the pattern on a prefix that is not clean.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_dirty_reach: Option<StateMatchOutput<K>>,
    /// How many matched states reached on a prefix that is not clean.
    #[serde(default, skip_serializing_if = "is_zero_u64")]
    pub dirty_reaches: u64,
    /// For each reason a matched state's verdict was undecided, the first such state and the
    /// count, in the order `undecided-state`, `not-ceil-free`, `undecided-match`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub undecided: Vec<UndecidedStateMatchesOutput<K>>,
    /// The states matched.
    pub matched: u64,
    /// The states every required mode refuted.
    pub refuted: u64,
    /// The undecided answers the solver gave the matcher; the run's `smtUnknowns` leaves them
    /// out. Absent when zero.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub smt_unknowns: usize,
    /// The matcher's stops for lack of native stack (each leaves its match `undecided-match`);
    /// the run's `stackStops` leaves them out. Absent when zero. A summary with a nonzero count
    /// is outside the determinism contract, as a run with nonzero `stackStops` is.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub stack_stops: usize,
    /// The summary of the chain's matching, present exactly when the request asked for a chain
    /// ([`StateMatchRequest::chain`]).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub chain: Option<ChainMatchesOutput<K>>,
}

/// The summary of a run's chain matching ([`StateMatchesOutput::chain`]), in the run's
/// depth-first order (docs/compatibility.md, "Chains").
///
/// A step matches a state as [`StateMatchesOutput`] says a state reaches its pattern (decided,
/// shown to exist, matched with empty constraints in every required mode), with the step's
/// imports substituted; an `unless` matches without the existence check. A *completion* is a
/// chain on one path; it is *clean* when the path up to its last step's state is clean.
/// Matching stops after the first clean completion no step state of which holds a term-level
/// `\and`.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ChainMatchesOutput<K = Value> {
    /// The first clean completion with no term-level `\and` in a step state, where one exists,
    /// and otherwise the first clean completion; absent when none. Among completions at one
    /// state, the least step depths win, then the least values of the variables later steps
    /// import.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_clean_completion: Option<ChainCompletionOutput<K>>,
    /// The first completion on a path that is not clean.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_dirty_completion: Option<ChainCompletionOutput<K>>,
    /// How many completions were on paths that are not clean.
    #[serde(default, skip_serializing_if = "is_zero_u64")]
    pub dirty_completions: u64,
    /// For each part and reason, in order (steps before unlesses, then by step, then by
    /// reason), the undecided matches. An undecided step extends its partial by the ways it
    /// decided only; an undecided unless drops its partial.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub undecided: Vec<ChainUndecidedOutput<K>>,
    /// The paths on which a partial occurrence was evicted beyond `partialCap`, counted where
    /// the first eviction happened. A completion may have been missed on them.
    #[serde(default, skip_serializing_if = "is_zero_u64")]
    pub overflowed_paths: u64,
    /// The most partial occurrences one path kept.
    pub peak_partials: u64,
    /// The states processed.
    pub states: u64,
    /// The step and unless matches made.
    pub evaluations: u64,
    /// The undecided answers the solver gave the chain matcher; the run's and `stateMatches`'
    /// `smtUnknowns` leave them out. Absent when zero.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub smt_unknowns: usize,
    /// The chain matcher's stops for lack of native stack; the run's and `stateMatches`'
    /// `stackStops` leave them out. Absent when zero.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub stack_stops: usize,
}

/// A completed chain: each step's match in step order, and the diagnostics of the path up to
/// the last step's state.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ChainCompletionOutput<K = Value> {
    pub steps: Vec<ChainStepMatchOutput<K>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput<K>>,
    /// A step state's term holds a term-level `\and` (present only when true).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub term_conjunction: bool,
}

/// One step of a completion: the step (from 1), its state's depth, the state, and the values
/// the step's own variables took (its imports are the earlier steps' values).
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ChainStepMatchOutput<K = Value> {
    pub step: usize,
    pub depth: u64,
    pub state: K,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub bindings: Vec<BindingOutput<K>>,
}

/// The undecided matches of one part of a chain for one reason: how many, and the first, with
/// the values of the imported variables it was matched with.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ChainUndecidedOutput<K = Value> {
    pub part: ChainPartOutput,
    /// The step (from 1) the part is, or whose `unless` it is.
    pub step: usize,
    pub reason: UndecidedMatchReasonOutput,
    pub count: u64,
    pub first: StateMatchOutput<K>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub bindings: Vec<BindingOutput<K>>,
}

/// A part of a chain: a step, or a step's `unless`.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ChainPartOutput {
    Step,
    Unless,
}

/// One matched state: the committed rewrite steps from the initial configuration to it, the
/// state, and the diagnostics of the path that reached it, up to it.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct StateMatchOutput<K = Value> {
    pub depth: u64,
    pub state: K,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput<K>>,
    /// The state's term holds a term-level `\and` (present only when true).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub term_conjunction: bool,
}

/// The first matched state left undecided for one reason, and how many were.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct UndecidedStateMatchesOutput<K = Value> {
    pub reason: UndecidedMatchReasonOutput,
    pub count: u64,
    pub first: StateMatchOutput<K>,
}

/// Why a matched state is undecided: it has a constraint or a variable (`undecided-state`), the
/// pattern matches a term not shown to exist (`not-ceil-free`: k-rust-backend's `ground_defined`
/// fails, so the term may denote nothing; every term with the stored `ceil_free` attribute
/// exists, and so does one holding an irreducible `value-production` application), or the
/// matcher did not decide
/// (`undecided-match`: undecided, matched under constraints, the modes disagreed, or a stop
/// interrupted it), or the matcher placed a list pattern's items on the state's list and stopped
/// at its counted bound of placements tried before a way it decided matched
/// (`placement-bound`).
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum UndecidedMatchReasonOutput {
    UndecidedState,
    NotCeilFree,
    UndecidedMatch,
    PlacementBound,
}

fn is_zero_u64(value: &u64) -> bool {
    *value == 0
}

/// A hook application a run left unevaluated: the hook and why, in the text of the
/// `unsupported-hook-unevaluated` diagnostic, and whether the definition's load or this run met
/// it.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct UnevaluatedHookOutput {
    pub hook: String,
    pub reason: String,
    pub observed_in: wire::ObservedInOutput,
}

impl From<&k_rust_backend::path_facts::UnevaluatedHook> for UnevaluatedHookOutput {
    fn from(unevaluated: &k_rust_backend::path_facts::UnevaluatedHook) -> Self {
        Self {
            hook: unevaluated.hook.clone(),
            reason: unevaluated.reason.to_string(),
            observed_in: unevaluated.observed_in.into(),
        }
    }
}

/// A value the definition leaves open that a run read: the hook that computed it and what the
/// definition leaves open about it (`class`, docs/compatibility.md, "Implementation-chosen hook
/// values": `order`, `item`, `float-destination`, `nan-sign`, `letter-case`, `signed-zero`,
/// `fresh-name`, `effect-order`, `fresh-association`, `float-rounding`, `outside-domain`,
/// `literal`). For `fresh-association`, the
/// compiler's association of a rule's two or more `!` names with counter offsets, `hook` is that
/// rule's `UNIQUE_ID`; for `literal`, the element of a literal the literal rules leave open, the
/// `UNIQUE_ID` of the rule or equation holding it, or a request's own literal as written.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct ChosenValueOutput {
    pub hook: String,
    pub class: String,
}

impl From<&k_rust_backend::builtin::ChosenValue> for ChosenValueOutput {
    fn from(chosen: &k_rust_backend::builtin::ChosenValue) -> Self {
        Self {
            hook: chosen.hook.to_string(),
            class: chosen.class.name().to_owned(),
        }
    }
}

/// The rules and equations an execution used, by `UNIQUE_ID`, each list sorted and without
/// repeats (docs/compatibility.md, "Run coverage").
///
/// - `applied`: every rewrite rule for which a step built a successor or an undefined step;
///   every equation of any kind (function, simplification, `anywhere`, overload, ceil,
///   predicate, `#Top` lemma) whose instance gave a result (its instantiated right-hand side, or
///   its subject stated bottom), wherever the run applied it (state simplification, a rule's
///   `requires`, `ensures`, right-hand side and definedness, another equation's condition, the
///   definedness analysis); every equation from which the run decided the definedness of an
///   operand that `#if`, `andThenBool` or `orElseBool` does not evaluate (one function-equation
///   step, or an unconditional ceil equation); and, for every rule of which a step began to
///   build a right-hand side alternative, its `requires` having held, every equation that the
///   load-time discharge of its definedness applied.
/// - `matched`: `applied`, plus every rule and equation whose condition the run began to decide
///   for an instance whose left-hand side matched (for a rewrite rule, or unified under a
///   narrowing condition the solver did not refute), whatever the verdict, including the
///   instances a definedness decision of an unevaluated operand considered and, for every rule
///   of which a step began to build a right-hand side alternative, every equation whose
///   condition its load-time discharge began to decide.
///
/// The lists cover every state the run explored, including leaves a `state-set` result merges
/// away, and are equal for `execute_kore` and `execute_observed_kore`, for both result
/// modalities, and for every earlier request to the backend. They are a deterministic function
/// of the definition, the request, the solver profile and the k-rust version. They never name a
/// builtin hook, an `smt-lemma`, macro or alias rule, a claim, or an equation that only the
/// load-time confluence check uses. A run that a stop, a timeout or a bound cut short reports
/// what it collected before it ended, which depends on where it stopped.
///
/// - `offered`, present exactly when the request set `collect_offered`: `matched`, plus every
///   rule and equation whose left-hand side matched (or was left undecided against) a subject
///   the run selected it as a candidate for at a site that selects by priority group (a rewrite
///   step and the fold of its lower groups, an equation scan of an application or a predicate,
///   the `#Top` lemmas of a conjunction operand, the definedness analysis and the decisions of an
///   unevaluated operand), whether the site tried it or stopped before it. An axiom in no list
///   cannot change the run under a priority raise, an `owise` removal or a removed
///   `concrete`/`symbolic` set-aside, nor under a lowering (a lower priority, an added `owise`,
///   `concrete` or `symbolic`). `matched` does not reach lowerings: a candidate whose match was
///   left undecided blocks the lower groups of its site and is recorded only in `offered`. No
///   list reaches a left-hand-side edit, nor the load-time uses of an axiom.
///
/// - `conditions`, present exactly when the request set `collect_conditions`: for each rewrite
///   rule it names whose `requires` the run began to decide (the rules it adds to `matched`),
///   the records of those entries ([`RuleConditionsOutput`]). They cover every state the run
///   explored, as the lists do, and are a deterministic function of the same inputs; unlike the
///   lists they are kept in the order the run first made each distinct entry, up to the
///   request's limit per rule.
///
/// - `applied_counts`, present exactly when the request set `collect_counts`: each id of
///   `applied` with the number of times the run applied it (at least 1; its keys are
///   `applied`): for a rewrite rule, the successors (one per right-hand-side alternative) and
///   undefined-step entries its steps built; for an equation, the instances that gave a result
///   where the run computed one, so an evaluation served from a memo of the run counts once.
///   Unlike the lists, the counts grow with the states explored (a `state-set` run that skips a
///   twin subtree counts less than the `path-set` run) and count attempts later undone as
///   often as they ran; they are a deterministic function of the same inputs.
///
/// - `committed`, present exactly when the request set `collect_committed`: every rewrite rule
///   whose successor the run committed to, its own normalization having shown it defined (a
///   transition of some path); a candidate rolled back because its successor was undefined, an
///   undefined-step entry, a cut-point rule's proposed successor and a successor a stop or the
///   work budget cut before its normalization are left out, and a successor a `state-set` merge
///   absorbed is in it. On a run whose explored paths all end in leaves it is the union of the
///   rewrite entries of every explored path's trace, absorbed paths included; it is a subset of
///   `applied` (docs/compatibility.md, "Committed transitions").
///
/// - `bindings`, present exactly when the request set `collect_bindings`: per rule and equation,
///   the named symbols that were the head, through injections, of a value a fired instance bound
///   to a left-hand-side variable that the axiom reads elsewhere, the values of the selected
///   template binders, and the alternatives of an axiom with several that a fired instance took
///   ([`BindingsOutput`]), and, where the collection sets a `depth` `D`, the syntax paths of
///   length `2..=D` the fired instances touched. A rewrite rule's instance is fired where the run
///   committed to its successor, as for `committed`; an equation's where it gave a result.
///
/// - `windows`, present exactly when the request set `collect_windows` to `d`: every sequence of
///   at most `d` rewrite rules, by id, that some path committed to as consecutive steps, a step
///   being committed as for `committed`, sorted. Its windows of length 1 are `committed`; no
///   equation is in a window, and neither is a cut-point rule's proposed step. A `state-set` run
///   reports the windows of the `path-set` run of the same request wherever the two explore the
///   same states: a merged arrival takes the windows that go on into the recorded state's
///   subtree (docs/compatibility.md, "Rule windows").
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct RunCoverageOutput<K = Value> {
    pub applied: Vec<String>,
    pub matched: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub offered: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub conditions: Option<Vec<RuleConditionsOutput<K>>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub applied_counts: Option<BTreeMap<String, u64>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub committed: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub guards: Option<Vec<AxiomGuardOutput<K>>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bindings: Option<BindingsOutput>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub windows: Option<Vec<Vec<String>>>,
}

/// What an execute request records of its run's fired instances (wire `collectBindings`;
/// [`ExecuteRequest::collect_bindings`]).
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct BindingCollection {
    /// The symbols, by KORE name, recorded where one is the head of an operand of a fired
    /// instance.
    #[serde(default)]
    pub symbols: Vec<String>,
    /// The template binders whose values are recorded; a binder, a variable of one axiom, is
    /// selected at most once, under its axiom's `UNIQUE_ID` or its label.
    #[serde(default)]
    pub binders: Vec<BinderSelection>,
    /// The longest syntax path recorded (a positive integer; [`BindingsOutput::paths`]): every
    /// sequence of the named symbols along consecutive argument positions, of length `2..=depth`,
    /// that starts at a position a fired instance inspected, built or took as an operand and lies
    /// in its left-hand or right-hand side under its substitution (docs/compatibility.md, "Run
    /// coverage"). Absent by default, and then no path is recorded; a depth of 1 records none.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub depth: Option<std::num::NonZeroUsize>,
}

impl BindingCollection {
    /// The symbols `symbols`, with no binder selected and no path recorded.
    pub fn new<S: Into<String>>(symbols: impl IntoIterator<Item = S>) -> Self {
        Self {
            symbols: symbols.into_iter().map(Into::into).collect(),
            binders: Vec::new(),
            depth: None,
        }
    }

    /// The backend's collection, or the binder selected twice.
    fn into_backend(self) -> Result<k_rust_backend::coverage::BindingCollection, (String, String)> {
        let mut collection = k_rust_backend::coverage::BindingCollection::new(self.symbols);
        collection.depth = self.depth;
        for BinderSelection {
            axiom,
            variable,
            cap,
        } in self.binders
        {
            let key = k_rust_backend::coverage::BinderKey { axiom, variable };
            if collection.binders.contains_key(&key) {
                return Err((key.axiom, key.variable));
            }
            collection.binders.insert(key, cap);
        }
        Ok(collection)
    }
}

/// A template binder an execute request selects: a variable of a rule or equation, and the most
/// values the run keeps of it.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct BinderSelection {
    /// The rule or equation, by its `UNIQUE_ID` or its label.
    pub axiom: String,
    /// The variable, by its name in the definition (`VarB`).
    pub variable: String,
    /// The most values kept: the least ones in integer order.
    pub cap: usize,
}

/// The bindings of a run's fired instances ([`RunCoverageOutput::bindings`]).
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct BindingsOutput {
    /// Per rule and equation with a recorded head, sorted by id.
    pub operands: Vec<AxiomOperandsOutput>,
    /// Per selected binder bound at some fired instance, sorted by axiom, then variable, the
    /// axiom by its `UNIQUE_ID`.
    pub binders: Vec<BinderValuesOutput>,
    /// The alternatives of an axiom with several that some fired instance took, sorted by axiom,
    /// then left-hand side, then right-hand side alternative (wire: present only when not
    /// empty).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub alternatives: Vec<FiredAlternativeOutput>,
    /// Per rule and equation with at least one, sorted by id, the syntax paths of length
    /// `2..=depth` its fired instances touched; present exactly when the collection set a
    /// `depth` ([`BindingCollection::depth`]).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub paths: Option<Vec<AxiomPathsOutput>>,
}

/// The syntax paths one rule's or equation's fired instances touched ([`BindingsOutput::paths`]).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct AxiomPathsOutput {
    /// The axiom's `UNIQUE_ID`.
    pub axiom: String,
    /// The paths, sorted.
    pub paths: Vec<SyntaxPathOutput>,
}

/// A syntax path `(P1, i1, P2, ..., Pn)`: `symbols` are `P1, ..., Pn` by KORE name, and
/// `positions` the 0-based argument positions `i1, ..., i(n-1)`, `symbols[j + 1]` being the head,
/// through injections, of argument `positions[j]` of `symbols[j]`'s application.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct SyntaxPathOutput {
    /// The symbols, outermost first.
    pub symbols: Vec<String>,
    /// The argument positions between them.
    pub positions: Vec<usize>,
}

/// An alternative of an axiom with several that a fired instance took: the axiom's rules share
/// its `UNIQUE_ID`, one per disjunct of its left-hand side (or reading of a function
/// equation), and a rewrite rule with a disjunctive right-hand side builds one successor per
/// alternative of it.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct FiredAlternativeOutput {
    /// The axiom's `UNIQUE_ID`.
    pub axiom: String,
    /// The left-hand side alternative, by its position; absent when there is one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lhs: Option<usize>,
    /// The right-hand side alternative of a rewrite rule, by its position in the disjunction;
    /// absent when the right-hand side is no disjunction, and for an equation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rhs: Option<usize>,
}

/// The operand heads of one rule's or equation's fired instances.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct AxiomOperandsOutput {
    /// The axiom's `UNIQUE_ID`.
    pub axiom: String,
    /// The named symbols that were the head of an operand, sorted.
    pub symbols: Vec<String>,
}

/// The values a selected binder took at the fired instances of its axiom.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct BinderValuesOutput {
    /// The axiom, by its `UNIQUE_ID`, whichever name the request selected it by.
    pub axiom: String,
    /// The variable, as the request names it.
    pub variable: String,
    /// The `Int` literals bound, in decimal: the least `cap` of them, ascending.
    pub values: Vec<String>,
    /// Whether a further literal was bound that the cap left out (wire: present only when
    /// true).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub truncated: bool,
    /// Whether some fired instance bound the variable to a value that is no `Int` literal (wire:
    /// present only when true).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub nonliteral: bool,
}

/// Which rules' and equations' guard outcomes an execute request collects (wire
/// `collectGuards`), and its bounds ([`ExecuteRequest::collect_guards`]).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct GuardCollection {
    /// The rules and equations whose entries are folded, each named by its `UNIQUE_ID` or its
    /// label. A name that is neither, or an axiom with an empty `requires`, collects nothing.
    pub axioms: Vec<String>,
    /// The largest entry, in term nodes, the run's cache of entries keeps (default 256): a
    /// larger one is evaluated every time the run makes it.
    #[serde(default = "default_max_value_size")]
    pub max_value_size: usize,
    /// The most polls one entry's evaluation may make (default 1,000,000): its work bound,
    /// since it runs off the run's clock. A node the bound stops is `undecided-stopped`.
    #[serde(default = "default_record_polls")]
    pub record_polls: u64,
    /// The most entries the run's cache recognizes before it is cleared (default 4,096); a miss
    /// costs one more evaluation, never a changed outcome.
    #[serde(default = "default_guard_cache_keys")]
    pub cache_keys: usize,
    /// The most valuation combinations kept per axiom (default 256): the least ones in their
    /// order, so the kept set is a function of the full set.
    #[serde(default = "default_combination_limit")]
    pub combination_limit: usize,
}

impl GuardCollection {
    /// The axioms `axioms`, with the default bounds.
    pub fn new<S: Into<String>>(axioms: impl IntoIterator<Item = S>) -> Self {
        Self {
            axioms: axioms.into_iter().map(Into::into).collect(),
            max_value_size: default_max_value_size(),
            record_polls: default_record_polls(),
            cache_keys: default_guard_cache_keys(),
            combination_limit: default_combination_limit(),
        }
    }
}

fn default_guard_cache_keys() -> usize {
    k_rust_backend::coverage::DEFAULT_GUARD_CACHE_KEYS
}

fn default_combination_limit() -> usize {
    k_rust_backend::coverage::DEFAULT_COMBINATION_LIMIT
}

impl From<GuardCollection> for k_rust_backend::coverage::GuardCollection {
    fn from(collection: GuardCollection) -> Self {
        let mut converted = Self::new(collection.axioms);
        converted.max_value_size = collection.max_value_size;
        converted.record_polls = collection.record_polls;
        converted.cache_keys = collection.cache_keys;
        converted.combination_limit = collection.combination_limit;
        converted
    }
}

/// The guard outcomes of one rule or equation over a run's entries into its `requires`.
///
/// A node's outcome counts only where the node is reached, in written order, the same way for
/// every connective: an operand of a conjunction (`andBool`, `andThenBool`, `\and`, and the
/// conjuncts of the `requires`) is reached where every operand before it is `true`, an operand of
/// a disjunction (`orBool`, `orElseBool`, `\or`) where every one before it is `false`, the right
/// operand of `impliesBool` and `\implies` where the left one is `true`, and the operands of
/// `xorBool`, `\iff`, `notBool`, `\not` and `\equals(b, literal)` where their node is. So for
/// `A andThenBool B` the short-circuit classes "A false", "A true and B false" and "both true"
/// are A's `false`, B's `false` and the conjunction's `true`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct AxiomGuardOutput<K = Value> {
    /// The axiom's `UNIQUE_ID`.
    pub axiom: String,
    /// The nodes of the written `requires`, in preorder.
    pub nodes: Vec<GuardNodeOutput<K>>,
    /// The guard outcomes of the entries: the attempt's verdict, with the run's solver.
    pub outcomes: Vec<GuardOutcomeOutput>,
    /// The distinct valuations of the guard's atoms (nodes `term` and `predicate`, in preorder)
    /// with the entry's guard outcome; an atom's truth here is the strict reading's, also where
    /// the short-circuit reading did not reach it.
    pub combinations: Vec<CombinationOutput>,
    /// Whether the run made a further combination that the request's limit left out (wire:
    /// present only when true).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub combinations_truncated: bool,
}

/// A node of a written `requires` with the outcomes it took where it was reached.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct GuardNodeOutput<K = Value> {
    /// The conjunct's index, then the operand's index at each level down.
    pub path: Vec<u32>,
    pub shape: GuardShapeOutput<K>,
    pub reached: Vec<NodeOutcomeOutput>,
}

/// What a guard node is, as written (wire: `node` names it).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "node", rename_all = "kebab-case")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub enum GuardShapeOutput<K = Value> {
    /// A connective; its operands are the next nodes whose path extends this one's by one.
    Connective { connective: ConnectiveOutput },
    /// `\equals(b, literal)` of a Boolean term `b`.
    Equals { literal: bool },
    /// A Boolean term that is no connective, with the variables the axiom writes.
    Term { term: K },
    /// A predicate that is no connective and no `\equals(b, literal)`.
    Predicate { term: K },
}

/// An outcome of a reached node.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NodeOutcomeOutput {
    True,
    False,
    /// A Boolean node denoted no value.
    Undefined,
    /// Left undecided by the solver-free evaluation: the instance has variables.
    UndecidedSymbolic,
    /// Left undecided: the instance holds an application no equation evaluated.
    UndecidedUnevaluated,
    /// Left undecided: the evaluation's own budget or stack ran out.
    UndecidedStopped,
}

impl From<k_rust_backend::coverage::NodeOutcome> for NodeOutcomeOutput {
    fn from(outcome: k_rust_backend::coverage::NodeOutcome) -> Self {
        use k_rust_backend::coverage::{NodeOutcome, OperandCause};
        match outcome {
            NodeOutcome::True => Self::True,
            NodeOutcome::False => Self::False,
            NodeOutcome::Undefined => Self::Undefined,
            NodeOutcome::Undecided(OperandCause::Symbolic) => Self::UndecidedSymbolic,
            NodeOutcome::Undecided(OperandCause::Unevaluated) => Self::UndecidedUnevaluated,
            NodeOutcome::Undecided(OperandCause::Stopped) => Self::UndecidedStopped,
        }
    }
}

/// The guard outcome of one entry.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum GuardOutcomeOutput {
    Held,
    /// Refuted, and the entry's evaluation found its first reached false conjunct false.
    RefutedFalse,
    /// Refuted, the first reached false conjunct being `\equals(b, literal)` of an undefined `b`.
    RefutedUndefined,
    /// Refuted by the attempt's solver or path condition only: the evaluation found no conjunct
    /// false.
    RefutedDecided,
    UndecidedNoSolver,
    UndecidedSolverUnknown,
    UndecidedUntranslatable,
    UndecidedInconsistentPath,
    UndecidedSolverError,
    UndecidedSimplification,
    /// The attempt went on under the condition left open, or a decision that only evaluates
    /// left it open.
    UndecidedOpen,
    /// The run did not try the entry, and its solver-free evaluation left the condition open.
    UndecidedUntried,
    Stopped,
}

impl From<k_rust_backend::coverage::GuardOutcome> for GuardOutcomeOutput {
    fn from(outcome: k_rust_backend::coverage::GuardOutcome) -> Self {
        use k_rust_backend::coverage::{AttemptCause, GuardOutcome, Refutation};
        match outcome {
            GuardOutcome::Held => Self::Held,
            GuardOutcome::Refuted(Refutation::False) => Self::RefutedFalse,
            GuardOutcome::Refuted(Refutation::Undefined) => Self::RefutedUndefined,
            GuardOutcome::Refuted(Refutation::Decided) => Self::RefutedDecided,
            GuardOutcome::Undecided(AttemptCause::NoSolver) => Self::UndecidedNoSolver,
            GuardOutcome::Undecided(AttemptCause::SolverUnknown) => Self::UndecidedSolverUnknown,
            GuardOutcome::Undecided(AttemptCause::Untranslatable) => Self::UndecidedUntranslatable,
            GuardOutcome::Undecided(AttemptCause::InconsistentPath) => {
                Self::UndecidedInconsistentPath
            }
            GuardOutcome::Undecided(AttemptCause::SolverError) => Self::UndecidedSolverError,
            GuardOutcome::Undecided(AttemptCause::Simplification) => Self::UndecidedSimplification,
            GuardOutcome::Undecided(AttemptCause::Open) => Self::UndecidedOpen,
            GuardOutcome::Undecided(AttemptCause::Untried) => Self::UndecidedUntried,
            GuardOutcome::Stopped => Self::Stopped,
        }
    }
}

/// One valuation of a guard's atoms with its entry's guard outcome.
#[derive(Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct CombinationOutput {
    pub atoms: Vec<TruthOutput>,
    pub outcome: GuardOutcomeOutput,
}

/// Which rules' condition entries an execute request records (wire `collectConditions`), and
/// how much it keeps ([`ExecuteRequest::collect_conditions`]).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct ConditionCollection {
    /// The rewrite rules whose entries are recorded, each named by its `UNIQUE_ID` or its label
    /// (as [`ExecuteRequest::terminal_rules`] names them). A name that is neither, or that
    /// names an equation, records nothing.
    pub rules: Vec<String>,
    /// The most records kept per rule: the first `limit` distinct entries in the run's order
    /// (default 32), with no preference among them, so an entry closer to satisfying the
    /// condition that the run makes later can be left out; a rule with a further distinct entry
    /// is marked [`RuleConditionsOutput::truncated`].
    #[serde(default = "default_condition_limit")]
    pub limit: usize,
    /// The largest value a record holds, in term nodes (default 256); a larger one is reported
    /// as [`RecordedValueOutput::Omitted`].
    #[serde(default = "default_max_value_size")]
    pub max_value_size: usize,
    /// The most polls the evaluation of one record may make (default 1,000,000): its work bound,
    /// since it runs off the run's clock. What the bound stops is reported as
    /// [`RecordedValueOutput::Stopped`] and [`TruthOutput::Undecided`]. A run with a step timeout
    /// may exceed it in wall time by at most (rules recorded × `limit`) records of up to this
    /// many polls each; a caller that uses the step timeout as an overall wall-clock guard lowers
    /// this bound, names fewer rules, or cancels the request.
    #[serde(default = "default_record_polls")]
    pub record_polls: u64,
}

impl ConditionCollection {
    /// The rules `rules`, with the default caps.
    pub fn new<S: Into<String>>(rules: impl IntoIterator<Item = S>) -> Self {
        Self {
            rules: rules.into_iter().map(Into::into).collect(),
            limit: default_condition_limit(),
            max_value_size: default_max_value_size(),
            record_polls: default_record_polls(),
        }
    }
}

fn default_condition_limit() -> usize {
    k_rust_backend::coverage::DEFAULT_CONDITION_LIMIT
}

fn default_max_value_size() -> usize {
    k_rust_backend::coverage::DEFAULT_MAX_VALUE_SIZE
}

fn default_record_polls() -> u64 {
    k_rust_backend::coverage::DEFAULT_RECORD_POLLS
}

impl From<ConditionCollection> for k_rust_backend::coverage::ConditionCollection {
    fn from(collection: ConditionCollection) -> Self {
        let mut converted = Self::new(collection.rules);
        converted.limit = collection.limit;
        converted.max_value_size = collection.max_value_size;
        converted.record_polls = collection.record_polls;
        converted
    }
}

/// The records of one rule's condition entries.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct RuleConditionsOutput<K = Value> {
    /// The rule's `UNIQUE_ID`.
    pub rule: String,
    /// The distinct entries, in the order the run first made them. Two entries are the same when
    /// they bind the condition's variables to the same terms under the same path and match
    /// conditions.
    pub records: Vec<ConditionRecordOutput<K>>,
    /// Whether the run made a further distinct entry that the request's limit left out (wire:
    /// present only when true).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub truncated: bool,
}

/// One entry into a rule's `requires` for a matched instance: the bindings, the condition with
/// every node's truth as the record's evaluation decides it, and the attempt's verdict.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ConditionRecordOutput<K = Value> {
    /// The instance's binding of each variable of the `requires` that the match bound, as the
    /// match bound it, sorted by variable; each variable is named as the rule is written in the
    /// definition's KORE.
    pub bindings: Vec<RecordedBindingOutput<K>>,
    /// The `requires` as written, one predicate node per conjunct: it holds exactly when every
    /// conjunct is `true`.
    pub condition: Vec<ConditionNodeOutput<K>>,
    /// What the attempt decided about the condition, with the run's solver (wire: absent only
    /// when the attempt ended otherwise, by a panic).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verdict: Option<VerdictOutput>,
    /// Whether a value the definition leaves open (`implementation-chosen-value`) was read by the
    /// run before the entry, on any path, or by the record's evaluation, so that the record's
    /// terms may be one model's (wire: present only when true).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub chosen: bool,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct RecordedBindingOutput<K = Value> {
    pub variable: K,
    pub value: RecordedValueOutput<K>,
}

/// What a rule attempt decided about its instantiated `requires`.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum VerdictOutput {
    /// It holds for the instance, and the attempt goes on to build the rule's successor, which
    /// can still fail (an indeterminate instantiation, no successor, an error).
    Held,
    /// It does not hold (false, undefined, or contradicted by the path): the rule does not
    /// apply to the instance.
    Refuted,
    /// The attempt could not decide it (no solver, an undecided or untranslatable query): the
    /// attempt is indeterminate or applies the rule under the condition left open.
    Undecided,
    /// A stop (lack of stack, a step deadline, a cancellation) ended the attempt while it
    /// decided the condition.
    Stopped,
    /// The condition bound variables of the left-hand side the match left unbound, and the
    /// attempt re-entered with them: the next record of the rule with those bindings is the
    /// complete entry, and this one's operands over them are symbolic.
    Reentered,
}

impl From<k_rust_backend::coverage::Verdict> for VerdictOutput {
    fn from(verdict: k_rust_backend::coverage::Verdict) -> Self {
        use k_rust_backend::coverage::Verdict;
        match verdict {
            Verdict::Held => Self::Held,
            Verdict::Refuted => Self::Refuted,
            Verdict::Undecided => Self::Undecided,
            Verdict::Stopped => Self::Stopped,
            Verdict::Reentered => Self::Reentered,
        }
    }
}

/// The truth of a node under the instance, as the record's evaluation decides it under the
/// path and match conditions, without a solver.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum TruthOutput {
    /// The node holds for the instance (a Boolean node evaluates to `true`), in every model
    /// unless the record is `chosen`.
    True,
    /// The node does not hold (a Boolean node evaluates to `false`; a predicate is refuted).
    False,
    /// A Boolean node denotes no value for the instance: a partial operation in it is outside its
    /// domain (also in an operand `andThenBool` or `orElseBool` discards), or the path and match
    /// conditions have no model. Never on a predicate, which is two-valued.
    Undefined,
    /// Not decided: the node may be true, false or (if Boolean) undefined.
    Undecided,
}

impl From<k_rust_backend::coverage::Truth> for TruthOutput {
    fn from(truth: k_rust_backend::coverage::Truth) -> Self {
        use k_rust_backend::coverage::Truth;
        match truth {
            Truth::True => Self::True,
            Truth::False => Self::False,
            Truth::Undefined => Self::Undefined,
            Truth::Undecided => Self::Undecided,
        }
    }
}

/// A connective of a condition. The K Boolean connectives (`notBool` .. `xorBool`) are functions
/// on `Bool` and strict, undefined wherever an operand is (also one `andThenBool` or
/// `orElseBool` does not evaluate); the matching-logic ones (`\not` ..
/// `\iff`) combine two-valued predicates.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub enum ConnectiveOutput {
    #[serde(rename = "notBool")]
    NotBool,
    #[serde(rename = "andBool")]
    AndBool,
    #[serde(rename = "andThenBool")]
    AndThenBool,
    #[serde(rename = "orBool")]
    OrBool,
    #[serde(rename = "orElseBool")]
    OrElseBool,
    #[serde(rename = "impliesBool")]
    ImpliesBool,
    #[serde(rename = "xorBool")]
    XorBool,
    #[serde(rename = "\\not")]
    Not,
    #[serde(rename = "\\and")]
    And,
    #[serde(rename = "\\or")]
    Or,
    #[serde(rename = "\\implies")]
    Implies,
    #[serde(rename = "\\iff")]
    Iff,
}

impl From<k_rust_backend::coverage::Connective> for ConnectiveOutput {
    fn from(connective: k_rust_backend::coverage::Connective) -> Self {
        use k_rust_backend::coverage::Connective;
        match connective {
            Connective::NotBool => Self::NotBool,
            Connective::AndBool => Self::AndBool,
            Connective::AndThenBool => Self::AndThenBool,
            Connective::OrBool => Self::OrBool,
            Connective::OrElseBool => Self::OrElseBool,
            Connective::ImpliesBool => Self::ImpliesBool,
            Connective::XorBool => Self::XorBool,
            Connective::Not => Self::Not,
            Connective::And => Self::And,
            Connective::Or => Self::Or,
            Connective::Implies => Self::Implies,
            Connective::Iff => Self::Iff,
        }
    }
}

/// A node of a condition as written, with its truth (wire: `node` names the shape, and every
/// node has `value`). A conjunct is a predicate: a matching-logic connective, an `equals`, or a
/// predicate atom; below `equals` and the K Boolean connectives the nodes are `Bool` terms.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "node", rename_all = "kebab-case")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub enum ConditionNodeOutput<K = Value> {
    /// A connective and its operands, in order.
    Connective {
        connective: ConnectiveOutput,
        children: Vec<ConditionNodeOutput<K>>,
        value: TruthOutput,
    },
    /// The predicate `\equals(b, literal)` of a Boolean term `b` (a K `requires b` is
    /// `\equals(b, true)`): `true` exactly where `b` is defined and equal to `literal`, so an
    /// undefined `b` makes it `false`.
    Equals {
        literal: bool,
        child: Box<ConditionNodeOutput<K>>,
        value: TruthOutput,
    },
    /// Anything else.
    Atom(ConditionAtomOutput<K>),
}

/// An atom of a condition, evaluated under the instance.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ConditionAtomOutput<K = Value> {
    /// The KORE symbol of a Boolean application; the matching-logic connective of a predicate
    /// atom (`\equals` of two terms other than a Boolean term and a literal, `\ceil`, `\floor`,
    /// `\in`, `\exists`, `\forall`, `\top`, `\bottom`) or `absent` (a key's absence from a map or
    /// set, operands the key and the collection); absent for a Boolean variable or literal.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub head: Option<String>,
    /// The symbol's `hook`, when it has one (such as `INT.lt`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hook: Option<String>,
    /// The operands, each simplified under the instance and the path and match conditions: the
    /// arguments of an application, the terms of `\equals`, `\ceil`, `\floor`, `\in` and
    /// `absent`, the term itself when it is no application, none for the other connectives.
    pub operands: Vec<RecordedValueOutput<K>>,
    /// The positions in the record's `bindings` of the variables the atom mentions: the bound
    /// values its operands depend on (wire: absent when empty).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub reads: Vec<usize>,
    /// The atom's truth.
    pub value: TruthOutput,
}

/// A term of a record, marked by what it denotes (wire: `kind`, and `term` for the first three).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub enum RecordedValueOutput<K = Value> {
    /// A ground value: constructors, injections, domain values, and maps, sets and lists of
    /// them, with no function application left. Its KORE means the same in every model of the
    /// definition, unless the record is `chosen`.
    Value { term: K },
    /// Variable-free, but holding an application the evaluation left as it is (a function with
    /// no applicable equation, an operation the simplification failed on): not a value, and its
    /// meaning depends on the definition.
    Unevaluated { term: K },
    /// A term with variables.
    Symbolic { term: K },
    /// Found undefined (`\bottom`) under the instance.
    Undefined,
    /// A stop interrupted its evaluation (the record's budget or stack, or a cancellation):
    /// nothing is known of its value.
    Stopped,
    /// Larger than the request's `maxValueSize` nodes.
    Omitted,
}

fn is_zero(count: &usize) -> bool {
    *count == 0
}

/// One leaf of an execution: a configuration `state` (a term under constraints) and how its
/// path ended.
///
/// The constraints of every leaf are definedness-explicit: each atom over a partial term is a
/// conjunct of a conjunction enclosing it that also holds that term's definedness, or a top-level
/// atom that shows its term defined, and an equality of two possibly undefined terms not both shown
/// defined takes the form `(⌈a⌉ /\ ⌈b⌉ /\ a = b) \/ (\not ⌈a⌉ /\ \not ⌈b⌉)`. That form makes every
/// K valuation that satisfies them extend to a model of their SMT translation (relative to the
/// definition's trusted `smt-hook`s, `smt-lemma`s and SMT prelude), and it is closed under
/// conjunction, so a solver `Unsat` on one leaf's constraints, or on their conjunction with other
/// leaves' constraints and with predicates `Admitted` returns, shows that there is no instance.
/// With [`ExecuteRequest::assume_state_defined`] the initial term's definedness is assumed and not
/// restated, and the statement holds relative to that assumption. Partial terms of the leaf's term
/// need not be stated: on an instance of the leaf they are defined. The constraints the request
/// brought in are admitted in that form, and a request whose constraints have no such form is
/// refused. Proof leaves are outside this statement, and so is a definition whose rule or
/// equation condition holds an `\equals` of two possibly undefined terms (a condition with an atom
/// over a term-level `\and` is covered: its instance states the conjunction's definedness beside
/// the atom); a definition whose axioms hold an `\equals` that reads a term as a predicate is
/// refused when it loads (docs/compatibility.md, "Solver decisions over partial operations").
/// For a state a client writes itself, [`Backend::implies_kore`] with a `\bottom` consequent
/// decides whether it has an instance.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ExecutionLeaf<K = Value> {
    pub state: K,
    /// The backend diagnostics of the work this leaf's path went through, each distinct one once.
    /// A leaf of a `state-set` result also carries those of every path whose equal configuration
    /// was merged into it, so its list may name work that is not on its own `trace`, and the
    /// result is free of diagnostics exactly when the `path-set` result of the same request is,
    /// but for the `implementation-chosen-value` marks and `contradicted-claim` records of a
    /// state merged during exploration, which are on
    /// [`ExecutionResult::implementation_chosen_values`] and
    /// [`ExecutionResult::contradicted_claims`] instead. Those are path facts: they stay on every
    /// path whose decisions rest on the work that found them, whatever became of that work
    /// (docs/compatibility.md, "Marks in executions", "A contradicted `total` attribute is
    /// named, not repaired").
    /// A merged diagnostic names variables as the path that met it named them, so a variable the
    /// request does not name may not occur in this leaf's `state` (it is never one of the leaf's
    /// own variables), and diagnostics equal up to such names are each listed.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput<K>>,
    /// Successors reported by a branch or cut-point halt, including each successor's diagnostics.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub candidates: Option<Vec<ExecutionCandidateOutput<K>>>,
    /// The branch's remaining path candidate, when one remains.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub remainder: Option<ExecutionRemainderOutput<K>>,
    pub depth: u64,
    pub reason: HaltReasonOutput,
    /// The rule responsible for an undefined step, when the `Trivial` halt names one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule_id: Option<String>,
    /// The rule's optional label, using the same label as observations and the rule catalog.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule_label: Option<String>,
    /// Present on a `Trivial` or `Vacuous` leaf when its emptiness comes from an equation of a
    /// symbol declared `total` (or `functional`) that reduced an application of it to bottom: the
    /// definition contradicts the attribute on that input. A diagnostic about the definition; the
    /// leaf's reason and state are the same with or without it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub contradicted_total: Option<ContradictedTotalOutput<K>>,
    /// The stopped step's structured cause: on every `indeterminate`, `simplification-error`
    /// and `unsupported-hook` halt, and on no other. For an indeterminate halt it is the reason
    /// the step could not be decided; for a failed simplification (`simplification-error`, and
    /// `unsupported-hook`, a simplification that met a hook k-rust does not evaluate) it is the
    /// failure, and `stack-exhausted` for a state that ran out of native stack. A client tells a
    /// bound (`iteration-limit`) or a query the solver did not answer from a defect of k-rust or
    /// of a hook declaration (`builtin`, `invalid-builtin-result-symbol`, a `smt` failure such as
    /// `missing-model`) by this field, never by `detail`. This uses the same encoding as
    /// `IncompleteSearchOutput::Indeterminate.reason` and the failure of
    /// `IncompleteSearchOutput::Simplification`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cause: Option<SearchFailureOutput<K>>,
    /// Legacy human-readable diagnostic context.
    ///
    /// This field is not a stable semantic encoding. Consumers must branch on `reason` and use
    /// `cause`, `candidates`, `remainder`, `branch`, and `observations` for structured evidence.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    /// The rewrite, remainder and simplification entries of this leaf's path, in order, ending
    /// with the simplifications of the leaf's own pattern; empty when the request set
    /// `trace: false` ([`ExecuteRequest::trace`]).
    pub trace: Vec<TraceEntry>,
    /// Committed transition identities, independent of the observation rule filter.
    /// Unobserved execution leaves this empty; an empty allowlist retains every identity.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub branch: Vec<TransitionIdOutput>,
    /// Ordered effects committed on this branch, regardless of observation.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub effects: Vec<EffectOutput>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub observations: Vec<ObservationEventOutput<K>>,
    /// The arrivals at a stop this leaf's path counted, present exactly when the request set
    /// [`ExecuteRequest::stop_count`]: the arrival a `cut-point-rule` or `terminal-rule` leaf
    /// ends at included, so such a leaf reports the request's count, and any other leaf the
    /// arrivals its path passed before it ended otherwise.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stops: Option<u64>,
    /// Every arrival at a stop this leaf's path passed, whatever the stop condition answered
    /// there, present exactly when the execution had a stop condition
    /// ([`Backend::execute_kore_with_condition`]); `stops` then counts the arrivals where the
    /// condition held.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub arrivals: Option<u64>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ExecutionCandidateOutput<K = Value> {
    pub state: K,
    pub unique_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput<K>>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ExecutionRemainderOutput<K = Value> {
    pub state: K,
    pub rule_ids: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput<K>>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum HaltReasonOutput {
    /// The request was cancelled while this leaf's state was being expanded, and the run ended:
    /// the states still pending were dropped, not explored. Under `state-set` this leaf is never
    /// merged into, nor absorbs, an equal leaf, so the result of a cancelled run always carries
    /// it.
    Cancelled,
    /// No ground instance satisfying the leaf's constraint has a rewrite successor.
    /// This does not assert that a satisfying instance exists.
    Stuck,
    /// An undefined step. Under the leaf's constraint some rule applies to every ground
    /// instance: it matches, its `requires` holds, and it blocks the lower priorities. Under
    /// strategy `all`, no instance has a defined successor, because the rule's right-hand side
    /// is undefined there or its `ensures` is false there, and no other applicable rule gives
    /// one. Strategy `any` also offers such instances to every later match of the rule and every
    /// later rule of the same priority, so under it too no rule of that priority gives an
    /// instance a defined successor.
    /// The leaf's state is the configuration before that step, and its constraint is the
    /// condition under which the step is undefined. That constraint may existentially quantify
    /// the rule's fresh variables (`?X`).
    /// The instances' events of that step are not on the leaf's path; an observed run records
    /// them as rolled back in `discarded`.
    /// This does not assert that a satisfying instance exists: the constraint is not checked for
    /// satisfiability, and a consumer that needs to know decides it.
    Trivial,
    /// The path's constraint was shown unsatisfiable, so the leaf has no instance: it simplified
    /// to `false`, or a solver answered `Unsat` for it, which refutes it because the constraint
    /// is definedness-explicit (see [`ExecutionLeaf`]). A step's successor that normalizes to
    /// `\bottom` is no successor, so it is reported as the step's `Trivial` leaf, or not at all
    /// where another candidate takes its instances; a `Vacuous` leaf is the initial state, a
    /// remainder, or the successor of a step whose pre-step state itself had no instance.
    Vacuous,
    Branch,
    CutPoint,
    /// The path arrived by one of the request's terminal rules and ends there. The halt records
    /// how the path arrived, not a property of the configuration, which may have successors when
    /// reached otherwise: under `state-set` a terminal leaf absorbs, and is absorbed by, only
    /// stuck and terminal leaves of its configuration, and is kept beside a branch, cut-point,
    /// bound, timeout or other leaf of it.
    Terminal,
    /// The path arrived at a stop where the in-process stop condition was left undecided
    /// ([`Backend::execute_kore_with_condition`]): continuing would run past a possible stop,
    /// and stopping would claim one that was not shown, so the path ends at the arrival's stop
    /// state (the state before a cut-point rule's step, the successor of a terminal rule's). It
    /// is no result of the run; only a request with a stop condition has it, and under
    /// `state-set` it is never merged.
    StopUndecided,
    /// An in-process probe found a difference at a point ([`Backend::execute_kore_with_probe`]),
    /// and the request ended there: the leaf's state is the point's observed state (the state
    /// before a before point's step, the normalized successor of an after point's). It is no end
    /// of the run; only a request with a probe has it, and under `state-set` it is never merged.
    ProbeDifference,
    /// An in-process probe needed nothing more of the path at a point
    /// ([`Backend::execute_kore_with_probe`]), and the path ended there, at the point's observed
    /// state. It is no end of the run; only a request with a probe has it, and under
    /// `state-set` it is never merged.
    ProbeDone,
    DepthBound,
    BreadthBound,
    /// The request's `max_work` was reached before this state was visited. The leaf's state is
    /// the state where exploration stopped, as it was taken from the worklist, unexpanded and
    /// unnormalised: it is not a reached result, its term may be unnormalised and its constraint
    /// unsatisfiable. The states still pending were not explored, so the result is incomplete.
    /// It is the last leaf of its result and never merged with another under `state-set`.
    WorkBound,
    /// The request's `max_polls` was reached while this leaf's state was being expanded, and
    /// the run ended: the leaf's state is the state as it stood when the bound stopped it, as a
    /// `cancelled` leaf's is, and the states still pending were dropped, not explored. It is not
    /// a reached result and the result is incomplete; unlike a cancellation it is deterministic
    /// (docs/compatibility.md, "Poll budget"). It is the last leaf of its result and never
    /// merged with another under `state-set`.
    PollBound,
    /// Rule applicability or a remainder could not be decided; no stuckness claim is made.
    Indeterminate,
    UnsupportedHook,
    SimplificationError,
    Timeout,
}

impl HaltReasonOutput {
    pub const ALL: [Self; 18] = [
        Self::Cancelled,
        Self::Stuck,
        Self::Trivial,
        Self::Vacuous,
        Self::Branch,
        Self::CutPoint,
        Self::Terminal,
        Self::StopUndecided,
        Self::ProbeDifference,
        Self::ProbeDone,
        Self::DepthBound,
        Self::BreadthBound,
        Self::WorkBound,
        Self::PollBound,
        Self::Indeterminate,
        Self::UnsupportedHook,
        Self::SimplificationError,
        Self::Timeout,
    ];
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct TraceEntry {
    pub depth: u64,
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    pub unique_id: String,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct PatternRequest {
    /// A KORE JSON envelope on the wire ([`deserialize_kore_pattern`]).
    #[serde(deserialize_with = "deserialize_kore_pattern")]
    pub state: KorePattern,
    #[serde(default)]
    pub module_name: Option<String>,
    #[serde(default = "default_backend_schema_version")]
    pub schema_version: u32,
}

impl PatternRequest {
    /// A request from `state` in the default module.
    pub fn new(state: KorePattern) -> Self {
        Self {
            state,
            module_name: None,
            schema_version: BACKEND_SCHEMA_VERSION,
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct ImplicationRequest {
    #[serde(deserialize_with = "deserialize_kore_pattern")]
    pub antecedent: KorePattern,
    #[serde(deserialize_with = "deserialize_kore_pattern")]
    pub consequent: KorePattern,
    #[serde(default)]
    pub module_name: Option<String>,
    #[serde(default = "default_backend_schema_version")]
    pub schema_version: u32,
}

impl ImplicationRequest {
    /// A request for `antecedent` implies `consequent` in the default module.
    pub fn new(antecedent: KorePattern, consequent: KorePattern) -> Self {
        Self {
            antecedent,
            consequent,
            module_name: None,
            schema_version: BACKEND_SCHEMA_VERSION,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ImplicationResult {
    pub schema_version: u32,
    pub status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub condition: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub failure: Option<ImplicationFailureOutput>,
}

/// The part of the consequent that the antecedent's instances outside it fail, on an `invalid`
/// or `unknown` implication that found one. It says nothing about whether such instances exist;
/// the status does.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ImplicationFailureOutput {
    /// The consequent's term does not match the antecedent's; there is no `condition`.
    TermMismatch,
    /// A remainder of matching the consequent's term against the antecedent's fails;
    /// `condition` is the part of the antecedent that would lie in the consequent.
    PartialCoverage,
    /// The consequent's term matches, and its condition is refuted on the antecedent, or (on an
    /// `unknown` result) fails on part of it; `condition` is the match's.
    ConsequentCondition,
}

impl ImplicationFailureOutput {
    pub const ALL: [Self; 3] = [
        Self::TermMismatch,
        Self::PartialCoverage,
        Self::ConsequentCondition,
    ];
}

/// The version of the implication result schema, the `schemaVersion` of an
/// [`ImplicationResult`]. It moves only when that schema changes; a change of which verdict,
/// condition or failure an implication computes leaves it as it is, and the k-rust revision
/// covers that ("Format versions" in `docs/compatibility.md`).
pub const IMPLICATION_SCHEMA_VERSION: u32 = 2;

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelResultOutput {
    pub satisfiable: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub substitution: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(default, deny_unknown_fields, rename_all = "camelCase")]
pub struct ProveRequest {
    pub module_name: Option<String>,
    /// The claim to prove: a label, a unique id, or `#index`. A claim whose left-hand side is a
    /// disjunction is one claim per disjunct under one label and unique id, and holds only if
    /// every disjunct does; a request proves one disjunct, so a label or unique id that names
    /// such a claim is refused with the `#index` selectors of its disjuncts.
    pub claim: Option<String>,
    /// Claims available as guarded circularities, selected by label, unique id, or `#index`.
    /// By default the selected claim and every trusted claim are available.
    pub circularities: Option<Vec<String>>,
    pub max_depth: Option<u64>,
    pub min_depth: u64,
    pub breadth_limit: Option<usize>,
    /// How many leaves that are not proven the proof looks for, and at most how many it reports
    /// (`ProofOptions::max_counterexamples`). Breadth-first, it explores every state no deeper
    /// than the shallowest depth holding that many, and a status other than `disproved` (which a
    /// certified refutation found anywhere gives) is the strongest among the leaves down to that
    /// depth, whatever order the search reaches them in. Depth-first (`depth_first`), it ends at
    /// the last of them, so its status depends on the order the rules are tried in.
    pub max_counterexamples: usize,
    /// Maximum simplifier iterations per proof step, counted as for
    /// `ExecuteRequest::max_simplification_iterations`: determined ground function evaluation
    /// is not counted.
    /// Proof configuration simplification keeps partial terms or original constraints after
    /// exhaustion and records a backend diagnostic before continuing.
    pub max_simplification_iterations: usize,
    pub allow_vacuous: bool,
    pub depth_first: bool,
    pub step_timeout_ms: Option<u64>,
    pub moving_average_timeout: bool,
    pub schema_version: u32,
}

impl Default for ProveRequest {
    fn default() -> Self {
        Self {
            module_name: None,
            claim: None,
            circularities: None,
            max_depth: None,
            min_depth: 0,
            breadth_limit: None,
            max_counterexamples: 1,
            max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            allow_vacuous: false,
            depth_first: false,
            step_timeout_ms: None,
            moving_average_timeout: false,
            schema_version: BACKEND_SCHEMA_VERSION,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofResultOutput<K> {
    pub claim: String,
    pub status: String,
    pub explored_states: u64,
    pub unexplored_states: u64,
    /// Trusted reachability claims available to this request, including the selected claim
    /// when trusted. This does not enumerate every axiom of the definition or SMT prelude.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub trusted_claims: Vec<String>,
    pub leaves: Vec<ProofLeafOutput<K>>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofLeafOutput<K> {
    pub state: K,
    /// Semantic and claim transitions; equation normalization does not increment it.
    pub depth: u64,
    pub outcome: ProofLeafOutcomeOutput,
    /// This stuck leaf certifies a counterexample under the core's exactness conditions.
    /// An uncertified stuck leaf is unresolved, not a counterexample.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub certified: bool,
    /// This leaf was accepted as proven by vacuity. Its displayed pattern can be the
    /// predecessor of an undefined step and is not necessarily empty.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub vacuous: bool,
    /// Actual claim applications on this path (guarded circularities or trusted claims),
    /// in trace order. This is not a finite execution or termination certificate.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub claim_steps: Vec<TraceEntry>,
    /// The declaration contradiction behind emptiness or an undefined step on this branch.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub contradicted_total: Option<ContradictedTotalOutput<K>>,
    /// Why a `timeout`, `stack-exhausted` or `indeterminate` leaf ended there, in words for a
    /// reader. Absent on every other outcome. Its text is not part of the result: the outcome
    /// is.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
}

/// Where the proof left one state of the claim's search.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ProofLeafOutcomeOutput {
    /// The state implies the claim's right-hand side.
    Proven,
    /// The claim is trusted: its one leaf is its left-hand side, taken as proven unexplored.
    Trusted,
    /// The state lies outside the claim's right-hand side, and the search did not continue it:
    /// no rule or circularity gives it a successor. It disproves the claim only when the
    /// result's status is `disproved`.
    Stuck,
    /// An undefined step: a rule applies to the state's instances and its result is empty for
    /// them, so they have no successor.
    Trivial,
    /// The state's constraint simplifies to bottom: it has no instance.
    Vacuous,
    /// The state was reached at the depth bound, and not explored.
    DepthBound,
    /// The state was pending, unexplored, when the search's frontier exceeded the breadth
    /// limit and the search ended.
    BreadthBound,
    /// The state's step passed its deadline; the proof ends there.
    Timeout,
    /// The state's step ran out of stack; the proof goes on with the other states.
    StackExhausted,
    /// Whether the state implies the right-hand side, or what its step or a circularity does to
    /// it, was not decided; `detail` says which.
    Indeterminate,
}

impl ProofLeafOutcomeOutput {
    pub const ALL: [Self; 10] = [
        Self::Proven,
        Self::Trusted,
        Self::Stuck,
        Self::Trivial,
        Self::Vacuous,
        Self::DepthBound,
        Self::BreadthBound,
        Self::Timeout,
        Self::StackExhausted,
        Self::Indeterminate,
    ];

    /// The outcome's name, as the host wire spells it.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Proven => "proven",
            Self::Trusted => "trusted",
            Self::Stuck => "stuck",
            Self::Trivial => "trivial",
            Self::Vacuous => "vacuous",
            Self::DepthBound => "depth-bound",
            Self::BreadthBound => "breadth-bound",
            Self::Timeout => "timeout",
            Self::StackExhausted => "stack-exhausted",
            Self::Indeterminate => "indeterminate",
        }
    }
}

/// The error of a facade operation: its text, and the [`StopCause`] when the operation stopped.
///
/// The operations of [`Backend`] whose error is a `BackendError` make the error of a stop
/// through `From<StopCause>` (at the operation boundary of [`Backend::with_solver`], for a stop
/// of simplification, implication or model generation, for a stopped proof leaf, and for an
/// execution leaf or search entry whose stop leaves no answer), so such an error of an operation
/// that stopped (cancelled, past its step deadline, out of stack, or under a failed solver
/// prelude) answers [`Self::stop_cause`]. A stop that an operation's contract excludes (a step
/// deadline reported by a search, which arms none) is a text error, and an error made from text
/// answers `None`.
#[derive(Debug)]
pub struct BackendError {
    message: String,
    stop: Option<StopCause>,
    refusal: Option<UnstatedDefinedness>,
    kind: Option<BackendErrorKind>,
}

/// What kind of failure a [`BackendError`] that is not a stop reports, for the failures a
/// caller must tell apart from one another without reading the text ([`BackendError::kind`]).
/// Most errors have no kind: the error's text is then its whole content. New kinds may be added.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum BackendErrorKind {
    /// The request's state is not an executable state of the definition (a symbol the
    /// definition does not declare, a macro or alias left in it, a sort mismatch).
    InvalidState,
    /// The request's state is executable but could not be internalized in the definition.
    StateNotInternalized,
    /// The request's patterns are nested deeper than the largest stack the backend provides for
    /// one operation: the depth exceeds a reservation the build fixes, so the refusal is a
    /// function of the request (`DefinitionError::InsufficientStack`).
    InsufficientStack,
    /// The request's patterns need a stack segment the system refused to map: the refusal
    /// depends on the host's memory and the calling thread's stack, not on the request alone
    /// (`DefinitionError::StackSegmentRefused`).
    StackSegmentRefused,
    /// The solver for the definition's module could not be created: the definition's SMT
    /// declarations, their translation, or the host refused the solver context.
    SolverInit,
    /// The in-process stop condition of an execution has no value at an arrival
    /// ([`Backend::execute_kore_with_condition`]): the stop criterion is undefined on this run,
    /// so the request has no result. The message names the rule, the depth and the reason.
    StopConditionRefused,
}

impl BackendError {
    /// An error that is not a stop: `message` is its whole content.
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            stop: None,
            refusal: None,
            kind: None,
        }
    }

    /// An error that is not a stop, of `kind`: `message` is its whole content.
    pub fn of_kind(kind: BackendErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind: Some(kind),
            ..Self::new(message)
        }
    }

    /// The error of a proof request whose claim is refused: its constraints have no
    /// definedness-explicit form (`ReachabilityClaim::unstated`), so it is not proven.
    pub fn refused_claim(reason: UnstatedDefinedness) -> Self {
        Self {
            message: format!(
                "could not prove claim: the claim's constraints cannot be read faithfully: {reason}"
            ),
            stop: None,
            refusal: Some(reason),
            kind: None,
        }
    }

    /// Why the claim of a proof request is refused, when this error refuses one
    /// ([`Self::refused_claim`]).
    pub fn claim_refusal(&self) -> Option<&UnstatedDefinedness> {
        self.refusal.as_ref()
    }

    /// The error's text, as its `Display` writes it.
    pub fn message(&self) -> &str {
        &self.message
    }

    /// The cause of the stop this error reports, or `None` when the operation did not stop but
    /// failed.
    pub fn stop_cause(&self) -> Option<&StopCause> {
        self.stop.as_ref()
    }

    /// The kind of this error ([`BackendErrorKind`]), set where the operation still holds the
    /// typed cause: a state the execute or search operations refuse or cannot internalize, a
    /// request nested too deep for the backend's stack, and a solver that could not be created.
    /// `None` for a stop ([`Self::stop_cause`]) and for every other error, whose text is then its
    /// whole content.
    pub fn kind(&self) -> Option<BackendErrorKind> {
        self.kind
    }
}

impl fmt::Display for BackendError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for BackendError {}

/// The error of an operation that stopped before producing its answer. It keeps the cause
/// ([`BackendError::stop_cause`]), and its text is the cause's own text, which names it
/// (`Request cancelled`, the step's timeout, the exhausted stack, `could not initialize Z3:
/// <failure>`), so a caller whose error is text reads the same message.
impl From<StopCause> for BackendError {
    #[deny(clippy::wildcard_enum_match_arm)]
    fn from(cause: StopCause) -> Self {
        match cause {
            StopCause::Cancelled
            | StopCause::PollBound(_)
            | StopCause::Deadline(_)
            | StopCause::StackExhausted(_)
            | StopCause::SolverPrelude(_) => Self {
                message: cause.to_string(),
                stop: Some(cause),
                refusal: None,
                kind: None,
            },
        }
    }
}

fn json_output_error(error: serde_json::Error) -> BackendError {
    BackendError::new(format!("could not serialize backend JSON: {error}"))
}

fn serialize_wire(value: &impl Serialize) -> Result<String, BackendError> {
    serde_json::to_string(value).map_err(json_output_error)
}

/// A persistent backend session over one compiled KORE definition.
pub struct Backend {
    session: BackendSession,
    options: BackendOptions,
    /// The stack the simplifier's recursion may take beyond its thread's in each operation
    /// (`nesting::with_simplification_stack_budget`).
    simplification_stack_budget: usize,
    #[cfg(feature = "z3-inference")]
    solvers: std::collections::BTreeMap<String, Z3Solver>,
    #[cfg(feature = "z3-inference")]
    smt_prelude: Option<String>,
}

impl Backend {
    pub fn new(
        definition_kore: &str,
        module_name: impl Into<String>,
        options: BackendOptions,
    ) -> Result<Self, BackendError> {
        let syntax =
            parse_definition(definition_kore).map_err(error("could not parse KORE definition"))?;
        Self::from_definition(syntax, module_name, options)
    }

    pub fn from_definition(
        syntax: k_rust_kore::kore::ast::Definition,
        module_name: impl Into<String>,
        options: BackendOptions,
    ) -> Result<Self, BackendError> {
        Self::from_session(BackendSession::new(syntax, module_name), options, None)
    }

    /// Internalize one selected module without constructing a solver yet.
    pub fn internalize_definition(
        syntax: &k_rust_kore::kore::ast::Definition,
        module_name: &str,
    ) -> Result<BackendDefinition, BackendError> {
        BackendDefinition::internalize(syntax, module_name)
            .map_err(error("could not internalize KORE definition"))
    }

    /// Internalize a source-compiled definition with the compiler's rewrite order.
    pub fn internalize_source_definition(
        syntax: &k_rust_kore::kore::ast::Definition,
        module_name: &str,
        execution_rewrite_order: &[String],
    ) -> Result<BackendDefinition, BackendError> {
        BackendDefinition::internalize_for_source_execution(
            syntax,
            module_name,
            execution_rewrite_order,
        )
        .map_err(error("could not internalize source execution definition"))
    }

    pub fn from_definition_with_prelude(
        syntax: k_rust_kore::kore::ast::Definition,
        module_name: impl Into<String>,
        options: BackendOptions,
        smt_prelude: String,
    ) -> Result<Self, BackendError> {
        Self::from_session(
            BackendSession::new(syntax, module_name),
            options,
            Some(smt_prelude),
        )
    }

    pub fn from_internalized(
        definition: BackendDefinition,
        options: BackendOptions,
    ) -> Result<Self, BackendError> {
        Self::from_session(BackendSession::with_definition(definition), options, None)
    }

    pub fn from_internalized_with_prelude(
        definition: BackendDefinition,
        options: BackendOptions,
        smt_prelude: Option<String>,
    ) -> Result<Self, BackendError> {
        Self::from_session(
            BackendSession::with_definition(definition),
            options,
            smt_prelude,
        )
    }

    pub fn from_session(
        session: BackendSession,
        options: BackendOptions,
        _smt_prelude: Option<String>,
    ) -> Result<Self, BackendError> {
        let mut backend = Self {
            session,
            options,
            simplification_stack_budget: k_rust_backend::nesting::SIMPLIFICATION_STACK_BUDGET,
            #[cfg(feature = "z3-inference")]
            solvers: Default::default(),
            #[cfg(feature = "z3-inference")]
            smt_prelude: _smt_prelude,
        };
        backend.with_solver(None, |_, _| Ok::<_, BackendError>(()))?;
        Ok(backend)
    }

    /// Set the native stack, in bytes, that the simplifier's recursion may take in each later
    /// operation beyond the stack the operation runs on; the default is
    /// [`k_rust_backend::nesting::SIMPLIFICATION_STACK_BUDGET`]. A function recursion deeper than
    /// that stops with [`StopCause::StackExhausted`]. A smaller budget stops a runaway recursion
    /// sooner and commits less memory before it does; 0 confines the simplifier to the stack the
    /// operation runs on. The budget is per thread; the segments of every thread of the process
    /// together stay within [`k_rust_backend::nesting::SIMPLIFICATION_STACK_PROCESS_BUDGET`].
    pub fn set_simplification_stack_budget(&mut self, bytes: usize) {
        self.simplification_stack_budget = bytes;
    }

    pub fn capabilities(&self) -> BackendCapabilities {
        BackendCapabilities {
            execution: true,
            simplification: true,
            implication: true,
            model_generation: cfg!(feature = "z3-inference"),
            proving: true,
            module_addition: true,
            smt: cfg!(feature = "z3-inference"),
            step_timeouts: !cfg!(target_arch = "wasm32"),
            search: true,
            observation: true,
            coverage: true,
            coverage_offered: true,
            coverage_counts: true,
            coverage_conditions: true,
            coverage_guards: true,
            coverage_guards_untried: true,
            coverage_bindings: true,
            coverage_committed: true,
            coverage_windows: true,
            coverage_binding_paths: true,
            state_matches: true,
            stack_stops: true,
            smt_unknowns: true,
            poll_bound: true,
            implementation_chosen_values: true,
            contradicted_claims: true,
            allowance_refusals: true,
            unsupported_hooks: true,
            short_circuit_readings: true,
            passed_stops: true,
            stop_count: true,
        }
    }

    pub fn default_module(&self) -> &str {
        self.session.default_module()
    }

    /// Whether this backend already holds the internalized definition of `module`: a module
    /// other than the default one is internalized by the first request that names it (or by
    /// [`Self::select_definition`]) and kept for later requests.
    pub fn is_loaded(&self, module: &str) -> bool {
        self.session.is_loaded(module)
    }

    /// Return the compiled rules in the definition selected for execution.
    ///
    /// A written sentence's kind is found by matching its `Source` and `Location` against
    /// `origins`. A position absent from the catalog compiled to no axiom of this definition.
    /// Equal written axioms yield one entry with all their origins. An identity shared by
    /// different entries has `shared_identity = true` and is refused by the observation filter.
    pub fn rule_catalog(
        &self,
        module_name: Option<&str>,
    ) -> Result<Vec<CompiledRuleOutput>, BackendError> {
        let definition = self
            .session
            .definition(module_name)
            .map_err(error("could not select backend module"))?;
        let mut identity_counts = BTreeMap::<&str, usize>::new();
        for axiom in definition.classified_axioms() {
            *identity_counts
                .entry(&axiom.attributes().unique_id)
                .or_default() += 1;
        }
        Ok(definition
            .classified_axioms()
            .iter()
            .map(|axiom| {
                let attributes = axiom.attributes();
                CompiledRuleOutput {
                    id: attributes.unique_id.clone(),
                    kind: match axiom {
                        ClassifiedAxiom::Rewrite { .. } => CompiledRuleKind::Rewrite,
                        ClassifiedAxiom::Function { .. } => CompiledRuleKind::FunctionEquation,
                        ClassifiedAxiom::Simplification { .. } => CompiledRuleKind::Simplification,
                        ClassifiedAxiom::Ceil { .. } => CompiledRuleKind::Definedness,
                    },
                    executable: attributes.executable,
                    label: attributes.label.clone(),
                    priority: attributes.priority,
                    origins: attributes.origins.iter().map(Into::into).collect(),
                    shared_identity: identity_counts[attributes.unique_id.as_str()] > 1,
                }
            })
            .collect())
    }

    pub fn select_definition(
        &mut self,
        module: Option<&str>,
    ) -> Result<Arc<BackendDefinition>, SessionError> {
        self.session.definition(module)
    }

    pub fn add_module(&mut self, source: &str, name_as_id: bool) -> Result<String, BackendError> {
        let module = parse_module(source).map_err(error("could not parse KORE module"))?;
        self.add_parsed_module(source, module, name_as_id)
            .map_err(error("could not add KORE module"))
    }

    pub fn add_parsed_module(
        &mut self,
        source: &str,
        module: k_rust_kore::kore::ast::Module,
        name_as_id: bool,
    ) -> Result<String, SessionError> {
        self.session.add_module(source, module, name_as_id)
    }

    /// Execute without observation; every leaf's `branch` and `observations` are empty.
    /// [`Self::execute_observed_kore`] returns the same non-observation leaf fields in the same
    /// order.
    ///
    /// Coverage. The leaves' constraints cover the initial state: take any ground instance of
    /// the initial state that satisfies its constraint. Some leaf's constraint is satisfied by
    /// that instance extended with values for the variables the path introduced. This holds in
    /// both solver profiles under strategy `all`, when no leaf is `depth-bound`,
    /// `breadth-bound`, `work-bound`, `branch`, `cut-point`, `timeout` or `cancelled` and no leaf carries
    /// diagnostics.
    /// Every step covers its instances. The applied candidates take the instances where
    /// their result is defined, the remainder takes the instances no rule of the productive
    /// priority group applies to, and a `trivial` leaf takes the instances some rule applies to
    /// without a defined result. That includes the instances where a carried `ensures` or
    /// right-hand-side definedness obligation fails, even when a sibling candidate continues.
    /// A step's `trivial` leaves precede the leaves of its successors.
    /// Strategy `any` makes no coverage claim.
    ///
    /// The execution runs a program ([`EvaluationMode::Execution`]): it lists the items of `keys_list`,
    /// `values` and `Set2List` in k-rust's order, which the definition does not fix, so its
    /// states must not decide a claim; prove through [`Self::prove_kore`]
    /// (docs/compatibility.md, "Implementation-chosen hook values").
    ///
    /// The result is a function of the backend's inputs and the request, the same on a fresh
    /// `Backend` and on this one after other requests, in any process and on any thread, outside
    /// the exclusions of docs/compatibility.md, "Determinism and concurrency" (cancellation, step
    /// timeouts, a result whose `stack_stops` is nonzero, a `Bytes` hook the memory allowance
    /// made refuse a result, a load-time check or discharge stopped for lack of stack, and in
    /// builds with Z3 a result whose `smt_unknowns` is nonzero).
    ///
    /// The result's KORE is held as patterns, each built from the operation's terms inside the
    /// operation, which its holder clones, compares, drops and prints with explicit stacks.
    /// The result serialized with serde is the JSON text [`Self::execute_json`] writes.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn execute_kore(
        &mut self,
        request: ExecuteRequest,
    ) -> Result<KoreExecutionResult, BackendError> {
        self.execute_using(request, None, InProcess::default(), ProbeRules::default())
    }

    /// [`Self::execute_kore`] with a stop condition: a path ends at its `stopCount`th arrival
    /// at a stop where `condition` holds of the arrival's stop state (the state before a
    /// cut-point rule's step, the normalized successor of a terminal rule's), and takes every
    /// other arrival as any other step (docs/compatibility.md, "Stop condition (in-process)").
    /// Each leaf reports its arrivals where the condition held (`stops`) and all its arrivals
    /// (`arrivals`); an undecided answer ends its path `stop-undecided`.
    ///
    /// In-process only: the condition is a callback, which no wire request carries. It is asked
    /// isolated from the run and off its clock, and may run another backend's operations (an
    /// observer definition's simplification), which keep their own records and budgets.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::execute_kore`] does, and with [`BackendErrorKind::StopConditionRefused`]
    /// where the condition refused at an arrival.
    pub fn execute_kore_with_condition(
        &mut self,
        request: ExecuteRequest,
        condition: &mut dyn StopCondition,
    ) -> Result<KoreExecutionResult, BackendError> {
        self.execute_kore_in_process(
            request,
            InProcess {
                condition: Some(condition),
                reading: None,
                probe: None,
            },
        )
    }

    /// [`Self::execute_kore`] with what an in-process caller adds ([`InProcess`]): a stop
    /// condition, as [`Self::execute_kore_with_condition`] asks it, and a reading of the
    /// candidates of a stop rule's step, which decides whether the step is its state's one
    /// successor, so whether it is an arrival (docs/compatibility.md, "Stop count").
    ///
    /// # Errors
    ///
    /// As [`Self::execute_kore_with_condition`].
    pub fn execute_kore_in_process(
        &mut self,
        request: ExecuteRequest,
        in_process: InProcess<'_>,
    ) -> Result<KoreExecutionResult, BackendError> {
        self.execute_kore_with_probe(request, ProbeRules::default(), in_process)
    }

    /// [`Self::execute_kore_in_process`] with the rules whose steps `in_process.probe` observes:
    /// the probe is asked at each point, a taken step of a rule `probe_rules` selects whose
    /// successor is defined, of the state before the step for a before point and of the
    /// normalized successor for an after point (docs/compatibility.md, "Probes (in-process)").
    /// Its `Differs` answer ends the request with a `probe-difference` leaf, its `Done` answer
    /// the path with a `probe-done` leaf. It is told once where the path splits and asked
    /// nothing after, or else where the path ends. Without a probe the rules change nothing.
    ///
    /// In-process only: the probe is a callback, which no wire request carries. It is asked
    /// isolated from the run and off its clock, and a probe that always continues leaves the
    /// result as it is without it.
    ///
    /// # Errors
    ///
    /// As [`Self::execute_kore_with_condition`].
    pub fn execute_kore_with_probe(
        &mut self,
        request: ExecuteRequest,
        probe_rules: ProbeRules,
        in_process: InProcess<'_>,
    ) -> Result<KoreExecutionResult, BackendError> {
        self.execute_using(request, None, in_process, probe_rules)
    }

    /// Execute with observation without changing the leaves or their order.
    /// For the same request, leaves match [`Self::execute_kore`] after clearing `branch` and
    /// `observations`.
    /// Branch identities are independent of the rule filter; `rules: Some(vec![])` returns
    /// every identity and no observation events.
    ///
    /// The result's KORE is held as patterns, as [`Self::execute_kore`]'s; serialized with serde,
    /// it is the JSON text [`Self::execute_observed_json`] writes.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn execute_observed_kore(
        &mut self,
        request: ObservedRequest<ExecuteRequest>,
    ) -> Result<KoreExecutionResult, BackendError> {
        self.execute_using(
            request.request,
            Some(request.rules),
            InProcess::default(),
            ProbeRules::default(),
        )
    }

    fn execute_using<K: wire::WireKore>(
        &mut self,
        mut request: ExecuteRequest,
        observation_rules: Option<Option<Vec<String>>>,
        in_process: InProcess<'_>,
        probe_rules: ProbeRules,
    ) -> Result<ExecutionResult<K>, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        if request.collect_offered && !request.collect_coverage {
            return Err(BackendError::new(
                "collectOffered requires collectCoverage: the offered level is part of the run's coverage",
            ));
        }
        if request.collect_counts && !request.collect_coverage {
            return Err(BackendError::new(
                "collectCounts requires collectCoverage: the counts are part of the run's coverage",
            ));
        }
        if request.collect_conditions.is_some() && !request.collect_coverage {
            return Err(BackendError::new(
                "collectConditions requires collectCoverage: the condition records are part of the run's coverage",
            ));
        }
        if request.collect_guards.is_some() && !request.collect_coverage {
            return Err(BackendError::new(
                "collectGuards requires collectCoverage: the guard outcomes are part of the run's coverage",
            ));
        }
        if request.collect_bindings.is_some() && !request.collect_coverage {
            return Err(BackendError::new(
                "collectBindings requires collectCoverage: the bindings are part of the run's coverage",
            ));
        }
        let collect_bindings = request
            .collect_bindings
            .take()
            .map(BindingCollection::into_backend)
            .transpose()
            .map_err(|(axiom, variable)| {
                BackendError::new(format!(
                    "collectBindings selects the binder {variable} of {axiom} twice"
                ))
            })?;
        if request.collect_committed && !request.collect_coverage {
            return Err(BackendError::new(
                "collectCommitted requires collectCoverage: the committed transitions are part of the run's coverage",
            ));
        }
        if request.collect_windows.is_some() && !request.collect_coverage {
            return Err(BackendError::new(
                "collectWindows requires collectCoverage: the rule windows are part of the run's coverage",
            ));
        }
        #[cfg(target_arch = "wasm32")]
        if request.step_timeout_ms.is_some() || request.moving_average_timeout {
            return Err(BackendError::new(
                "step timeouts require a host monotonic clock and are unavailable in this WebAssembly build",
            ));
        }
        let mut syntax = request.state;
        let module = request.module_name.as_deref();
        let mut match_request = request.match_states;
        // The run reads the state and the target only as associated: it validates and
        // internalizes them and names the state's variables, and echoes neither.
        let definition = self.associate_request(
            module,
            std::iter::once(&mut syntax).chain(
                match_request
                    .iter_mut()
                    .flat_map(StateMatchRequest::patterns_mut),
            ),
        )?;
        // A binder is a variable of one axiom, which a selection names by its `UNIQUE_ID` or
        // its label: two selections of one binder under its two names are one selected twice.
        if let Some((first, second)) = collect_bindings
            .as_ref()
            .and_then(|collection| collection.selected_twice(&definition))
        {
            return Err(BackendError::new(format!(
                "collectBindings selects the binder {} of {} twice, also as the binder of {}",
                first.variable, first.axiom, second.axiom
            )));
        }
        let mut patterns = vec![&syntax];
        patterns.extend(match_request.iter().flat_map(StateMatchRequest::patterns));
        self.with_solver_on(definition, &patterns, |definition, solver| {
            definition
                .validate_executable_pattern(&syntax)
                .map_err(kinded(
                    "invalid executable state",
                    BackendErrorKind::InvalidState,
                ))?;
            // An execution runs a program, which takes k-rust's element of a literal the definition
            // leaves open and marks every leaf with it, the state-match target's included.
            let literals = k_rust_backend::definition::RequestLiterals::new();
            let initial = definition
                .admit_unverified(&syntax, &[])
                .for_execution(&literals)
                .internalize_pattern()
                .map_err(kinded(
                    "could not internalize execution state",
                    BackendErrorKind::StateNotInternalized,
                ))?;
            // The target is internalized as `search_pattern_kore` internalizes its pattern. It is
            // not added to the run's request names: the matcher matches only states without
            // variables, so no name of the run can meet one of the target's, and the run mints
            // the names it would mint without the option.
            let match_target = |pattern: &KorePattern, context: &'static str| {
                definition
                    .admit_unverified(pattern, &[])
                    .for_execution(&literals)
                    .as_match_target()
                    .internalize_pattern()
                    .map_err(error(context))
            };
            let match_states = match_request
                .as_ref()
                .map(|matching| {
                    let target = match_target(
                        &matching.pattern,
                        "could not internalize the state-match pattern",
                    )?;
                    let chain = matching
                        .chain
                        .as_ref()
                        .map(|chain| chain_options(chain, &match_target))
                        .transpose()?;
                    Ok::<_, BackendError>(StateMatchOptions {
                        target,
                        proof_agreement: matching.proof_agreement,
                        chain,
                    })
                })
                .transpose()?;
            let options = ExecutionOptions {
                max_depth: request.max_depth.unwrap_or(u64::MAX),
                max_breadth: request.max_breadth,
                max_simplification_iterations: request.max_simplification_iterations,
                mode: match request.strategy {
                    ExecutionStrategy::All => ExecutionMode::All,
                    ExecutionStrategy::Any => ExecutionMode::Any,
                },
                branch_mode: if request.stop_at_branch {
                    ExecutionBranchMode::StopAtBranch
                } else {
                    ExecutionBranchMode::ExploreAll
                },
                cut_point_rules: request.cut_point_rules.into_iter().collect(),
                terminal_rules: request.terminal_rules.into_iter().collect(),
                stop_count: request.stop_count.unwrap_or(std::num::NonZeroU64::MIN),
                step_timeout: request.step_timeout_ms.map(Duration::from_millis),
                moving_average_timeout: request.moving_average_timeout,
                assume_initial_defined: request.assume_state_defined,
                result_modality: request.result_modality.into(),
                retain_trace: request.trace,
                // The state as received, before its aliases are unfolded: none here, since an
                // executable state has none, but every path names its request the same way.
                request_names: RequestNames::of_received(&[&syntax]),
                // An execution runs a program, so it lists collections in k-rust's order.
                evaluation: EvaluationMode::Execution,
                // The backend opens the collection inside its execute entry, after this
                // operation has selected (and possibly built) the module, so the sets never hold
                // what building a module applied.
                collect_coverage: request.collect_coverage,
                collect_offered: request.collect_offered,
                collect_counts: request.collect_counts,
                collect_conditions: request.collect_conditions.map(Into::into),
                collect_guards: request.collect_guards.map(Into::into),
                collect_bindings,
                max_work: request.max_work,
                max_polls: request.max_polls,
                discard_stopped: request.cancelled_result == CancelledResultOutput::Error,
                match_states,
                collect_committed: request.collect_committed,
                collect_windows: request.collect_windows,
                request_literals: literals.to_vec(),
                probe_rules,
            };
            let observation = observation_rules
                .map(|rules| observation_options(definition, rules))
                .transpose()?;
            let asked = in_process.condition.is_some();
            let in_process_run =
                asked || in_process.reading.is_some() || in_process.probe.is_some();
            let result = match (in_process_run, &observation) {
                (true, observation) => execute_in_process(
                    definition,
                    initial,
                    options,
                    solver,
                    observation.as_ref(),
                    in_process,
                )
                .map_err(|refusal| {
                    BackendError::of_kind(
                        BackendErrorKind::StopConditionRefused,
                        refusal.to_string(),
                    )
                })?,
                (false, Some(observation)) => {
                    execute_observed_with_solver(definition, initial, options, solver, observation)
                }
                (false, None) => execute_with_solver(definition, initial, options, solver),
            };
            wire::execute_answer(
                request.cancelled_result,
                request.stop_count.is_some() || asked,
                asked,
                result,
            )
        })
    }

    /// The search runs a program ([`EvaluationMode::Execution`]): it lists the items of `keys_list`,
    /// `values` and `Set2List` in k-rust's order, which the definition does not fix, so its
    /// states must not decide a claim; prove through [`Self::prove_kore`]
    /// (docs/compatibility.md, "Implementation-chosen hook values").
    ///
    /// The response's KORE is held as patterns, as [`Self::execute_kore`]'s; serialized with
    /// serde, it is the JSON text [`Self::search_json`] writes.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn search_kore(
        &mut self,
        request: SearchRequest,
    ) -> Result<KoreSearchResponse, BackendError> {
        self.search_using(request, None)
    }

    /// [`Self::search_kore`] with observation, as [`Self::execute_observed_kore`] is
    /// [`Self::execute_kore`] with observation; serialized with serde, the response is the JSON
    /// text [`Self::search_observed_json`] writes.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn search_observed_kore(
        &mut self,
        request: ObservedRequest<SearchRequest>,
    ) -> Result<KoreSearchResponse, BackendError> {
        self.search_using(request.request, Some(request.rules))
    }

    fn search_using<K: wire::WireKore>(
        &mut self,
        request: SearchRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<SearchResponse<K>, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let mut options = search_options(&request);
        let mut syntax = request.state;
        options.request_names = RequestNames::of_received(&[&syntax]);
        let module = request.module_name.as_deref();
        // The search reads the state only as associated: it validates and internalizes it.
        let definition = self.associate_request(module, [&mut syntax])?;
        self.with_solver_on(definition, &[&syntax], |definition, solver| {
            definition
                .validate_executable_pattern(&syntax)
                .map_err(kinded(
                    "invalid executable state",
                    BackendErrorKind::InvalidState,
                ))?;
            // A search of a program marks the literals it reads whose element the definition
            // leaves open, on every state, the target's included.
            let literals = k_rust_backend::definition::RequestLiterals::new();
            let initial = definition
                .admit_unverified(&syntax, &[])
                .for_execution(&literals)
                .internalize_pattern()
                .map_err(kinded(
                    "could not internalize search state",
                    BackendErrorKind::StateNotInternalized,
                ))?;
            let options = SearchOptions {
                request_literals: literals.to_vec(),
                ..options
            };
            let result = match observation_rules {
                Some(rules) => {
                    let observation = observation_options(definition, rules)?;
                    search_graph_observed_with_solver(
                        definition,
                        initial,
                        options,
                        solver,
                        &observation,
                    )
                }
                None => search_graph_with_solver(definition, initial, options, solver),
            };
            wire::search_response(result, schema_version)
        })
    }

    /// The search runs a program ([`EvaluationMode::Execution`]): it lists the items of `keys_list`,
    /// `values` and `Set2List` in k-rust's order, which the definition does not fix, so its
    /// states must not decide a claim; prove through [`Self::prove_kore`]
    /// (docs/compatibility.md, "Implementation-chosen hook values").
    ///
    /// The response's KORE is held as patterns, as [`Self::execute_kore`]'s; serialized with
    /// serde, it is the JSON text [`Self::search_paths_json`] writes.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn search_paths_kore(
        &mut self,
        request: SearchRequest,
    ) -> Result<KorePathSearchResponse, BackendError> {
        self.search_paths_using(request, None)
    }

    /// [`Self::search_paths_kore`] with observation, as [`Self::execute_observed_kore`] is
    /// [`Self::execute_kore`] with observation; serialized with serde, the response is the JSON
    /// text [`Self::search_paths_observed_json`] writes.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn search_paths_observed_kore(
        &mut self,
        request: ObservedRequest<SearchRequest>,
    ) -> Result<KorePathSearchResponse, BackendError> {
        self.search_paths_using(request.request, Some(request.rules))
    }

    fn search_paths_using<K: wire::WireKore>(
        &mut self,
        request: SearchRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<PathSearchResponse<K>, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let mut options = search_options(&request);
        let mut syntax = request.state;
        options.request_names = RequestNames::of_received(&[&syntax]);
        let module = request.module_name.as_deref();
        // The search reads the state only as associated: it validates and internalizes it.
        let definition = self.associate_request(module, [&mut syntax])?;
        self.with_solver_on(definition, &[&syntax], |definition, solver| {
            definition
                .validate_executable_pattern(&syntax)
                .map_err(kinded(
                    "invalid executable state",
                    BackendErrorKind::InvalidState,
                ))?;
            // A search of a program marks the literals it reads whose element the definition
            // leaves open, on every state, the target's included.
            let literals = k_rust_backend::definition::RequestLiterals::new();
            let initial = definition
                .admit_unverified(&syntax, &[])
                .for_execution(&literals)
                .internalize_pattern()
                .map_err(kinded(
                    "could not internalize path-search state",
                    BackendErrorKind::StateNotInternalized,
                ))?;
            let options = SearchOptions {
                request_literals: literals.to_vec(),
                ..options
            };
            let result = match observation_rules {
                Some(rules) => {
                    let observation = observation_options(definition, rules)?;
                    search_paths_observed_with_solver(
                        definition,
                        initial,
                        options,
                        solver,
                        &observation,
                    )
                }
                None => search_paths_with_solver(definition, initial, options, solver),
            };
            wire::path_search_response(result, schema_version)
        })
    }

    /// The search runs a program ([`EvaluationMode::Execution`]): it lists the items of `keys_list`,
    /// `values` and `Set2List` in k-rust's order, which the definition does not fix, so its
    /// states must not decide a claim; prove through [`Self::prove_kore`]
    /// (docs/compatibility.md, "Implementation-chosen hook values").
    ///
    /// The response's KORE is held as patterns, as [`Self::execute_kore`]'s; serialized with
    /// serde, it is the JSON text [`Self::search_pattern_json`] writes.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn search_pattern_kore(
        &mut self,
        request: SearchPatternRequest,
    ) -> Result<KorePatternSearchResponse, BackendError> {
        self.search_pattern_using(request, None)
    }

    /// [`Self::search_pattern_kore`] with observation, as [`Self::execute_observed_kore`] is
    /// [`Self::execute_kore`] with observation; serialized with serde, the response is the JSON
    /// text [`Self::search_pattern_observed_json`] writes.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn search_pattern_observed_kore(
        &mut self,
        request: ObservedRequest<SearchPatternRequest>,
    ) -> Result<KorePatternSearchResponse, BackendError> {
        self.search_pattern_using(request.request, Some(request.rules))
    }

    fn search_pattern_using<K: wire::WireKore>(
        &mut self,
        request: SearchPatternRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<PatternSearchResponse<K>, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let mut options = pattern_search_options(&request);
        let mut initial_syntax = request.state;
        let mut target_syntax = request.pattern;
        // The target is internalized without the executable check, so it may apply aliases that
        // drop variables the client wrote; the search mints no name spelled like one of them.
        options.request_names = RequestNames::of_received(&[&initial_syntax, &target_syntax]);
        let module = request.module_name.as_deref();
        // The search reads the state and the target only as associated: it validates and
        // internalizes them.
        let definition =
            self.associate_request(module, [&mut initial_syntax, &mut target_syntax])?;
        let patterns = [&initial_syntax, &target_syntax];
        self.with_solver_on(definition, &patterns, |definition, solver| {
            definition
                .validate_executable_pattern(&initial_syntax)
                .map_err(kinded(
                    "invalid executable state",
                    BackendErrorKind::InvalidState,
                ))?;
            // A search of a program marks the literals it reads whose element the definition
            // leaves open, on every state, the target's included.
            let literals = k_rust_backend::definition::RequestLiterals::new();
            let initial = definition
                .admit_unverified(&initial_syntax, &[])
                .for_execution(&literals)
                .internalize_pattern()
                .map_err(kinded(
                    "could not internalize pattern-search state",
                    BackendErrorKind::StateNotInternalized,
                ))?;
            let target = definition
                .admit_unverified(&target_syntax, &[])
                .for_execution(&literals)
                .as_match_target()
                .internalize_pattern()
                .map_err(error("could not internalize search pattern"))?;
            let options = SearchOptions {
                request_literals: literals.to_vec(),
                ..options
            };
            let result = match observation_rules {
                Some(rules) => {
                    let observation = observation_options(definition, rules)?;
                    search_pattern_observed_with_solver(
                        definition,
                        initial,
                        &target,
                        options,
                        solver,
                        &observation,
                    )
                }
                None => search_pattern_with_solver(definition, initial, &target, options, solver),
            };
            wire::pattern_search_response(result, schema_version)
        })
    }

    /// The response's KORE is held as patterns, as [`Self::execute_kore`]'s; serialized with
    /// serde, it is the JSON text [`Self::search_pattern_paths_json`] writes.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn search_pattern_paths_kore(
        &mut self,
        request: SearchPatternRequest,
    ) -> Result<KorePathPatternSearchResponse, BackendError> {
        self.search_pattern_paths_using(request, None)
    }

    /// [`Self::search_pattern_paths_kore`] with observation, as [`Self::execute_observed_kore`] is
    /// [`Self::execute_kore`] with observation; serialized with serde, the response is the JSON
    /// text [`Self::search_pattern_paths_observed_json`] writes.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn search_pattern_paths_observed_kore(
        &mut self,
        request: ObservedRequest<SearchPatternRequest>,
    ) -> Result<KorePathPatternSearchResponse, BackendError> {
        self.search_pattern_paths_using(request.request, Some(request.rules))
    }

    fn search_pattern_paths_using<K: wire::WireKore>(
        &mut self,
        request: SearchPatternRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<PathPatternSearchResponse<K>, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let mut options = pattern_search_options(&request);
        let mut initial_syntax = request.state;
        let mut target_syntax = request.pattern;
        // The target is internalized without the executable check, so it may apply aliases that
        // drop variables the client wrote; the search mints no name spelled like one of them.
        options.request_names = RequestNames::of_received(&[&initial_syntax, &target_syntax]);
        let module = request.module_name.as_deref();
        // The search reads the state and the target only as associated: it validates and
        // internalizes them.
        let definition =
            self.associate_request(module, [&mut initial_syntax, &mut target_syntax])?;
        let patterns = [&initial_syntax, &target_syntax];
        self.with_solver_on(definition, &patterns, |definition, solver| {
            definition
                .validate_executable_pattern(&initial_syntax)
                .map_err(kinded(
                    "invalid executable state",
                    BackendErrorKind::InvalidState,
                ))?;
            // A search of a program marks the literals it reads whose element the definition
            // leaves open, on every state, the target's included.
            let literals = k_rust_backend::definition::RequestLiterals::new();
            let initial = definition
                .admit_unverified(&initial_syntax, &[])
                .for_execution(&literals)
                .internalize_pattern()
                .map_err(kinded(
                    "could not internalize path-pattern-search state",
                    BackendErrorKind::StateNotInternalized,
                ))?;
            let target = definition
                .admit_unverified(&target_syntax, &[])
                .for_execution(&literals)
                .as_match_target()
                .internalize_pattern()
                .map_err(error("could not internalize search pattern"))?;
            let options = SearchOptions {
                request_literals: literals.to_vec(),
                ..options
            };
            let result = match observation_rules {
                Some(rules) => {
                    let observation = observation_options(definition, rules)?;
                    search_pattern_paths_observed_with_solver(
                        definition,
                        initial,
                        &target,
                        options,
                        solver,
                        &observation,
                    )
                }
                None => {
                    search_pattern_paths_with_solver(definition, initial, &target, options, solver)
                }
            };
            wire::path_pattern_search_response(result, schema_version)
        })
    }

    /// Write an observed execution response without retaining its expanded KORE JSON as values.
    pub fn execute_observed_to_writer<W: std::io::Write>(
        &mut self,
        request: ObservedRequest<ExecuteRequest>,
        writer: W,
    ) -> Result<(), BackendError> {
        let response = self.execute_using::<Box<RawValue>>(
            request.request,
            Some(request.rules),
            InProcess::default(),
            ProbeRules::default(),
        )?;
        serde_json::to_writer(writer, &response).map_err(json_output_error)
    }

    pub fn execute_json(&mut self, request: ExecuteRequest) -> Result<String, BackendError> {
        serialize_wire(&self.execute_using::<Box<RawValue>>(
            request,
            None,
            InProcess::default(),
            ProbeRules::default(),
        )?)
    }

    pub fn execute_observed_json(
        &mut self,
        request: ObservedRequest<ExecuteRequest>,
    ) -> Result<String, BackendError> {
        serialize_wire(&self.execute_using::<Box<RawValue>>(
            request.request,
            Some(request.rules),
            InProcess::default(),
            ProbeRules::default(),
        )?)
    }

    pub fn search_json(&mut self, request: SearchRequest) -> Result<String, BackendError> {
        serialize_wire(&self.search_using::<Box<RawValue>>(request, None)?)
    }

    pub fn search_observed_json(
        &mut self,
        request: ObservedRequest<SearchRequest>,
    ) -> Result<String, BackendError> {
        serialize_wire(&self.search_using::<Box<RawValue>>(request.request, Some(request.rules))?)
    }

    pub fn search_paths_json(&mut self, request: SearchRequest) -> Result<String, BackendError> {
        serialize_wire(&self.search_paths_using::<Box<RawValue>>(request, None)?)
    }

    pub fn search_paths_observed_json(
        &mut self,
        request: ObservedRequest<SearchRequest>,
    ) -> Result<String, BackendError> {
        serialize_wire(
            &self.search_paths_using::<Box<RawValue>>(request.request, Some(request.rules))?,
        )
    }

    pub fn search_pattern_json(
        &mut self,
        request: SearchPatternRequest,
    ) -> Result<String, BackendError> {
        serialize_wire(&self.search_pattern_using::<Box<RawValue>>(request, None)?)
    }

    pub fn search_pattern_observed_json(
        &mut self,
        request: ObservedRequest<SearchPatternRequest>,
    ) -> Result<String, BackendError> {
        serialize_wire(
            &self.search_pattern_using::<Box<RawValue>>(request.request, Some(request.rules))?,
        )
    }

    pub fn search_pattern_paths_json(
        &mut self,
        request: SearchPatternRequest,
    ) -> Result<String, BackendError> {
        serialize_wire(&self.search_pattern_paths_using::<Box<RawValue>>(request, None)?)
    }

    pub fn search_pattern_paths_observed_json(
        &mut self,
        request: ObservedRequest<SearchPatternRequest>,
    ) -> Result<String, BackendError> {
        serialize_wire(
            &self.search_pattern_paths_using::<Box<RawValue>>(
                request.request,
                Some(request.rules),
            )?,
        )
    }

    /// Simplify the request's pattern, as [`Self::simplify_kore`] does with
    /// [`Admission::Unverified`], and write the simplified pattern as KORE JSON text, inside the
    /// operation, on the stack it runs on.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn simplify_json(&mut self, request: PatternRequest) -> Result<String, BackendError> {
        self.simplify_with(request, |pattern| {
            serialize_wire(&encode_pattern(&pattern)?)
        })
    }

    fn simplify_with<T>(
        &mut self,
        request: PatternRequest,
        finish: impl FnOnce(KorePattern) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        let mut syntax = request.state;
        let module = request.module_name.as_deref();
        // A proof route (`k_rust_backend::evaluation`), the definition's first load included.
        let _proof = EvaluationScope::enter(EvaluationMode::Proof);
        let definition = self.associate_request(module, [&mut syntax])?;
        self.simplify_associated(definition, &syntax, Admission::Unverified, finish)
    }

    /// Decide whether the request's antecedent implies its consequent, as [`Self::implies_kore`]
    /// does with [`Admission::Unverified`], and write the answer as an [`ImplicationResult`] in
    /// JSON text, inside the operation, on the stack it runs on.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn implies_json(&mut self, request: ImplicationRequest) -> Result<String, BackendError> {
        self.implies_with(request, |result| serialize_wire(&result))
    }

    fn implies_with<T>(
        &mut self,
        request: ImplicationRequest,
        finish: impl FnOnce(ImplicationResult) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        let mut antecedent = request.antecedent;
        let mut consequent = request.consequent;
        let module = request.module_name.as_deref();
        // A proof route (`k_rust_backend::evaluation`), the definition's first load included.
        let _proof = EvaluationScope::enter(EvaluationMode::Proof);
        let definition = self.associate_request(module, [&mut antecedent, &mut consequent])?;
        self.implies_associated(
            definition,
            &antecedent,
            &consequent,
            Admission::Unverified,
            |verdict, result_sort| {
                finish(ImplicationResult {
                    schema_version: IMPLICATION_SCHEMA_VERSION,
                    status: match verdict.status() {
                        ImplicationStatus::Valid => "valid",
                        ImplicationStatus::Invalid => "invalid",
                        ImplicationStatus::Indeterminate => "unknown",
                    }
                    .into(),
                    failure: verdict.failure().map(implication_failure),
                    condition: verdict
                        .into_condition()
                        .as_ref()
                        .map(|condition| condition_pattern(condition, &result_sort))
                        .transpose()?,
                })
            },
        )
    }

    /// Ask for a model of the request's predicate, as `Backend::model_for` does with
    /// [`Admission::Unverified`] in builds with the `z3-inference` feature, and write the answer as
    /// a [`ModelResultOutput`] in JSON text, inside the operation, on the stack it runs on; a build
    /// without that feature refuses every request.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn get_model_json(&mut self, request: PatternRequest) -> Result<String, BackendError> {
        self.get_model_with(request, |result| serialize_wire(&result))
    }

    fn get_model_with<T>(
        &mut self,
        request: PatternRequest,
        finish: impl FnOnce(ModelResultOutput) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        #[cfg(not(feature = "z3-inference"))]
        {
            let _ = (request, finish);
            Err(BackendError::new(
                "model generation requires the SMT-enabled build (the `z3-inference` feature); this build has no Z3",
            ))
        }
        #[cfg(feature = "z3-inference")]
        {
            let mut syntax = request.state;
            let module = request.module_name.as_deref();
            // A proof route (`k_rust_backend::evaluation`), the definition's first load
            // included.
            let _proof = EvaluationScope::enter(EvaluationMode::Proof);
            let definition = self.associate_request(module, [&mut syntax])?;
            self.model_for_associated(
                definition,
                &syntax,
                Admission::Unverified,
                |result, result_sort| {
                    finish(match result {
                        ModelResult::Sat(substitution) => ModelResultOutput {
                            satisfiable: "sat".into(),
                            substitution: result_sort
                                .as_ref()
                                .and_then(|sort| model_substitution(&substitution, sort))
                                .as_ref()
                                .map(encode_pattern)
                                .transpose()?,
                            reason: None,
                        },
                        ModelResult::Unsat => ModelResultOutput {
                            satisfiable: "unsat".into(),
                            substitution: None,
                            reason: None,
                        },
                        ModelResult::Unknown(reason) => ModelResultOutput {
                            satisfiable: "unknown".into(),
                            substitution: None,
                            reason: Some(if result_sort.is_none() {
                                "the pattern contains no model predicate".into()
                            } else {
                                reason
                            }),
                        },
                    })
                },
            )
        }
    }

    /// The `#index` selector of every claim `selector` names (a label, a unique id or an
    /// `#index`): one per disjunct of a claim whose left-hand side is a disjunction, which a proof
    /// request proves one at a time, and one for any other claim.
    pub fn claim_disjuncts(
        &self,
        module_name: Option<&str>,
        selector: &str,
    ) -> Result<Vec<String>, BackendError> {
        let definition = self
            .session
            .definition(module_name)
            .map_err(error("could not select backend module"))?;
        Ok(proving::select_claims(&definition, selector)?
            .into_iter()
            .map(|(index, _)| format!("#{index}"))
            .collect())
    }

    /// Prove one claim, selected by [`ProveRequest::claim`]. A claim whose left-hand side is a
    /// disjunction is proven one disjunct per request, each selected by its `#index`; it holds
    /// only if every disjunct is proven, and a label or unique id that names it is refused.
    ///
    /// Each leaf's KORE is held as patterns, as [`Self::execute_kore`]'s; serialized with serde,
    /// the result is the JSON text [`Self::prove_json`] writes.
    ///
    /// Cancellation and the other stops: [Bounding an operation](crate::backend#bounding-an-operation).
    pub fn prove_kore(&mut self, request: ProveRequest) -> Result<KoreProofResult, BackendError> {
        self.prove_using(request)
    }

    /// [`Self::prove_kore`] as JSON text: each leaf's KORE is written as text inside the operation,
    /// on the stack it runs on.
    pub fn prove_json(&mut self, request: ProveRequest) -> Result<String, BackendError> {
        serialize_wire(&self.prove_using::<Box<RawValue>>(request)?)
    }

    /// ```toml algorithm-site
    /// id = "backend.proof.search"
    /// role = "part"
    /// sites = ["Backend::prove_using"]
    /// ```
    fn prove_using<K: wire::WireKore>(
        &mut self,
        request: ProveRequest,
    ) -> Result<ProofResultOutput<K>, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        #[cfg(target_arch = "wasm32")]
        if request.step_timeout_ms.is_some() || request.moving_average_timeout {
            return Err(BackendError::new(
                "step timeouts require a host monotonic clock and are unavailable in this WebAssembly build",
            ));
        }
        // A proof route, including the definition's first load, whose analyses the proof reads
        // (`k_rust_backend::evaluation`).
        let _proof = EvaluationScope::enter(EvaluationMode::Proof);
        self.with_solver(request.module_name.as_deref(), |definition, solver| {
            let (claim_index, claim) = proving::select_claim(definition, request.claim.as_deref())?;
            // Circularities are claims, each disjunct of a disjunctive claim its own; a name
            // selects every disjunct of the claim it names.
            let mut seen = BTreeSet::new();
            let circularities = if let Some(selectors) = &request.circularities {
                let mut circularities = Vec::new();
                for selector in selectors {
                    for (index, candidate) in proving::select_claims(definition, selector)? {
                        if seen.insert(index) {
                            circularities.push(candidate);
                        }
                    }
                }
                circularities
            } else {
                definition
                    .reachability_claims()
                    .iter()
                    .enumerate()
                    .filter(|(index, candidate)| {
                        (std::ptr::eq(*candidate, claim) || candidate.attributes.trusted)
                            && seen.insert(*index)
                    })
                    .map(|(_, candidate)| candidate)
                    .collect()
            };
            let result = proving::run_claim(
                definition,
                claim,
                &circularities,
                ProofOptions {
                    max_depth: request.max_depth.unwrap_or(u64::MAX),
                    min_depth: request.min_depth,
                    breadth_limit: request.breadth_limit,
                    max_counterexamples: request.max_counterexamples,
                    max_simplification_iterations: request.max_simplification_iterations,
                    allow_vacuous: request.allow_vacuous,
                    search_order: if request.depth_first {
                        ProofSearchOrder::DepthFirst
                    } else {
                        ProofSearchOrder::BreadthFirst
                    },
                    step_timeout: request.step_timeout_ms.map(Duration::from_millis),
                    moving_average_timeout: request.moving_average_timeout,
                },
                solver,
            )
            .map_err(|failure| match failure {
                ProofError::UnstatedDefinedness(reason) => BackendError::refused_claim(reason),
                failure => error("could not prove claim")(failure),
            })?;
            // A cancelled request or a failed solver prelude ends the proof without a leaf for
            // the state it stopped, so no leaf names it. No answer of the solver means anything
            // under a failed prelude, so that is the operation's error. A cancellation is too,
            // unless the verdict no longer depends on the work it prevented
            // (`cancellation_keeps_verdict`). A passed step deadline and an exhausted stack stop
            // one state, which their leaves report.
            match &result.stopped {
                Some(cause @ StopCause::SolverPrelude(_)) => {
                    return Err(BackendError::from(cause.clone()));
                }
                Some(cause @ StopCause::Cancelled) if !result.settled => {
                    return Err(BackendError::from(cause.clone()));
                }
                // Only an execution counts a bound of polls.
                Some(
                    StopCause::Cancelled
                    | StopCause::PollBound(_)
                    | StopCause::Deadline(_)
                    | StopCause::StackExhausted(_),
                )
                | None => {}
            }
            Ok(ProofResultOutput {
                claim: claim
                    .attributes
                    .label
                    .clone()
                    .unwrap_or_else(|| format!("#{claim_index}")),
                status: proof_status(result.status).into(),
                explored_states: result.explored_states,
                unexplored_states: result.unexplored_states,
                trusted_claims: circularities
                    .iter()
                    .copied()
                    .chain(std::iter::once(claim))
                    .filter(|claim| claim.attributes.trusted && claim.unstated.is_none())
                    .map(|claim| {
                        claim
                            .attributes
                            .label
                            .clone()
                            .unwrap_or_else(|| claim.attributes.unique_id.clone())
                    })
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect(),
                leaves: result
                    .leaves
                    .into_iter()
                    .map(|leaf| {
                        let (outcome, detail) =
                            proof_leaf_outcome(&leaf.outcome, &leaf.pattern.term.sort())?;
                        Ok(ProofLeafOutput {
                            state: K::from_source(&externalize::constrained_pattern(
                                &leaf.pattern,
                            ))?,
                            depth: leaf.depth,
                            outcome,
                            detail,
                            certified: leaf.certified,
                            vacuous: leaf.proven_vacuously(),
                            claim_steps: leaf
                                .trace
                                .into_iter()
                                .filter(|entry| entry.kind == TraceKind::Claim)
                                .map(trace_entry)
                                .collect(),
                            contradicted_total: leaf
                                .contradicted_total
                                .as_deref()
                                .map(wire::contradicted_total_output)
                                .transpose()?,
                        })
                    })
                    .collect::<Result<_, BackendError>>()?,
            })
        })
    }

    /// Run `operation` on the definition of `module` with that definition's solver, as one
    /// operation boundary in both builds: a request stopped before it starts does not run
    /// `operation`. With the `z3-inference` feature the boundary also sees the solver's prelude:
    /// a solver whose prelude already failed does not run `operation`, and a prelude failure
    /// found while it runs is its result even when `operation` returned. Such a stop reaches the
    /// caller as its [`StopCause`] (re-exported in this module), through `E`'s `From<StopCause>`;
    /// see the module docs, "Bounding an operation".
    ///
    /// The definition of `module` is loaded, on first use, before the boundary; a cancellation
    /// does not interrupt the load, and the load does not read the token, so the definition it
    /// caches is the one a load outside any token's scope gives (module docs, "Bounding an
    /// operation", point 6).
    ///
    /// The operation runs on a stack that holds the definition's recursive passes over its own
    /// patterns and terms (`BackendDefinition::with_stack_for`); an operation over a request's
    /// patterns uses [`Self::with_solver_over`].
    pub fn with_solver<T, E>(
        &mut self,
        module: Option<&str>,
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError> + From<StopCause>,
    {
        self.with_solver_over(module, &[], operation)
    }

    /// [`Self::with_solver`] for an operation over the KORE `patterns` of a request.
    ///
    /// The whole operation, from preparing the solver to the result it returns, runs on a stack
    /// that holds the backend's recursive passes over `patterns` with their aliases unfolded,
    /// over the definition, and over the internal terms built from them
    /// (`BackendDefinition::with_stack_for`), so it must return only external results and drop
    /// its internal terms itself. Evaluation that recurses deeper than that stack goes on on
    /// segments up to the operation's simplification stack budget
    /// ([`Self::set_simplification_stack_budget`]). Patterns too deep for the largest stack the
    /// backend provides are refused with `InsufficientStack` before the operation runs.
    ///
    /// The stack is sized for `patterns` as given, so `operation` must read those patterns
    /// and no deeper form of them. The facade's own operations pass the request with its
    /// builtin collections associated (`BackendDefinition::associated_collections`), so that a
    /// collection's length adds no level to the stack they take; a caller that wants the same
    /// associates its patterns in the selected definition first and reads the associated ones.
    pub fn with_solver_over<T, E>(
        &mut self,
        module: Option<&str>,
        patterns: &[&KorePattern],
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError> + From<StopCause>,
    {
        let definition = self.definition_of(module).map_err(E::from)?;
        self.with_solver_on(definition, patterns, operation)
    }

    /// The definition of `module`, selected as every operation selects it, loaded on first use.
    pub(crate) fn definition_of(
        &self,
        module: Option<&str>,
    ) -> Result<Arc<BackendDefinition>, BackendError> {
        self.session
            .definition(module)
            .map_err(error("could not select backend module"))
    }

    /// The definition of `module` ([`Self::definition_of`]), after associating the builtin
    /// collections of `patterns`, a request's own copies, in it, in place
    /// (`BackendDefinition::associate_collections`): the request the operation sizes its stack
    /// for and internalizes.
    pub(crate) fn associate_request<'p>(
        &self,
        module: Option<&str>,
        patterns: impl IntoIterator<Item = &'p mut KorePattern>,
    ) -> Result<Arc<BackendDefinition>, BackendError> {
        let definition = self.definition_of(module)?;
        for pattern in patterns {
            definition.associate_collections(pattern);
        }
        Ok(definition)
    }

    /// [`Self::with_solver_over`] on `definition`, already selected.
    pub(crate) fn with_solver_on<T, E>(
        &mut self,
        definition: Arc<BackendDefinition>,
        patterns: &[&KorePattern],
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError> + From<StopCause>,
    {
        let depth = definition.operation_depth(patterns);
        let budget = self.simplification_stack_budget;
        k_rust_backend::nesting::with_stack(depth, || {
            k_rust_backend::nesting::with_simplification_stack_budget(budget, || {
                self.run_with_solver(definition, operation)
            })
        })
        .map_err(|cause| {
            let context = "the request is too deep for the backend";
            match &cause {
                DefinitionError::InsufficientStack { .. } => {
                    kinded(context, BackendErrorKind::InsufficientStack)(cause)
                }
                DefinitionError::StackSegmentRefused { .. } => {
                    kinded(context, BackendErrorKind::StackSegmentRefused)(cause)
                }
                // `nesting::with_stack` refuses only for stack; another refusal is no stack
                // refusal, and keeps no kind.
                _ => error(context)(cause),
            }
        })
        .map_err(E::from)?
    }

    #[cfg(feature = "z3-inference")]
    fn run_with_solver<T, E>(
        &mut self,
        definition: Arc<BackendDefinition>,
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError> + From<StopCause>,
    {
        let module = definition.main_module().to_string();
        if !self.solvers.contains_key(&module) {
            let options = Z3Options {
                budget: self.options.smt_budget,
                retry_limit: self.options.smt_retry_limit,
            };
            let solver = if let Some(prelude) = self.smt_prelude.as_deref() {
                Z3Solver::with_options_and_prelude(&definition, options, Some(prelude))
            } else {
                Z3Solver::with_options(&definition, options)
            }
            .map_err(kinded(
                "could not initialize Z3",
                BackendErrorKind::SolverInit,
            ))
            .map_err(E::from)?;
            self.solvers.insert(module.clone(), solver);
        }
        // The operation queries the solver through a counter of its `Unknown` answers, which
        // gives them to an open `stop::with_operation_record` of the caller: the solver's answers
        // and identity are unchanged.
        let solver = k_rust_backend::smt::UndecidedCounting::new(
            self.solvers.get(&module).expect("solver was inserted"),
        );
        let solver: &dyn SmtSolver = &solver;
        // The operation boundary. Its entry poll sees the prelude signal of a solver whose
        // prelude an earlier operation found failed, and a request stopped before it starts, so
        // neither runs; its exit poll sees a prelude failure found during this operation, also
        // one whose stop a refinement dismissed, and that stop replaces `operation`'s value,
        // since no answer of the solver means anything under a failed prelude. The caller
        // receives the cause itself.
        stop::operation(solver, || operation(&definition, solver))
            .map_err(|stop| E::from(stop.into_cause()))?
    }

    #[cfg(not(feature = "z3-inference"))]
    fn run_with_solver<T, E>(
        &mut self,
        definition: Arc<BackendDefinition>,
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError> + From<StopCause>,
    {
        let _ = self.options;
        // The operation boundary, as in the Z3 build: a request stopped before it starts does
        // not run. `NoSolver` has no prelude signal, so the boundary sees only the request's own
        // stops on entry and nothing on exit.
        stop::operation(&NoSolver, || operation(&definition, &NoSolver))
            .map_err(|stop| E::from(stop.into_cause()))?
    }
}

fn search_options(request: &SearchRequest) -> SearchOptions {
    bounded_search_options(
        request.search_type,
        request.max_depth,
        request.max_breadth,
        request.max_results,
        request.max_simplification_iterations,
    )
}

fn bounded_search_options(
    search_type: SearchTypeArg,
    max_depth: Option<u64>,
    max_breadth: Option<usize>,
    max_results: Option<usize>,
    max_simplification_iterations: usize,
) -> SearchOptions {
    SearchOptions {
        search_type: match search_type {
            SearchTypeArg::Final => SearchType::Final,
            SearchTypeArg::All => SearchType::Star,
            SearchTypeArg::OneStep => SearchType::One,
            SearchTypeArg::OneOrMoreSteps => SearchType::Plus,
        },
        max_depth: max_depth.unwrap_or(u64::MAX),
        max_breadth,
        max_results,
        max_simplification_iterations,
        request_names: RequestNames::default(),
        // Every search (`search_kore`, `search_paths_kore`, `search_pattern*` and their other
        // forms) explores the runs of a program, so it lists collections in k-rust's order.
        evaluation: EvaluationMode::Execution,
        // Each search sets the open literals its patterns hold.
        request_literals: Vec::new(),
        // The responses carry each reported state's trace.
        retain_trace: true,
    }
}

fn default_backend_schema_version() -> u32 {
    BACKEND_SCHEMA_VERSION
}

fn default_trace() -> bool {
    true
}

fn default_result_modality() -> ResultModalityOutput {
    ResultModalityOutput::StateSet
}

fn validate_backend_schema_version(schema_version: u32) -> Result<(), BackendError> {
    wire::validate_schema_version(schema_version)
}

fn pattern_search_options(request: &SearchPatternRequest) -> SearchOptions {
    bounded_search_options(
        request.search_type,
        request.max_depth,
        request.max_breadth,
        request.max_results,
        request.max_simplification_iterations,
    )
}

fn observation_options(
    definition: &BackendDefinition,
    rules: Option<Vec<String>>,
) -> Result<ObservationOptions, BackendError> {
    match rules {
        Some(rules) => ObservationOptions::with_rules(definition, rules)
            .map_err(error("could not install observation filter")),
        None => Ok(ObservationOptions::all()),
    }
}

fn encode_pattern(pattern: &KorePattern) -> Result<Value, BackendError> {
    kore_codec::to_value(pattern).map_err(error("could not encode KORE JSON"))
}

fn trace_entry(entry: k_rust_backend::rewrite::TraceEntry) -> TraceEntry {
    TraceEntry {
        depth: entry.depth,
        kind: match entry.kind {
            TraceKind::Simplification => "simplification",
            TraceKind::Rewrite => "rewrite",
            TraceKind::Claim => "claim",
            TraceKind::Remainder => "remainder",
        }
        .into(),
        label: entry.label,
        unique_id: entry.unique_id,
    }
}

/// The published reason of a leaf and its detail: the reason in words, a predicate it names
/// printed at `sort`, the sort of the leaf's term. A consumer branches on the typed reason; the
/// detail is for a reader.
fn halt_reason(
    reason: &HaltReason,
    sort: &Sort,
) -> Result<(HaltReasonOutput, Option<String>), BackendError> {
    let detail = || Some(reason.at(sort).to_string());
    Ok(match reason {
        HaltReason::Stopped(cause) => return stopped_halt_reason(cause),
        HaltReason::Stuck => (HaltReasonOutput::Stuck, None),
        HaltReason::Trivial { .. } => (HaltReasonOutput::Trivial, None),
        HaltReason::Vacuous { .. } => (HaltReasonOutput::Vacuous, None),
        HaltReason::Branch { .. } => (HaltReasonOutput::Branch, detail()),
        HaltReason::CutPointRule { .. } => (HaltReasonOutput::CutPoint, detail()),
        HaltReason::TerminalRule { .. } => (HaltReasonOutput::Terminal, detail()),
        HaltReason::StopUndecided { .. } => (HaltReasonOutput::StopUndecided, detail()),
        HaltReason::ProbeDifference { .. } => (HaltReasonOutput::ProbeDifference, detail()),
        HaltReason::ProbeDone { .. } => (HaltReasonOutput::ProbeDone, detail()),
        HaltReason::DepthBound => (HaltReasonOutput::DepthBound, None),
        HaltReason::BreadthBound => (HaltReasonOutput::BreadthBound, None),
        HaltReason::WorkBound => (HaltReasonOutput::WorkBound, None),
        HaltReason::Indeterminate(_) => (HaltReasonOutput::Indeterminate, detail()),
        HaltReason::Simplification(error @ SimplificationError::UnsupportedHook { .. }) => {
            (HaltReasonOutput::UnsupportedHook, Some(error.to_string()))
        }
        HaltReason::Simplification(_) => (HaltReasonOutput::SimplificationError, detail()),
    })
}

/// The published reason of a leaf whose state stopped. A cancelled state is `cancelled`, a spent
/// bound of polls `poll-bound` (with the bound named in its detail) and a passed step deadline
/// `timeout`; an exhausted stack keeps the `simplification-error` kind the
/// failure it used to be spelled as had, with the stop as its detail and `stack-exhausted` as
/// its structured cause (`ExecutionLeaf::cause`). A failed solver prelude
/// leaves no answer of the operation meaningful, so it is the operation's error, not a leaf.
#[deny(clippy::wildcard_enum_match_arm)]
fn stopped_halt_reason(
    cause: &StopCause,
) -> Result<(HaltReasonOutput, Option<String>), BackendError> {
    match cause {
        StopCause::Cancelled => Ok((HaltReasonOutput::Cancelled, None)),
        StopCause::PollBound(_) => Ok((HaltReasonOutput::PollBound, Some(cause.to_string()))),
        StopCause::Deadline(_) => Ok((HaltReasonOutput::Timeout, Some(cause.to_string()))),
        StopCause::StackExhausted(_) => Ok((
            HaltReasonOutput::SimplificationError,
            Some(cause.to_string()),
        )),
        StopCause::SolverPrelude(_) => Err(BackendError::from(cause.clone())),
    }
}

fn condition_pattern(
    condition: &k_rust_backend::implication::ImplicationCondition,
    result_sort: &Sort,
) -> Result<Value, BackendError> {
    let top = || KorePattern::Top {
        sort: externalize::sort(result_sort),
    };
    let predicate = externalize::predicates_pattern(
        &condition.predicates,
        result_sort,
        |predicate| externalize::predicate_pattern(predicate, result_sort),
        externalize::ConjunctionShape::Flat,
    )
    .unwrap_or_else(top);
    let substitution = externalize::substitution_pattern(
        &condition.substitution,
        result_sort,
        externalize::BindingOrder::Container,
        externalize::ConjunctionShape::Flat,
    )
    .unwrap_or_else(top);
    let witnesses = externalize::substitution_pattern(
        &condition.witnesses,
        result_sort,
        externalize::BindingOrder::Container,
        externalize::ConjunctionShape::Flat,
    )
    .unwrap_or_else(top);
    Ok(serde_json::json!({
        "predicate": encode_pattern(&predicate)?,
        "substitution": encode_pattern(&substitution)?,
        "witnesses": encode_pattern(&witnesses)?,
    }))
}

#[cfg(feature = "z3-inference")]
fn model_substitution(substitution: &Substitution, result_sort: &Sort) -> Option<KorePattern> {
    externalize::substitution_pattern(
        substitution,
        result_sort,
        externalize::BindingOrder::Container,
        externalize::ConjunctionShape::Flat,
    )
}

fn implication_failure(failure: ImplicationFailure) -> ImplicationFailureOutput {
    match failure {
        ImplicationFailure::TermMismatch => ImplicationFailureOutput::TermMismatch,
        ImplicationFailure::PartialCoverage => ImplicationFailureOutput::PartialCoverage,
        ImplicationFailure::ConsequentCondition => ImplicationFailureOutput::ConsequentCondition,
    }
}

/// The published outcome of a proof leaf, with the words of its reason; a predicate they name is
/// printed at `sort`, the sort of the leaf's term. A cancelled request or a failed solver prelude
/// ends the proof without a leaf for the state it stopped, so neither is a leaf's outcome; named
/// on one, it is the operation's error.
#[deny(clippy::wildcard_enum_match_arm)]
pub fn proof_leaf_outcome(
    outcome: &ProofLeafOutcome,
    sort: &Sort,
) -> Result<(ProofLeafOutcomeOutput, Option<String>), BackendError> {
    Ok(match outcome {
        ProofLeafOutcome::Proven(_) => (ProofLeafOutcomeOutput::Proven, None),
        ProofLeafOutcome::Trusted => (ProofLeafOutcomeOutput::Trusted, None),
        ProofLeafOutcome::Stuck => (ProofLeafOutcomeOutput::Stuck, None),
        ProofLeafOutcome::Trivial => (ProofLeafOutcomeOutput::Trivial, None),
        ProofLeafOutcome::Vacuous => (ProofLeafOutcomeOutput::Vacuous, None),
        ProofLeafOutcome::DepthBound => (ProofLeafOutcomeOutput::DepthBound, None),
        ProofLeafOutcome::BreadthBound => (ProofLeafOutcomeOutput::BreadthBound, None),
        ProofLeafOutcome::Stopped(cause) => match cause {
            StopCause::Deadline(_) => (ProofLeafOutcomeOutput::Timeout, Some(cause.to_string())),
            StopCause::StackExhausted(_) => (
                ProofLeafOutcomeOutput::StackExhausted,
                Some(cause.to_string()),
            ),
            // A proof counts no bound of polls; were one to stop it, it would end the proof
            // as a cancellation does, with no leaf.
            StopCause::Cancelled | StopCause::PollBound(_) | StopCause::SolverPrelude(_) => {
                return Err(BackendError::from(cause.clone()));
            }
        },
        ProofLeafOutcome::Indeterminate(reason) => (
            ProofLeafOutcomeOutput::Indeterminate,
            Some(reason.at(sort).to_string()),
        ),
    })
}

fn proof_status(status: ProofStatus) -> &'static str {
    match status {
        ProofStatus::Proven => "proven",
        ProofStatus::Disproved => "disproved",
        ProofStatus::Failed => "failed",
        ProofStatus::Indeterminate => "indeterminate",
        ProofStatus::DepthBound => "depth-bound",
        ProofStatus::BreadthBound => "breadth-bound",
    }
}

/// Admit `pattern`, read from outside the definition, to internalization under `sort_variables`
/// as `admission` decides. A `Verified` admission runs the standalone verifier under the same
/// sort variables the witness carries to internalization, and reports its failure with the
/// verifier's message, naming the input as `what`.
fn admit<'a>(
    definition: &'a BackendDefinition,
    pattern: &'a KorePattern,
    sort_variables: &'a [Name],
    admission: Admission,
    what: &str,
) -> Result<Admitted<'a>, BackendError> {
    match admission {
        Admission::Verified => definition
            .verify_standalone_pattern(pattern, sort_variables)
            .map_err(|cause| BackendError::new(format!("invalid {what}: {cause}"))),
        Admission::Unverified => Ok(definition.admit_unverified(pattern, sort_variables)),
    }
}

/// The backend's chain of a request's `matchStates.chain`: each part's pattern internalized by
/// `match_target`, as the state-match pattern is, and each named variable as the term of its
/// own pattern, so that it is the variable of the parts it names. The chain is refused unless
/// [`ChainOptions::check`] accepts it.
fn chain_options(
    chain: &ChainRequest,
    match_target: &dyn Fn(
        &KorePattern,
        &'static str,
    ) -> Result<k_rust_backend::rewrite::Pattern, BackendError>,
) -> Result<CheckedChain, BackendError> {
    let variables = |variables: &[KoreVariable]| {
        variables
            .iter()
            .map(|variable| {
                let internalized = match_target(
                    &KorePattern::Variable(variable.clone()),
                    "could not internalize a chain variable",
                )?;
                match internalized.term.kind() {
                    k_rust_backend::term::TermKind::Variable(internal)
                        if internalized.constraints.is_empty() =>
                    {
                        Ok(internal.clone())
                    }
                    _ => Err(BackendError::new(format!(
                        "invalid matchStates.chain: the variable {} does not internalize as an element variable",
                        variable.name
                    ))),
                }
            })
            .collect::<Result<Vec<_>, BackendError>>()
    };
    let steps = chain
        .steps
        .iter()
        .map(|step| {
            Ok(ChainStep {
                target: match_target(
                    &step.pattern,
                    "could not internalize a chain step's pattern",
                )?,
                imports: variables(&step.imports)?,
                exports: variables(&step.exports)?,
                unless: step
                    .unless
                    .as_ref()
                    .map(|unless| {
                        Ok::<_, BackendError>(UnlessPart {
                            target: match_target(
                                &unless.pattern,
                                "could not internalize a chain unless's pattern",
                            )?,
                            imports: variables(&unless.imports)?,
                        })
                    })
                    .transpose()?,
            })
        })
        .collect::<Result<Vec<_>, BackendError>>()?;
    ChainOptions {
        steps,
        partial_cap: chain.partial_cap,
    }
    .checked()
    .map_err(|invalid| BackendError::new(format!("invalid matchStates.chain: {invalid}")))
}

fn error<E: fmt::Display>(context: &'static str) -> impl FnOnce(E) -> BackendError {
    move |cause| BackendError::new(format!("{context}: {cause}"))
}

/// [`error`], of `kind` ([`BackendError::kind`]).
fn kinded<E: fmt::Display>(
    context: &'static str,
    kind: BackendErrorKind,
) -> impl FnOnce(E) -> BackendError {
    move |cause| BackendError::of_kind(kind, format!("{context}: {cause}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kore::{parser::parse_pattern, printer::Printer};
    use std::collections::BTreeSet;

    /// `counter_erased` replaces the content of the top `<generatedCounter>` cell with 0, so two
    /// configurations that differ only there have one erasure, and leaves every other pattern,
    /// a counter that is not the top cell's last argument included, as it is.
    #[test]
    fn the_counter_erasure_identifies_configurations_only_up_to_the_counter() {
        let config = |a: &str, counter: &str| {
            parse_pattern(&format!(
                r#"Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'a'-GT-'{{}}(\dv{{SortInt{{}}}}("{a}")), Lbl'-LT-'generatedCounter'-GT-'{{}}({counter}))"#
            ))
            .unwrap()
        };
        let zero = config("3", r#"\dv{SortInt{}}("0")"#);
        let seven = config("3", r#"\dv{SortInt{}}("7")"#);
        assert_eq!(*counter_erased(&seven), zero);
        assert!(matches!(
            counter_erased(&zero),
            std::borrow::Cow::Borrowed(_)
        ));
        assert_eq!(*counter_erased(&config("3", "X:SortInt{}")), zero);
        assert_ne!(
            *counter_erased(&config("4", r#"\dv{SortInt{}}("7")"#)),
            zero
        );
        for unchanged in [
            r#"Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("5")), Lbl'-LT-'a'-GT-'{}(\dv{SortInt{}}("3")))"#,
            r#"Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("5")))"#,
            r#"\dv{SortInt{}}("5")"#,
        ] {
            let pattern = parse_pattern(unchanged).unwrap();
            assert!(
                matches!(counter_erased(&pattern), std::borrow::Cow::Borrowed(same) if *same == pattern),
                "{unchanged}"
            );
        }
    }

    /// The wire's budget is the default units when it names none, a clock when it names only
    /// `smtTimeoutMs`, those units when it names only `smtResourceLimit` (positive: 0, Z3's "no
    /// limit", is refused rather than read as unbounded), and refused when it names both.
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the expected budget of the wire's `smtTimeoutMs`"
    )]
    fn the_wire_budget_is_units_unless_it_names_a_clock_alone() {
        let read = |text: &str| serde_json::from_str::<BackendOptions>(text);
        assert_eq!(read("{}").unwrap(), BackendOptions::DEFAULT);
        assert_eq!(BackendOptions::default(), BackendOptions::DEFAULT);
        assert_eq!(
            BackendOptions::DEFAULT.smt_budget,
            SmtBudget::Units(DEFAULT_SMT_RESOURCE_LIMIT)
        );
        assert_eq!(BackendOptions::DEFAULT.smt_retry_limit, 3);
        assert_eq!(
            read(r#"{"smtResourceLimit": 250000}"#).unwrap(),
            BackendOptions {
                smt_budget: SmtBudget::Units(std::num::NonZeroU32::new(250_000).unwrap()),
                smt_retry_limit: 3,
            }
        );
        assert_eq!(
            read(r#"{"smtTimeoutMs": 40, "smtRetryLimit": 1}"#).unwrap(),
            BackendOptions {
                smt_budget: SmtBudget::clock(40),
                smt_retry_limit: 1,
            }
        );
        let both = read(r#"{"smtTimeoutMs": 40, "smtResourceLimit": 250000}"#).unwrap_err();
        assert!(both.to_string().contains("not both"), "{both}");
        assert!(read(r#"{"smtResourceLimit": 0}"#).is_err());
        assert_eq!(z3_version().is_some(), cfg!(feature = "z3-inference"));
        // The bindings' fields read as the wire's.
        assert_eq!(
            BackendOptions::requested(None, None, None),
            Ok(BackendOptions::DEFAULT)
        );
        assert_eq!(
            BackendOptions::requested(Some(40), None, Some(1)),
            read(r#"{"smtTimeoutMs": 40, "smtRetryLimit": 1}"#).map_err(|e| e.to_string())
        );
        assert_eq!(
            BackendOptions::requested(None, Some(250_000), None),
            read(r#"{"smtResourceLimit": 250000}"#).map_err(|e| e.to_string())
        );
        assert!(BackendOptions::requested(Some(40), Some(9), None).is_err());
        assert!(BackendOptions::requested(None, Some(0), None).is_err());
    }

    /// The solver record names the mode and its one bound, the retries and, in a build with Z3,
    /// the build; it serializes in the order of its members' names, without the absent bound.
    #[test]
    #[expect(clippy::disallowed_methods, reason = "the record of a clocked solver")]
    fn the_solver_record_names_the_mode_and_its_bound() {
        let units = SolverReport::of(BackendOptions::DEFAULT);
        assert_eq!(
            (
                units.mode.as_str(),
                units.units,
                units.clock_ms,
                units.retries
            ),
            ("resource", Some(DEFAULT_SMT_RESOURCE_LIMIT.get()), None, 3)
        );
        assert_eq!(units.z3.is_some(), z3_build().is_some());
        let clock = SolverReport::of(BackendOptions {
            smt_budget: SmtBudget::clock(40),
            smt_retry_limit: 1,
        });
        assert_eq!(
            (
                clock.mode.as_str(),
                clock.units,
                clock.clock_ms,
                clock.retries
            ),
            ("clock", None, Some(40), 1)
        );
        let text = serde_json::to_string(&SolverReport { z3: None, ..units }).unwrap();
        assert_eq!(text, r#"{"mode":"resource","retries":3,"units":370000}"#);
    }

    /// The default options are the backend crate's own default solver options.
    #[test]
    fn the_default_options_are_the_solvers_default() {
        #[cfg(feature = "z3-inference")]
        assert_eq!(
            Z3Options {
                budget: BackendOptions::DEFAULT.smt_budget,
                retry_limit: BackendOptions::DEFAULT.smt_retry_limit,
            },
            Z3Options::DEFAULT
        );
    }

    /// A Z3 build names its version and the digest of its library file: on Linux whenever Z3 is
    /// linked dynamically or the build named its static archive, which it does for the published
    /// x86-64 Linux asset; a build without Z3 has none.
    #[test]
    fn the_z3_build_names_its_library() {
        let Some(build) = z3_build() else {
            assert!(z3_version().is_none());
            return;
        };
        assert_eq!(Some(build.version), z3_version());
        let named_statically = !Z3_ARCHIVE_SHA256.is_empty();
        if cfg!(target_os = "linux") && (named_statically || cfg!(target_arch = "x86_64")) {
            let digest = build.library_sha256.as_deref().expect("a named Z3 library");
            assert_eq!(digest.len(), 64);
            assert!(
                digest
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            );
        }
        assert!(std::ptr::eq(build, z3_build().unwrap()));
        assert!(names_release("Z3 4.16.0.0", "4.16.0") && names_release("4.12.5.0", "4.12.5"));
        assert!(!names_release("Z3 4.16.10.0", "4.16.1") && !names_release("Z3 4.16.0.0", ""));
        assert!(names_release(
            "5.3.3.0 430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e 430d19e",
            "5.3.3"
        ));
    }

    /// The wire spellings of `all`, each read back as its value, as a set of distinct names.
    fn wire_names<T>(all: &[T]) -> BTreeSet<String>
    where
        T: Serialize + serde::de::DeserializeOwned + PartialEq + fmt::Debug,
    {
        let names: BTreeSet<String> = all
            .iter()
            .map(|value| {
                let spelling = serde_json::to_string(value).unwrap();
                assert_eq!(&serde_json::from_str::<T>(&spelling).unwrap(), value);
                serde_json::from_str::<String>(&spelling).unwrap()
            })
            .collect();
        assert_eq!(names.len(), all.len());
        names
    }

    /// Assert that each package's TypeScript declaration of `interface` spells `field` as the
    /// union of `expected`, one `| 'name'` line each.
    fn assert_typescript_union(interface: &str, field: &str, expected: &BTreeSet<String>) {
        for package in ["k-rust-napi", "k-rust-wasm"] {
            let path = format!(
                "{}/../{package}/typescript/index.ts",
                env!("CARGO_MANIFEST_DIR")
            );
            let declaration = std::fs::read_to_string(&path).unwrap();
            let body = declaration
                .split_once(&format!("export interface {interface} {{"))
                .unwrap()
                .1;
            let union = body.split_once(&format!("  {field}:\n")).unwrap().1;
            let actual: BTreeSet<String> = union
                .lines()
                .take_while(|line| line.trim_start().starts_with('|'))
                .map(|line| {
                    line.trim()
                        .trim_start_matches('|')
                        .trim()
                        .trim_matches('\'')
                        .to_string()
                })
                .collect();
            assert_eq!(&actual, expected, "{path} {interface}.{field}");
        }
    }

    /// Each package's TypeScript declaration of `interface` has the member line `member`.
    fn assert_typescript_member(interface: &str, member: &str) {
        for package in ["k-rust-napi", "k-rust-wasm"] {
            let path = format!(
                "{}/../{package}/typescript/index.ts",
                env!("CARGO_MANIFEST_DIR")
            );
            let declaration = std::fs::read_to_string(&path).unwrap();
            let body = declaration
                .split_once(&format!("export interface {interface} {{\n"))
                .unwrap()
                .1;
            let body = body.split_once("\n}\n").unwrap().0;
            assert!(
                body.lines().any(|line| line == format!("  {member}")),
                "{path} {interface} lacks `{member}`"
            );
        }
    }

    /// The undecided-answer count is declared where the facade writes it: an optional number on
    /// the execution result (absent at zero) and a capability flag, true in every build.
    #[test]
    fn the_undecided_answer_count_matches_typescript_declarations() {
        assert_typescript_member("ExecutionResult", "smtUnknowns?: number");
        assert_typescript_member("BackendCapabilities", "smtUnknowns: boolean");
        let backend = Backend::new(
            r#"[] module MAIN sort SortK{} [] endmodule []"#,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["smtUnknowns"], true);
        assert_eq!(capabilities["stackStops"], true);
    }

    /// The bound of polls is declared where the facade reads and writes it: the optional request
    /// field, the count every execution result carries, and a capability flag, true in every
    /// build.
    #[test]
    fn the_poll_bound_matches_typescript_declarations() {
        assert_typescript_member("ExecuteOptions", "maxPolls?: number");
        assert_typescript_member("ExecutionResult", "polls: number");
        assert_typescript_member("BackendCapabilities", "pollBound: boolean");
        let backend = Backend::new(
            r#"[] module MAIN sort SortK{} [] endmodule []"#,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["pollBound"], true);
    }

    /// The offered level of run coverage is declared where the facade reads and writes it: the
    /// request flag, the optional list of the coverage, and a capability flag, true in every
    /// build.
    #[test]
    fn the_offered_coverage_matches_typescript_declarations() {
        assert_typescript_member("ExecuteOptions", "collectOffered?: boolean");
        assert_typescript_member("RunCoverage", "offered?: string[]");
        assert_typescript_member("BackendCapabilities", "coverageOffered: boolean");
        let backend = Backend::new(
            r#"[] module MAIN sort SortK{} [] endmodule []"#,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["coverageOffered"], true);
    }

    /// The applied counts of run coverage are declared where the facade reads and writes them:
    /// the request flag, the optional map of the coverage, and a capability flag, true in every
    /// build.
    #[test]
    fn the_applied_counts_match_typescript_declarations() {
        assert_typescript_member("ExecuteOptions", "collectCounts?: boolean");
        assert_typescript_member("RunCoverage", "appliedCounts?: Record<string, number>");
        assert_typescript_member("BackendCapabilities", "coverageCounts: boolean");
        let backend = Backend::new(
            r#"[] module MAIN sort SortK{} [] endmodule []"#,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["coverageCounts"], true);
    }

    /// Syntax paths are declared where the facade reads and writes them: the collection's depth,
    /// the bindings' paths and a capability flag, true in every build; a collection without a
    /// depth writes no `depth` and reads back without one.
    #[test]
    fn the_syntax_paths_match_typescript_declarations() {
        assert_typescript_member("BindingCollection", "depth?: number");
        assert_typescript_member(
            "RunBindings",
            "paths?: { axiom: string; paths: { symbols: string[]; positions: number[] }[] }[]",
        );
        assert_typescript_member("BackendCapabilities", "coverageBindingPaths: boolean");
        let backend = Backend::new(
            r#"[] module MAIN sort SortK{} [] endmodule []"#,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["coverageBindingPaths"], true);
        let collection = BindingCollection::new(["LblA"]);
        assert_eq!(
            serde_json::to_value(&collection).unwrap(),
            serde_json::json!({"symbols": ["LblA"], "binders": []})
        );
        let deep: BindingCollection =
            serde_json::from_value(serde_json::json!({"symbols": ["LblA"], "depth": 2})).unwrap();
        assert_eq!(deep.depth, std::num::NonZeroUsize::new(2));
    }

    /// Order-free guard outcomes are declared where the facade writes them: the guard outcome
    /// `undecided-untried`, one line of each package's `GuardOutcome` union, and a capability
    /// flag, true in every build.
    #[test]
    fn the_untried_guard_outcome_matches_typescript_declarations() {
        assert_typescript_member("BackendCapabilities", "coverageGuardsUntried: boolean");
        assert_eq!(
            wire_names(&[GuardOutcomeOutput::UndecidedUntried]),
            BTreeSet::from(["undecided-untried".to_owned()])
        );
        for package in ["k-rust-napi", "k-rust-wasm"] {
            let path = format!(
                "{}/../{package}/typescript/index.ts",
                env!("CARGO_MANIFEST_DIR")
            );
            let declaration = std::fs::read_to_string(&path).unwrap();
            let union = declaration
                .split_once("export type GuardOutcome =\n")
                .unwrap()
                .1
                .split_once("\n\n")
                .unwrap()
                .0;
            assert!(
                union.lines().any(|line| line == "  | 'undecided-untried'"),
                "{path}"
            );
        }
        let backend = Backend::new(
            r#"[] module MAIN sort SortK{} [] endmodule []"#,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["coverageGuardsUntried"], true);
    }

    /// Rule windows are declared where the facade reads and writes them: the request's option,
    /// the coverage's list and a capability flag, true in every build.
    #[test]
    fn the_rule_windows_match_typescript_declarations() {
        assert_typescript_member("ExecuteOptions", "collectWindows?: number");
        assert_typescript_member("RunCoverage", "windows?: string[][]");
        assert_typescript_member("BackendCapabilities", "coverageWindows: boolean");
        let backend = Backend::new(
            r#"[] module MAIN sort SortK{} [] endmodule []"#,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["coverageWindows"], true);
    }

    /// State matches and committed transitions are declared where the facade reads and writes
    /// them: the request's options, the result's summary and the coverage's list, the summary's
    /// types and reasons, and two capability flags, true in every build.
    #[test]
    fn the_state_matches_match_typescript_declarations() {
        assert_typescript_member("ExecuteOptions", "matchStates?: StateMatchRequest");
        assert_typescript_member("ExecuteOptions", "collectCommitted?: boolean");
        assert_typescript_member("StateMatchRequest", "pattern: Kore");
        assert_typescript_member("StateMatchRequest", "proofAgreement?: boolean");
        assert_typescript_member("ExecutionResult", "stateMatches?: StateMatches");
        assert_typescript_member("RunCoverage", "committed?: string[]");
        assert_typescript_member("StateMatches", "firstCleanReach?: StateMatch");
        assert_typescript_member("StateMatches", "firstDirtyReach?: StateMatch");
        assert_typescript_member("StateMatches", "dirtyReaches?: number");
        assert_typescript_member("StateMatches", "undecided?: UndecidedStateMatches[]");
        assert_typescript_member("StateMatches", "matched: number");
        assert_typescript_member("StateMatches", "refuted: number");
        assert_typescript_member("StateMatches", "smtUnknowns?: number");
        assert_typescript_member("StateMatches", "stackStops?: number");
        assert_typescript_member("StateMatch", "depth: number");
        assert_typescript_member("StateMatch", "state: Kore");
        assert_typescript_member("StateMatch", "diagnostics?: BackendDiagnostic[]");
        assert_typescript_member("StateMatch", "termConjunction?: boolean");
        assert_typescript_member("UndecidedStateMatches", "reason: UndecidedMatchReason");
        assert_typescript_member("UndecidedStateMatches", "count: number");
        assert_typescript_member("UndecidedStateMatches", "first: StateMatch");
        assert_typescript_member("StateMatchRequest", "chain?: ChainRequest");
        assert_typescript_member("ChainRequest", "steps: ChainStepRequest[]");
        assert_typescript_member("ChainRequest", "partialCap: number");
        assert_typescript_member("ChainStepRequest", "pattern: Kore");
        assert_typescript_member("ChainStepRequest", "imports?: Kore[]");
        assert_typescript_member("ChainStepRequest", "exports?: Kore[]");
        assert_typescript_member("ChainStepRequest", "unless?: UnlessRequest");
        assert_typescript_member("UnlessRequest", "pattern: Kore");
        assert_typescript_member("UnlessRequest", "imports?: Kore[]");
        assert_typescript_member("StateMatches", "chain?: ChainMatches");
        assert_typescript_member("ChainMatches", "firstCleanCompletion?: ChainCompletion");
        assert_typescript_member("ChainMatches", "firstDirtyCompletion?: ChainCompletion");
        assert_typescript_member("ChainMatches", "dirtyCompletions?: number");
        assert_typescript_member("ChainMatches", "undecided?: ChainUndecided[]");
        assert_typescript_member("ChainMatches", "overflowedPaths?: number");
        assert_typescript_member("ChainMatches", "peakPartials: number");
        assert_typescript_member("ChainMatches", "states: number");
        assert_typescript_member("ChainMatches", "evaluations: number");
        assert_typescript_member("ChainMatches", "smtUnknowns?: number");
        assert_typescript_member("ChainMatches", "stackStops?: number");
        assert_typescript_member("ChainCompletion", "steps: ChainStepMatch[]");
        assert_typescript_member("ChainCompletion", "diagnostics?: BackendDiagnostic[]");
        assert_typescript_member("ChainCompletion", "termConjunction?: boolean");
        assert_typescript_member("ChainStepMatch", "step: number");
        assert_typescript_member("ChainStepMatch", "depth: number");
        assert_typescript_member("ChainStepMatch", "state: Kore");
        assert_typescript_member("ChainStepMatch", "bindings?: BackendBinding[]");
        assert_typescript_member("ChainUndecided", "part: ChainPart");
        assert_typescript_member("ChainUndecided", "step: number");
        assert_typescript_member("ChainUndecided", "reason: UndecidedMatchReason");
        assert_typescript_member("ChainUndecided", "count: number");
        assert_typescript_member("ChainUndecided", "first: StateMatch");
        assert_typescript_member("ChainUndecided", "bindings?: BackendBinding[]");
        assert_typescript_member("BackendCapabilities", "coverageCommitted: boolean");
        assert_typescript_member("BackendCapabilities", "stateMatches: boolean");
        for package in ["k-rust-napi", "k-rust-wasm"] {
            let path = format!(
                "{}/../{package}/typescript/index.ts",
                env!("CARGO_MANIFEST_DIR")
            );
            let declaration = std::fs::read_to_string(&path).unwrap();
            for reason in [
                UndecidedMatchReasonOutput::UndecidedState,
                UndecidedMatchReasonOutput::NotCeilFree,
                UndecidedMatchReasonOutput::UndecidedMatch,
                UndecidedMatchReasonOutput::PlacementBound,
            ] {
                let spelling = serde_json::to_value(reason).unwrap();
                let quoted = format!("'{}'", spelling.as_str().unwrap());
                assert!(declaration.contains(&quoted), "{path} lacks {quoted}");
            }
        }
        let backend = Backend::new(
            r#"[] module MAIN sort SortK{} [] endmodule []"#,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["coverageCommitted"], true);
        assert_eq!(capabilities["stateMatches"], true);
    }

    /// The condition records of run coverage are declared where the facade reads and writes
    /// them: the request's collection, the optional list of the coverage, the record types, and
    /// a capability flag, true in every build.
    #[test]
    fn the_condition_records_match_typescript_declarations() {
        assert_typescript_member("ExecuteOptions", "collectConditions?: ConditionCollection");
        assert_typescript_member("RunCoverage", "conditions?: RuleConditions[]");
        assert_typescript_member("ConditionCollection", "rules: string[]");
        assert_typescript_member("ConditionCollection", "limit?: number");
        assert_typescript_member("ConditionCollection", "maxValueSize?: number");
        assert_typescript_member("ConditionCollection", "recordPolls?: number");
        assert_typescript_member("RuleConditions", "rule: string");
        assert_typescript_member("RuleConditions", "records: ConditionRecord[]");
        assert_typescript_member("RuleConditions", "truncated?: boolean");
        assert_typescript_member("ConditionRecord", "bindings: RecordedBinding[]");
        assert_typescript_member("ConditionRecord", "condition: ConditionNode[]");
        assert_typescript_member("ConditionRecord", "verdict?: ConditionVerdict");
        assert_typescript_member("ConditionRecord", "chosen?: boolean");
        assert_typescript_member("RecordedBinding", "variable: Kore");
        assert_typescript_member("RecordedBinding", "value: RecordedValue");
        assert_typescript_member("ConditionAtom", "head?: string");
        assert_typescript_member("ConditionAtom", "hook?: string");
        assert_typescript_member("ConditionAtom", "operands: RecordedValue[]");
        assert_typescript_member("ConditionAtom", "reads?: number[]");
        assert_typescript_member("ConditionAtom", "value: ConditionTruth");
        assert_typescript_member("BackendCapabilities", "coverageConditions: boolean");
        // Every wire spelling of the unions is declared in both packages.
        for package in ["k-rust-napi", "k-rust-wasm"] {
            let path = format!(
                "{}/../{package}/typescript/index.ts",
                env!("CARGO_MANIFEST_DIR")
            );
            let declaration = std::fs::read_to_string(&path).unwrap();
            let spellings = |values: Vec<serde_json::Value>| {
                values
                    .into_iter()
                    .map(|value| value.as_str().unwrap().to_owned())
                    .collect::<Vec<_>>()
            };
            let verdicts = spellings(
                [
                    VerdictOutput::Held,
                    VerdictOutput::Refuted,
                    VerdictOutput::Undecided,
                    VerdictOutput::Stopped,
                    VerdictOutput::Reentered,
                ]
                .map(|verdict| serde_json::to_value(verdict).unwrap())
                .to_vec(),
            );
            let truths = spellings(
                [
                    TruthOutput::True,
                    TruthOutput::False,
                    TruthOutput::Undefined,
                    TruthOutput::Undecided,
                ]
                .map(|truth| serde_json::to_value(truth).unwrap())
                .to_vec(),
            );
            let connectives = spellings(
                [
                    ConnectiveOutput::NotBool,
                    ConnectiveOutput::AndBool,
                    ConnectiveOutput::AndThenBool,
                    ConnectiveOutput::OrBool,
                    ConnectiveOutput::OrElseBool,
                    ConnectiveOutput::ImpliesBool,
                    ConnectiveOutput::XorBool,
                    ConnectiveOutput::Not,
                    ConnectiveOutput::And,
                    ConnectiveOutput::Or,
                    ConnectiveOutput::Implies,
                    ConnectiveOutput::Iff,
                ]
                .map(|connective| serde_json::to_value(connective).unwrap())
                .to_vec(),
            );
            for spelling in verdicts.iter().chain(&truths).chain(&connectives) {
                let quoted = format!("'{}'", spelling.replace('\\', "\\\\"));
                assert!(declaration.contains(&quoted), "{path} lacks {quoted}");
            }
            for kind in [
                "value",
                "unevaluated",
                "symbolic",
                "undefined",
                "stopped",
                "omitted",
            ] {
                assert!(
                    declaration.contains(&format!("'{kind}'")),
                    "{path} lacks {kind}"
                );
            }
        }
        let backend = Backend::new(
            r#"[] module MAIN sort SortK{} [] endmodule []"#,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["coverageConditions"], true);
        // The wire tags of a recorded value and of a condition node.
        let value: RecordedValueOutput = serde_json::from_value(serde_json::json!({
            "kind": "unevaluated",
            "term": {"format": "KORE", "version": 1, "term": null},
        }))
        .unwrap();
        assert!(matches!(value, RecordedValueOutput::Unevaluated { .. }));
        for kind in ["undefined", "stopped", "omitted"] {
            let value: RecordedValueOutput =
                serde_json::from_value(serde_json::json!({ "kind": kind })).unwrap();
            assert_eq!(serde_json::to_value(&value).unwrap()["kind"], kind);
        }
        let node: ConditionNodeOutput = serde_json::from_value(serde_json::json!({
            "node": "connective",
            "connective": "\\implies",
            "children": [
                {"node": "equals", "literal": false, "value": "true", "child": {
                    "node": "atom", "operands": [], "value": "false",
                }},
                {"node": "connective", "connective": "notBool", "children": [], "value": "undefined"},
            ],
            "value": "undecided",
        }))
        .unwrap();
        assert!(matches!(
            node,
            ConditionNodeOutput::Connective {
                connective: ConnectiveOutput::Implies,
                value: TruthOutput::Undecided,
                ..
            }
        ));
    }

    /// The run-level records are declared where the facade writes them: the optional lists of
    /// the execution result and of the four search responses, the record types with where each
    /// record was observed, and three capability flags, true in every build.
    #[test]
    fn the_run_level_records_match_typescript_declarations() {
        for result in [
            "ExecutionResult",
            "SearchResult",
            "PathSearchResult",
            "PatternSearchResult",
            "PathPatternSearchResult",
        ] {
            assert_typescript_member(result, "contradictedClaims?: ContradictedClaim[]");
            assert_typescript_member(result, "allowanceRefusals?: UnevaluatedHook[]");
            assert_typescript_member(result, "unsupportedHooks?: UnevaluatedHook[]");
            assert_typescript_member(result, "shortCircuitReadings?: ShortCircuitReading[]");
        }
        for capability in [
            "contradictedClaims",
            "allowanceRefusals",
            "unsupportedHooks",
            "shortCircuitReadings",
        ] {
            assert_typescript_member("BackendCapabilities", &format!("{capability}: boolean"));
        }
        for member in [
            "operator?: string",
            "outcome: 'undefined' | 'undecided'",
            "head?: string",
            "operand: Kore",
            "rewriteRuleId?: string",
            "rewriteRuleLabel?: string",
            "rewriteRuleOrigin?: RuleOrigin",
            "observedIn: ObservedIn",
        ] {
            assert_typescript_member("ShortCircuitReading", member);
        }
        for member in [
            "ruleId: string",
            "ruleLabel?: string",
            "origin?: RuleOrigin",
            "application: Kore",
            "undefined: Kore",
            "rewriteRuleId?: string",
            "rewriteRuleLabel?: string",
            "rewriteRuleOrigin?: RuleOrigin",
            "ground: boolean",
            "observedIn: ObservedIn",
        ] {
            assert_typescript_member("ContradictedClaimFields", member);
        }
        assert_typescript_member("ExecutionResult", "passedStops?: PassedStop[]");
        assert_typescript_member("BackendCapabilities", "passedStops: boolean");
        assert_typescript_member("PassedStop", "rule: string");
        assert_typescript_member("PassedStop", "depth: number");
        assert_typescript_member("UnevaluatedHook", "hook: string");
        assert_typescript_member("UnevaluatedHook", "reason: string");
        assert_typescript_member("UnevaluatedHook", "observedIn: ObservedIn");
        let backend = Backend::new(
            r#"[] module MAIN sort SortK{} [] endmodule []"#,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        for capability in [
            "contradictedClaims",
            "allowanceRefusals",
            "unsupportedHooks",
            "shortCircuitReadings",
            "passedStops",
        ] {
            assert_eq!(capabilities[capability], true, "{capability}");
        }
        let value = serde_json::json!({"hook": "BYTES.padRight", "reason": "too long", "observedIn": "load"});
        let output: UnevaluatedHookOutput = serde_json::from_value(value.clone()).unwrap();
        assert_eq!(serde_json::to_value(&output).unwrap(), value);
        // A reading round-trips, its optional fields absent when unset.
        for value in [
            serde_json::json!({
                "operator": "BOOL.andThen",
                "outcome": "undefined",
                "head": "Lbl'Unds'divInt'Unds'",
                "operand": {"tag": "EVar", "name": "X", "sort": {"tag": "SortApp", "name": "SortInt", "args": []}},
                "rewriteRuleId": "r",
                "rewriteRuleLabel": "MAIN.r",
                "observedIn": "run",
            }),
            serde_json::json!({
                "outcome": "undecided",
                "operand": {"tag": "EVar", "name": "X", "sort": {"tag": "SortApp", "name": "SortInt", "args": []}},
                "observedIn": "load",
            }),
        ] {
            let output: ShortCircuitReadingOutput = serde_json::from_value(value.clone()).unwrap();
            assert_eq!(serde_json::to_value(&output).unwrap(), value);
        }
    }

    /// The marks of open values are declared where the facade writes them: the result's optional
    /// list of `{hook, class}`, the class names, and a capability flag, true in every build.
    #[test]
    fn the_implementation_chosen_values_match_typescript_declarations() {
        use k_rust_backend::builtin::ChosenClass;
        for interface in [
            "ExecutionResult",
            "SearchResult",
            "PathSearchResult",
            "PatternSearchResult",
            "PathPatternSearchResult",
        ] {
            assert_typescript_member(interface, "implementationChosenValues?: ChosenValue[]");
        }
        assert_typescript_member("BackendCapabilities", "implementationChosenValues: boolean");
        assert_typescript_member("ChosenValue", "hook: string");
        assert_typescript_member("ChosenValue", "class: ChosenClass");
        let classes = [
            ChosenClass::Order,
            ChosenClass::Item,
            ChosenClass::FloatDestination,
            ChosenClass::NanSign,
            ChosenClass::LetterCase,
            ChosenClass::SignedZero,
            ChosenClass::FreshName,
            ChosenClass::EffectOrder,
            ChosenClass::FreshAssociation,
            ChosenClass::FloatRounding,
            ChosenClass::OutsideDomain,
            ChosenClass::Literal,
        ]
        .map(|class| class.name().to_owned())
        .into_iter()
        .collect::<BTreeSet<_>>();
        for package in ["k-rust-napi", "k-rust-wasm"] {
            let path = format!(
                "{}/../{package}/typescript/index.ts",
                env!("CARGO_MANIFEST_DIR")
            );
            let declaration = std::fs::read_to_string(&path).unwrap();
            let union = declaration
                .split_once("export type ChosenClass =\n")
                .unwrap()
                .1;
            let declared: BTreeSet<String> = union
                .lines()
                .take_while(|line| line.trim_start().starts_with('|'))
                .map(|line| {
                    line.trim()
                        .trim_start_matches('|')
                        .trim()
                        .trim_matches('\'')
                        .to_owned()
                })
                .collect();
            assert_eq!(declared, classes, "{path} ChosenClass");
        }
        let backend = Backend::new(
            r#"[] module MAIN sort SortK{} [] endmodule []"#,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["implementationChosenValues"], true);
        let value = serde_json::json!({"hook": "MAP.choice", "class": "item"});
        let output: ChosenValueOutput = serde_json::from_value(value.clone()).unwrap();
        assert_eq!(serde_json::to_value(&output).unwrap(), value);
    }

    #[test]
    fn execution_halt_reasons_match_typescript_declarations() {
        assert_typescript_union(
            "ExecutionLeaf",
            "reason",
            &wire_names(&HaltReasonOutput::ALL),
        );
    }

    #[test]
    fn implication_failures_match_typescript_declarations() {
        assert_typescript_union(
            "ImplicationResult",
            "failure?",
            &wire_names(&ImplicationFailureOutput::ALL),
        );
    }

    #[test]
    fn proof_leaf_outcomes_match_typescript_declarations() {
        assert_typescript_union(
            "ProofLeaf",
            "outcome",
            &wire_names(&ProofLeafOutcomeOutput::ALL),
        );
    }

    /// `krust kprove` prints a leaf's outcome by `name`, so its reader and a host reading the
    /// wire see the same word.
    #[test]
    fn a_proof_leaf_outcome_is_named_as_the_wire_spells_it() {
        for outcome in ProofLeafOutcomeOutput::ALL {
            assert_eq!(
                serde_json::to_value(outcome).unwrap(),
                serde_json::Value::from(outcome.name())
            );
        }
    }

    const DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            sort SortT{} []
            symbol a{}() : SortS{} [constructor{}()]
            symbol b{}() : SortS{} [constructor{}()]
            symbol c{}() : SortS{} [constructor{}()]
            symbol t{}() : SortT{} [constructor{}()]
            symbol macroValue{}() : SortS{} [constructor{}(), macro{}()]
            alias weakExistsFinally{S}(S) : S
                where weakExistsFinally{S}(@X:S) := @X:S []
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()),
                \and{SortS{}}(b{}(), \top{SortS{}}())
            ) [label{}("a-to-b")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(b{}(), \top{SortS{}}()),
                \and{SortS{}}(c{}(), \top{SortS{}}())
            ) [label{}("b-to-c")]
            claim{} \implies{SortS{}}(
                \and{SortS{}}(\top{SortS{}}(), a{}()),
                weakExistsFinally{SortS{}}(
                    \and{SortS{}}(c{}(), \top{SortS{}}())
                )
            ) [label{}("reaches-c")]
        endmodule []"#;

    const DIAMOND_DEFINITION: &str = r#"[]
        module DIAMOND
            sort SortS{} []
            symbol initial{}() : SortS{} [constructor{}()]
            symbol left{}() : SortS{} [constructor{}()]
            symbol right{}() : SortS{} [constructor{}()]
            symbol merged{}() : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(initial{}(), \top{SortS{}}()), left{}()
            ) [label{}("initial-left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(initial{}(), \top{SortS{}}()), right{}()
            ) [label{}("initial-right")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(left{}(), \top{SortS{}}()), merged{}()
            ) [label{}("left-merged")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(right{}(), \top{SortS{}}()), merged{}()
            ) [label{}("right-merged")]
        endmodule []"#;

    const LOG_DEFINITION: &str = r#"[]
        module MAIN
            sort SortString{} [hasDomainValues{}()]
            sort SortK{} []
            symbol dotk{}() : SortK{} [constructor{}()]
            hooked-symbol log{}(SortString{}) : SortK{}
                [function{}(), total{}(), hook{}("IO.logString")]
        endmodule []"#;

    const EFFECTFUL_BRANCH_DEFINITION: &str = r#"[]
        module MAIN
            sort SortString{} [hasDomainValues{}()]
            sort SortK{} []
            sort SortState{} []
            symbol initial{}() : SortState{} [constructor{}()]
            symbol left{}(SortK{}) : SortState{} [constructor{}()]
            symbol right{}(SortK{}) : SortState{} [constructor{}()]
            symbol dotk{}() : SortK{} [constructor{}()]
            hooked-symbol log{}(SortString{}) : SortK{}
                [function{}(), hook{}("IO.logString")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()),
                left{}(log{}(\dv{SortString{}}("left")))
            ) [label{}("left")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()),
                right{}(log{}(\dv{SortString{}}("right")))
            ) [label{}("right")]
        endmodule []"#;

    const OBSERVATION_ERASURE_DEFINITION: &str = r#"[]
        module MAIN
            sort SortString{} [hasDomainValues{}()]
            sort SortK{} []
            sort SortState{} []
            symbol initial{}() : SortState{} [constructor{}()]
            symbol left{}(SortK{}) : SortState{} [constructor{}()]
            symbol right{}(SortK{}) : SortState{} [constructor{}()]
            symbol merged{}() : SortState{} [constructor{}()]
            symbol dotk{}() : SortK{} [constructor{}()]
            hooked-symbol log{}(SortString{}) : SortK{}
                [function{}(), hook{}("IO.logString")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()),
                left{}(log{}(\dv{SortString{}}("same")))
            ) [label{}("left")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()),
                right{}(log{}(\dv{SortString{}}("same")))
            ) [label{}("right")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(left{}(dotk{}()), \top{SortState{}}()), merged{}()
            ) [label{}("left-merged")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(right{}(dotk{}()), \top{SortState{}}()), merged{}()
            ) [label{}("right-merged")]
        endmodule []"#;

    const UNSUPPORTED_HOOK_DEFINITION: &str = r#"[]
        module MAIN
            sort SortState{} [hasDomainValues{}()]
            hooked-symbol missing{}(SortState{}) : SortState{}
                [function{}(), hook{}("TEST.missing")]
        endmodule []"#;

    #[cfg(not(feature = "z3-inference"))]
    const INDETERMINATE_DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            symbol wrap{}(SortInt{}) : SortS{} [constructor{}()]
            symbol done{}() : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortInt{}, SortS{}}(X:SortInt{}, \dv{SortInt{}}("0"))
                ), done{}()
            ) [label{}("guarded")]
        endmodule []"#;

    #[cfg(not(feature = "z3-inference"))]
    const NARROWING_DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
            symbol zero{}() : SortS{} [constructor{}()]
            symbol done{}() : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(zero{}()), \top{SortS{}}()), done{}()
            ) [label{}("narrow")]
        endmodule []"#;

    /// The module `MAIN` of [`SET_BINDING_DEFINITION`] without its `mint` rule.
    const SET_BINDING_BASE: &str = r#"[]
        module MAIN
            sort SortS{} []
            symbol go{}() : SortS{} [constructor{}()]
            symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
        endmodule []"#;

    /// `mint`'s right-hand side holds a set variable its left-hand side does not bind, so a step
    /// from `go()` would give `wrap(@Y')`, a fresh free set variable: the definition is refused
    /// at load (GAP K40 review fix, `RulePatternError::UnboundSetVariable`).
    const SET_BINDING_DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            symbol go{}() : SortS{} [constructor{}()]
            symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(go{}(), \top{SortS{}}()),
                wrap{}(@Y:SortS{})
            ) [label{}("mint")]
        endmodule []"#;

    /// A hook declared at an arity its builtin does not take (`INT.add` of three arguments), and
    /// a step to an application of it on values.
    const WRONG_ARITY_HOOK_DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            symbol go{}(SortInt{}) : SortS{} [constructor{}()]
            symbol done{}(SortInt{}) : SortS{} [constructor{}()]
            hooked-symbol add3{}(SortInt{}, SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.add")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(go{}(X:SortInt{}), \top{SortS{}}()),
                done{}(add3{}(X:SortInt{}, \dv{SortInt{}}("1"), \dv{SortInt{}}("2")))
            ) [label{}("go")]
        endmodule []"#;

    /// `IO.logString` in a definition without the `dotk` symbol its result needs.
    const LOG_WITHOUT_DOTK_DEFINITION: &str = r#"[]
        module MAIN
            sort SortString{} [hasDomainValues{}()]
            sort SortK{} []
            sort SortS{} []
            symbol go{}() : SortS{} [constructor{}()]
            symbol done{}(SortK{}) : SortS{} [constructor{}()]
            hooked-symbol log{}(SortString{}) : SortK{}
                [function{}(), total{}(), hook{}("IO.logString")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(go{}(), \top{SortS{}}()),
                done{}(log{}(\dv{SortString{}}("x")))
            ) [label{}("go")]
        endmodule []"#;

    /// (FZ-CRASH-CAUSE) A `simplification-error` leaf carries its structured cause, in the
    /// encoding search uses for its failure, so that a client tells a builtin failure (a hook
    /// declared at a signature its builtin does not take, a result symbol the definition lacks)
    /// from a bound or an undecided query without reading the leaf's text.
    #[test]
    fn simplification_error_leaves_publish_their_cause() {
        let cases = [
            (WRONG_ARITY_HOOK_DEFINITION, r#"go{}(\dv{SortInt{}}("5"))"#),
            (LOG_WITHOUT_DOTK_DEFINITION, "go{}()"),
        ];
        let mut causes = Vec::new();
        for (definition, state) in cases {
            let mut backend = Backend::new(definition, "MAIN", BackendOptions::DEFAULT).unwrap();
            let result = backend
                .execute_kore(ExecuteRequest::new(kore(state)))
                .unwrap();
            assert_eq!(result.leaves.len(), 1, "{state}");
            let leaf = &result.leaves[0];
            assert_eq!(
                leaf.reason,
                HaltReasonOutput::SimplificationError,
                "{state}: {:?}",
                leaf.detail
            );
            let encoded = serde_json::to_value(leaf).unwrap();
            let decoded: ExecutionLeaf = serde_json::from_value(encoded.clone()).unwrap();
            assert_eq!(serde_json::to_value(decoded).unwrap(), encoded);
            causes.push(encoded["cause"].clone());
        }
        assert_eq!(
            causes,
            [
                serde_json::json!({
                    "kind": "builtin",
                    "error": {"kind": "wrong-arity", "hook": "INT.add", "expected": 2, "actual": 3}
                }),
                serde_json::json!({
                    "kind": "invalid-builtin-result-symbol",
                    "hook": "IO.logString",
                    "symbol": "dotk"
                }),
            ]
        );
    }

    /// (FZ-CRASH-CAUSE) A rule condition over a function smt-hooked to an operator SMT-LIB lacks:
    /// the solver rejects the script for text the definition supplied, so the leaf's cause is a
    /// `malformed-script` failure that carries no `translationBlamed` (its JSON is what it was
    /// before the field existed).
    #[cfg(feature = "z3-inference")]
    #[test]
    fn a_script_rejected_for_the_definitions_smt_text_is_not_blamed_on_the_wire() {
        const DEFINITION: &str = r#"[]
            module MAIN
                sort SortS{} []
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol go{}(SortInt{}) : SortS{} [constructor{}()]
                symbol done{}() : SortS{} [constructor{}()]
                symbol bogus{}(SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("no-such-operator")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        go{}(X:SortInt{}),
                        \equals{SortBool{}, SortS{}}(bogus{}(X:SortInt{}), \dv{SortBool{}}("true"))
                    ), done{}()
                ) [label{}("go")]
            endmodule []"#;
        let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::DEFAULT).unwrap();
        let result = backend
            .execute_kore(ExecuteRequest::new(kore(r#"go{}(\dv{SortInt{}}("5"))"#)))
            .unwrap();
        let encoded = serde_json::to_value(&result.leaves[0]).unwrap();
        let error = &encoded["cause"]["error"];
        assert_eq!(error["kind"], "malformed-script", "{encoded}");
        assert!(error["message"].is_string(), "{encoded}");
        assert!(error.get("translationBlamed").is_none(), "{encoded}");
    }

    #[cfg(not(feature = "z3-inference"))]
    #[test]
    fn execution_indeterminate_leaves_publish_search_causes() {
        let cases = [
            (INDETERMINATE_DEFINITION, "wrap{}(Y:SortInt{})", "requires"),
            (NARROWING_DEFINITION, "wrap{}(Y:SortS{})", "smt"),
        ];
        for (definition, state, kind) in cases {
            let mut backend = Backend::new(definition, "MAIN", BackendOptions::DEFAULT).unwrap();
            let leaf = backend
                .execute_kore(ExecuteRequest::new(kore(state)))
                .unwrap()
                .leaves
                .remove(0);
            assert_eq!(leaf.reason, HaltReasonOutput::Indeterminate, "{state}");
            let encoded = serde_json::to_value(&leaf).unwrap();
            assert_eq!(encoded["cause"]["kind"], kind, "{state}: {encoded}");
            assert!(encoded["cause"]["rule"].is_string(), "{encoded}");
            assert!(leaf.cause.as_ref().unwrap().solver_unavailable());
            if kind == "smt" {
                assert_eq!(encoded["cause"]["error"]["kind"], "unavailable");
            }
            let decoded: ExecutionLeaf = serde_json::from_value(encoded.clone()).unwrap();
            assert_eq!(serde_json::to_value(decoded).unwrap(), encoded);
        }
        let leaf = backend()
            .execute_kore(ExecuteRequest::new(kore("a{}()")))
            .unwrap()
            .leaves
            .remove(0);
        assert_ne!(leaf.reason, HaltReasonOutput::Indeterminate);
        assert!(leaf.cause.is_none());
        assert!(serde_json::to_value(leaf).unwrap().get("cause").is_none());
    }

    /// GAP K40 (review fix): a rewrite rule whose right-hand side holds a set variable its
    /// left-hand side does not bind is refused, naming the variable and the rule, both in the
    /// definition a backend starts from and in a module added to it: a step would put a fresh
    /// free set variable in the state, which may denote several elements while the backend
    /// reads each term as one. Before, `go()` stepped to `wrap(@Y')`, and the published
    /// `match` cause of an element variable bound to it had that route; no request or rule
    /// route reaches it now.
    #[test]
    fn a_rewrite_rule_minting_a_set_variable_is_refused_at_load_and_by_add_module() {
        let names = |message: &str| message.contains("`@Y`") && message.contains("mint");
        let loaded = Backend::new(SET_BINDING_DEFINITION, "MAIN", BackendOptions::DEFAULT)
            .err()
            .expect("the definition is refused");
        assert!(names(loaded.message()), "{}", loaded.message());
        let mut backend = Backend::new(SET_BINDING_BASE, "MAIN", BackendOptions::DEFAULT).unwrap();
        let added = backend
            .add_module(
                r#"module MINT import MAIN []
                    axiom{} \rewrites{SortS{}}(
                        \and{SortS{}}(go{}(), \top{SortS{}}()),
                        wrap{}(@Y:SortS{})
                    ) [label{}("mint")]
                endmodule []"#,
                false,
            )
            .unwrap_err();
        assert!(names(added.message()), "{}", added.message());
    }

    fn backend() -> Backend {
        Backend::new(DEFINITION, "MAIN", BackendOptions::DEFAULT).unwrap()
    }

    /// A request the backend refuses is refused in words that name what is wrong: the rule
    /// filter's unknown id, the sort an added module may not declare, what an execution state
    /// lacks or has that a constrained term may not (without saying it is a rule's), the token a
    /// module's text may not have.
    #[test]
    fn refused_requests_are_stated_in_words() {
        let mut backend = backend();
        let filter = backend
            .execute_observed_kore(ObservedRequest {
                request: ExecuteRequest::new(kore("a{}()")),
                rules: Some(vec!["missing".into()]),
            })
            .unwrap_err();
        assert_eq!(
            filter.message(),
            "could not install observation filter: no executable rewrite, function equation, \
             simplification or definedness rule has the id 'missing'"
        );
        let sorted = backend
            .add_module(
                "module NEWSORT import MAIN [] sort SortNew{} [] endmodule []",
                false,
            )
            .unwrap_err();
        assert_eq!(
            sorted.message(),
            "could not add KORE module: an added module may not declare sorts, and this one \
             declares 'SortNew'"
        );
        let predicate = backend
            .execute_kore(ExecuteRequest::new(kore(r"\top{SortS{}}()")))
            .unwrap_err();
        assert_eq!(
            predicate.message(),
            "could not internalize execution state: Invalid pattern: the pattern states no term, \
             only predicates, where a term is needed"
        );
        assert_eq!(
            predicate.kind(),
            Some(BackendErrorKind::StateNotInternalized)
        );
        let disjunction = backend
            .execute_kore(ExecuteRequest::new(kore(r"\or{SortS{}}(a{}(), b{}())")))
            .unwrap_err();
        assert_eq!(
            disjunction.message(),
            "could not internalize execution state: Invalid pattern: a term of the pattern is a \
             disjunction (\\or) of terms where one term is needed"
        );
        let rewrite = r"\and{SortS{}}(a{}(), \rewrites{SortS{}}(a{}(), b{}()))";
        let rewrite = backend
            .execute_kore(ExecuteRequest::new(kore(rewrite)))
            .unwrap_err();
        assert_eq!(
            rewrite.message(),
            "could not internalize execution state: Invalid pattern: a predicate of the pattern \
             uses \\rewrites, which the backend does not read as a predicate"
        );
        let trailing = "module BROKEN import MAIN [] endmodule [] ]";
        let broken = backend.add_module(trailing, false).unwrap_err();
        assert_eq!(
            broken.message(),
            format!(
                "could not parse KORE module: unexpected trailing token ']' at byte {}",
                trailing.len() - 1
            )
        );
    }

    /// A solver that cannot be created for the definition is an error of kind `SolverInit`,
    /// which the caller tells from every other error without reading its text: here the
    /// definition's SMT declarations do not translate (an `smtlib` symbol over a sort variable).
    #[cfg(feature = "z3-inference")]
    #[test]
    fn a_solver_that_cannot_be_created_is_a_solver_init_error() {
        let definition = r#"[]
        module MAIN
            sort SortS{} []
            symbol a{}() : SortS{} [constructor{}()]
            symbol f{S}(S) : S [function{}(), smtlib{}("f")]
        endmodule []"#;
        let error = Backend::new(definition, "MAIN", BackendOptions::DEFAULT)
            .err()
            .expect("the solver is not created");
        assert_eq!(error.kind(), Some(BackendErrorKind::SolverInit), "{error}");
        assert!(
            error.message().starts_with("could not initialize Z3: "),
            "{error}"
        );
        assert_eq!(error.stop_cause(), None);
    }

    #[test]
    fn json_text_paths_match_pattern_responses() {
        let execute = || ExecuteRequest::new(kore("a{}()"));
        let search = || SearchRequest::new(kore("a{}()"));
        let pattern = || SearchPatternRequest::new(kore("a{}()"), kore("c{}()"));
        let observed_execute = || ObservedRequest {
            request: execute(),
            rules: None,
        };
        let observed_search = || ObservedRequest {
            request: search(),
            rules: None,
        };
        let observed_pattern = || ObservedRequest {
            request: pattern(),
            rules: None,
        };

        macro_rules! same_json {
            ($kore_method:ident, $json_method:ident, $request:expr) => {{
                let expected =
                    serde_json::to_string(&backend().$kore_method($request).unwrap()).unwrap();
                let actual = backend().$json_method($request).unwrap();
                assert_eq!(actual, expected, stringify!($json_method));
            }};
        }
        same_json!(execute_kore, execute_json, execute());
        same_json!(
            execute_observed_kore,
            execute_observed_json,
            observed_execute()
        );
        same_json!(search_kore, search_json, search());
        same_json!(
            search_observed_kore,
            search_observed_json,
            observed_search()
        );
        same_json!(search_paths_kore, search_paths_json, search());
        same_json!(
            search_paths_observed_kore,
            search_paths_observed_json,
            observed_search()
        );
        same_json!(search_pattern_kore, search_pattern_json, pattern());
        same_json!(
            search_pattern_observed_kore,
            search_pattern_observed_json,
            observed_pattern()
        );
        same_json!(
            search_pattern_paths_kore,
            search_pattern_paths_json,
            pattern()
        );
        same_json!(
            search_pattern_paths_observed_kore,
            search_pattern_paths_observed_json,
            observed_pattern()
        );
        let proof = || ProveRequest {
            claim: Some("reaches-c".into()),
            ..ProveRequest::default()
        };
        same_json!(prove_kore, prove_json, proof());
        // The simplification route's pattern form takes the request's pattern and module, and
        // its pattern serializes as the KORE JSON the text form writes.
        assert_eq!(
            backend()
                .simplify_json(PatternRequest::new(kore("a{}()")))
                .unwrap(),
            serde_json::to_string(
                &backend()
                    .simplify_kore(None, &kore("a{}()"), Admission::Unverified)
                    .unwrap()
            )
            .unwrap(),
            "simplify_json"
        );

        let mut written = Vec::new();
        backend()
            .execute_observed_to_writer(observed_execute(), &mut written)
            .unwrap();
        assert_eq!(
            written,
            backend()
                .execute_observed_json(observed_execute())
                .unwrap()
                .into_bytes()
        );
    }

    #[test]
    fn executable_facade_rejects_nested_macro_and_alias_states_before_internalization() {
        let alias = kore("weakExistsFinally{SortS{}}(a{}())");
        let nested_macro = kore(r#"\and{SortS{}}(a{}(), macroValue{}())"#);
        let assert_invalid = |error: BackendError, symbol: &str| {
            assert_eq!(
                error.kind(),
                Some(BackendErrorKind::InvalidState),
                "{error}"
            );
            let error = error.to_string();
            assert!(error.contains("invalid executable state"), "{error}");
            assert!(error.contains(symbol), "{error}");
        };

        assert_invalid(
            backend()
                .execute_kore(ExecuteRequest::new(alias.clone()))
                .unwrap_err(),
            "weakExistsFinally",
        );
        assert_invalid(
            backend()
                .search_kore(SearchRequest::new(nested_macro.clone()))
                .unwrap_err(),
            "macroValue",
        );
        assert_invalid(
            backend()
                .search_paths_kore(SearchRequest::new(alias.clone()))
                .unwrap_err(),
            "weakExistsFinally",
        );
        assert_invalid(
            backend()
                .search_pattern_kore(SearchPatternRequest::new(nested_macro, kore("a{}()")))
                .unwrap_err(),
            "macroValue",
        );
        assert_invalid(
            backend()
                .search_pattern_paths_kore(SearchPatternRequest::new(alias, kore("a{}()")))
                .unwrap_err(),
            "weakExistsFinally",
        );
    }

    fn kore(source: &str) -> KorePattern {
        parse_pattern(source).unwrap()
    }

    fn json(source: &str) -> Value {
        encode_pattern(&kore(source)).unwrap()
    }

    fn text(pattern: KorePattern) -> String {
        Printer::compact().print_pattern(&pattern)
    }

    #[test]
    fn search_wire_types_round_trip_every_disposition() {
        let state = SearchStateOutput {
            state: json("a{}()"),
            diagnostics: vec![BackendDiagnosticOutput::SimplificationBudgetExhausted {
                limit: 3,
                subject: BudgetSubjectOutput::Term,
            }],
            depth: 1,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
        };
        let variants = vec![
            IncompleteSearchOutput::ResultBound,
            IncompleteSearchOutput::DepthBound {
                state: state.clone(),
            },
            IncompleteSearchOutput::BreadthBound {
                states: vec![state.clone()],
            },
            IncompleteSearchOutput::Indeterminate {
                state: state.clone(),
                reason: SearchFailureOutput::Requires {
                    rule: "rule-id".into(),
                    predicates: Vec::new(),
                },
            },
            IncompleteSearchOutput::Cancelled {
                state: state.clone(),
            },
            IncompleteSearchOutput::Simplification {
                state: state.clone(),
                error: SearchFailureOutput::IterationLimit {
                    limit: 100,
                    term: None,
                },
            },
            IncompleteSearchOutput::Match {
                state: state.clone(),
                bindings: Vec::new(),
                remainder: Vec::new(),
            },
            IncompleteSearchOutput::PlacementBound {
                state: state.clone(),
                bound: 65536,
            },
            IncompleteSearchOutput::Smt {
                state,
                error: SmtFailureOutput::Unavailable,
            },
        ];

        for expected in variants {
            let json = serde_json::to_string(&expected).unwrap();
            let actual = serde_json::from_str::<IncompleteSearchOutput>(&json).unwrap();
            assert_eq!(actual, expected, "{json}");
        }

        let effect = EffectOutput::UserLog {
            message: "hello".into(),
        };
        let json = serde_json::to_string(&effect).unwrap();
        assert_eq!(serde_json::from_str::<EffectOutput>(&json).unwrap(), effect);
        assert!(serde_json::from_str::<EffectOutput>(r#"{"kind":"future"}"#).is_err());
        assert!(
            serde_json::from_str::<EffectOutput>(
                r#"{"kind":"user-log","message":"hello","future":true}"#,
            )
            .is_err()
        );
    }

    #[test]
    fn search_request_rejects_unknown_fields_and_schemas() {
        assert!(serde_json::from_str::<SearchRequest>(r#"{"bogus":1}"#).is_err());

        let request = serde_json::from_value::<SearchRequest>(serde_json::json!({
            "state": json("a{}()"),
            "schemaVersion": 99,
        }))
        .unwrap();
        let error = request.validate_schema().unwrap_err();
        assert!(error.to_string().contains("schema version 99"), "{error}");
        assert!(error.to_string().contains("version 1"), "{error}");
    }

    #[test]
    fn legacy_persistent_requests_reject_unknown_fields() {
        assert!(serde_json::from_str::<BackendOptions>(r#"{"bogus":1}"#).is_err());
        assert!(serde_json::from_str::<ExecuteRequest>(r#"{"state":null,"bogus":1}"#).is_err());
        assert!(serde_json::from_str::<PatternRequest>(r#"{"state":null,"bogus":1}"#).is_err());
        assert!(
            serde_json::from_str::<ImplicationRequest>(
                r#"{"antecedent":null,"consequent":null,"bogus":1}"#,
            )
            .is_err()
        );
        assert!(serde_json::from_str::<ProveRequest>(r#"{"bogus":1}"#).is_err());

        let error = backend()
            .execute_kore(ExecuteRequest {
                schema_version: 99,
                ..ExecuteRequest::new(kore("a{}()"))
            })
            .unwrap_err();
        assert!(error.to_string().contains("schema version 99"), "{error}");
    }

    const DEEP_REQUEST_LEVELS: usize = 200_000;

    /// KORE JSON for a `\not` chain `levels` deep, built without a JSON value.
    fn deep_kore_json(levels: usize) -> String {
        let sort = r#"{"tag":"SortApp","name":"SortK","args":[]}"#;
        let mut json = String::from(r#"{"format":"KORE","version":1,"term":"#);
        for _ in 0..levels {
            json.push_str(&format!(r#"{{"tag":"Not","sort":{sort},"arg":"#));
        }
        json.push_str(&format!(r#"{{"tag":"Top","sort":{sort}}}"#));
        json.push_str(&"}".repeat(levels + 1));
        json
    }

    fn deep_not_depth(mut pattern: &KorePattern) -> usize {
        let mut depth = 0;
        while let KorePattern::Not { argument, .. } = pattern {
            depth += 1;
            pattern = argument;
        }
        depth
    }

    #[test]
    fn deep_kore_request_fields_decode_on_the_test_thread() {
        let deep = deep_kore_json(DEEP_REQUEST_LEVELS);

        let execute =
            deserialize_request::<ExecuteRequest>(&format!(r#"{{"state":{deep},"maxDepth":0}}"#))
                .unwrap();
        assert_eq!(deep_not_depth(&execute.state), DEEP_REQUEST_LEVELS);
        assert_eq!(execute.max_depth, Some(0));
        drop(execute);

        let observed = deserialize_request::<ObservedRequest<SearchPatternRequest>>(&format!(
            r#"{{"request":{{"state":{deep},"pattern":{deep}}},"rules":[]}}"#
        ))
        .unwrap();
        assert_eq!(deep_not_depth(&observed.request.state), DEEP_REQUEST_LEVELS);
        assert_eq!(observed.request.state, observed.request.pattern);
        drop(observed);

        let implication = deserialize_request::<ImplicationRequest>(&format!(
            r#"{{"antecedent":{deep},"consequent":{deep}}}"#
        ))
        .unwrap();
        assert_eq!(deep_not_depth(&implication.consequent), DEEP_REQUEST_LEVELS);
        drop(implication);

        let simplify =
            deserialize_request::<PatternRequest>(&format!(r#"{{"state":{deep}}}"#)).unwrap();
        assert_eq!(
            format!("{simplify:?}").matches("Not {").count(),
            DEEP_REQUEST_LEVELS
        );
    }

    #[test]
    fn deep_malformed_kore_request_fields_are_ordinary_errors() {
        let unclosed_arrays = format!(r#"{{"state":{}"#, "[".repeat(DEEP_REQUEST_LEVELS));
        let error = deserialize_request::<ExecuteRequest>(&unclosed_arrays).unwrap_err();
        assert!(error.to_string().contains("EOF"), "{error}");

        let deep = deep_kore_json(DEEP_REQUEST_LEVELS);
        let unclosed_term = format!(r#"{{"state":{}"#, &deep[..deep.len() - 10]);
        let error = deserialize_request::<SearchRequest>(&unclosed_term).unwrap_err();
        assert!(error.to_string().contains("EOF"), "{error}");

        let mut wrong_tag = deep.replacen(r#""tag":"Top""#, r#""tag":"Bogus""#, 1);
        let error = deserialize_request::<SearchRequest>(&format!(r#"{{"state":{wrong_tag}}}"#))
            .unwrap_err();
        assert!(error.to_string().contains("invalid KORE JSON"), "{error}");
        wrong_tag.clear();

        let error = deserialize_request::<ExecuteRequest>(r#"{"maxDepth":0}"#).unwrap_err();
        assert!(
            error.to_string().contains("missing field `state`"),
            "{error}"
        );
        let error = deserialize_request::<ExecuteRequest>(r#"{"state":null}"#).unwrap_err();
        assert!(error.to_string().contains("invalid KORE JSON"), "{error}");
    }

    /// No field outside the KORE fields has a type that nests, so serde rejects a deep value
    /// there at its first level, with its recursion limit as a backstop.
    #[test]
    fn deep_values_outside_kore_fields_are_ordinary_errors() {
        let state = deep_kore_json(1);
        let nested = format!(
            "{}{}",
            "[".repeat(DEEP_REQUEST_LEVELS),
            "]".repeat(DEEP_REQUEST_LEVELS)
        );
        for request in [
            format!(r#"{{"state":{state},"moduleName":{nested}}}"#),
            format!(r#"{{"state":{state},"cutPointRules":{nested}}}"#),
            format!(r#"{{"state":{state},"bogus":{nested}}}"#),
        ] {
            assert!(deserialize_request::<ExecuteRequest>(&request).is_err());
        }
        assert!(
            deserialize_request::<ObservedRequest<ExecuteRequest>>(&format!(
                r#"{{"request":{{"state":{state}}},"rules":{nested}}}"#
            ))
            .is_err()
        );
    }

    #[test]
    fn prove_request_accepts_explicit_circularities() {
        assert!(
            serde_json::from_str::<ProveRequest>(
                r#"{"claim":"reaches-c","circularities":["reaches-c"]}"#,
            )
            .is_ok()
        );
    }

    #[test]
    fn persistent_proof_uses_only_explicit_or_trusted_circularities() {
        let definition = r#"[]
            module MAIN
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}()]
                symbol b{}() : SortS{} [constructor{}()]
                symbol c{}() : SortS{} [constructor{}()]
                symbol d{}() : SortS{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()), b{}()
                ) [label{}("a-to-b")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(b{}(), \top{SortS{}}()), c{}()
                ) [label{}("b-to-c")]
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    weakAlwaysFinally{SortS{}}(d{}())
                ) [label{}("ca")]
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(b{}(), \top{SortS{}}()),
                    weakAlwaysFinally{SortS{}}(d{}())
                ) [label{}("cb"), trusted{}()]
            endmodule []"#;

        let mut backend = Backend::new(definition, "MAIN", BackendOptions::DEFAULT).unwrap();
        let default = backend
            .prove_kore(ProveRequest {
                claim: Some("ca".into()),
                ..ProveRequest::default()
            })
            .unwrap();
        assert_eq!(default.status, "proven");

        let isolated = backend
            .prove_kore(ProveRequest {
                claim: Some("ca".into()),
                circularities: Some(vec!["ca".into()]),
                ..ProveRequest::default()
            })
            .unwrap();
        assert_eq!(isolated.status, "disproved");
    }

    #[test]
    fn persistent_proof_keeps_both_modalities_under_one_emitted_id() {
        let definition = r#"[]
            module MAIN
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}()]
                symbol b{}() : SortS{} [constructor{}()]
                symbol c{}() : SortS{} [constructor{}()]
                alias weakExistsFinally{S}(S) : S
                    where weakExistsFinally{S}(@X:S) := @X:S []
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()), b{}()
                ) []
                claim{} \implies{SortS{}}(a{}(), weakAlwaysFinally{SortS{}}(c{}()))
                    [label{}("goal")]
                claim{} \implies{SortS{}}(b{}(), weakExistsFinally{SortS{}}(c{}()))
                    [label{}("one"), trusted{}(), UNIQUE'Unds'ID{}("shared")]
                claim{} \implies{SortS{}}(b{}(), weakAlwaysFinally{SortS{}}(c{}()))
                    [label{}("all"), trusted{}(), UNIQUE'Unds'ID{}("shared")]
            endmodule []"#;
        let mut backend = Backend::new(definition, "MAIN", BackendOptions::DEFAULT).unwrap();
        let result = backend
            .prove_kore(ProveRequest {
                claim: Some("goal".into()),
                ..ProveRequest::default()
            })
            .unwrap();
        assert_eq!(result.status, "proven");
    }

    #[test]
    fn encodes_deep_patterns_without_the_default_json_recursion_limit() {
        let mut source = r"\top{SortS{}}()".to_owned();
        for _ in 0..160 {
            source = format!(r"\not{{SortS{{}}}}({source})");
        }

        let pattern = parse_pattern(&source).unwrap();
        assert!(encode_pattern(&pattern).is_ok());
    }

    #[test]
    fn persistent_backend_executes_and_proves() {
        let mut backend = backend();
        let execution = backend
            .execute_kore(ExecuteRequest {
                max_depth: Some(2),
                ..ExecuteRequest::new(kore("a{}()"))
            })
            .unwrap();
        assert_eq!(execution.leaves.len(), 1);
        assert_eq!(text(execution.leaves[0].state.clone()), "c{}()");
        assert!(
            serde_json::to_value(&execution).unwrap()["leaves"][0]
                .get("diagnostics")
                .is_none()
        );

        let implication = backend
            .implies_with(
                ImplicationRequest {
                    antecedent: kore("X:S"),
                    consequent: kore("X:S"),
                    module_name: None,
                    schema_version: BACKEND_SCHEMA_VERSION,
                },
                Ok,
            )
            .unwrap();
        assert_eq!(implication.status, "valid");

        let proof = backend
            .prove_kore(ProveRequest {
                claim: Some("reaches-c".into()),
                ..ProveRequest::default()
            })
            .unwrap();
        assert_eq!(proof.status, "proven");
    }

    #[test]
    fn execution_exposes_the_leaf_budget_diagnostic_on_the_wire() {
        let mut backend = Backend::new(
            include_str!("../../tests/fixtures/execution-budget.kore"),
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let result = backend
            .execute_kore(ExecuteRequest {
                max_simplification_iterations: 3,
                ..ExecuteRequest::new(kore("start{}()"))
            })
            .unwrap();
        assert_eq!(result.leaves.len(), 1);
        let value = serde_json::to_value(result).unwrap();
        assert_eq!(
            value["leaves"][0]["diagnostics"],
            serde_json::json!([{
                "kind": "simplification-budget-exhausted",
                "limit": 3,
                "subject": "term"
            }])
        );
    }

    /// A leaf's `detail` is for a reader: a branch states its successors' count and rules in
    /// words, not the reason's Rust value with its patterns and substitutions.
    #[test]
    fn a_branch_leaf_states_its_detail_in_words() {
        let mut backend = Backend::new(
            include_str!("../../tests/fixtures/execution-candidates.kore"),
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let result = backend
            .execute_kore(ExecuteRequest {
                stop_at_branch: true,
                ..ExecuteRequest::new(kore("start{}()"))
            })
            .unwrap();
        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one branch leaf: {:?}", result.leaves);
        };
        assert_eq!(leaf.reason, HaltReasonOutput::Branch);
        let detail = leaf.detail.as_deref().unwrap_or_default();
        assert!(
            ["to-b and to-g", "to-g and to-b"]
                .map(|rules| format!("the step branches into 2 successors by rules {rules}"))
                .contains(&detail.to_owned()),
            "{detail}"
        );
    }

    #[test]
    fn branch_candidates_expose_only_their_own_diagnostics_on_the_wire() {
        let mut backend = Backend::new(
            include_str!("../../tests/fixtures/execution-candidates.kore"),
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let result = backend
            .execute_kore(ExecuteRequest {
                max_simplification_iterations: 3,
                stop_at_branch: true,
                ..ExecuteRequest::new(kore("start{}()"))
            })
            .unwrap();
        let value = serde_json::to_value(result).unwrap();
        let [leaf] = value["leaves"].as_array().unwrap().as_slice() else {
            panic!("expected one branch leaf: {value}");
        };
        assert_eq!(leaf["reason"], "branch");
        assert!(leaf.get("diagnostics").is_none());
        let candidates = leaf["candidates"].as_array().unwrap();
        assert_eq!(candidates.len(), 2);
        let diagnosed = candidates
            .iter()
            .find(|candidate| candidate["label"] == "to-g")
            .unwrap();
        assert_eq!(
            diagnosed["diagnostics"],
            serde_json::json!([{
                "kind": "simplification-budget-exhausted",
                "limit": 3,
                "subject": "term"
            }])
        );
        let plain = candidates
            .iter()
            .find(|candidate| candidate["label"] == "to-b")
            .unwrap();
        assert!(plain.get("diagnostics").is_none());
        assert_eq!(
            text(kore_codec::from_value(&plain["state"]).unwrap()),
            "b{}()"
        );
    }

    /// `stopCount` ends a path at that arrival at a stop and reports each leaf's count as
    /// `stops`: on `a -> b -> c -> d`, every step selected, a terminal count of 2 ends at `c`, a
    /// cut-point count of 2 at `b` before `bc`, and a count past the arrivals ends stuck at `d`
    /// after 3; a request without it reports no count. The request member, the leaf's field and
    /// the capability are declared in TypeScript.
    #[test]
    fn the_stop_count_reaches_the_facade() {
        let mut backend = Backend::new(CHAIN, "MAIN", BackendOptions::DEFAULT).unwrap();
        let rules = || vec!["ab".to_owned(), "bc".to_owned(), "cd".to_owned()];
        let mut run = |terminal: bool, stop_count: Option<u64>| {
            let (cut_point_rules, terminal_rules) = if terminal {
                (Vec::new(), rules())
            } else {
                (rules(), Vec::new())
            };
            let result = backend
                .execute_kore(ExecuteRequest {
                    cut_point_rules,
                    terminal_rules,
                    stop_count: stop_count.map(|count| std::num::NonZeroU64::new(count).unwrap()),
                    ..ExecuteRequest::new(kore("a{}()"))
                })
                .unwrap();
            let value = serde_json::to_value(result).unwrap();
            let [leaf] = value["leaves"].as_array().unwrap().as_slice() else {
                panic!("expected one leaf: {value}");
            };
            (
                leaf["reason"].as_str().unwrap().to_owned(),
                leaf["depth"].as_u64().unwrap(),
                text(kore_codec::from_value(&leaf["state"]).unwrap()),
                leaf.get("stops").map(|stops| stops.as_u64().unwrap()),
            )
        };
        let end = |reason: &str, depth, state: &str, stops| {
            (reason.to_owned(), depth, state.to_owned(), stops)
        };
        assert_eq!(run(true, None), end("terminal", 1, "b{}()", None));
        assert_eq!(run(true, Some(1)), end("terminal", 1, "b{}()", Some(1)));
        assert_eq!(run(true, Some(2)), end("terminal", 2, "c{}()", Some(2)));
        assert_eq!(run(false, Some(2)), end("cut-point", 1, "b{}()", Some(2)));
        assert_eq!(run(true, Some(5)), end("stuck", 3, "d{}()", Some(3)));
        assert_eq!(run(false, Some(5)), end("stuck", 3, "d{}()", Some(3)));
        assert_typescript_member("ExecuteOptions", "stopCount?: number");
        assert_typescript_member("ExecutionLeaf", "stops?: number");
        assert_typescript_member("BackendCapabilities", "stopCount: boolean");
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["stopCount"], true);
    }

    /// The in-process stop condition reaches the facade: the count counts the arrivals where it
    /// holds, each leaf reports its events (`stops`) and its arrivals (`arrivals`), an undecided
    /// answer ends the path `stop-undecided`, and a refusal fails the request with its kind,
    /// naming the rule and the depth. On `a -> b -> c -> d`, every step selected.
    #[test]
    fn the_stop_condition_reaches_the_facade() {
        let mut backend = Backend::new(CHAIN, "MAIN", BackendOptions::DEFAULT).unwrap();
        let rules = || vec!["ab".to_owned(), "bc".to_owned(), "cd".to_owned()];
        // The condition holds at `holds`, is undecided at `undecided` and refuses at `refused`.
        let mut run = |terminal: bool, count: u64, holds: &str, undecided: &str, refused: &str| {
            let (cut_point_rules, terminal_rules) = if terminal {
                (Vec::new(), rules())
            } else {
                (rules(), Vec::new())
            };
            let mut condition = |arrival: &StopArrival<'_>| {
                let state = text(arrival.configuration());
                if state == undecided {
                    StopDecision::Undecided("its budget ran out".to_owned())
                } else if state == refused {
                    StopDecision::Refused("the cell holds a variable".to_owned())
                } else if state == holds {
                    StopDecision::Holds
                } else {
                    StopDecision::Fails
                }
            };
            let result = backend.execute_kore_with_condition(
                ExecuteRequest {
                    cut_point_rules,
                    terminal_rules,
                    stop_count: Some(std::num::NonZeroU64::new(count).unwrap()),
                    ..ExecuteRequest::new(kore("a{}()"))
                },
                &mut condition,
            )?;
            let value = serde_json::to_value(result).unwrap();
            let [leaf] = value["leaves"].as_array().unwrap().as_slice() else {
                panic!("expected one leaf: {value}");
            };
            Ok::<_, BackendError>((
                leaf["reason"].as_str().unwrap().to_owned(),
                leaf["depth"].as_u64().unwrap(),
                text(kore_codec::from_value(&leaf["state"]).unwrap()),
                leaf["stops"].as_u64().unwrap(),
                leaf["arrivals"].as_u64().unwrap(),
            ))
        };
        let end = |reason: &str, depth, state: &str, stops, arrivals| {
            (reason.to_owned(), depth, state.to_owned(), stops, arrivals)
        };
        assert_eq!(
            run(false, 1, "b{}()", "", "").unwrap(),
            end("cut-point", 1, "b{}()", 1, 2)
        );
        assert_eq!(
            run(true, 1, "c{}()", "", "").unwrap(),
            end("terminal", 2, "c{}()", 1, 2)
        );
        assert_eq!(
            run(true, 1, "", "", "").unwrap(),
            end("stuck", 3, "d{}()", 0, 3)
        );
        assert_eq!(
            run(false, 1, "", "b{}()", "").unwrap(),
            end("stop-undecided", 1, "b{}()", 0, 2)
        );
        assert_eq!(
            run(true, 1, "", "c{}()", "").unwrap(),
            end("stop-undecided", 2, "c{}()", 0, 2)
        );
        let refused = run(false, 1, "", "", "c{}()").unwrap_err();
        assert_eq!(refused.kind(), Some(BackendErrorKind::StopConditionRefused));
        assert_eq!(
            refused.to_string(),
            "the stop condition has no value at the arrival before `cd` at depth 2: the cell holds a variable"
        );
        assert_typescript_member("ExecutionLeaf", "arrivals?: number");
    }

    /// An in-process probe reaches the facade: a probe that continues leaves the result as the
    /// plain request's, a difference ends the request `probe-difference` at the point's observed
    /// state, and `Done` ends the path `probe-done` there. On `a -> b -> c -> d`, `ab` a before
    /// point and `bc` an after point.
    #[test]
    fn the_probe_reaches_the_facade() {
        struct Answering {
            at: &'static str,
            answer: ProbeDecision,
            asked: Vec<(StopSide, u64, String)>,
            ended: Vec<String>,
        }
        impl Probe for Answering {
            fn observe(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision {
                let state = text(point.configuration());
                self.asked
                    .push((point.side(), point.depth(), state.clone()));
                if state == self.at {
                    self.answer.clone()
                } else {
                    ProbeDecision::Continue
                }
            }

            fn ended(&mut self, leaf: &ProbeLeaf<'_>) {
                self.ended.push(text(leaf.configuration()));
            }
        }
        let mut backend = Backend::new(CHAIN, "MAIN", BackendOptions::DEFAULT).unwrap();
        let rules = || ProbeRules {
            before: ["ab".to_owned()].into(),
            after: ["bc".to_owned()].into(),
        };
        let mut run = |at: &'static str, answer: ProbeDecision| {
            let mut probe = Answering {
                at,
                answer,
                asked: Vec::new(),
                ended: Vec::new(),
            };
            let result = backend
                .execute_kore_with_probe(
                    ExecuteRequest::new(kore("a{}()")),
                    rules(),
                    InProcess {
                        probe: Some(&mut probe),
                        ..InProcess::default()
                    },
                )
                .unwrap();
            (serde_json::to_value(result).unwrap(), probe)
        };
        let leaf = |value: &serde_json::Value| {
            let [leaf] = value["leaves"].as_array().unwrap().as_slice() else {
                panic!("expected one leaf: {value}");
            };
            (
                leaf["reason"].as_str().unwrap().to_owned(),
                leaf["depth"].as_u64().unwrap(),
                text(kore_codec::from_value(&leaf["state"]).unwrap()),
            )
        };
        let (continued, probe) = run("", ProbeDecision::Continue);
        assert_eq!(
            probe.asked,
            [
                (StopSide::Before, 0, "a{}()".to_owned()),
                (StopSide::After, 2, "c{}()".to_owned())
            ]
        );
        assert_eq!(probe.ended, ["d{}()"]);
        let plain = Backend::new(CHAIN, "MAIN", BackendOptions::DEFAULT)
            .unwrap()
            .execute_kore(ExecuteRequest::new(kore("a{}()")))
            .unwrap();
        assert_eq!(continued, serde_json::to_value(plain).unwrap());
        let (differs, probe) = run("c{}()", ProbeDecision::Differs("c".to_owned()));
        assert_eq!(
            leaf(&differs),
            ("probe-difference".into(), 2, "c{}()".into())
        );
        assert!(probe.ended.is_empty());
        let (done, _) = run("a{}()", ProbeDecision::Done);
        assert_eq!(leaf(&done), ("probe-done".into(), 0, "a{}()".into()));
    }

    /// A chain of three steps, `a -> b -> c -> d`, labelled `ab`, `bc` and `cd`.
    const CHAIN: &str = r#"[]
            module MAIN
                sort SortState{} []
                symbol a{}() : SortState{} [constructor{}()]
                symbol b{}() : SortState{} [constructor{}()]
                symbol c{}() : SortState{} [constructor{}()]
                symbol d{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(a{}(), \top{SortState{}}()), b{}()
                ) [label{}("ab")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(b{}(), \top{SortState{}}()), c{}()
                ) [label{}("bc")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(c{}(), \top{SortState{}}()), d{}()
                ) [label{}("cd")]
            endmodule []"#;

    #[test]
    fn cut_point_candidates_expose_their_diagnostics_on_the_wire() {
        let mut backend = Backend::new(
            include_str!("../../tests/fixtures/execution-budget.kore"),
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let result = backend
            .execute_kore(ExecuteRequest {
                max_simplification_iterations: 3,
                cut_point_rules: vec!["to-g".into()],
                ..ExecuteRequest::new(kore("start{}()"))
            })
            .unwrap();
        let value = serde_json::to_value(result).unwrap();
        let [leaf] = value["leaves"].as_array().unwrap().as_slice() else {
            panic!("expected one cut-point leaf: {value}");
        };
        assert_eq!(leaf["reason"], "cut-point");
        assert!(leaf.get("diagnostics").is_none());
        assert_eq!(leaf["candidates"].as_array().unwrap().len(), 1);
        assert_eq!(leaf["candidates"][0]["label"], "to-g");
        assert_eq!(
            leaf["candidates"][0]["diagnostics"],
            serde_json::json!([{
                "kind": "simplification-budget-exhausted",
                "limit": 3,
                "subject": "term"
            }])
        );
    }

    fn search_diagnostics_backend() -> Backend {
        Backend::new(
            include_str!("../../tests/fixtures/search-diagnostics.kore"),
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap()
    }

    fn term_exhausted_json() -> Value {
        serde_json::json!([{
            "kind": "simplification-budget-exhausted",
            "limit": 3,
            "subject": "term"
        }])
    }

    /// The rule's axiom is the sentence `sentence` of module `MAIN`, written without `Source`
    /// or `Location`, so its origin is present and names it by that place alone.
    fn condition_exhausted_json(rule_id: &str, sentence: usize) -> Value {
        serde_json::json!([
            {"kind": "simplification-budget-exhausted", "limit": 3, "subject": "predicates"},
            {
                "kind": "rule-condition-unsimplified",
                "ruleId": rule_id,
                "origin": {
                    "source": null,
                    "location": null,
                    "sentence": {"module": "MAIN", "index": sentence}
                },
                "limit": 3
            }
        ])
    }

    /// The entry of `entries` whose `field` state prints starting with `state`.
    fn entry_at<'a>(entries: &'a Value, field: Option<&str>, state: &str) -> &'a Value {
        entries
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| {
                let entry = field.map_or(*entry, |field| &entry[field]);
                text(kore_codec::from_value(&entry["state"]).unwrap()).starts_with(state)
            })
            .unwrap_or_else(|| panic!("no entry at {state}: {entries:#}"))
    }

    #[test]
    fn search_states_and_witnesses_expose_their_paths_diagnostics_on_the_wire() {
        let mut backend = search_diagnostics_backend();
        let request = SearchRequest {
            max_simplification_iterations: 3,
            ..SearchRequest::new(kore("start{}()"))
        };

        let states = serde_json::to_value(backend.search_kore(request.clone()).unwrap()).unwrap();
        let paths = serde_json::to_value(backend.search_paths_kore(request).unwrap()).unwrap();

        assert_eq!(states["states"].as_array().unwrap().len(), 3, "{states:#}");
        assert_eq!(states["incomplete"], serde_json::json!([]));
        assert_eq!(
            entry_at(&states["states"], None, "held{}(")["diagnostics"],
            term_exhausted_json()
        );
        assert!(
            entry_at(&states["states"], None, "b{}()")
                .get("diagnostics")
                .is_none()
        );
        assert_eq!(
            entry_at(&states["states"], None, "c{}()")["diagnostics"],
            condition_exhausted_json("norm-c", 11)
        );
        assert_eq!(paths["witnesses"].as_array().unwrap().len(), 3, "{paths:#}");
        assert_eq!(
            entry_at(&paths["witnesses"], None, "held{}(")["diagnostics"],
            term_exhausted_json()
        );
        assert!(
            entry_at(&paths["witnesses"], None, "b{}()")
                .get("diagnostics")
                .is_none()
        );
        assert_eq!(
            entry_at(&paths["witnesses"], None, "c{}()")["diagnostics"],
            condition_exhausted_json("norm-c", 11)
        );
    }

    #[test]
    fn search_matches_expose_their_own_diagnostics_apart_from_their_states_on_the_wire() {
        let mut backend = search_diagnostics_backend();
        let request = SearchPatternRequest {
            max_simplification_iterations: 3,
            ..SearchPatternRequest::new(
                kore("start{}()"),
                kore(
                    r#"\and{SortS{}}(X:SortS{}, \equals{SortS{}, SortS{}}(check{}(X:SortS{}), ok{}()))"#,
                ),
            )
        };

        let states =
            serde_json::to_value(backend.search_pattern_kore(request.clone()).unwrap()).unwrap();
        let paths =
            serde_json::to_value(backend.search_pattern_paths_kore(request).unwrap()).unwrap();

        for (response, field) in [(&states, "state"), (&paths, "witness")] {
            let on_b = entry_at(&response["matches"], Some(field), "b{}()");
            assert!(on_b[field].get("diagnostics").is_none(), "{response:#}");
            assert_eq!(
                on_b["diagnostics"],
                condition_exhausted_json("check-ok", 12)
            );
            let on_c = entry_at(&response["matches"], Some(field), "c{}()");
            assert_eq!(
                on_c[field]["diagnostics"],
                condition_exhausted_json("norm-c", 11)
            );
            assert_eq!(
                on_c["diagnostics"],
                condition_exhausted_json("check-ok", 12)
            );
        }
    }

    /// A failed implication names the part of the consequent the antecedent fails by its wire
    /// name.
    #[test]
    fn a_failed_implication_names_the_part_of_the_consequent_it_fails() {
        let mut backend = backend();
        for (consequent, failure) in [
            ("b{}()", "term-mismatch"),
            (
                r#"\and{SortS{}}(a{}(), \equals{SortS{}, SortS{}}(a{}(), b{}()))"#,
                "consequent-condition",
            ),
        ] {
            let result = backend
                .implies_with(
                    ImplicationRequest {
                        antecedent: kore("a{}()"),
                        consequent: kore(consequent),
                        module_name: None,
                        schema_version: BACKEND_SCHEMA_VERSION,
                    },
                    Ok,
                )
                .unwrap();
            let result = serde_json::to_value(result).unwrap();
            assert_eq!(result["status"], "invalid", "{result:#}");
            assert_eq!(result["failure"], failure, "{result:#}");
        }
    }

    #[test]
    fn persistent_backend_answers_implications_between_bottom_top_and_a_regular_pattern() {
        let bottom = r#"\bottom{SortS{}}()"#;
        let top = r#"\top{SortS{}}()"#;
        let regular = "a{}()";
        let cases = [
            (bottom, bottom, "valid", "Bottom"),
            (bottom, top, "valid", "Bottom"),
            (bottom, regular, "valid", "Bottom"),
            (regular, bottom, "invalid", "Bottom"),
            (regular, top, "valid", "Top"),
            (regular, regular, "valid", "Top"),
        ];
        let mut backend = backend();

        for (antecedent, consequent, status, predicate) in cases {
            let result = backend
                .implies_with(
                    ImplicationRequest {
                        antecedent: kore(antecedent),
                        consequent: kore(consequent),
                        module_name: None,
                        schema_version: BACKEND_SCHEMA_VERSION,
                    },
                    Ok,
                )
                .unwrap_or_else(|error| panic!("{antecedent} => {consequent} returned {error}"));
            let result = serde_json::to_value(result).unwrap();
            assert_eq!(result["status"], status, "{result:#}");
            assert_eq!(
                result["condition"]["predicate"]["term"]["tag"], predicate,
                "{result:#}"
            );
            assert_eq!(
                result["condition"]["substitution"]["term"]["tag"], "Top",
                "{result:#}"
            );
            assert_eq!(
                result["condition"]["witnesses"]["term"]["tag"], "Top",
                "{result:#}"
            );
        }

        for consequent in [bottom, top, regular] {
            let error = backend
                .implies_with(
                    ImplicationRequest {
                        antecedent: kore(top),
                        consequent: kore(consequent),
                        module_name: None,
                        schema_version: BACKEND_SCHEMA_VERSION,
                    },
                    Ok,
                )
                .expect_err("a top antecedent must be rejected");
            assert!(error.to_string().contains("function-like"), "{error}");
        }
    }

    #[test]
    fn persistent_backend_short_circuits_a_not_consequent() {
        let result = backend()
            .implies_with(
                ImplicationRequest {
                    antecedent: kore("a{}()"),
                    consequent: kore(r#"\not{SortS{}}(a{}())"#),
                    module_name: None,
                    schema_version: BACKEND_SCHEMA_VERSION,
                },
                Ok,
            )
            .unwrap();
        assert_eq!(result.status, "invalid");
        assert!(result.condition.is_none());
    }

    #[test]
    fn implies_rejects_internalized_sort_mismatch() {
        let error = backend()
            .implies_with(
                ImplicationRequest {
                    antecedent: kore("a{}()"),
                    consequent: kore("t{}()"),
                    module_name: None,
                    schema_version: BACKEND_SCHEMA_VERSION,
                },
                Ok,
            )
            .unwrap_err();
        // The sorts are named as KORE sorts, as the request wrote them.
        assert_eq!(
            error.to_string(),
            "antecedent and consequent sorts differ after internalization: SortS{} and SortT{}"
        );
    }

    #[test]
    fn persistent_implication_conditions_keep_bindings_separate() {
        use k_rust_backend::{
            implication::ImplicationCondition, substitution::Substitution, term::Variable,
        };

        let definition = backend().session.definition(None).unwrap();
        let sort = Sort::simple("SortS");
        let condition = ImplicationCondition {
            predicates: vec![Predicate::False],
            substitution: Substitution::from([(
                Variable::new("X", sort),
                definition
                    .admit_unverified(&parse_pattern("a{}()").unwrap(), &[])
                    .internalize_term()
                    .unwrap(),
            )]),
            witnesses: Substitution::from([(
                Variable::new("Y", sort),
                definition
                    .admit_unverified(&parse_pattern("b{}()").unwrap(), &[])
                    .internalize_term()
                    .unwrap(),
            )]),
        };

        let output = condition_pattern(&condition, &sort).unwrap();
        assert_eq!(output["predicate"]["term"]["tag"], "Bottom", "{output:#}");
        assert_eq!(
            output["substitution"]["term"]["tag"], "Equals",
            "{output:#}"
        );
        assert_eq!(
            output["substitution"]["term"]["first"]["name"], "X",
            "{output:#}"
        );
        assert_eq!(output["witnesses"]["term"]["tag"], "Equals", "{output:#}");
        assert_eq!(
            output["witnesses"]["term"]["first"]["name"], "Y",
            "{output:#}"
        );
    }

    #[test]
    fn persistent_implication_results_advertise_schema_version_two() {
        let result = backend()
            .implies_with(
                ImplicationRequest {
                    antecedent: kore("a{}()"),
                    consequent: kore("a{}()"),
                    module_name: None,
                    schema_version: BACKEND_SCHEMA_VERSION,
                },
                Ok,
            )
            .unwrap();
        let result = serde_json::to_value(result).unwrap();

        assert_eq!(result["schemaVersion"], 2, "{result:#}");
    }

    #[test]
    fn persistent_backend_names_and_structures_unsupported_hook_failures() {
        let state = kore(r#"missing{}(\dv{SortState{}}("value"))"#);
        let mut backend =
            Backend::new(UNSUPPORTED_HOOK_DEFINITION, "MAIN", BackendOptions::DEFAULT).unwrap();

        let execution = backend
            .execute_kore(ExecuteRequest::new(state.clone()))
            .unwrap();
        assert_eq!(
            execution.leaves[0].reason,
            HaltReasonOutput::UnsupportedHook
        );
        let encoded_execution = serde_json::to_value(&execution).unwrap();
        assert_eq!(encoded_execution["leaves"][0]["reason"], "unsupported-hook");
        assert!(
            execution.leaves[0]
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("TEST.missing")),
            "{:#?}",
            execution.leaves[0]
        );

        let search = backend.search_kore(SearchRequest::new(state)).unwrap();
        let encoded = serde_json::to_value(search).unwrap();
        let encoded = encoded.to_string();
        assert!(
            encoded.contains(r#""kind":"unsupported-hook""#),
            "{encoded}"
        );
        assert!(encoded.contains("TEST.missing"), "{encoded}");
    }

    #[test]
    fn persistent_backend_searches_states_and_reports_bounds() {
        let mut backend = backend();
        let result = backend
            .search_kore(SearchRequest::new(kore("a{}()")))
            .unwrap();
        assert_eq!(result.schema_version, BACKEND_SCHEMA_VERSION);
        assert_eq!(result.modality, ResultModalityOutput::StateSet);
        assert_eq!(result.states.len(), 1);
        assert_eq!(text(result.states[0].state.clone()), "c{}()");
        assert!(result.incomplete.is_empty());

        let bounded = backend
            .search_kore(SearchRequest {
                max_results: Some(0),
                ..SearchRequest::new(kore("a{}()"))
            })
            .unwrap();
        assert!(bounded.states.is_empty());
        assert_eq!(bounded.incomplete, [IncompleteSearchOutput::ResultBound]);
    }

    #[test]
    fn persistent_backend_searches_deterministic_path_witnesses() {
        let request = SearchRequest::new(kore("initial{}()"));
        let mut backend =
            Backend::new(DIAMOND_DEFINITION, "DIAMOND", BackendOptions::DEFAULT).unwrap();
        let first = backend.search_paths_kore(request.clone()).unwrap();
        let second = backend.search_paths_kore(request).unwrap();

        assert_eq!(first.modality, ResultModalityOutput::PathSet);
        assert_eq!(first.witnesses.len(), 2);
        assert_eq!(first.witnesses, second.witnesses);
        let paths = first
            .witnesses
            .iter()
            .map(|witness| {
                witness
                    .id
                    .iter()
                    .map(|transition| transition.rule.as_str())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert!(paths.contains(&vec!["initial-left", "left-merged"]));
        assert!(paths.contains(&vec!["initial-right", "right-merged"]));
    }

    #[test]
    fn persistent_backend_searches_patterns_in_both_modalities() {
        let mut backend = backend();
        let state_set = backend
            .search_pattern_kore(SearchPatternRequest::new(kore("a{}()"), kore("c{}()")))
            .unwrap();
        assert_eq!(state_set.modality, ResultModalityOutput::StateSet);
        assert_eq!(state_set.matches.len(), 1);
        assert_eq!(text(state_set.matches[0].state.state.clone()), "c{}()");

        let mut diamond =
            Backend::new(DIAMOND_DEFINITION, "DIAMOND", BackendOptions::DEFAULT).unwrap();
        let path_set = diamond
            .search_pattern_paths_kore(SearchPatternRequest::new(
                kore("initial{}()"),
                kore("merged{}()"),
            ))
            .unwrap();
        assert_eq!(path_set.modality, ResultModalityOutput::PathSet);
        assert_eq!(path_set.matches.len(), 2);
        assert!(
            path_set
                .matches
                .iter()
                .all(|found| found.witness.id.len() == 2)
        );
    }

    /// The target of a pattern search is internalized without the executable check, so it may
    /// apply an alias that drops a variable the client wrote. The search still mints no name
    /// spelled like it: the rule's existential `Y` is first minted `Ex#Y!0`, which is spelled
    /// `Ex-hY-b0` like the variable the target's `ignore` drops.
    #[test]
    fn pattern_searches_mint_apart_from_target_variables_an_alias_drops() {
        const DEFINITION: &str = r#"[]
module DROP
  sort S{} []
  symbol a{}() : S{} [constructor{}(), functional{}()]
  symbol c{}(S{}) : S{} [constructor{}(), functional{}()]
  symbol pair{}(S{}, S{}) : S{} [constructor{}(), functional{}()]
  alias ignore{}(S{}) : S{} where ignore{}(V:S{}) := a{}() []
  axiom{} \rewrites{S{}}(
    \and{S{}}(c{}(Z:S{}), \top{S{}}()),
    \and{S{}}(pair{}(Y:S{}, a{}()), \top{S{}}())
  ) [label{}("mint")]
endmodule []"#;
        let mut backend = Backend::new(DEFINITION, "DROP", BackendOptions::DEFAULT).unwrap();
        let request = SearchPatternRequest::new(
            kore("c{}(a{}())"),
            kore("pair{}(W:S{}, ignore{}(Ex-hY-b0:S{}))"),
        );
        let states =
            serde_json::to_string(&backend.search_pattern_kore(request.clone()).unwrap()).unwrap();
        let paths =
            serde_json::to_string(&backend.search_pattern_paths_kore(request).unwrap()).unwrap();
        for response in [states, paths] {
            assert!(response.contains("Ex-hY-b"), "{response}");
            assert!(!response.contains("Ex-hY-b0"), "{response}");
        }
    }

    #[test]
    fn observed_searches_expose_filtered_transition_streams_atomically() {
        let request = SearchRequest::new(kore("a{}()"));
        let mut backend = backend();
        let observed = backend
            .search_observed_kore(ObservedRequest {
                request: request.clone(),
                rules: Some(vec!["a-to-b".into()]),
            })
            .unwrap();
        assert_eq!(observed.states[0].branch.len(), 2);
        let [ObservationEventOutput::Transition { id, .. }] =
            observed.states[0].observations.as_slice()
        else {
            panic!("expected one filtered transition observation")
        };
        assert_eq!(id.rule, "a-to-b");

        let error = backend
            .search_observed_kore(ObservedRequest {
                request,
                rules: Some(vec!["a-to-b".into(), "missing".into()]),
            })
            .unwrap_err();
        assert!(
            error.to_string().contains("has the id 'missing'"),
            "{error}"
        );
    }

    #[test]
    fn execute_preserves_effects_and_observed_execution_attributes_them() {
        let request = ExecuteRequest::new(kore(r#"log{}(\dv{SortString{}}("one line"))"#));
        let mut backend = Backend::new(LOG_DEFINITION, "MAIN", BackendOptions::DEFAULT).unwrap();
        let ordinary = backend.execute_kore(request.clone()).unwrap();
        assert_eq!(
            ordinary.effects,
            [EffectOutput::UserLog {
                message: "one line".into()
            }]
        );
        assert_eq!(ordinary.leaves.len(), 1);
        assert_eq!(ordinary.leaves[0].effects, ordinary.effects);
        assert!(ordinary.leaves[0].observations.is_empty());

        let observed = backend
            .execute_observed_kore(ObservedRequest {
                request,
                rules: None,
            })
            .unwrap();
        let [
            ObservationEventOutput::Evaluation {
                rule,
                class,
                anchor,
                effects,
                ..
            },
        ] = observed.leaves[0].observations.as_slice()
        else {
            panic!("expected one builtin evaluation observation")
        };
        assert_eq!(rule, "builtin:IO.logString");
        assert_eq!(*class, EvaluationClassOutput::Builtin);
        assert_eq!(*anchor, 0);
        assert_eq!(effects, &ordinary.effects);
        assert_eq!(observed.leaves[0].effects, ordinary.leaves[0].effects);
    }

    #[test]
    fn execute_exposes_each_branches_effects_without_observation() {
        let request = ExecuteRequest::new(kore("initial{}()"));
        let mut backend =
            Backend::new(EFFECTFUL_BRANCH_DEFINITION, "MAIN", BackendOptions::DEFAULT).unwrap();
        let ordinary = backend.execute_kore(request.clone()).unwrap();
        assert_eq!(ordinary.leaves.len(), 2);
        assert!(ordinary.effects.is_empty());
        assert!(
            ordinary
                .leaves
                .iter()
                .all(|leaf| leaf.observations.is_empty())
        );
        let branch_effects = |result: &KoreExecutionResult| {
            let mut effects = result
                .leaves
                .iter()
                .map(|leaf| (leaf.trace[0].label.clone().unwrap(), leaf.effects.clone()))
                .collect::<Vec<_>>();
            effects.sort_by(|left, right| left.0.cmp(&right.0));
            effects
        };
        assert_eq!(
            branch_effects(&ordinary),
            [
                (
                    "left".into(),
                    vec![EffectOutput::UserLog {
                        message: "left".into()
                    }]
                ),
                (
                    "right".into(),
                    vec![EffectOutput::UserLog {
                        message: "right".into()
                    }]
                ),
            ]
        );

        let observed = backend
            .execute_observed_kore(ObservedRequest {
                request,
                rules: None,
            })
            .unwrap();
        assert_eq!(branch_effects(&observed), branch_effects(&ordinary));
        assert!(observed.effects.is_empty());
    }

    #[test]
    fn observation_preserves_facade_leaves_order_and_filter_independent_identities() {
        let mut backend = Backend::new(
            OBSERVATION_ERASURE_DEFINITION,
            "MAIN",
            BackendOptions::DEFAULT,
        )
        .unwrap();
        let erase = |mut result: KoreExecutionResult| {
            for leaf in &mut result.leaves {
                leaf.branch.clear();
                leaf.observations.clear();
            }
            serde_json::to_value(result).unwrap()
        };

        for (modality, expected_leaves) in [
            (ResultModalityOutput::StateSet, 1),
            (ResultModalityOutput::PathSet, 2),
        ] {
            let request = ExecuteRequest {
                result_modality: modality,
                ..ExecuteRequest::new(kore("initial{}()"))
            };
            let plain = backend.execute_kore(request.clone()).unwrap();
            let all = backend
                .execute_observed_kore(ObservedRequest {
                    request: request.clone(),
                    rules: None,
                })
                .unwrap();
            let selected = backend
                .execute_observed_kore(ObservedRequest {
                    request: request.clone(),
                    rules: Some(vec!["left".into()]),
                })
                .unwrap();
            let none = backend
                .execute_observed_kore(ObservedRequest {
                    request,
                    rules: Some(vec![]),
                })
                .unwrap();

            assert_eq!(plain.leaves.len(), expected_leaves, "{modality:?}");
            assert!(plain.leaves.iter().all(|leaf| leaf.branch.is_empty()));
            assert!(plain.leaves.iter().all(|leaf| leaf.observations.is_empty()));
            assert!(plain.leaves.iter().all(|leaf| leaf.effects
                == [EffectOutput::UserLog {
                    message: "same".into(),
                }]));
            let expected = erase(plain);
            for observed in [&all, &selected, &none] {
                assert_eq!(erase(observed.clone()), expected, "{modality:?}");
                assert_eq!(
                    observed
                        .leaves
                        .iter()
                        .map(|leaf| &leaf.branch)
                        .collect::<Vec<_>>(),
                    all.leaves
                        .iter()
                        .map(|leaf| &leaf.branch)
                        .collect::<Vec<_>>(),
                    "{modality:?}"
                );
            }
            assert!(
                all.leaves
                    .iter()
                    .all(|leaf| leaf.depth > 0 && !leaf.branch.is_empty())
            );
            assert!(all.leaves.iter().any(|leaf| !leaf.observations.is_empty()));
            assert!(none.leaves.iter().all(|leaf| leaf.observations.is_empty()));
        }
    }

    #[test]
    fn observed_path_set_execution_keeps_converging_paths_apart() {
        let request = |modality: &str| {
            serde_json::from_value::<ExecuteRequest>(serde_json::json!({
                "state": json("initial{}()"),
                "resultModality": modality,
            }))
            .unwrap()
        };
        let labels = |leaf: &KoreExecutionLeaf| {
            leaf.observations
                .iter()
                .filter_map(|event| match event {
                    ObservationEventOutput::Transition { rule_label, .. } => rule_label.clone(),
                    _ => None,
                })
                .collect::<Vec<_>>()
        };
        let mut backend =
            Backend::new(DIAMOND_DEFINITION, "DIAMOND", BackendOptions::DEFAULT).unwrap();

        let state_set = backend
            .execute_observed_kore(ObservedRequest {
                request: request("state-set"),
                rules: None,
            })
            .unwrap();
        assert_eq!(state_set.modality, ResultModalityOutput::StateSet);
        assert_eq!(state_set.leaves.len(), 1);
        assert_eq!(
            serde_json::to_value(&state_set).unwrap()["modality"],
            "state-set"
        );

        let path_set = backend
            .execute_observed_kore(ObservedRequest {
                request: request("path-set"),
                rules: None,
            })
            .unwrap();
        assert_eq!(path_set.modality, ResultModalityOutput::PathSet);
        assert_eq!(
            serde_json::to_value(&path_set).unwrap()["modality"],
            "path-set"
        );
        let [left, right] = path_set.leaves.as_slice() else {
            panic!("expected one leaf per path: {:#?}", path_set.leaves);
        };
        for leaf in [left, right] {
            assert_eq!(text(leaf.state.clone()), "merged{}()");
            // Compared on the wire so the check is independent of the Rust type of `reason`.
            assert_eq!(serde_json::to_value(leaf).unwrap()["reason"], "stuck");
        }
        assert_ne!(left.branch, right.branch);
        assert_eq!(labels(left), ["initial-left", "left-merged"]);
        assert_eq!(labels(right), ["initial-right", "right-merged"]);

        let default = backend
            .execute_kore(ExecuteRequest::new(kore("initial{}()")))
            .unwrap();
        assert_eq!(default.modality, ResultModalityOutput::StateSet);
        assert_eq!(default.leaves.len(), 1);
    }

    #[test]
    fn observed_execution_anchors_a_successor_evaluation_after_its_rewrite() {
        const EVALUATING_DEFINITION: &str = r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                sort SortState{} []
                symbol start{}() : SortState{} [constructor{}()]
                symbol next{}(SortS{}) : SortState{} [constructor{}()]
                symbol value{}() : SortS{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \top{R}()),
                    \equals{SortS{}, R}(
                        value{}(),
                        \and{SortS{}}(\dv{SortS{}}("value"), \top{SortS{}}())
                    )
                ) [label{}("value-equation")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(start{}(), \top{SortState{}}()),
                    next{}(value{}())
                ) [label{}("step")]
            endmodule []"#;
        let mut backend =
            Backend::new(EVALUATING_DEFINITION, "MAIN", BackendOptions::DEFAULT).unwrap();
        let request = ExecuteRequest::new(kore("start{}()"));
        let ordinary = backend.execute_kore(request.clone()).unwrap();

        let observed = backend
            .execute_observed_kore(ObservedRequest {
                request,
                rules: None,
            })
            .unwrap();
        let [leaf] = observed.leaves.as_slice() else {
            panic!("expected one leaf")
        };
        let [
            ObservationEventOutput::Transition { id, class, .. },
            ObservationEventOutput::Evaluation {
                rule,
                class: evaluation_class,
                rule_label,
                anchor,
                after,
                ..
            },
        ] = leaf.observations.as_slice()
        else {
            panic!("expected a rewrite then its successor's evaluation: {leaf:?}")
        };
        assert_eq!(leaf.branch.as_slice(), std::slice::from_ref(id));
        assert_eq!(id.rule, "step");
        assert_eq!(*class, TransitionClassOutput::Rewrite);
        assert_eq!(rule, "value-equation");
        assert_eq!(*evaluation_class, EvaluationClassOutput::FunctionEquation);
        assert_eq!(rule_label.as_deref(), Some("value-equation"));
        assert_eq!(*anchor, 1);
        assert_eq!(text(after.clone()), r#"next{}(\dv{SortS{}}("value"))"#);
        assert_eq!(
            text(leaf.state.clone()),
            text(ordinary.leaves[0].state.clone())
        );

        let wire = serde_json::to_value(&leaf.observations[1]).unwrap();
        assert_eq!(wire["kind"], "evaluation");
        assert_eq!(wire["class"], "function-equation");
        assert_eq!(wire["ruleLabel"], "value-equation");
        assert_eq!(wire["anchor"], 1);
        assert_eq!(
            serde_json::to_value(
                serde_json::from_value::<ObservationEventOutput>(wire.clone()).unwrap()
            )
            .unwrap(),
            wire
        );
    }

    #[test]
    fn observed_execution_selects_function_equation_without_its_rewrite() {
        const DEFINITION: &str = r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                sort SortBool{} [hasDomainValues{}()]
                sort SortState{} []
                symbol start{}() : SortState{} [constructor{}()]
                symbol done{}(SortBool{}) : SortState{} [constructor{}()]
                symbol isZero{}(SortS{}) : SortBool{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortS{}, R}(Z:SortS{}, \dv{SortS{}}("z")),
                            \top{R}()
                        )
                    ),
                    \equals{SortBool{}, R}(
                        isZero{}(Z:SortS{}),
                        \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}())
                    )
                ) [label{}("is-zero-z")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(start{}(), \top{SortState{}}()),
                    done{}(isZero{}(\dv{SortS{}}("z")))
                ) [label{}("step")]
            endmodule []"#;
        let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::DEFAULT).unwrap();
        let request = ExecuteRequest::new(kore("start{}()"));
        let selected = backend
            .execute_observed_kore(ObservedRequest {
                request: request.clone(),
                rules: Some(vec!["is-zero-z".into()]),
            })
            .unwrap();
        let [leaf] = selected.leaves.as_slice() else {
            panic!("expected one leaf: {selected:?}");
        };
        assert_eq!(leaf.branch.len(), 1);
        assert_eq!(leaf.branch[0].rule, "step");
        let [
            ObservationEventOutput::Evaluation {
                rule,
                class,
                anchor,
                ..
            },
        ] = leaf.observations.as_slice()
        else {
            panic!("expected only the selected equation: {leaf:?}");
        };
        assert_eq!(rule, "is-zero-z");
        assert_eq!(*class, EvaluationClassOutput::FunctionEquation);
        assert_eq!(*anchor, 1);
        assert_eq!(
            text(leaf.state.clone()),
            r#"done{}(\dv{SortBool{}}("true"))"#
        );

        let selected = backend
            .execute_observed_kore(ObservedRequest {
                request,
                rules: Some(vec!["step".into(), "is-zero-z".into()]),
            })
            .unwrap();
        assert!(matches!(
            selected.leaves[0].observations.as_slice(),
            [
                ObservationEventOutput::Transition { .. },
                ObservationEventOutput::Evaluation { .. }
            ]
        ));
    }

    /// Two written copies of one rule, in the shape K-in-K2's `duplicate_unlabelled.k` fixture has.
    const DUPLICATE_UNLABELLED: &str = "module DUPLICATE_UNLABELLED-SYNTAX
  syntax S ::= \"x\" [symbol(x)]
             | \"y\" [symbol(y)]
endmodule

module DUPLICATE_UNLABELLED
  imports DUPLICATE_UNLABELLED-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule x => y
  rule x => y
endmodule
";

    /// `<k> x </k>` in the generated configuration of [`DUPLICATE_UNLABELLED`].
    const DUPLICATE_UNLABELLED_STATE: &str = r#"Lbl'-LT-'generatedTop'-GT-'{}(
        Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortS{}, SortKItem{}}(Lblx{}()), dotk{}())),
        Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))
    )"#;

    /// The source-compiled execution definition, internalized as `krust krun` does.
    fn source_definition(source: &str, module: &str) -> BackendDefinition {
        use crate::{
            builtin::embedded,
            kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
            outer::{LoadOptions, ResolvedSource, load_with_options},
        };

        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("duplicate.k", source),
            module,
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .unwrap();
        let compiled = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
        let syntax = parse_definition(&compiled.definition_kore).unwrap();
        // The main module is emitted last, under its KORE-encoded name.
        let main_module = syntax.modules.last().unwrap().name.clone();
        Backend::internalize_source_definition(
            &syntax,
            &main_module,
            &compiled.execution_rewrite_order,
        )
        .unwrap()
    }

    /// The `UNIQUE_ID` and origin locations of the rewrite rule whose first origin is on `line`.
    fn rule_on_line(definition: &BackendDefinition, line: usize) -> (String, Vec<String>) {
        let prefix = format!("Location({line},");
        let rules = definition
            .rewrite_theory()
            .values()
            .flat_map(|priorities| priorities.values())
            .flatten()
            .filter(|stored| {
                stored.rule.attributes.origins[0]
                    .location
                    .as_deref()
                    .is_some_and(|location| location.starts_with(&prefix))
            })
            .collect::<Vec<_>>();
        let [stored] = rules.as_slice() else {
            panic!("expected one stored rule written on line {line}: {rules:?}");
        };
        let attributes = &stored.rule.attributes;
        (
            attributes.unique_id.clone(),
            attributes
                .origins
                .iter()
                .map(|origin| origin.location.clone().unwrap())
                .collect(),
        )
    }

    #[test]
    fn source_duplicated_rule_executes_and_is_observed_as_one_rule() {
        let single_source = DUPLICATE_UNLABELLED.replacen("  rule x => y\n", "", 1);
        let single = source_definition(&single_source, "DUPLICATE_UNLABELLED");
        let duplicated = source_definition(DUPLICATE_UNLABELLED, "DUPLICATE_UNLABELLED");

        let (single_id, single_origins) = rule_on_line(&single, 12);
        let (id, origins) = rule_on_line(&duplicated, 12);
        assert_eq!(single_origins, ["Location(12,3,12,14)"]);
        assert_eq!(origins, ["Location(12,3,12,14)", "Location(13,3,13,14)"]);
        assert_eq!(id, single_id);

        let request = ExecuteRequest {
            stop_at_branch: true,
            ..ExecuteRequest::new(kore(DUPLICATE_UNLABELLED_STATE))
        };
        let mut outcomes = Vec::new();
        for definition in [single, duplicated] {
            let mut backend =
                Backend::from_internalized(definition, BackendOptions::DEFAULT).expect("backend");
            let result = backend.execute_kore(request.clone()).unwrap();
            let [leaf] = result.leaves.as_slice() else {
                panic!("expected one leaf: {:?}", result.leaves);
            };
            assert_ne!(leaf.reason, HaltReasonOutput::Branch);
            assert!(text(leaf.state.clone()).contains("Lbly{}()"));
            assert_eq!(leaf.depth, 1);

            let observed = backend
                .execute_observed_kore(ObservedRequest {
                    request: request.clone(),
                    rules: Some(vec![id.clone()]),
                })
                .unwrap();
            let [observed_leaf] = observed.leaves.as_slice() else {
                panic!("expected one observed leaf: {:?}", observed.leaves);
            };
            let [ObservationEventOutput::Transition { id: transition, .. }] =
                observed_leaf.observations.as_slice()
            else {
                panic!(
                    "expected one rule application: {:?}",
                    observed_leaf.observations
                );
            };
            assert_eq!(transition.rule, id);
            outcomes.push((
                text(leaf.state.clone()),
                leaf.reason,
                serde_json::to_value(&observed_leaf.observations).unwrap(),
            ));
        }
        assert_eq!(outcomes[0], outcomes[1]);
    }

    #[test]
    fn capabilities_advertise_search_and_observation() {
        let capabilities = backend().capabilities();
        assert!(capabilities.search);
        assert!(capabilities.observation);
    }

    #[test]
    fn prove_request_budget_reaches_the_prover() {
        let mut chain = String::new();
        for index in 0..=128 {
            chain.push_str(&format!(
                "symbol chain{index}{{}}() : SortS{{}} [function{{}}()]\n"
            ));
        }
        for index in 0..128 {
            let next = index + 1;
            chain.push_str(&format!(
                r#"
                axiom{{R}} \implies{{R}}(
                    \top{{R}}(),
                    \equals{{SortS{{}}, R}}(
                        chain{index}{{}}(),
                        \and{{SortS{{}}}}(chain{next}{{}}(), \top{{SortS{{}}}}())
                    )
                ) [label{{}}("chain-{index}"), simplification{{}}()]
                "#
            ));
        }
        chain.push_str(
            r#"
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortS{}, R}(
                        chain128{}(),
                        \and{SortS{}}(a{}(), \top{SortS{}}())
                    )
                ) [label{}("chain-done"), simplification{}()]
            "#,
        );
        let definition = format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                symbol a{{}}() : SortS{{}} [constructor{{}}()]
                symbol c{{}}() : SortS{{}} [constructor{{}}()]
                alias weakAlwaysFinally{{S}}(S) : S
                    where weakAlwaysFinally{{S}}(@X:S) := @X:S []
                {chain}
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(
                        a{{}}(),
                        \equals{{SortS{{}}, SortS{{}}}}(chain0{{}}(), a{{}}())
                    ),
                    c{{}}()
                ) [label{{}}("conditional")]
                claim{{}} \implies{{SortS{{}}}}(
                    \and{{SortS{{}}}}(a{{}}(), \top{{SortS{{}}}}()),
                    weakAlwaysFinally{{SortS{{}}}}(c{{}}())
                ) [label{{}}("budgeted-claim")]
            endmodule []"#
        );
        let mut backend = Backend::new(&definition, "MAIN", BackendOptions::DEFAULT).unwrap();

        let result = backend
            .prove_kore(ProveRequest {
                max_simplification_iterations: 1,
                ..ProveRequest::default()
            })
            .expect("budget exhaustion should be represented as a proof result");

        // Without SMT, an exhausted side condition remains indeterminate; with the native
        // solver the leaf is stuck, but its constraint holds the unevaluated `chain0()`, so it
        // fails the claim without certifying a refutation. Neither may establish the claim.
        assert!(
            matches!(result.status.as_str(), "failed" | "indeterminate"),
            "{result:#?}"
        );
        // The exhausted budget leaves the side condition undecided; it is not a failure of the
        // simplification of the state.
        for leaf in &result.leaves {
            match leaf.outcome {
                ProofLeafOutcomeOutput::Proven | ProofLeafOutcomeOutput::Stuck => {}
                ProofLeafOutcomeOutput::Indeterminate => assert!(
                    leaf.detail.as_deref().is_some_and(|detail| detail
                        .starts_with("the requires clause of rule conditional is undecided")),
                    "{result:#?}"
                ),
                _ => panic!("{result:#?}"),
            }
        }
        let completed = backend
            .prove_kore(ProveRequest {
                max_simplification_iterations: 256,
                ..ProveRequest::default()
            })
            .unwrap();
        assert_eq!(completed.status, "proven", "{completed:#?}");
    }

    #[test]
    fn added_modules_are_available_to_later_calls() {
        let mut backend = backend();
        let module = r#"module EXTRA
            import MAIN []
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(c{}(), \top{SortS{}}()),
                \and{SortS{}}(a{}(), \top{SortS{}}())
            ) [label{}("c-to-a")]
        endmodule []"#;
        backend.add_module(module, true).unwrap();
        let execution = backend
            .execute_kore(ExecuteRequest {
                module_name: Some("EXTRA".into()),
                max_depth: Some(1),
                ..ExecuteRequest::new(kore("c{}()"))
            })
            .unwrap();
        assert_eq!(text(execution.leaves[0].state.clone()), "a{}()");
    }

    /// KORE JSON terms `levels` deep that decode but are not patterns of the definition: a `\not`
    /// chain whose leaf applies an undeclared symbol, a chain of an undeclared symbol, and a
    /// domain value at a deep undeclared sort.
    fn deep_invalid_kore_json(levels: usize) -> [String; 3] {
        let sort = r#"{"tag":"SortApp","name":"SortS","args":[]}"#;
        let undefined = r#"{"tag":"App","name":"undefined","sorts":[],"args":[]}"#;
        let constant = r#"{"tag":"App","name":"a","sorts":[],"args":[]}"#;
        let term = |prefix: &str, leaf: &str, suffix: &str| {
            format!(
                r#"{{"format":"KORE","version":1,"term":{}{leaf}{}}}"#,
                prefix.repeat(levels),
                suffix.repeat(levels)
            )
        };
        let deep_sort = format!(
            "{}{sort}{}",
            r#"{"tag":"SortApp","name":"SortMissing","args":["#.repeat(levels),
            "]}".repeat(levels)
        );
        [
            term(
                &format!(r#"{{"tag":"Not","sort":{sort},"arg":"#),
                undefined,
                "}",
            ),
            term(
                r#"{"tag":"App","name":"nosuch","sorts":[],"args":["#,
                constant,
                "]}",
            ),
            format!(
                r#"{{"format":"KORE","version":1,"term":{{"tag":"DV","sort":{deep_sort},"value":"1"}}}}"#
            ),
        ]
    }

    /// The stack of Node's main thread, which the Node-API binding runs the facade on.
    const NODE_MAIN_STACK: usize = 8 << 20;

    /// Levels beyond what `NODE_MAIN_STACK` holds for the facade's passes in either build: a
    /// state of applications overflows such a thread at about 600 levels unoptimized (opt-level
    /// 0, the `debugging` profile) and 8,000 in a release build when the passes run on it
    /// directly.
    const BEYOND_THE_THREAD: usize = 10_000;

    fn on_thread<R: Send + 'static>(stack: usize, work: impl FnOnce() -> R + Send + 'static) -> R {
        std::thread::Builder::new()
            .stack_size(stack)
            .spawn(work)
            .expect("worker should spawn")
            .join()
            .expect("worker should finish")
    }

    /// Every route of the facade that the Node-API and WebAssembly hosts call, run on `deep`,
    /// each with a shallow pattern where the route takes two.
    fn every_route(backend: &mut Backend, deep: &KorePattern) -> Vec<Result<(), BackendError>> {
        let shallow = kore("a{}()");
        let routes = vec![
            backend
                .execute_json(ExecuteRequest {
                    max_depth: Some(0),
                    ..ExecuteRequest::new(deep.clone())
                })
                .map(drop),
            backend
                .search_json(SearchRequest::new(deep.clone()))
                .map(drop),
            backend
                .search_pattern_json(SearchPatternRequest::new(deep.clone(), shallow.clone()))
                .map(drop),
            backend
                .search_pattern_json(SearchPatternRequest::new(shallow.clone(), deep.clone()))
                .map(drop),
            backend
                .simplify_json(PatternRequest::new(deep.clone()))
                .map(drop),
            backend
                .implies_json(ImplicationRequest::new(deep.clone(), shallow.clone()))
                .map(drop),
            backend
                .implies_json(ImplicationRequest::new(shallow, deep.clone()))
                .map(drop),
        ];
        // Without Z3, model generation reports its capability boundary before it reads the
        // pattern.
        #[cfg(feature = "z3-inference")]
        let routes = routes
            .into_iter()
            .chain([backend
                .get_model_json(PatternRequest::new(deep.clone()))
                .map(drop)])
            .collect();
        routes
    }

    /// A request beyond what Node's main thread holds that decodes but is not a pattern of the
    /// definition is answered on every route of the facade as a shallow one is, with the
    /// ordinary error its fault calls for where the route reads the fault, never with a refusal
    /// for want of stack: the backend provides the stack its passes need. One
    /// 10,000-level term is held at a time; unoptimized (opt-level 0, the `debugging` profile)
    /// each request touches about 120 MB of stack, and the test takes a few seconds.
    #[test]
    fn deep_invalid_requests_are_ordinary_errors_on_every_route() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend = backend();
            for (term, deep) in deep_invalid_kore_json(BEYOND_THE_THREAD).iter().enumerate() {
                let deep = deserialize_request::<PatternRequest>(&format!(r#"{{"state":{deep}}}"#))
                    .unwrap()
                    .state;
                let outcomes = every_route(&mut backend, &deep);
                assert!(outcomes[0].is_err(), "term {term} executes");
                for (route, outcome) in outcomes.into_iter().enumerate() {
                    if let Err(error) = outcome {
                        assert!(
                            !error
                                .to_string()
                                .contains("the backend provides for one operation"),
                            "term {term} route {route}: {error}"
                        );
                    }
                }
            }
            // The backend still serves ordinary requests.
            let execution = backend
                .execute_kore(ExecuteRequest::new(kore("a{}()")))
                .unwrap();
            assert_eq!(text(execution.leaves[0].state.clone()), "c{}()");
        });
    }

    /// A request deeper than the largest stack the backend provides is refused with
    /// `InsufficientStack` on every route before any pass over it runs. One term that deep (about
    /// 700,000 levels at opt-level 1, a million in a release build, 175,000 unoptimized) is held
    /// at a time; at opt-level 1 the test peaks at about 930 MB of resident memory and takes about
    /// 8 s.
    #[test]
    fn requests_deeper_than_the_backend_provides_for_are_refused() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend = backend();
            for deep in deep_invalid_kore_json(k_rust_backend::nesting::max_depth() + 1) {
                let deep = deserialize_request::<PatternRequest>(&format!(r#"{{"state":{deep}}}"#))
                    .unwrap()
                    .state;
                for error in every_route(&mut backend, &deep) {
                    let error = error.expect_err("a request too deep is refused");
                    assert_eq!(
                        error.kind(),
                        Some(BackendErrorKind::InsufficientStack),
                        "{error}"
                    );
                    assert!(
                        error
                            .to_string()
                            .contains("the backend provides for one operation"),
                        "{error}"
                    );
                }
            }
            let execution = backend
                .execute_kore(ExecuteRequest::new(kore("a{}()")))
                .unwrap();
            assert_eq!(text(execution.leaves[0].state.clone()), "c{}()");
        });
    }

    /// A module whose axiom is a `\not` chain beyond what Node's main thread holds is added
    /// when the chain is a well-formed predicate and is the ordinary error of its fault when it
    /// is over a symbol the definition does not declare; a chain deeper than the backend
    /// provides for is refused with `InsufficientStack`. One module of up to about 10 MB of text
    /// is held at a time; at opt-level 1 the test peaks at about 450 MB of resident memory and
    /// takes a few seconds.
    #[test]
    fn deep_modules_are_loaded_or_ordinary_errors() {
        on_thread(NODE_MAIN_STACK, || {
            let module = |levels: usize, leaf: &str| {
                let condition = format!(
                    "{}{leaf}{}",
                    r"\not{SortS{}}(".repeat(levels),
                    ")".repeat(levels)
                );
                format!(
                    r"module EXTRA import MAIN []
                        axiom{{}} \rewrites{{SortS{{}}}}(
                            \and{{SortS{{}}}}(c{{}}(), {condition}),
                            \and{{SortS{{}}}}(a{{}}(), \top{{SortS{{}}}}())
                        ) []
                    endmodule []"
                )
            };
            let mut backend = backend();
            let too_deep = k_rust_backend::nesting::max_depth() + 1;
            for (levels, leaf, refused) in [
                (BEYOND_THE_THREAD, "undefined{}()", false),
                (too_deep, "undefined{}()", true),
                (too_deep, r"\top{SortS{}}()", true),
            ] {
                let error = backend
                    .add_module(&module(levels, leaf), false)
                    .unwrap_err();
                assert_eq!(
                    error
                        .to_string()
                        .contains("the backend provides for one operation"),
                    refused,
                    "{error}"
                );
            }
            let id = backend
                .add_module(&module(BEYOND_THE_THREAD, r"\top{SortS{}}()"), false)
                .expect("a deep well-formed module is added");
            // An operation in the extended definition runs on the stack its deep rule needs.
            let execution = backend
                .execute_kore(ExecuteRequest {
                    module_name: Some(id),
                    max_depth: Some(1),
                    ..ExecuteRequest::new(kore("c{}()"))
                })
                .unwrap();
            assert_eq!(text(execution.leaves[0].state.clone()), "a{}()");
            let execution = backend
                .execute_kore(ExecuteRequest::new(kore("a{}()")))
                .unwrap();
            assert_eq!(text(execution.leaves[0].state.clone()), "c{}()");
        });
    }

    /// A definition whose rule `step` adds one `wrap` level under `go` each step.
    const DEEP_DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            symbol a{}() : SortS{} [constructor{}(), functional{}()]
            symbol wrap{}(SortS{}) : SortS{} [constructor{}(), functional{}()]
            symbol go{}(SortS{}) : SortS{} [constructor{}(), functional{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(go{}(X:SortS{}), \top{SortS{}}()),
                \and{SortS{}}(go{}(wrap{}(X:SortS{})), \top{SortS{}}())
            ) [label{}("step")]
        endmodule []"#;

    /// KORE JSON for `go` over `levels` applications of `wrap` over `a`, or the `wrap` chain
    /// alone.
    fn wrap_json(levels: usize, go: bool) -> String {
        let wrap = r#"{"tag":"App","name":"wrap","sorts":[],"args":["#;
        let leaf = r#"{"tag":"App","name":"a","sorts":[],"args":[]}"#;
        let chain = format!("{}{leaf}{}", wrap.repeat(levels), "]}".repeat(levels));
        let term = if go {
            format!(r#"{{"tag":"App","name":"go","sorts":[],"args":[{chain}]}}"#)
        } else {
            chain
        };
        format!(r#"{{"format":"KORE","version":1,"term":{term}}}"#)
    }

    /// Whether two KORE JSON texts denote the same pattern, compared without printing them.
    fn same_kore(left: &str, right: &str) -> bool {
        k_rust_kore::kore::json::from_str(left).unwrap()
            == k_rust_kore::kore::json::from_str(right).unwrap()
    }

    /// The states of the leaves of an execution response, as the KORE JSON text they carry.
    fn leaf_states(response: &str) -> Vec<String> {
        #[derive(Deserialize)]
        struct Response {
            leaves: Vec<Leaf>,
        }
        #[derive(Deserialize)]
        struct Leaf {
            state: Box<RawValue>,
        }
        serde_json::from_str::<Response>(response)
            .unwrap()
            .leaves
            .into_iter()
            .map(|leaf| leaf.state.get().to_owned())
            .collect()
    }

    /// A state of 6,000 applications, which ran on Node's main thread when the passes ran on
    /// the thread directly in a release build, still executes there: the backend provides the
    /// stack measured for it instead of refusing it. Unoptimized (opt-level 0, the `debugging`
    /// profile) the request touches about 70 MB of stack and takes well under a second.
    #[test]
    fn a_deep_state_executes_on_node_s_main_thread() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend =
                Backend::new(DEEP_DEFINITION, "MAIN", BackendOptions::DEFAULT).unwrap();
            let request = deserialize_request::<ExecuteRequest>(&format!(
                r#"{{"state":{},"maxDepth":0}}"#,
                wrap_json(6_000, false)
            ))
            .unwrap();
            let response = backend.execute_json(request).unwrap();
            let [state] = leaf_states(&response).try_into().unwrap();
            assert!(same_kore(&state, &wrap_json(6_000, false)));
        });
    }

    /// The state an execution returns is accepted as the next request's state: `go` over 1,900
    /// applications steps 300 times on Node's main thread, and its 2,200-level result steps
    /// again from there.
    #[test]
    fn a_returned_state_is_accepted_again() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend =
                Backend::new(DEEP_DEFINITION, "MAIN", BackendOptions::DEFAULT).unwrap();
            let mut state = wrap_json(1_900, true);
            for levels in [2_200, 2_500] {
                let request = deserialize_request::<ExecuteRequest>(&format!(
                    r#"{{"state":{state},"maxDepth":300}}"#
                ))
                .unwrap();
                let [leaf] = leaf_states(&backend.execute_json(request).unwrap())
                    .try_into()
                    .unwrap();
                assert!(same_kore(&leaf, &wrap_json(levels, true)), "{levels}");
                state = leaf;
            }
        });
    }

    /// `DEEP_DEFINITION` with the claim `deep`, that `go` over `levels` applications of `wrap`
    /// over `a` always reaches `a`.
    fn deep_claim_definition(levels: usize) -> String {
        let chain = format!(
            "go{{}}({}a{{}}(){})",
            "wrap{}(".repeat(levels),
            ")".repeat(levels)
        );
        DEEP_DEFINITION.replace(
            "endmodule []",
            &format!(
                r#"alias weakAlwaysFinally{{S}}(S) : S
                    where weakAlwaysFinally{{S}}(@X:S) := @X:S []
                claim{{}} \implies{{SortS{{}}}}(
                    \and{{SortS{{}}}}({chain}, \top{{SortS{{}}}}()),
                    weakAlwaysFinally{{SortS{{}}}}(a{{}}())
                ) [label{{}}("deep")]
            endmodule []"#
            ),
        )
    }

    /// A caller's stack on which a proof result held as a `serde_json::Value` overflows when it is
    /// serialized there from about 800 levels of its leaf (the `dev` profile, opt-level 1), while
    /// `prove_json` completes on it at 2,000.
    const SMALL_STACK: usize = 256 << 10;

    /// Levels of a proof's leaf beyond what `SMALL_STACK` holds for the leaf as a value.
    const DEEP_PROOF_LEVELS: usize = 2_000;

    /// A proof whose leaf is 2,000 levels deep is written as text by `prove_json` on a 256 KiB
    /// thread: the operation writes the leaf's KORE inside the stack it provides, and the
    /// caller receives text it can drop on any thread. The test takes well under a second.
    #[test]
    fn a_deep_proof_result_is_written_inside_the_operation() {
        let definition = deep_claim_definition(DEEP_PROOF_LEVELS);
        let response = on_thread(SMALL_STACK, move || {
            let mut backend = Backend::new(&definition, "MAIN", BackendOptions::DEFAULT).unwrap();
            backend
                .prove_json(ProveRequest {
                    max_depth: Some(1),
                    ..ProveRequest::default()
                })
                .unwrap()
        });
        let [leaf] = leaf_states(&response).try_into().unwrap();
        assert!(same_kore(&leaf, &wrap_json(DEEP_PROOF_LEVELS + 1, true)));
    }

    /// `prove_json` writes the result `prove_kore` returns.
    #[test]
    fn prove_json_writes_the_proof_result() {
        let mut backend =
            Backend::new(&deep_claim_definition(3), "MAIN", BackendOptions::DEFAULT).unwrap();
        let request = ProveRequest {
            max_depth: Some(1),
            ..ProveRequest::default()
        };
        let text = backend.prove_json(request.clone()).unwrap();
        let value = backend.prove_kore(request).unwrap();
        let json = serde_json::from_str::<Value>(&text).unwrap();
        assert_eq!(json, serde_json::to_value(&value).unwrap());
        assert_eq!(value.leaves.len(), 1, "{value:#?}");
        assert_eq!(json["leaves"][0]["outcome"], "depth-bound", "{json:#}");
        assert!(json["leaves"][0].get("detail").is_none(), "{json:#}");
    }

    /// An n-ary `\and` of term arguments is internalized as a chain of `n - 1` binary
    /// conjunctions nested to the right, and a request may nest binary ones to the left, so a
    /// wide request is deep inside the backend: 50,000 conjuncts execute on Node's main thread,
    /// and 200,000 execute as well where the backend provides the stack for them (an optimized
    /// build) and are otherwise refused, never overflowing the thread. A chain of one conjunct
    /// owes no definedness obligation in either nesting (`definedness::and_side` relates first
    /// conjuncts). The requests take 10 to 25 MB of text each; at opt-level 1 the test peaks at
    /// about 500 MB of resident memory and takes about two seconds.
    #[test]
    fn wide_conjunctions_execute_or_are_refused() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend =
                Backend::new(DEEP_DEFINITION, "MAIN", BackendOptions::DEFAULT).unwrap();
            let constant = r#"{"tag":"App","name":"a","sorts":[],"args":[]}"#;
            let and =
                r#"{"tag":"And","sort":{"tag":"SortApp","name":"SortS","args":[]},"patterns":["#;
            for (conjuncts, left) in [
                (50_000, false),
                (50_000, true),
                (200_000, false),
                (200_000, true),
            ] {
                let term = if left {
                    format!(
                        "{}{constant}{}",
                        and.repeat(conjuncts - 1),
                        format!(",{constant}]}}").repeat(conjuncts - 1)
                    )
                } else {
                    format!("{and}{}]}}", vec![constant; conjuncts].join(","))
                };
                let request = deserialize_request::<ExecuteRequest>(&format!(
                    r#"{{"state":{{"format":"KORE","version":1,"term":{term}}},"maxDepth":0}}"#
                ))
                .unwrap();
                let outcome = backend.execute_json(request);
                if conjuncts <= k_rust_backend::nesting::max_depth() {
                    outcome.unwrap_or_else(|error| panic!("{conjuncts}, left {left}: {error}"));
                } else {
                    let error = outcome.unwrap_err();
                    assert!(
                        error
                            .to_string()
                            .contains("the backend provides for one operation"),
                        "{error}"
                    );
                }
            }
        });
    }

    /// Ground functions whose simplification descends once per level of the term: `f` and `h`
    /// have no equations, `g` moves under each `w` it meets, and `len` counts a `cons` list,
    /// adding with the `INT.add` hook on the way back up.
    const FUNCTION_CHAINS: &str = r#"[]
        module MAIN
            sort SortS{} []
            sort SortL{} []
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            symbol a{}() : SortS{} [constructor{}(), functional{}()]
            symbol w{}(SortS{}) : SortS{} [constructor{}(), functional{}()]
            symbol nil{}() : SortL{} [constructor{}(), functional{}()]
            symbol cons{}(SortS{}, SortL{}) : SortL{} [constructor{}(), functional{}()]
            symbol f{}(SortS{}) : SortS{} [function{}(), total{}()]
            symbol h{}(SortS{}, SortS{}) : SortS{} [function{}(), total{}()]
            symbol g{}(SortS{}) : SortS{} [function{}(), total{}()]
            symbol len{}(SortL{}) : SortInt{} [function{}(), total{}()]
            hooked-symbol intAdd{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.add")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortS{}, R}(X0:SortS{}, w{}(X:SortS{})), \top{R}())),
                \equals{SortS{}, R}(g{}(X0:SortS{}), \and{SortS{}}(w{}(g{}(X:SortS{})), \top{SortS{}}()))
            ) [label{}("g-w")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortL{}, R}(X0:SortL{}, nil{}()), \top{R}())),
                \equals{SortInt{}, R}(len{}(X0:SortL{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))
            ) [label{}("len-nil")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortL{}, R}(X0:SortL{}, cons{}(H:SortS{}, T:SortL{})), \top{R}())),
                \equals{SortInt{}, R}(
                    len{}(X0:SortL{}),
                    \and{SortInt{}}(intAdd{}(\dv{SortInt{}}("1"), len{}(T:SortL{})), \top{SortInt{}}())
                )
            ) [label{}("len-cons")]
        endmodule []"#;

    /// The KORE JSON term of `levels` nested applications of `symbol` around `leaf`, each with
    /// the arguments `before` ahead of the nested one and `after` behind it.
    fn nested(levels: usize, symbol: &str, before: &str, after: &str, leaf: &str) -> String {
        let open = format!(r#"{{"tag":"App","name":"{symbol}","sorts":[],"args":[{before}"#);
        let close = format!("{after}]}}");
        format!("{}{leaf}{}", open.repeat(levels), close.repeat(levels))
    }

    /// The simplifier descends once per level of these terms, so its frames are among the passes
    /// over internal terms that the stack the backend provides per level must hold. At 5,000
    /// levels each request needs more than Node's main thread in every build (the simplifier
    /// takes about 2 KiB per level in a release build), so the facade runs it on a segment of
    /// exactly the size `nesting::stack_for_depth` gives for its height: a simplifier whose
    /// frames per level outgrew the bound stops with `StackExhausted` there, which the exact
    /// results rule out, or overflows the segment and aborts the test binary. At opt-level 1 each
    /// request touches about 20 MB of stack and the test takes about a second.
    #[test]
    fn deep_function_chains_simplify_on_the_stack_the_backend_provides() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend =
                Backend::new(FUNCTION_CHAINS, "MAIN", BackendOptions::DEFAULT).unwrap();
            // Confined to the stack sized from the input, the bound under test.
            backend.set_simplification_stack_budget(0);
            let envelope = |term: &str| format!(r#"{{"format":"KORE","version":1,"term":{term}}}"#);
            let levels = 5_000;
            let a = nested(1, "a", "", "", "");
            let nil = nested(1, "nil", "", "", "");
            let chain = nested(levels, "f", "", "", &a);
            let binary = nested(levels, "h", "", &format!(",{a}"), &a);
            let g_over_w = nested(1, "g", "", "", &nested(levels, "w", "", "", &a));
            let w_over_g = nested(levels, "w", "", "", &nested(1, "g", "", "", &a));
            let list = nested(levels, "cons", &format!("{a},"), "", &nil);
            let len = nested(1, "len", "", "", &list);
            let count = format!(
                r#"{{"tag":"DV","sort":{{"tag":"SortApp","name":"SortInt","args":[]}},"value":"{levels}"}}"#
            );
            for (name, request, expected) in [
                ("f", &chain, &chain),
                ("h", &binary, &binary),
                ("g over w", &g_over_w, &w_over_g),
                ("len", &len, &count),
            ] {
                let request = deserialize_request::<PatternRequest>(&format!(
                    r#"{{"state":{}}}"#,
                    envelope(request)
                ))
                .unwrap();
                let simplified = backend
                    .simplify_json(request)
                    .unwrap_or_else(|error| panic!("{name}: {error}"));
                assert!(same_kore(&simplified, &envelope(expected)), "{name}");
            }
        });
    }

    /// `lenb` counts a `cons` list like `len`, but its result nests four additions above the
    /// count of the tail, each a level of the term simplifier's recursion (about 2 KiB in an
    /// optimized build, `k_rust_backend`'s `tests::recursion_stack`), so its simplification takes
    /// more stack per level of the list than the backend provides per level (4 KiB in a release
    /// build, 6 KiB at opt-level 1, 24 KiB unoptimized): on the segment the facade maps for 10,000
    /// levels it reaches its red zone with thousands of levels of the list still below it. Each
    /// level binds the rest of the list, whose definedness is then derived, and the request must
    /// end with the count or with `StackExhausted`, not abort. Before the definedness walk kept
    /// its work on the heap, debug builds aborted here with a segmentation fault inside it (the
    /// release build skips the walk on the `ceil_free` list; `definedness::tests` cover it).
    #[test]
    fn a_simplification_that_outgrows_the_stack_bound_stops_at_its_red_zone() {
        on_thread(NODE_MAIN_STACK, || {
            let definition = FUNCTION_CHAINS.replace(
                "endmodule []",
                r#"
                symbol lenb{}(SortL{}) : SortInt{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \and{R}(\in{SortL{}, R}(X0:SortL{}, nil{}()), \top{R}())),
                    \equals{SortInt{}, R}(lenb{}(X0:SortL{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))
                ) [label{}("lenb-nil")]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \and{R}(\in{SortL{}, R}(X0:SortL{}, cons{}(H:SortS{}, T:SortL{})), \top{R}())),
                    \equals{SortInt{}, R}(
                        lenb{}(X0:SortL{}),
                        \and{SortInt{}}(
                            intAdd{}(\dv{SortInt{}}("1"), intAdd{}(\dv{SortInt{}}("0"), intAdd{}(\dv{SortInt{}}("0"), intAdd{}(\dv{SortInt{}}("0"), lenb{}(T:SortL{}))))),
                            \top{SortInt{}}()
                        )
                    )
                ) [label{}("lenb-cons")]
                endmodule []"#,
            );
            let mut backend = Backend::new(&definition, "MAIN", BackendOptions::DEFAULT).unwrap();
            // Confined to the stack sized from the input, the bound under test.
            backend.set_simplification_stack_budget(0);
            let levels = BEYOND_THE_THREAD;
            let a = nested(1, "a", "", "", "");
            let nil = nested(1, "nil", "", "", "");
            let count = nested(
                1,
                "lenb",
                "",
                "",
                &nested(levels, "cons", &format!("{a},"), "", &nil),
            );
            let request = deserialize_request::<PatternRequest>(&format!(
                r#"{{"state":{{"format":"KORE","version":1,"term":{count}}}}}"#
            ))
            .unwrap();
            match backend.simplify_json(request) {
                Ok(simplified) => assert!(
                    same_kore(
                        &simplified,
                        &format!(
                            r#"{{"format":"KORE","version":1,"term":{{"tag":"DV","sort":{{"tag":"SortApp","name":"SortInt","args":[]}},"value":"{levels}"}}}}"#
                        )
                    ),
                    "{simplified}"
                ),
                Err(error) => assert!(
                    error.to_string().contains(
                        &StopCause::StackExhausted(k_rust_backend::stop::StackLimit::ThreadBudget(
                            0
                        ))
                        .to_string()
                    ),
                    "{error}"
                ),
            }
        });
    }

    #[cfg(not(feature = "z3-inference"))]
    #[test]
    fn portable_model_generation_reports_the_capability_boundary() {
        let error = backend()
            .get_model_with(PatternRequest::new(kore("a{}()")), Ok)
            .unwrap_err();
        assert!(error.to_string().contains("no Z3"));
    }

    /// An error made from a stop keeps the cause, and its text is the cause's own text.
    #[test]
    fn a_stop_error_keeps_its_cause_and_its_text() {
        let causes = [
            StopCause::Cancelled,
            StopCause::Deadline(StepTimeoutMode::Manual(Duration::from_millis(5))),
            StopCause::StackExhausted(StackLimit::ThreadBudget(1 << 30)),
            StopCause::SolverPrelude(PreludeFailure::Inconsistent),
        ];
        for cause in causes {
            let error = BackendError::from(cause.clone());
            assert_eq!(error.stop_cause(), Some(&cause));
            assert_eq!(error.to_string(), cause.to_string());
            assert_eq!(error.message(), cause.to_string());
        }
        assert_eq!(
            BackendError::from(StopCause::Cancelled).to_string(),
            "Request cancelled"
        );
    }

    /// An error made from text has no cause.
    #[test]
    fn a_text_error_has_no_stop_cause() {
        let error = BackendError::new("could not select backend module: none");
        assert_eq!(error.stop_cause(), None);
        assert_eq!(error.message(), "could not select backend module: none");
        assert_eq!(error.to_string(), "could not select backend module: none");
    }
}
