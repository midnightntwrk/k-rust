//! Stops: a computation ended before producing its answer because a resource or context it runs
//! under ran out or failed (design CBC-04).
//!
//! There are four such causes: the request was cancelled, the deadline of the active rewrite or
//! proof step passed, the thread came within the red zone of its native stack, or the solver's
//! prelude failed. Each resource belongs to an owner (the step, the request, the operation that
//! uses the solver), so a site below that owner cannot know what the missing answer means for the
//! owner's outcome, and must not substitute a value for it. A stop is therefore carried as a
//! [`Stop`] and propagated with `?` up to its owner, which publishes it with
//! [`Stop::into_cause`]; a failure (a fact about the sub-question itself) is not a stop.
//!
//! A [`Stop`] cannot be built outside this module; it is minted where a stop signal is observed:
//!
//! ```compile_fail,E0451
//! use k_rust_backend::stop::{Stop, StopCause};
//!
//! let stop: Stop = Stop { cause: StopCause::Cancelled, armed: todo!() };
//! assert_eq!(stop.into_cause(), StopCause::Cancelled);
//! ```
//!
//! The same stop obtained from the one poll, under a cancelled request token, and published:
//!
//! ```
//! use k_rust_backend::stop::{self, CancellationToken, Stop, StopCause};
//!
//! let token = CancellationToken::new();
//! token.cancel();
//! let stop: Stop = token.scope(stop::check).unwrap_err();
//! assert_eq!(stop.into_cause(), StopCause::Cancelled);
//! ```

#[cfg(debug_assertions)]
use std::panic::Location;
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
use std::{
    cell::RefCell,
    fmt,
    sync::{
        Arc, OnceLock,
        atomic::{AtomicBool, Ordering},
    },
};

use crate::{smt::SmtSolver, timeout::StepTimeoutMode};

/// Why a computation stopped. Deliberately not `#[non_exhaustive]`: every consumer decides every
/// cause, and adding one is a breaking change.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum StopCause {
    /// The request was cancelled by its client, or its session ended.
    Cancelled,
    /// The deadline of the active rewrite or proof step passed; the mode is the one that armed it.
    Deadline(StepTimeoutMode),
    /// Less than `STACK_RED_ZONE` bytes of this thread's native stack remained.
    StackExhausted,
    /// The solver's prelude is unsatisfiable or undecided, so none of its answers means anything.
    SolverPrelude(PreludeFailure),
}

/// How a solver's prelude (definition axioms and user prelude) failed.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum PreludeFailure {
    /// The prelude is unsatisfiable, so every query posed under it is trivially unsatisfiable.
    Inconsistent,
    /// The solver could not decide the prelude; the payload is its reason.
    Unknown(Arc<str>),
}

/// The texts the surfaces print for a failed prelude: `InconsistentPrelude` and
/// `UnknownPrelude("<reason>")`, the reason quoted and escaped.
impl fmt::Display for PreludeFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Inconsistent => formatter.write_str("InconsistentPrelude"),
            Self::Unknown(reason) => write!(formatter, "UnknownPrelude({:?})", &**reason),
        }
    }
}

/// The fault texts the surfaces print for each cause: a cancelled request is `Request cancelled`,
/// a failed prelude `could not initialize Z3: <failure>`, and an exhausted stack
/// `simplification exhausted the native stack of the current thread`, the text of the
/// simplifier's stack-exhaustion error.
impl fmt::Display for StopCause {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled => formatter.write_str("Request cancelled"),
            Self::Deadline(mode) => write!(
                formatter,
                "the step exceeded its {} timeout of {:?}",
                match mode {
                    StepTimeoutMode::Manual(_) => "manual",
                    StepTimeoutMode::MovingAverage(_) => "moving-average",
                },
                mode.timeout()
            ),
            Self::StackExhausted => formatter
                .write_str("simplification exhausted the native stack of the current thread"),
            Self::SolverPrelude(failure) => write!(formatter, "could not initialize Z3: {failure}"),
        }
    }
}

/// What a stop ends. A cause that ends more work outranks one that ends less.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum StopScope {
    /// The state being stepped: the deadline of its step, or the thread's stack.
    Step,
    /// Every remaining state of the request.
    Request,
    /// Every operation that uses the solver.
    Solver,
}

impl StopCause {
    /// The work this cause ends; the one definition of precedence between simultaneous causes.
    pub const fn scope(&self) -> StopScope {
        match self {
            Self::Deadline(_) | Self::StackExhausted => StopScope::Step,
            Self::Cancelled => StopScope::Request,
            Self::SolverPrelude(_) => StopScope::Solver,
        }
    }
}

/// Evidence that a stop was observed.
///
/// Minted only by [`check`], `check_stack`, [`operation`] and `Stop::solver_prelude`; consumed
/// only by `?`, [`Stop::into_cause`], [`Stop::merge`] or [`Stop::forgo_refinement`]. In debug
/// builds dropping it any other way panics, naming where it was minted: the drop is a fallback
/// that decided an outcome from a missing answer.
#[must_use = "propagate a stop with `?` or publish it with `Stop::into_cause`"]
#[derive(Debug)]
pub struct Stop {
    cause: StopCause,
    armed: Armed,
}

/// Equality of causes. Comparing borrows, so it neither consumes nor disarms; it exists so that
/// `Unwind<F>` and the layered results are `PartialEq`, which assertions over them need.
impl PartialEq for Stop {
    fn eq(&self, other: &Self) -> bool {
        self.cause == other.cause
    }
}

impl Eq for Stop {}

impl Stop {
    #[cold]
    #[inline(never)]
    #[cfg_attr(debug_assertions, track_caller)]
    fn mint(cause: StopCause) -> Self {
        Self {
            cause,
            armed: Armed::new(),
        }
    }

    /// The prelude check of a solver found its prelude failed.
    #[cfg_attr(debug_assertions, track_caller)]
    pub(crate) fn solver_prelude(failure: PreludeFailure) -> Self {
        Self::mint(StopCause::SolverPrelude(failure))
    }

    pub fn cause(&self) -> &StopCause {
        &self.cause
    }

    /// Publish the stop in a step's or operation's result.
    pub fn into_cause(self) -> StopCause {
        let Self { cause, armed } = self;
        armed.disarm();
        cause
    }

    /// Two stops observed by one computation: keep the one of wider scope, the first on a tie.
    pub fn merge(self, later: Self) -> Self {
        if later.cause.scope() > self.cause.scope() {
            let _published = self.into_cause();
            later
        } else {
            let _published = later.into_cause();
            self
        }
    }

    /// Dismiss the stop because the interrupted computation only refined an outcome that is
    /// already sound without it. Each call site states the outcome it keeps.
    ///
    /// A dismissed stop of `Request` or `Solver` scope is not lost: its signal stays raised, so
    /// the owner's next poll mints it again, and [`operation`]'s exit poll publishes a dismissed
    /// `Solver` stop.
    pub fn forgo_refinement(self) {
        let _dismissed = self.into_cause();
    }
}

/// Result of a computation that can stop: the stop is the outer layer.
pub type Stoppable<T> = Result<T, Stop>;

// ---- the unreported-stop checker ---------------------------------------------------------

/// The drop check of a [`Stop`]: in debug builds it records where the stop was minted and panics
/// if it is dropped before being disarmed; in release builds it is zero-sized, has no drop glue,
/// and `disarm` compiles to nothing.
#[cfg(debug_assertions)]
#[derive(Debug)]
struct Armed(&'static Location<'static>);

#[cfg(not(debug_assertions))]
#[derive(Debug)]
struct Armed;

#[cfg(not(debug_assertions))]
const _: () = assert!(std::mem::size_of::<Armed>() == 0);

impl Armed {
    #[cfg_attr(debug_assertions, track_caller)]
    fn new() -> Self {
        #[cfg(debug_assertions)]
        {
            Self(Location::caller())
        }
        #[cfg(not(debug_assertions))]
        {
            Self
        }
    }

    /// Consume the check without running it; in release builds there is nothing to run.
    fn disarm(self) {
        #[cfg(debug_assertions)]
        std::mem::forget(self);
    }
}

#[cfg(debug_assertions)]
impl Drop for Armed {
    fn drop(&mut self) {
        // A stop dropped while its thread unwinds is not a fallback: the unwinding panic already
        // reports the failure, and a second panic would abort the process.
        if !std::thread::panicking() {
            panic!(
                "a stop minted at {} was dropped without being propagated or published \
                 (a fallback absorbed it; design CBC-04)",
                self.0
            );
        }
    }
}

// ---- the one registry and the one poll ---------------------------------------------------

thread_local! {
    static REGISTRY: RefCell<Registry> = const { RefCell::new(Registry::EMPTY) };
}

/// Every stop signal visible to the computation running on this thread. Backend work is
/// synchronous and thread-confined, so a thread-local registry keeps the poll free of arguments
/// while each scope restores what it replaced when it ends.
struct Registry {
    /// The cancellation token of the request being served.
    request: Option<CancellationToken>,
    /// The prelude signals of the solvers the enclosing operations use.
    solvers: Vec<PreludeSignal>,
    /// The earliest deadline of the active steps, with the mode of the step that armed it.
    #[cfg(not(target_arch = "wasm32"))]
    deadline: Option<(Instant, StepTimeoutMode)>,
}

impl Registry {
    const EMPTY: Self = Self {
        request: None,
        solvers: Vec::new(),
        #[cfg(not(target_arch = "wasm32"))]
        deadline: None,
    };

    /// The raised cause of widest scope, if any: the signals are read in decreasing
    /// `StopScope` order (solver, request, step deadline), so the first raised one wins.
    fn raised(&self) -> Option<StopCause> {
        if let Some(failure) = self.raised_prelude() {
            return Some(StopCause::SolverPrelude(failure.clone()));
        }
        if self.request_cancelled() {
            return Some(StopCause::Cancelled);
        }
        #[cfg(not(target_arch = "wasm32"))]
        if let Some((deadline, mode)) = self.deadline
            && Instant::now() >= deadline
        {
            return Some(StopCause::Deadline(mode));
        }
        None
    }

    fn raised_prelude(&self) -> Option<&PreludeFailure> {
        self.solvers.iter().find_map(PreludeSignal::failure)
    }

    fn request_cancelled(&self) -> bool {
        self.request
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled)
    }
}

/// The one cooperative interruption point. Loop heads, hook loops and solver retries call it.
#[inline]
#[cfg_attr(debug_assertions, track_caller)]
pub fn check() -> Result<(), Stop> {
    match REGISTRY.with(|registry| registry.borrow().raised()) {
        None => Ok(()),
        Some(cause) => Err(Stop::mint(cause)),
    }
}

/// Legacy predicate behind `cancellation::cancellation_requested`: the request was cancelled or
/// an installed solver prelude failed. Deleted with its shim by CBC-04-T11.
pub(crate) fn legacy_cancellation_requested() -> bool {
    REGISTRY.with(|registry| {
        let registry = registry.borrow();
        registry.request_cancelled() || registry.raised_prelude().is_some()
    })
}

/// Legacy predicate behind `timeout::interruption_requested`: any signal of the registry is
/// raised. Deleted with its shim by CBC-04-T11.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "no production caller once hooks poll `stop::check`; deleted with its shim by CBC-04-T11"
    )
)]
pub(crate) fn legacy_interruption_requested() -> bool {
    REGISTRY.with(|registry| registry.borrow().raised().is_some())
}

/// Bytes of native stack that must remain when the simplifier enters a round of
/// `simplify_with_budget` or a call of `simplify_predicate_with_budget`, the points at which it
/// checks the stack.
///
/// The zone must hold the deepest stretch of the same thread between two checks: the frames of
/// one level of simplifier recursion (about 2.5 KiB in release builds and 16 KiB in debug builds,
/// measured on ground function recursion), plus the matching, builtin hooks, and SMT solver call
/// that run on the thread between two checks. In a debug build a whole simplification of a
/// conditional equation whose condition Z3 decides takes 62 KiB of stack from its entry, and the
/// Z3 call on such a condition alone takes 23 KiB (both measured by stack painting); the zone is
/// twice the whole simplification.
/// The zone is also a floor below which a thread simplifies nothing, so it stays well under the
/// smallest thread stacks embedders commonly run (512 KiB, the macOS default for secondary
/// threads).
#[cfg(not(target_family = "wasm"))]
const STACK_RED_ZONE: usize = 128 * 1024;

/// Whether the current thread has less than `STACK_RED_ZONE` bytes of stack left.
///
/// The resource is bytes of this thread's stack, and only the OS knows its bounds, which
/// `stacker` reads for every native thread whoever created it. A thread whose bounds cannot be
/// read, and every wasm32 build, where the engine's call-stack limit is invisible to the module,
/// is unguarded: an unknown remaining stack never counts as exhausted.
#[inline]
fn stack_exhausted() -> bool {
    #[cfg(not(target_family = "wasm"))]
    {
        stacker::remaining_stack().is_some_and(|remaining| remaining < STACK_RED_ZONE)
    }
    #[cfg(target_family = "wasm")]
    {
        false
    }
}

/// The stack guard: a [`StopCause::StackExhausted`] stop when `stack_exhausted` holds.
#[inline]
#[cfg_attr(debug_assertions, track_caller)]
pub(crate) fn check_stack() -> Result<(), Stop> {
    if stack_exhausted() {
        Err(Stop::mint(StopCause::StackExhausted))
    } else {
        Ok(())
    }
}

/// A cheaply clonable signal used to cancel one in-process backend request.
#[derive(Clone, Debug, Default)]
pub struct CancellationToken(Arc<AtomicBool>);

impl CancellationToken {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn cancel(&self) {
        self.0.store(true, Ordering::Release);
    }

    pub fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Acquire)
    }

    /// Install this token as the request token for `action`; restores the previous one on exit,
    /// including when `action` panics.
    pub fn scope<T>(&self, action: impl FnOnce() -> T) -> T {
        let previous =
            REGISTRY.with(|registry| registry.borrow_mut().request.replace(self.clone()));
        let _restore = RequestGuard(previous);
        action()
    }
}

struct RequestGuard(Option<CancellationToken>);

impl Drop for RequestGuard {
    fn drop(&mut self) {
        let previous = self.0.take();
        REGISTRY.with(|registry| registry.borrow_mut().request = previous);
    }
}

/// A solver's prelude-failure signal, raised once with the failure and shared by every clone of
/// the solver, so every operation using the solver observes a failure found by any of them.
#[derive(Clone, Debug, Default)]
pub struct PreludeSignal(Arc<OnceLock<PreludeFailure>>);

impl PreludeSignal {
    /// Raise the signal. A prelude is checked once, so its failure does not change; a second
    /// raise keeps the first failure.
    #[cfg_attr(not(feature = "z3"), allow(dead_code))]
    pub(crate) fn raise(&self, failure: PreludeFailure) {
        let _first_failure_kept = self.0.set(failure);
    }

    pub fn failure(&self) -> Option<&PreludeFailure> {
        self.0.get()
    }

    fn same_signal(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

/// Install `signal` for the rest of the enclosing scope unless it is installed already; the
/// returned guard uninstalls it, including on unwinding.
fn install(signal: &PreludeSignal) -> Option<SolverGuard> {
    REGISTRY.with(|registry| {
        let mut registry = registry.borrow_mut();
        if registry
            .solvers
            .iter()
            .any(|installed| installed.same_signal(signal))
        {
            None
        } else {
            registry.solvers.push(signal.clone());
            Some(SolverGuard)
        }
    })
}

struct SolverGuard;

impl Drop for SolverGuard {
    fn drop(&mut self) {
        // Guards live in nested scopes, so the signal a guard installed is the last one.
        REGISTRY.with(|registry| registry.borrow_mut().solvers.pop());
    }
}

/// Install `signal` for `body` without polling, as [`operation`] installs its solver's signal;
/// tests observe the registry through it.
#[cfg(test)]
pub(crate) fn with_prelude_signal<T>(signal: &PreludeSignal, body: impl FnOnce() -> T) -> T {
    let _installed = install(signal);
    body()
}

/// The operation boundary.
///
/// Installs `solver`'s prelude signal for `body` unless it is already installed (pointer
/// equality), so every loop inside observes a prelude failure found by any operation sharing the
/// solver. Polls on entry: a request cancelled before it starts, or a solver whose prelude
/// already failed, does not run. On exit it polls the solver's prelude signal, so a prelude
/// failure found during a refinement whose stop was dismissed is still the operation's result;
/// `body`'s value is then discarded, so `body` publishes its own stops in-band rather than
/// returning a [`Stop`].
#[cfg_attr(debug_assertions, track_caller)]
pub fn operation<T>(solver: &dyn SmtSolver, body: impl FnOnce() -> T) -> Stoppable<T> {
    let signal = solver.prelude_signal();
    let _installed = signal.and_then(install);
    check()?;
    let value = body();
    match signal.and_then(PreludeSignal::failure) {
        None => Ok(value),
        Some(failure) => Err(Stop::solver_prelude(failure.clone())),
    }
}

/// Arm the step deadline for the rest of the enclosing scope, keeping the earlier one (and its
/// mode) when a deadline is already armed; the returned guard restores the previous deadline.
/// Used only by `timeout::StepTimeoutController::begin_step`.
#[cfg(not(target_arch = "wasm32"))]
pub(crate) fn arm_deadline(deadline: Instant, mode: StepTimeoutMode) -> DeadlineGuard {
    let previous = REGISTRY.with(|registry| {
        let mut registry = registry.borrow_mut();
        let previous = registry.deadline;
        registry.deadline = Some(match previous {
            Some(armed) if armed.0 <= deadline => armed,
            _ => (deadline, mode),
        });
        previous
    });
    DeadlineGuard { previous }
}

/// Restores the step deadline that `arm_deadline` replaced.
#[cfg(not(target_arch = "wasm32"))]
#[must_use = "the deadline is disarmed when the guard is dropped"]
pub(crate) struct DeadlineGuard {
    previous: Option<(Instant, StepTimeoutMode)>,
}

#[cfg(not(target_arch = "wasm32"))]
impl Drop for DeadlineGuard {
    fn drop(&mut self) {
        let previous = self.previous;
        REGISTRY.with(|registry| registry.borrow_mut().deadline = previous);
    }
}

// ---- `?` inside one module ---------------------------------------------------------------

/// The error type for `?` inside one module: both layers propagate. Never returned across a
/// module boundary; [`Layered::layered`] converts it there.
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Unwind<F> {
    Stop(Stop),
    Fail(F),
}

impl<F> From<Stop> for Unwind<F> {
    fn from(stop: Stop) -> Self {
        Self::Stop(stop)
    }
}

impl<F> Unwind<F> {
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the layered modules convert failures with `?` and the cross `From` pairs; no \
                      module maps an `Unwind` failure by hand yet"
        )
    )]
    pub(crate) fn map_fail<G>(self, map: impl FnOnce(F) -> G) -> Unwind<G> {
        match self {
            Self::Stop(stop) => Unwind::Stop(stop),
            Self::Fail(failure) => Unwind::Fail(map(failure)),
        }
    }
}

/// `impl From<F> for Unwind<F>` per failure type (a blanket impl would overlap `From<Stop>`), and
/// `impl From<G> for Unwind<F>` for each failure `G` that `F` wraps, so that `callee(..)??` in an
/// `Unwind<F>` function propagates a callee failure `G` through `F`'s wrapping variant. There is
/// deliberately no `From<Stop>` for any failure type.
macro_rules! unwind_failures {
    ($($failure:ty),* $(,)?) => {
        $(impl From<$failure> for Unwind<$failure> {
            fn from(failure: $failure) -> Self {
                Self::Fail(failure)
            }
        })*
    };
}

unwind_failures!(
    crate::builtin::BuiltinError,
    crate::simplify::SimplificationError,
    crate::implication::ImplicationError,
);

impl From<crate::builtin::BuiltinError> for Unwind<crate::simplify::SimplificationError> {
    fn from(failure: crate::builtin::BuiltinError) -> Self {
        Self::Fail(crate::simplify::SimplificationError::Builtin(failure))
    }
}

impl From<crate::simplify::SimplificationError> for Unwind<crate::implication::ImplicationError> {
    fn from(failure: crate::simplify::SimplificationError) -> Self {
        Self::Fail(crate::implication::ImplicationError::Simplification(
            failure,
        ))
    }
}

impl From<crate::matching::SortError> for Unwind<crate::implication::ImplicationError> {
    fn from(failure: crate::matching::SortError) -> Self {
        Self::Fail(crate::implication::ImplicationError::Subsorting(failure))
    }
}

/// Converts a module's internal `Unwind` result into the layered result it returns across the
/// module boundary: the stop outside, the failure inside.
pub(crate) trait Layered<T, F> {
    fn layered(self) -> Stoppable<Result<T, F>>;
}

impl<T, F> Layered<T, F> for Result<T, Unwind<F>> {
    #[inline]
    fn layered(self) -> Stoppable<Result<T, F>> {
        match self {
            Ok(value) => Ok(Ok(value)),
            Err(Unwind::Fail(failure)) => Ok(Err(failure)),
            Err(Unwind::Stop(stop)) => Err(stop),
        }
    }
}

// The layering adds no bytes: the stop variant fits in each failure's niche. A regression would
// grow the frames of the recursive simplifier that `STACK_RED_ZONE` is sized for, so the
// assertions hold wherever the red zone does. On wasm32 the stack is unguarded, and there the
// 8-byte alignment of `StopCause::Deadline`'s `Duration` rounds the 4-byte-aligned failures up
// by 4 bytes.
#[cfg(not(target_family = "wasm"))]
const _: () = {
    use std::mem::size_of;

    use crate::{
        builtin::BuiltinError,
        implication::ImplicationError,
        simplify::SimplificationError,
        smt::{Satisfiability, SmtError},
    };

    assert!(size_of::<Unwind<BuiltinError>>() == size_of::<BuiltinError>());
    assert!(size_of::<Unwind<SimplificationError>>() == size_of::<SimplificationError>());
    assert!(size_of::<Unwind<ImplicationError>>() == size_of::<ImplicationError>());
    assert!(
        size_of::<Stoppable<Result<Satisfiability, SmtError>>>()
            == size_of::<Result<Satisfiability, SmtError>>()
    );
};

#[cfg(test)]
mod tests {
    use std::{
        cell::Cell,
        panic::{AssertUnwindSafe, catch_unwind},
        time::Duration,
    };

    use super::*;
    use crate::{
        rule::Predicate,
        simplify::SimplificationError,
        smt::{NoSolver, Satisfiability, SmtError, Validity},
        substitution::Substitution,
    };

    /// The cause `check` reports, published so that no stop is dropped armed.
    fn polled() -> Option<StopCause> {
        check().err().map(Stop::into_cause)
    }

    fn registry_is_empty() -> bool {
        REGISTRY.with(|registry| {
            let registry = registry.borrow();
            #[cfg(not(target_arch = "wasm32"))]
            let no_deadline = registry.deadline.is_none();
            #[cfg(target_arch = "wasm32")]
            let no_deadline = true;
            registry.request.is_none() && registry.solvers.is_empty() && no_deadline
        })
    }

    fn raised_signal(failure: PreludeFailure) -> PreludeSignal {
        let signal = PreludeSignal::default();
        signal.raise(failure);
        signal
    }

    fn cancelled_token() -> CancellationToken {
        let token = CancellationToken::new();
        token.cancel();
        token
    }

    fn passed_deadline(mode: StepTimeoutMode) -> DeadlineGuard {
        arm_deadline(Instant::now(), mode)
    }

    const MANUAL: StepTimeoutMode = StepTimeoutMode::Manual(Duration::from_secs(1));
    const AVERAGE: StepTimeoutMode = StepTimeoutMode::MovingAverage(Duration::from_secs(2));

    #[test]
    fn check_is_ok_with_an_empty_registry() {
        assert!(registry_is_empty());
        assert_eq!(polled(), None);
        assert!(!legacy_cancellation_requested());
        assert!(!legacy_interruption_requested());
    }

    #[test]
    fn each_signal_alone_yields_its_cause() {
        cancelled_token().scope(|| assert_eq!(polled(), Some(StopCause::Cancelled)));
        CancellationToken::new().scope(|| assert_eq!(polled(), None));

        let signal = raised_signal(PreludeFailure::Unknown("timeout".into()));
        with_prelude_signal(&signal, || {
            assert_eq!(
                polled(),
                Some(StopCause::SolverPrelude(PreludeFailure::Unknown(
                    "timeout".into()
                )))
            );
        });
        with_prelude_signal(&PreludeSignal::default(), || assert_eq!(polled(), None));

        {
            let _deadline = passed_deadline(MANUAL);
            assert_eq!(polled(), Some(StopCause::Deadline(MANUAL)));
        }
        {
            let _deadline = arm_deadline(Instant::now() + Duration::from_secs(3600), MANUAL);
            assert_eq!(polled(), None);
        }

        let exhausted = std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| check_stack().err().map(Stop::into_cause))
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(exhausted, Some(StopCause::StackExhausted));
        assert_eq!(check_stack().err().map(Stop::into_cause), None);
        assert!(registry_is_empty());
    }

    #[test]
    fn the_cause_of_widest_scope_wins() {
        let signal = raised_signal(PreludeFailure::Inconsistent);
        let prelude = StopCause::SolverPrelude(PreludeFailure::Inconsistent);
        {
            let _deadline = passed_deadline(MANUAL);
            cancelled_token().scope(|| {
                assert_eq!(polled(), Some(StopCause::Cancelled));
                with_prelude_signal(&signal, || assert_eq!(polled(), Some(prelude.clone())));
            });
            with_prelude_signal(&signal, || assert_eq!(polled(), Some(prelude.clone())));
        }
        assert!(StopCause::Cancelled.scope() > StopCause::Deadline(MANUAL).scope());
        assert!(prelude.scope() > StopCause::Cancelled.scope());
        assert_eq!(
            StopCause::StackExhausted.scope(),
            StopCause::Deadline(MANUAL).scope()
        );
    }

    #[test]
    fn scopes_and_deadlines_restore_on_exit() {
        let outer = cancelled_token();
        outer.scope(|| {
            CancellationToken::new().scope(|| assert_eq!(polled(), None));
            assert_eq!(polled(), Some(StopCause::Cancelled));
        });
        let signal = raised_signal(PreludeFailure::Inconsistent);
        with_prelude_signal(&signal, || {
            // Installing an installed signal again does not uninstall it on exit.
            with_prelude_signal(&signal, || {});
            assert!(polled().is_some());
        });
        {
            let _deadline = passed_deadline(MANUAL);
        }
        assert!(registry_is_empty());
        assert_eq!(polled(), None);
    }

    #[test]
    fn scopes_and_deadlines_restore_when_the_body_panics() {
        let token = cancelled_token();
        let signal = raised_signal(PreludeFailure::Inconsistent);
        let unwound = catch_unwind(AssertUnwindSafe(|| {
            token.scope(|| {
                with_prelude_signal(&signal, || {
                    let _deadline = passed_deadline(MANUAL);
                    panic!("the body panics");
                })
            })
        }));
        assert!(unwound.is_err());
        let unwound = catch_unwind(AssertUnwindSafe(|| {
            operation(&SignalledSolver(PreludeSignal::default()), || {
                panic!("the operation panics")
            })
        }));
        assert!(unwound.is_err());
        assert!(registry_is_empty());
        assert_eq!(polled(), None);
    }

    #[test]
    fn nested_deadlines_keep_the_earliest_and_its_mode() {
        let now = Instant::now();
        let later = now + Duration::from_secs(3600);
        {
            let _outer = arm_deadline(now, MANUAL);
            {
                let _inner = arm_deadline(later, AVERAGE);
                assert_eq!(polled(), Some(StopCause::Deadline(MANUAL)));
            }
            assert_eq!(polled(), Some(StopCause::Deadline(MANUAL)));
        }
        {
            let _outer = arm_deadline(later, MANUAL);
            assert_eq!(polled(), None);
            {
                let _inner = arm_deadline(now, AVERAGE);
                assert_eq!(polled(), Some(StopCause::Deadline(AVERAGE)));
            }
            assert_eq!(polled(), None);
        }
        assert!(registry_is_empty());
    }

    /// A solver with a prelude signal and no answers.
    struct SignalledSolver(PreludeSignal);

    impl SmtSolver for SignalledSolver {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            Ok(Err(SmtError::Unavailable))
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(Err(SmtError::Unavailable))
        }

        fn prelude_signal(&self) -> Option<&PreludeSignal> {
            Some(&self.0)
        }
    }

    #[test]
    fn operation_under_a_raised_prelude_signal_does_not_run_its_body() {
        let solver = SignalledSolver(raised_signal(PreludeFailure::Inconsistent));
        let ran = Cell::new(false);
        let result = operation(&solver, || ran.set(true));
        assert_eq!(
            result.map_err(Stop::into_cause),
            Err(StopCause::SolverPrelude(PreludeFailure::Inconsistent))
        );
        assert!(!ran.get());
        assert!(registry_is_empty());
    }

    #[test]
    fn operation_publishes_a_prelude_failure_whose_stop_the_body_dismissed() {
        let solver = SignalledSolver(PreludeSignal::default());
        let result = operation(&solver, || {
            solver.0.raise(PreludeFailure::Unknown("incomplete".into()));
            match check() {
                Ok(()) => unreachable!("the installed signal is raised"),
                // The refinement is abandoned; the unrefined answer is kept.
                Err(stop) => stop.forgo_refinement(),
            }
            7
        });
        assert_eq!(
            result.map_err(Stop::into_cause),
            Err(StopCause::SolverPrelude(PreludeFailure::Unknown(
                "incomplete".into()
            )))
        );
        assert!(registry_is_empty());
    }

    #[test]
    fn operation_with_a_clean_body_yields_its_value() {
        let solver = SignalledSolver(PreludeSignal::default());
        let result = operation(&solver, || {
            assert_eq!(polled(), None);
            7
        });
        assert_eq!(result.map_err(Stop::into_cause), Ok(7));
        assert_eq!(operation(&NoSolver, || 8).map_err(Stop::into_cause), Ok(8));
        assert!(registry_is_empty());
    }

    #[test]
    fn operation_polls_the_request_on_entry() {
        let ran = Cell::new(false);
        let result = cancelled_token().scope(|| operation(&NoSolver, || ran.set(true)));
        assert_eq!(result.map_err(Stop::into_cause), Err(StopCause::Cancelled));
        assert!(!ran.get());
    }

    #[test]
    fn operation_installs_its_solver_signal_for_the_body() {
        let solver = SignalledSolver(PreludeSignal::default());
        let result = operation(&solver, || {
            solver.0.raise(PreludeFailure::Inconsistent);
            polled()
        });
        assert_eq!(
            result.map_err(Stop::into_cause),
            Err(StopCause::SolverPrelude(PreludeFailure::Inconsistent))
        );
        // Uninstalled on exit: the raised signal no longer stops this thread.
        assert_eq!(polled(), None);
    }

    /// A layered result, as a module boundary returns it.
    fn layered_answer() -> Stoppable<Result<u32, &'static str>> {
        check()?;
        Ok(Ok(1))
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "dropped without being propagated or published")]
    #[expect(
        clippy::let_unit_value,
        reason = "reproduces the fallback shape `let decided = answer.unwrap_or(fallback)` verbatim"
    )]
    fn a_single_layer_fallback_over_a_stop_panics() {
        cancelled_token().scope(|| {
            let answer: Result<(), Stop> = check();
            let _decided = answer.unwrap_or(());
        });
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "dropped without being propagated or published")]
    fn a_two_layer_wildcard_fallback_over_a_stop_panics() {
        cancelled_token().scope(|| {
            let _decided = match layered_answer() {
                Ok(Ok(value)) => value,
                _ => 0,
            };
        });
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "dropped without being propagated or published")]
    fn is_ok_over_a_stoppable_result_panics() {
        cancelled_token().scope(|| {
            let _decided = layered_answer().is_ok();
        });
    }

    #[test]
    fn publishing_merging_and_dismissing_do_not_panic() {
        let token = cancelled_token();
        let signal = raised_signal(PreludeFailure::Inconsistent);
        token.scope(|| {
            assert_eq!(check().unwrap_err().into_cause(), StopCause::Cancelled);
            check().unwrap_err().forgo_refinement();
            let merged = with_prelude_signal(&signal, || {
                let first = check().unwrap_err();
                first.merge(check().unwrap_err())
            });
            assert_eq!(
                merged.into_cause(),
                StopCause::SolverPrelude(PreludeFailure::Inconsistent)
            );
            let _deadline = passed_deadline(MANUAL);
            let wider = check().unwrap_err();
            let narrower = check_stack().err().unwrap_or_else(|| check().unwrap_err());
            assert_eq!(wider.merge(narrower).into_cause(), StopCause::Cancelled);
        });
        // A narrower later stop loses; a wider later stop wins.
        let deadline = {
            let _deadline = passed_deadline(AVERAGE);
            check().unwrap_err()
        };
        let cancelled = cancelled_token().scope(|| check().unwrap_err());
        assert_eq!(deadline.merge(cancelled).into_cause(), StopCause::Cancelled);
    }

    #[test]
    fn stops_compare_by_cause() {
        let token = cancelled_token();
        token.scope(|| {
            let first = check().unwrap_err();
            let second = check().unwrap_err();
            assert_eq!(first, second);
            first.forgo_refinement();
            second.forgo_refinement();
        });
    }

    #[test]
    fn unwind_propagates_both_layers_and_layers_at_the_boundary() {
        fn inner(stop: bool) -> Result<u32, Unwind<SimplificationError>> {
            if stop {
                check()?;
            }
            Err(arity_failure())?
        }
        fn arity_failure() -> crate::builtin::BuiltinError {
            crate::builtin::BuiltinError::WrongArity {
                hook: "INT.add".into(),
                expected: 2,
                actual: 1,
            }
        }
        assert_eq!(
            inner(false).layered(),
            Ok(Err(SimplificationError::Builtin(arity_failure())))
        );
        let stopped = cancelled_token().scope(|| inner(true).layered());
        assert_eq!(stopped.map_err(Stop::into_cause), Err(StopCause::Cancelled));
        let mapped = inner(false)
            .map_err(|unwind| unwind.map_fail(|failure| failure.to_string()))
            .err();
        assert!(matches!(mapped, Some(Unwind::Fail(_))));
    }

    #[test]
    fn displays_reproduce_the_surface_texts() {
        assert_eq!(
            StopCause::StackExhausted.to_string(),
            "simplification exhausted the native stack of the current thread"
        );
        assert_eq!(
            SimplificationError::Stopped(StopCause::StackExhausted).to_string(),
            StopCause::StackExhausted.to_string()
        );
        assert_eq!(
            PreludeFailure::Inconsistent.to_string(),
            "InconsistentPrelude"
        );
        assert_eq!(
            PreludeFailure::Unknown("a \"quoted\" reason".into()).to_string(),
            r#"UnknownPrelude("a \"quoted\" reason")"#
        );
        assert_eq!(
            StopCause::SolverPrelude(PreludeFailure::Inconsistent).to_string(),
            "could not initialize Z3: InconsistentPrelude"
        );
        assert_eq!(StopCause::Cancelled.to_string(), "Request cancelled");
    }
}
