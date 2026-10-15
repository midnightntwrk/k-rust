//! Stops: a computation ended before producing its answer because a resource or context it runs
//! under ran out or failed (design CBC-04).
//!
//! There are four such causes: the request was cancelled, the deadline of the active rewrite or
//! proof step passed, the simplifier's recursion exhausted its native stack, or the solver's
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
    cell::{Cell, RefCell},
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
    /// Less than `STACK_RED_ZONE` bytes of native stack remained to the simplifier, and it could
    /// not go on on a new segment; the payload says which limit refused the segment.
    StackExhausted(StackLimit),
    /// The solver's prelude is unsatisfiable or undecided, so none of its answers means anything.
    SolverPrelude(PreludeFailure),
}

/// The limit that refused the simplifier's recursion another stack segment
/// ([`StopCause::StackExhausted`]).
///
/// The three are different facts with different remedies: a thread's budget is reached by one
/// recursion that went too deep (or by a budget set too small), the process's by deep recursions
/// on several threads at once or by one thread whose budget an embedder set above the process's
/// (`nesting::with_simplification_stack_budget` accepts any), and the system's refusal by an
/// address space or memory smaller than the budgets assume.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum StackLimit {
    /// The segments held on this thread would exceed its budget, the bytes given
    /// (`nesting::SIMPLIFICATION_STACK_BUDGET`, or `nesting::with_simplification_stack_budget`).
    ThreadBudget(usize),
    /// The segments held on every thread of the process would exceed the process's budget, the
    /// bytes given (`nesting::SIMPLIFICATION_STACK_PROCESS_BUDGET`).
    ProcessBudget(usize),
    /// Both budgets admitted the segment, and the system refused to map it.
    MappingRefused(crate::nesting::SegmentRefused),
}

/// A size in bytes as the stop texts print it: in GiB or MiB when it is a whole number of them.
fn display_bytes(bytes: usize) -> String {
    if bytes != 0 && bytes.is_multiple_of(1 << 30) {
        format!("{} GiB", bytes >> 30)
    } else if bytes != 0 && bytes.is_multiple_of(1 << 20) {
        format!("{} MiB", bytes >> 20)
    } else {
        format!("{bytes} bytes")
    }
}

/// The texts that name each limit, after `simplification exhausted its native stack: `.
impl fmt::Display for StackLimit {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ThreadBudget(budget) => write!(
                formatter,
                "the thread's stack and its budget of {} more are used up: a recursion went too \
                 deep",
                display_bytes(*budget)
            ),
            Self::ProcessBudget(budget) => write!(
                formatter,
                "the segments of every thread together reached the process's budget of {}: \
                 deep recursions on several threads at once, or one thread whose budget is above \
                 the process's",
                display_bytes(*budget)
            ),
            Self::MappingRefused(refused) => write!(
                formatter,
                "the system refused to map another {} segment: the address space or memory \
                 the process may use ran out before the stack budget did",
                display_bytes(refused.size)
            ),
        }
    }
}

/// How a solver's prelude (definition axioms and user prelude) failed.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum PreludeFailure {
    /// The prelude is unsatisfiable, so every query posed under it is trivially unsatisfiable.
    Inconsistent,
    /// The solver could not decide the prelude; the payload is its reason.
    Unknown(Arc<str>),
}

/// Why a solver's prelude failed, in words: it is unsatisfiable, or the solver did not decide
/// whether it is satisfiable, followed by the solver's own reason.
impl fmt::Display for PreludeFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Inconsistent => formatter.write_str(
                "the SMT prelude (the definition's SMT axioms and any user prelude) is \
                 unsatisfiable",
            ),
            Self::Unknown(reason) => write!(
                formatter,
                "the solver did not decide whether the SMT prelude (the definition's SMT axioms \
                 and any user prelude) is satisfiable ({reason})"
            ),
        }
    }
}

/// The fault texts the surfaces print for each cause: a cancelled request is `Request cancelled`,
/// a failed prelude `could not initialize Z3: <failure>`, and an exhausted stack
/// `simplification exhausted its native stack: <limit>`, where the limit is the
/// [`StackLimit`]'s text, for example `the thread's stack and its budget of 1 GiB more are used
/// up: a recursion went too deep`.
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
            Self::StackExhausted(limit) => {
                write!(
                    formatter,
                    "simplification exhausted its native stack: {limit}"
                )
            }
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
            Self::Deadline(_) | Self::StackExhausted(_) => StopScope::Step,
            Self::Cancelled => StopScope::Request,
            Self::SolverPrelude(_) => StopScope::Solver,
        }
    }
}

/// Evidence that a stop was observed.
///
/// Minted only by [`check`], `with_stack_headroom`, [`operation`] and `Stop::solver_prelude`; consumed
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

    /// The simplifier's recursion was refused another stack segment by `limit`; the enclosing
    /// [`with_poll_budget`] scope records it.
    #[cfg(not(target_family = "wasm"))]
    #[cfg_attr(debug_assertions, track_caller)]
    fn out_of_stack(limit: StackLimit) -> Self {
        REGISTRY.with(|registry| registry.borrow().record_stack_stop());
        Self::mint(StopCause::StackExhausted(limit))
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
    /// The budget of polls of the enclosing [`with_poll_budget`] scope, if any.
    polls: Option<PollBudget>,
}

/// A budget of polls ([`with_poll_budget`]): a bound on the work of a computation that is a
/// function of the computation alone, since it counts the points at which the computation polls.
/// It is a `Cell` because [`check`] reads the registry through a shared borrow.
struct PollBudget {
    /// The polls that may still pass.
    remaining: Cell<u64>,
    /// The cause every poll past the budget raises.
    mode: StepTimeoutMode,
    /// What the scope met so far.
    record: Cell<PollBudgetRecord>,
}

/// What a [`with_poll_budget`] scope met: whether its budget refused a poll, and whether a stop
/// for lack of native stack was minted on its thread while it ran, whether or not that stop
/// reached the scope's caller (a site that only refines a sound outcome may dismiss it,
/// [`Stop::forgo_refinement`]).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct PollBudgetRecord {
    pub(crate) budget_exhausted: bool,
    pub(crate) stack_exhausted: bool,
}

impl PollBudgetRecord {
    /// Whether the scope met either stop.
    pub(crate) fn any(self) -> bool {
        self.budget_exhausted || self.stack_exhausted
    }
}

impl Registry {
    const EMPTY: Self = Self {
        request: None,
        solvers: Vec::new(),
        #[cfg(not(target_arch = "wasm32"))]
        deadline: None,
        polls: None,
    };

    /// The raised cause of widest scope, if any: the signals are read in decreasing
    /// `StopScope` order (solver, request, step deadline, poll budget), so the first raised one
    /// wins. Called once per poll: a poll that reaches the budget spends one poll of it.
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
        if let Some(budget) = &self.polls {
            match budget.remaining.get().checked_sub(1) {
                Some(remaining) => budget.remaining.set(remaining),
                None => {
                    budget.record.set(PollBudgetRecord {
                        budget_exhausted: true,
                        ..budget.record.get()
                    });
                    // The budget, not a clock, is spent; the cause is the step deadline's because
                    // a spent budget means what a passed deadline means to every site the stop
                    // crosses: the step's work ended before its answer.
                    return Some(StopCause::Deadline(budget.mode));
                }
            }
        }
        None
    }

    /// Note in the enclosing [`with_poll_budget`] scope, if any, that a stop for lack of native
    /// stack was minted.
    #[cfg(not(target_family = "wasm"))]
    fn record_stack_stop(&self) {
        if let Some(budget) = &self.polls {
            budget.record.set(PollBudgetRecord {
                stack_exhausted: true,
                ..budget.record.get()
            });
        }
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

/// Bytes of native stack that must remain when the simplifier enters a call of
/// `simplify_with_budget` or `simplify_predicate_with_budget`, the points at which it checks the
/// stack (`with_stack_headroom`); with less, the call runs on a new segment or stops.
///
/// The zone must hold the deepest stretch of the same thread between two checks: the frames of
/// one level of simplifier recursion (at most 3.0 KiB in a release build, 4.0 KiB at opt-level 1
/// with debug assertions, the `dev` profile, and 17.3 KiB unoptimized: the distance between
/// consecutive checks along ground function chains `f^N(a)`, `h(…h(a, a)…, a)`, `g(w^N(a))` with
/// `g(w(X)) = w(g(X))`, and list counts over `cons` that add with `INT.add` once or twice per
/// level), plus the matching, builtin hooks, and SMT solver call that run on the thread between
/// two checks. Unoptimized (opt-level 0, the `debugging` profile), a whole simplification of a
/// conditional equation whose condition Z3 decides takes 62 KiB of stack from its entry, and the
/// Z3 call on such a condition alone takes 23 KiB (both measured by stack painting); the zone is
/// twice the whole simplification.
///
/// So a walk between two checks must not take stack in proportion to the height of a term: the
/// simplifier reaches the zone with the rest of a deep term still below it whenever its descent
/// takes more stack per level of the term than `nesting` provides (as an equation's does when its
/// result nests several function applications for each level of the argument it consumes), and such
/// a walk would then overrun the zone and abort the process. The walks the simplifier runs on terms
/// of any height keep their pending work on the heap instead, after a few levels of recursion at
/// most: definedness (`definedness::ceil_term`), apartness (`Term::apart_with`, eight levels,
/// `RECURSIVE_APART_LEVELS`), `Eq` and `Ord` for `Term` (eight levels,
/// `RECURSIVE_COMPARISON_LEVELS`), and the `KEQUAL` hook. The zone does not bound walks over the definition's own patterns (matching a
/// left-hand side, instantiating a right-hand side), which take stack in proportion to the height
/// of the definition's rules; the translation of a condition for the SMT solver and the solver
/// itself; hooks other than `KEQUAL` that walk their operands (`SUBSTITUTION`); or the derived
/// `Clone`, `Hash` and `Eq` of predicates, which a predicate's simplification applies to the rest
/// of a chain of connectives. Those take the stack `nesting::with_stack` provides for the height of
/// the operation's patterns, which holds them while the simplifier's descent stays within the
/// per-level bound there.
///
/// The zone is also a floor below which a thread simplifies nothing, so it stays well under the
/// smallest thread stacks embedders commonly run (512 KiB, the macOS default for secondary
/// threads). The stack that `nesting` provides for the recursive passes over patterns and
/// definitions keeps the same zone beyond what those passes take.
pub(crate) const STACK_RED_ZONE: usize = 128 * 1024;

/// Bytes of native stack left on the current thread, when they are known.
///
/// The resource is bytes of this thread's stack, and only the OS knows its bounds, which
/// `stacker` reads for every native thread whoever created it. The bounds of a thread that
/// `stacker` cannot read, and of every wasm32 build, where the engine's call-stack limit is
/// invisible to the module, are unknown, and a guard on them admits everything.
#[inline]
pub(crate) fn remaining_stack() -> Option<usize> {
    #[cfg(not(target_family = "wasm"))]
    {
        stacker::remaining_stack()
    }
    #[cfg(target_family = "wasm")]
    {
        None
    }
}

/// Whether the current thread has less than `STACK_RED_ZONE` bytes of stack left; an unknown
/// remaining stack never counts as exhausted.
#[inline]
fn stack_exhausted() -> bool {
    remaining_stack().is_some_and(|remaining| remaining < STACK_RED_ZONE)
}

/// The native stack of each segment [`with_stack_headroom`] runs the simplifier's recursion on:
/// a few thousand levels of it in a release build, so that the mapping is paid once per few
/// thousand levels. It is far above `STACK_RED_ZONE`, which the work on a fresh segment needs.
#[cfg(not(target_family = "wasm"))]
const SIMPLIFICATION_SEGMENT: usize = 16 << 20;

std::thread_local! {
    /// The bytes of the segments [`with_stack_headroom`] holds on this thread, and the most it may
    /// hold (`nesting::with_simplification_stack_budget`).
    static SIMPLIFICATION_SEGMENTS: Cell<(usize, usize)> =
        const { Cell::new((0, crate::nesting::SIMPLIFICATION_STACK_BUDGET)) };
}

/// The bytes of the segments [`with_stack_headroom`] holds on every thread of the process, which
/// stay within `nesting::SIMPLIFICATION_STACK_PROCESS_BUDGET`.
#[cfg(not(target_family = "wasm"))]
static PROCESS_SEGMENTS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Count one more segment of `segment` bytes in `total` if the count stays within `budget`, and
/// say whether it did.
#[cfg(not(target_family = "wasm"))]
fn reserve_segment(total: &std::sync::atomic::AtomicUsize, segment: usize, budget: usize) -> bool {
    total
        .try_update(Ordering::Relaxed, Ordering::Relaxed, |held| {
            held.checked_add(segment)
                .filter(|holding| *holding <= budget)
        })
        .is_ok()
}

/// The budget of the segments the simplifier's recursion may hold on this thread while `work`
/// runs; see `nesting::with_simplification_stack_budget`.
pub(crate) fn with_segment_budget<R>(budget: usize, work: impl FnOnce() -> R) -> R {
    struct Restore(usize);
    impl Drop for Restore {
        fn drop(&mut self) {
            SIMPLIFICATION_SEGMENTS.with(|segments| segments.set((segments.get().0, self.0)));
        }
    }
    let previous = SIMPLIFICATION_SEGMENTS.with(|segments| {
        let (held, previous) = segments.get();
        segments.set((held, budget));
        previous
    });
    let _restore = Restore(previous);
    work()
}

/// Run `work`, one level of the simplifier's recursion, with at least `STACK_RED_ZONE` bytes of
/// native stack. On a thread with that much left it runs inline: the check the simplifier has
/// always made at each level, and nothing more. Below it, `work` and the recursion under it run on
/// a new segment of `SIMPLIFICATION_SEGMENT` bytes, while the segments held on this thread stay
/// within the thread's budget and those held on every thread within the process's; past either,
/// or when the system refuses to map the segment, it stops with [`StopCause::StackExhausted`]
/// naming that limit, without running.
///
/// So a recursion takes stack only as deep as it goes: an operation that stays within its
/// thread's stack maps nothing, and one that recurses deeper pays one mapping per segment.
#[inline]
#[cfg_attr(debug_assertions, track_caller)]
pub(crate) fn with_stack_headroom<R, E: From<Stop>>(
    work: impl FnOnce() -> Result<R, E>,
) -> Result<R, E> {
    if stack_exhausted() {
        on_new_segment(work)
    } else {
        work()
    }
}

/// On wasm32 the remaining stack is unknown, so it is never exhausted and no segment is mapped.
#[cfg(target_family = "wasm")]
fn on_new_segment<R, E: From<Stop>>(work: impl FnOnce() -> Result<R, E>) -> Result<R, E> {
    work()
}

#[cfg(not(target_family = "wasm"))]
#[cold]
#[cfg_attr(debug_assertions, track_caller)]
fn on_new_segment<R, E: From<Stop>>(work: impl FnOnce() -> Result<R, E>) -> Result<R, E> {
    on_new_segment_within(
        &PROCESS_SEGMENTS,
        crate::nesting::SIMPLIFICATION_STACK_PROCESS_BUDGET,
        SIMPLIFICATION_SEGMENT,
        work,
    )
}

/// [`on_new_segment`] with the process's count and budget and the segment's size given:
/// `process` holds the bytes of the segments held on every thread, which stay within
/// `process_budget`, and the segment is `segment` bytes.
#[cfg(not(target_family = "wasm"))]
#[cfg_attr(debug_assertions, track_caller)]
fn on_new_segment_within<R, E: From<Stop>>(
    process: &std::sync::atomic::AtomicUsize,
    process_budget: usize,
    segment: usize,
    work: impl FnOnce() -> Result<R, E>,
) -> Result<R, E> {
    struct Release<'a> {
        held: usize,
        segment: usize,
        process: &'a std::sync::atomic::AtomicUsize,
    }
    impl Drop for Release<'_> {
        fn drop(&mut self) {
            SIMPLIFICATION_SEGMENTS.with(|segments| segments.set((self.held, segments.get().1)));
            self.process.fetch_sub(self.segment, Ordering::Relaxed);
        }
    }
    let (held, budget) = SIMPLIFICATION_SEGMENTS.with(Cell::get);
    let Some(holding) = held
        .checked_add(segment)
        .filter(|holding| *holding <= budget)
    else {
        return Err(Stop::out_of_stack(StackLimit::ThreadBudget(budget)).into());
    };
    if !reserve_segment(process, segment, process_budget) {
        return Err(Stop::out_of_stack(StackLimit::ProcessBudget(process_budget)).into());
    }
    SIMPLIFICATION_SEGMENTS.with(|segments| segments.set((holding, budget)));
    let _release = Release {
        held,
        segment,
        process,
    };
    match crate::nesting::map_segment(segment, work) {
        Ok(result) => result,
        Err(refused) => Err(Stop::out_of_stack(StackLimit::MappingRefused(refused)).into()),
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

/// Runs `action` with no request cancellation, no solver prelude signal, no step deadline and no
/// poll budget in force on this thread, and restores them afterwards: a computation whose result
/// is cached with a definition (the load-time critical-pair check) must not depend on the request
/// that happens to load it. Stops `action` arms itself (its own poll budget) still apply inside.
pub(crate) fn detached<T>(action: impl FnOnce() -> T) -> T {
    let saved =
        REGISTRY.with(|registry| std::mem::replace(&mut *registry.borrow_mut(), Registry::EMPTY));
    let _restore = DetachedGuard(Some(saved));
    action()
}

struct DetachedGuard(Option<Registry>);

impl Drop for DetachedGuard {
    fn drop(&mut self) {
        if let Some(saved) = self.0.take() {
            REGISTRY.with(|registry| *registry.borrow_mut() = saved);
        }
    }
}

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
/// solver. Polls on entry: a request that was cancelled before it starts, or a solver whose prelude
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

/// Runs `action` with at most `polls` polls of [`check`] passing on this thread: every later poll
/// raises `StopCause::Deadline(mode)`, as a passed deadline of that mode would, so every site the
/// stop crosses treats it as it treats a deadline. Unlike a deadline, the budget is spent by the
/// computation's own polls, so where it stops the computation is a function of the computation
/// alone, not of the time it takes on a loaded host or of the clock (which wasm32 lacks). Once
/// spent it stays spent for the rest of the scope, so a stop a site dismisses is raised again at
/// the next poll.
///
/// The budget replaces an enclosing one for the scope and is restored when the scope ends,
/// including on unwinding; a budget installed under it is the only one in force while it runs.
/// Returns `action`'s value and what the scope met ([`PollBudgetRecord`]).
pub(crate) fn with_poll_budget<T>(
    polls: u64,
    mode: StepTimeoutMode,
    action: impl FnOnce() -> T,
) -> (T, PollBudgetRecord) {
    struct Restore(Option<PollBudget>);
    impl Drop for Restore {
        fn drop(&mut self) {
            let previous = self.0.take();
            REGISTRY.with(|registry| registry.borrow_mut().polls = previous);
        }
    }
    let budget = PollBudget {
        remaining: Cell::new(polls),
        mode,
        record: Cell::new(PollBudgetRecord::default()),
    };
    let previous = REGISTRY.with(|registry| registry.borrow_mut().polls.replace(budget));
    let restore = Restore(previous);
    let value = action();
    let record = REGISTRY.with(|registry| {
        registry
            .borrow()
            .polls
            .as_ref()
            .map_or_else(PollBudgetRecord::default, |budget| budget.record.get())
    });
    drop(restore);
    (value, record)
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

    #[test]
    fn scopes_and_restores_active_tokens() {
        let outer = CancellationToken::new();
        let inner = CancellationToken::new();
        outer.cancel();

        assert_eq!(polled(), None);
        outer.scope(|| {
            assert!(polled().is_some());
            inner.scope(|| assert_eq!(polled(), None));
            assert!(polled().is_some());
        });
        assert_eq!(polled(), None);
    }

    #[test]
    fn cloned_tokens_signal_across_threads() {
        let token = CancellationToken::new();
        let signal = token.clone();
        std::thread::spawn(move || signal.cancel()).join().unwrap();

        assert!(token.is_cancelled());
    }

    #[test]
    fn prelude_signal_composes_with_outer_cancellation_and_does_not_leak() {
        let outer = CancellationToken::new();
        let operation = PreludeSignal::default();
        outer.scope(|| {
            with_prelude_signal(&operation, || {
                assert_eq!(polled(), None);
                operation.raise(PreludeFailure::Inconsistent);
                assert!(polled().is_some());
                assert!(!outer.is_cancelled());
            });
            assert_eq!(polled(), None);
            let next = PreludeSignal::default();
            with_prelude_signal(&next, || assert_eq!(polled(), None));
            outer.cancel();
            with_prelude_signal(&next, || assert!(polled().is_some()));
        });
        assert_eq!(polled(), None);
    }

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
            registry.request.is_none()
                && registry.solvers.is_empty()
                && no_deadline
                && registry.polls.is_none()
        })
    }

    /// A budget of `n` polls lets `n` polls pass, raises the mode's deadline cause at every later
    /// one, records that it did, and is gone when its scope ends.
    #[test]
    fn a_poll_budget_passes_its_polls_then_stops_every_later_one() {
        for polls in [0, 1, 3] {
            let (outcomes, record) = with_poll_budget(polls, MANUAL, || {
                (0..polls + 2).map(|_| polled()).collect::<Vec<_>>()
            });
            let passed = usize::try_from(polls).unwrap();
            assert!(
                outcomes[..passed].iter().all(Option::is_none),
                "{outcomes:?}"
            );
            assert!(
                outcomes[passed..]
                    .iter()
                    .all(|outcome| *outcome == Some(StopCause::Deadline(MANUAL))),
                "{outcomes:?}"
            );
            assert_eq!(
                record,
                PollBudgetRecord {
                    budget_exhausted: true,
                    stack_exhausted: false
                }
            );
            assert!(registry_is_empty());
        }
        let ((), record) = with_poll_budget(2, MANUAL, || {
            assert_eq!((polled(), polled()), (None, None));
        });
        assert_eq!(record, PollBudgetRecord::default());
    }

    /// An inner budget is the only one in force in its scope, the outer one is restored after it
    /// (on unwinding too), a detached computation runs without either, and a wider cause still
    /// wins over a spent budget.
    #[test]
    fn a_poll_budget_is_scoped() {
        let ((), outer) = with_poll_budget(1, MANUAL, || {
            let ((), inner) = with_poll_budget(0, AVERAGE, || {
                assert_eq!(polled(), Some(StopCause::Deadline(AVERAGE)));
            });
            assert!(inner.budget_exhausted);
            detached(|| assert_eq!(polled(), None));
            let unwound = catch_unwind(AssertUnwindSafe(|| {
                with_poll_budget(0, AVERAGE, || panic!("unwinds through the scope"))
            }));
            assert!(unwound.is_err());
            assert_eq!(polled(), None);
            assert_eq!(polled(), Some(StopCause::Deadline(MANUAL)));
            cancelled_token().scope(|| assert_eq!(polled(), Some(StopCause::Cancelled)));
        });
        assert!(outer.budget_exhausted);
        assert!(registry_is_empty());
    }

    /// A stack stop minted inside a budget's scope is recorded there, even when a site dismisses
    /// it before it reaches the scope's caller.
    #[cfg(not(target_family = "wasm"))]
    #[test]
    fn a_poll_budget_records_a_dismissed_stack_stop() {
        let record = std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                with_poll_budget(u64::MAX, MANUAL, || {
                    with_segment_budget(0, || {
                        with_stack_headroom(|| Ok::<_, Stop>(()))
                            .expect_err("the thread's budget refuses a segment")
                            .forgo_refinement();
                    });
                })
                .1
            })
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(
            record,
            PollBudgetRecord {
                budget_exhausted: false,
                stack_exhausted: true
            }
        );
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

        let headroom = || {
            with_stack_headroom(|| Ok::<_, Stop>(()))
                .err()
                .map(Stop::into_cause)
        };
        let exhausted = std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || with_segment_budget(0, headroom))
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(
            exhausted,
            Some(StopCause::StackExhausted(StackLimit::ThreadBudget(0)))
        );
        assert_eq!(headroom(), None);
        assert!(registry_is_empty());
    }

    /// Below the red zone, the work runs on a new segment while the budget holds one, and the
    /// segment is released afterwards, from the thread's count and the process's; nested past the
    /// budget, it stops.
    #[test]
    fn a_recursion_below_the_red_zone_goes_on_on_segments_within_the_budget() {
        fn descend(levels: usize) -> Result<usize, Stop> {
            with_stack_headroom(|| {
                let frame = std::hint::black_box([0_u8; 4096]);
                Ok(if levels == 0 {
                    0
                } else {
                    descend(levels - 1)? + usize::from(frame[0] == 0)
                })
            })
        }
        let held = || SIMPLIFICATION_SEGMENTS.with(Cell::get).0;
        let outcome = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                // About 9,000 levels of 4 KiB: two segments beyond the thread.
                let deep = with_segment_budget(3 * SIMPLIFICATION_SEGMENT, || descend(9_000));
                let released = held();
                let stopped = with_segment_budget(SIMPLIFICATION_SEGMENT, || descend(9_000))
                    .err()
                    .map(Stop::into_cause);
                // One segment at a time, more segments in all than the process may hold at once:
                // each is released from the process's count too.
                let repeated = (0..=crate::nesting::SIMPLIFICATION_STACK_PROCESS_BUDGET
                    / SIMPLIFICATION_SEGMENT)
                    .all(|_| {
                        with_segment_budget(SIMPLIFICATION_SEGMENT, || descend(200))
                            .map_err(Stop::into_cause)
                            .is_ok()
                    });
                (deep.ok(), released, stopped, held(), repeated)
            })
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(
            outcome,
            (
                Some(9_000),
                0,
                Some(StopCause::StackExhausted(StackLimit::ThreadBudget(
                    SIMPLIFICATION_SEGMENT
                ))),
                0,
                true
            )
        );
    }

    /// A segment is counted in a total while the total stays within its budget, and a released
    /// one makes room for another.
    #[test]
    fn a_segment_is_reserved_only_within_the_total_budget() {
        let total = std::sync::atomic::AtomicUsize::new(0);
        let budget = 2 * SIMPLIFICATION_SEGMENT;
        let segment = SIMPLIFICATION_SEGMENT;
        assert!(reserve_segment(&total, segment, budget));
        assert!(reserve_segment(&total, segment, budget));
        assert!(!reserve_segment(&total, segment, budget));
        assert_eq!(total.load(Ordering::Relaxed), budget);
        total.fetch_sub(segment, Ordering::Relaxed);
        assert!(reserve_segment(&total, segment, budget));
        assert!(!reserve_segment(&total, segment, budget + segment - 1));
    }

    /// A segment the thread's budget allows is refused when the process's count is at its
    /// budget, and it is released from that count afterwards.
    #[test]
    fn a_segment_is_refused_at_the_process_budget() {
        let process = std::sync::atomic::AtomicUsize::new(0);
        let held = || SIMPLIFICATION_SEGMENTS.with(Cell::get).0;
        let outcome = with_segment_budget(3 * SIMPLIFICATION_SEGMENT, || {
            let segment = SIMPLIFICATION_SEGMENT;
            on_new_segment_within(&process, segment, segment, || {
                let inner = on_new_segment_within(&process, segment, segment, || Ok::<_, Stop>(()))
                    .err()
                    .map(Stop::into_cause);
                Ok::<_, Stop>((inner, held(), process.load(Ordering::Relaxed)))
            })
        });
        assert_eq!(
            outcome.ok(),
            Some((
                Some(StopCause::StackExhausted(StackLimit::ProcessBudget(
                    SIMPLIFICATION_SEGMENT
                ))),
                SIMPLIFICATION_SEGMENT,
                SIMPLIFICATION_SEGMENT
            ))
        );
        assert_eq!((held(), process.load(Ordering::Relaxed)), (0, 0));
    }

    /// A segment both budgets admit and the system refuses to map (here larger than the address
    /// space of the process) stops with the refused mapping named, not with a budget: the work
    /// does not run, and the segment is released from the thread's count and the process's.
    #[cfg(target_pointer_width = "64")]
    #[test]
    fn a_segment_the_system_refuses_stops_naming_the_refused_mapping() {
        let process = std::sync::atomic::AtomicUsize::new(0);
        let held = || SIMPLIFICATION_SEGMENTS.with(Cell::get).0;
        let segment = 1 << 60;
        let mut ran = false;
        let stopped = with_segment_budget(usize::MAX, || {
            on_new_segment_within(&process, usize::MAX, segment, || {
                ran = true;
                Ok::<_, Stop>(())
            })
            .err()
            .map(Stop::into_cause)
        });
        assert!(!ran);
        assert_eq!(
            stopped,
            Some(StopCause::StackExhausted(StackLimit::MappingRefused(
                crate::nesting::SegmentRefused { size: segment }
            )))
        );
        assert_eq!((held(), process.load(Ordering::Relaxed)), (0, 0));
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
        for limit in [
            StackLimit::ThreadBudget(0),
            StackLimit::ProcessBudget(0),
            StackLimit::MappingRefused(crate::nesting::SegmentRefused { size: 0 }),
        ] {
            assert_eq!(
                StopCause::StackExhausted(limit).scope(),
                StopCause::Deadline(MANUAL).scope()
            );
        }
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

    /// A layered result, as a module boundary returns it. Only the drop-check tests, which run
    /// under debug assertions, use it.
    #[cfg(debug_assertions)]
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
            let narrower = check().unwrap_err();
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
        // Each limit is named with its own remedy, and its size as the budget or segment had it.
        assert_eq!(
            StopCause::StackExhausted(StackLimit::ThreadBudget(1 << 30)).to_string(),
            "simplification exhausted its native stack: the thread's stack and its budget of \
             1 GiB more are used up: a recursion went too deep"
        );
        assert_eq!(
            StopCause::StackExhausted(StackLimit::ProcessBudget(4 << 30)).to_string(),
            "simplification exhausted its native stack: the segments of every thread together \
             reached the process's budget of 4 GiB: deep recursions on several threads at once, \
             or one thread whose budget is above the process's"
        );
        assert_eq!(
            StopCause::StackExhausted(StackLimit::MappingRefused(crate::nesting::SegmentRefused {
                size: 16 << 20
            }))
            .to_string(),
            "simplification exhausted its native stack: the system refused to map another \
             16 MiB segment: the address space or memory the process may use ran out before the \
             stack budget did"
        );
        assert_eq!(
            StopCause::StackExhausted(StackLimit::ThreadBudget(0)).to_string(),
            "simplification exhausted its native stack: the thread's stack and its budget of \
             0 bytes more are used up: a recursion went too deep"
        );
        assert_eq!(
            PreludeFailure::Inconsistent.to_string(),
            "the SMT prelude (the definition's SMT axioms and any user prelude) is unsatisfiable"
        );
        assert_eq!(
            PreludeFailure::Unknown("timeout".into()).to_string(),
            "the solver did not decide whether the SMT prelude (the definition's SMT axioms and \
             any user prelude) is satisfiable (timeout)"
        );
        assert_eq!(
            StopCause::SolverPrelude(PreludeFailure::Inconsistent).to_string(),
            "could not initialize Z3: the SMT prelude (the definition's SMT axioms and any user \
             prelude) is unsatisfiable"
        );
        assert_eq!(StopCause::Cancelled.to_string(), "Request cancelled");
    }
}
