//! A probe: an in-process caller that observes the steps of selected rules along a run's path,
//! and may end the request or the path there ([`ExecutionOptions::probe_rules`](super::ExecutionOptions::probe_rules)).
//!
//! # Meaning
//!
//! A *point* is a step `s → s'` by a rule [`ProbeRules`] selects, on its before or after side,
//! whose successor `s'` is defined, and which the path takes. Its *observed state* is `s` for a
//! before point and the normalized `s'` for an after point, the same states a stop's cut-point
//! and terminal rules end a path at ([`StopSide`]). A rule is selected by its label or its
//! `UNIQUE_ID`, as a stop rule is.
//!
//! The probe is asked at each point ([`Probe::observe`]), once, in path order; at one step the
//! before point is asked before the after point. Its answer decides what follows:
//! - [`ProbeDecision::Continue`]: nothing; the path goes on as without the probe.
//! - [`ProbeDecision::Differs`]: the request ends. The path's leaf is the observed state, with
//!   the halt [`HaltReason::ProbeDifference`](super::HaltReason::ProbeDifference), and no
//!   pending state is explored.
//! - [`ProbeDecision::Done`]: the path ends, its leaf the observed state with the halt
//!   [`HaltReason::ProbeDone`](super::HaltReason::ProbeDone).
//!
//! Neither halt is an end of the system: each says where the probe stopped the run, never that
//! the configuration is final. Neither is ever merged with another leaf, and only a request
//! with a probe has them.
//!
//! A point exists only because its step's successor is defined, so the leaf an answer makes
//! carries the successor's diagnostics: the path's up to the step and every one the step and
//! the successor's normalization added (a simplification budget spent before an equation that
//! would have shown the successor undefined, a path fact). At an after point they are the
//! observed state's own; at a before point the leaf is otherwise the state before the step.
//!
//! Whether a step's successor is defined is shown by the successor's own normalization, so the
//! points of a step are asked once that normalization shows it defined, before anything else
//! is done with it (the depth bound, merging, the next step). A step whose successor is
//! undefined, or whose normalization did not finish (a stop, a failed simplification, the work
//! budget reached first), has no point. A step a stop ends the path before is not taken, so the
//! `stop_count`th event of a cut-point rule has no point; a terminal rule's step is taken, so
//! its after point is asked, and the path then ends at the terminal rule unless the probe ended
//! it first.
//!
//! # One path
//!
//! A probe that does not follow paths ([`Probe::follows_paths`], the default) observes one
//! path. A run's path splits where the state being expanded leaves more than one path: several
//! successors (applied candidates or a remainder), a successor beside leaves of the same step (an
//! undefined step's instances), or a branch leaf reporting several successors. There the probe is
//! told once ([`Probe::branched`]), and from then on it is asked nothing: its callbacks name no
//! path it can tell apart, so the points of several paths, in the order the run explores them,
//! are no sequence of one path. Where the path ends first, at any leaf other than the probe's
//! own, the probe is told once ([`Probe::ended`]) and reads the leaf's state.
//! Under strategy `any` each instance of a state takes the successors of one rule at most, but
//! a state still leaves several paths where its instances take different rules or a remainder
//! (a symbolic state), or where the rule's right-hand side has several alternatives; the probe
//! is told of a split there as under `all`.
//!
//! # Several paths
//!
//! A probe that follows paths is asked along every path the run explores, each named by a
//! [`ProbePath`]: every point ([`ProbeArrival::path`]), every end ([`ProbeLeaf::path`]) and a
//! return ([`ProbeCycle::path`]) names the path it is of. The run starts on
//! [`ProbePath::ROOT`]. Where the state being expanded on a path leaves anything but one
//! successor and no leaf, the path splits, in this order:
//! 1. each path it leaves, a successor or a leaf, gets a new name, and the probe is told that the
//!    new path starts as the old one stands ([`Probe::fork`]), before any point of it is asked;
//! 2. the probe is told the old path's state at that depth left exactly those paths
//!    ([`Probe::split`]), and is asked nothing more of the old path;
//! 3. each leaf among them is told as the end of its own path ([`Probe::ended`]), unless the
//!    probe's own answer made it.
//!
//! A split into no path is a state the run found to have no instance (its normalization is
//! `\bottom`), or whose step it found undefined where a leaf of another path already stands for
//! those instances: no path of the definition goes on from it. A split into one path renames it, where a point of a terminal rule's step was
//! asked within the expansion: its path is forked before that point, since the run does not yet
//! know there what else the expansion leaves. The initial states are the paths the root splits
//! into at depth 0 when there are several. A leaf a breadth bound makes of a pending state is told
//! as the end of that state's path.
//!
//! The points of a step are asked once its successor's normalization shows it defined, on the
//! successor's path, so a step's points are always asked after the split of its state is told.
//!
//! An answer of a path is that path's: `Done` ends that path only, and the run goes on with the
//! others; `Differs` ends the request. A path the run stops exploring without a leaf of its own
//! (the work budget reached on another path, a stop that ends the run, a difference) is told
//! nothing more: what the probe holds of it is where the run left it. Such a path's state is
//! pending, never normalized, and was forked where its parent split, since the run expands a
//! state's one successor next: nothing was asked of the path after its fork, so what the probe
//! holds of it is what it held of the path it was forked from when that path split.
//!
//! ## Merging
//!
//! A state-set run that explores every branch merges an arriving state into an equal state of its
//! depth whose expansion completed (`exploration_merge`): the arriving state's subtree would give
//! the same leaves. Under a probe that follows paths it gives the same answers too only where the
//! probe's state of both paths is the same, so the probe's history of the arriving state's path
//! ([`Probe::history`], read once the points of the step into it were asked) is part of what the
//! two states must share. Two states whose histories differ are never merged, and both are
//! expanded. A merged state's path is told so ([`Probe::merged`]): its continuation is the
//! recorded state's, on the path the probe was told of that state, which the probe sees there.
//!
//! The history is the probe's: equal histories of two paths must say that the probe answers alike
//! on both from equal states, and that what it keeps of either it keeps of the other. A digest of
//! everything a path's later answers rest on is one. A probe whose history is the same on every
//! path leaves the run's merging as it is without the probe.
//!
//! ## Cycles on several paths
//!
//! A probe that follows paths is told of a return ("Cycles") only before the run's first split:
//! a return proves that its path runs forever only where that path left each state up to it by its
//! one successor, which nothing checks once several paths interleave.
//!
//! # What the run records of a step with a point
//!
//! A step whose points are asked is taken: its successor was built, normalized and shown
//! defined. Where an answer ends the path at a before point, the run's own records count the
//! step as they count every taken step: the rule is committed and its bindings recorded
//! (coverage), and the successor is matched as a reached state
//! ([`ExecutionOptions::match_states`](super::ExecutionOptions::match_states)); so is the
//! successor at an after point, which takes part in no merging. The leaf is the observed state:
//! its depth, trace, branch, observations, effects and counts end before the step, and only its
//! diagnostics, as above, include the step's. A cut-point rule's last event differs: its step is
//! not taken, so it is proposed and never committed, its successor is not matched, and the leaf
//! carries it as a proposal.
//!
//! # Continue changes nothing
//!
//! A probe that always continues, and whose history is the same on every path where it follows
//! paths ("Merging"), leaves the run as it is without the probe: the same leaves, coverage, traces
//! and work. The probe is asked at a point of the successor's normalization
//! the run reaches anyway and costs the run no state visit; nothing the probe does is the run's
//! (below).
//!
//! # Isolation
//!
//! The probe is asked from the stepping loop, between two phases of a state's expansion, never
//! inside a simplification or a rewrite, and isolated from the run as a stop condition is
//! (`stop_condition`, "Isolation"): it reports to no coverage set, emits no diagnostic into
//! the run, notes no path fact, fills none of the run's memos, runs off the run's clock, in a
//! proof evaluation scope without a console and outside the run's definition scope. A
//! cancellation of the request stays visible inside it and ends the run at its next poll.
//!
//! # Cycles
//!
//! A probe that keeps states ([`Probe::cycle_states`]) is told when its path returns to an
//! earlier state of itself with the probe's progress unchanged ([`Probe::cycled`]). Such a return
//! proves that the path runs forever, repeating the steps between the two states, and that the
//! probe sees nothing new on it. The run recognizes the return; the probe decides what it means.
//!
//! The run compares each state of the path, once its normalization is done and before its step,
//! with the states it keeps. Two states are one state where their configurations are the same
//! ground term with no constraint, and their stop events and arrivals at a stop
//! ([`ExecutionOptions::stop_count`](super::ExecutionOptions::stop_count)), committed effects and
//! console are alike. Only such states are compared and kept:
//! - A ground term with no constraint denotes one element in every model, so two equal ones are
//!   one state in every model. A state with a variable or a constraint denotes a set of states,
//!   and two syntactically equal ones need not be one state of one path, so a symbolic state is
//!   never compared: an equality the run cannot decide is never a return.
//! - An initial input is not kept: the run treats its definedness otherwise than a reached
//!   state's.
//! - The run compares under strategy `all` only, where a state the path leaves by one successor
//!   has that successor and no other in the definition.
//!
//! What a state's path does next rests on the state alone. Its successors are the definition's
//! rewrites of its configuration, cut by the stops its stop events and arrivals select, and its
//! console reads read the console as it stands. The depth, the work and the clock only cut a path,
//! and the merge table plays no part on one path. So where the path left the earlier state by one
//! successor at each state up to the later one, the path from the later state is the path from the
//! earlier one again, forever. This rests on the definition's step of a state being a function of
//! the state and on the run having decided each of those steps, not on what the run would decide
//! on a second pass. Whether each step was decided without a diagnostic, and whether the states
//! are real, are facts of the leaf the probe's answer makes, which the probe's caller reads.
//!
//! The probe's progress ([`Probe::progress`]) stands for everything its later answers rest on
//! besides the states it observes. It is read at each compared state, after the points of the step
//! into it and before those of the step out of it, and the kept states are those reached since
//! the progress last changed. An equal progress at both states says the probe's state did not
//! change between them. So at each point of the next pass the probe is in the state it was in at
//! that point of the first, observes the state it observed there, and answers as it did.
//!
//! The run keeps at most `cycle_states` states since the progress last changed. A state is
//! compared with the kept states and then kept if there is room; a state reached once the room is
//! full is compared but not kept. So a return to a state reached past the room is not recognized,
//! and no cycle is claimed for it. The room bounds the memory, and a state costs a lookup by its
//! configuration's stored hash.
//!
//! The probe is told of a return at most once, isolated as at a point, with the state, the depth
//! of the earlier equal state, and the rule whose step reached the state. Its answer is read as
//! at an after point of that rule, whose observed state is the state:
//! - `Differs` ends the request, and `Done` the path, each with a leaf of the state.
//! - `Continue` lets the run go on as without the probe, which is not told of a return again.
//!
//! # Reading a state
//!
//! The observed state is read through [`ProbeState`]: a cell by its path of cell symbols, its
//! cost the walk down the path and the size of the cell; a handle on a cell
//! ([`ProbeState::cell_handle`]), which tells an unchanged cell from a changed one at the cost
//! of a pointer comparison while the handle is held; and a list cell's length and the items
//! from a position on ([`ProbeState::list_len`], [`ProbeState::list_items`]), so a log is read
//! by what was appended since the last read.

use std::collections::BTreeSet;

use k_rust_kore::kore::ast as kore;
use rustc_hash::FxHashMap;

use super::{HaltReason, StopSide};
use crate::term::{Term, TermKind};
use crate::transition::{EffectJournal, ExecutionIoState};

/// The rules whose steps a probe observes, by label or `UNIQUE_ID`, on each side of the step
/// ([module documentation](self)).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ProbeRules {
    /// The rules whose steps are before points: the observed state is the state before the step.
    pub before: BTreeSet<String>,
    /// The rules whose steps are after points: the observed state is the normalized successor.
    pub after: BTreeSet<String>,
}

impl ProbeRules {
    /// Whether no rule is selected on either side.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.before.is_empty() && self.after.is_empty()
    }
}

/// A path of a run, as a probe that follows paths is told of it ([module documentation](self),
/// "Several paths"). The run names each path once; a probe that does not follow paths sees only
/// [`Self::ROOT`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProbePath(pub(crate) u64);

impl ProbePath {
    /// The path the run starts on.
    pub const ROOT: Self = Self(0);

    /// The path's number: [`Self::ROOT`] is 0, and every other path is numbered after every
    /// path the run named before it.
    #[must_use]
    pub const fn index(self) -> u64 {
        self.0
    }
}

/// What a [`Probe`] answers at a point.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProbeDecision {
    /// The path goes on as without the probe.
    Continue,
    /// The request ends at the observed state, `probe-difference`, with this reason.
    Differs(String),
    /// The path ends at the observed state, `probe-done`.
    Done,
}

/// An in-process observer of a run's path ([module documentation](self)).
pub trait Probe {
    /// Answer a point: a taken step of a selected rule whose successor is defined. A before
    /// point reads the state before the step, an after point the normalized successor.
    fn observe(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision;

    /// The path split at the state at `depth`: from here the run has more than one path, and
    /// the probe is asked nothing more. Asked at most once, and only of a probe that does not
    /// follow paths.
    fn branched(&mut self, depth: u64) {
        let _ = depth;
    }

    /// The path [`ProbeLeaf::path`] ended at `leaf`, a leaf other than one the probe's own answer
    /// made. Asked at most once of each path; of a probe that does not follow paths, only before
    /// its path split, and never after [`Self::branched`].
    fn ended(&mut self, leaf: &ProbeLeaf<'_>);

    /// Whether the probe follows every path of the run ([module documentation](self), "Several
    /// paths"), rather than one path up to its first split. Read once, when the run starts.
    fn follows_paths(&self) -> bool {
        false
    }

    /// The new path `into` starts as the path `from` stands: the probe's state of `into` is its
    /// state of `from` now. Asked only of a probe that follows paths, before any question of
    /// `into`.
    fn fork(&mut self, from: ProbePath, into: ProbePath) {
        let _ = (from, into);
    }

    /// The state at `depth` of the path `path` left exactly the paths `into`, each forked from
    /// `path` ([`Self::fork`]); none where no path of the definition goes on from it. The probe
    /// is asked nothing more of `path`. Asked only of a probe that follows paths.
    fn split(&mut self, path: ProbePath, depth: u64, into: &[ProbePath]) {
        let _ = (path, depth, into);
    }

    /// The state at `depth` of the path `path` was merged into an equal state of that depth, of
    /// a path with an equal history ([`Self::history`]), whose expansion completed: its
    /// continuation is that state's, and the probe is asked nothing more of `path`. Asked only of
    /// a probe that follows paths, under a state-set run that explores every branch.
    fn merged(&mut self, path: ProbePath, depth: u64) {
        let _ = (path, depth);
    }

    /// The probe's history of the path `path`, which a state of it must share with a recorded
    /// state to be merged into it ([module documentation](self), "Merging"): equal histories say
    /// that the probe answers alike on both paths from equal states. Read, isolated, at each state
    /// the merge table compares, once the points of the step into it were asked. Asked only of a
    /// probe that follows paths.
    fn history(&self, path: ProbePath) -> [u8; 32] {
        let _ = path;
        [0; 32]
    }

    /// How many states of the path, reached since the probe's progress last changed, the run
    /// keeps to recognize a return to one of them ([module documentation](self), "Cycles"). Read
    /// once, when the run starts. 0, the default, keeps none: the probe is never told of a return,
    /// and the run does no work for it.
    fn cycle_states(&self) -> usize {
        0
    }

    /// The probe's progress: a number that changes whenever anything its later answers and its
    /// own state rest on changes, other than the states it observes. Two equal readings say that
    /// nothing the probe's answers rest on changed between them. A count of every change the probe
    /// made to what it keeps is one; the probe must not answer by the clock or by chance. Read at
    /// each state the run compares, isolated as a point is.
    fn progress(&self) -> u64 {
        0
    }

    /// The path returned to an earlier state of itself with the probe's progress unchanged, so it
    /// runs forever and the probe sees nothing new on it ([module documentation](self),
    /// "Cycles"). Asked at most once, only while the path has not split or ended; the answer is
    /// read as at an after point of [`ProbeCycle::rule`].
    fn cycled(&mut self, cycle: &ProbeCycle<'_>) -> ProbeDecision {
        let _ = cycle;
        ProbeDecision::Continue
    }
}

/// A state as a probe reads it: its depth and its configuration.
pub struct ProbeState<'a> {
    pub(crate) depth: u64,
    pub(crate) term: &'a Term,
}

impl ProbeState<'_> {
    /// The depth of the state on its path.
    #[must_use]
    pub fn depth(&self) -> u64 {
        self.depth
    }

    /// The state's whole configuration (its term, without its constraints), as KORE. Its cost
    /// is the size of the configuration; [`Self::cell`] converts one cell.
    #[must_use]
    pub fn configuration(&self) -> kore::Pattern {
        crate::externalize::term(self.term)
    }

    /// The cell at `path` of the configuration, as KORE, or `None` where the configuration holds
    /// no such cell.
    ///
    /// `path` names cell symbols from the configuration's top cell down: `path[0]` is the
    /// configuration's own symbol, and each further symbol is that of a cell the previous one
    /// holds as a direct argument. Only that cell is converted, so the cost is the walk down the
    /// path and the size of the cell, not of the configuration.
    #[must_use]
    pub fn cell(&self, path: &[&str]) -> Option<kore::Pattern> {
        cell_term(self.term, path).map(crate::externalize::term)
    }

    /// A handle on the cell at `path` ([`Self::cell`]), or `None` where there is no such cell.
    /// Two handles are [`CellHandle::same`] when they hold the same term node: a cell no step
    /// rewrote keeps its node, so an unchanged cell is told from a changed one without
    /// converting either. The handle holds the node, so it is not freed while the handle exists.
    #[must_use]
    pub fn cell_handle(&self, path: &[&str]) -> Option<CellHandle> {
        cell_term(self.term, path).map(|cell| CellHandle(cell.clone()))
    }

    /// The number of items of the list the cell at `path` holds, or `None` where there is no
    /// such cell or its content is not a list of known items.
    ///
    /// The cell's content is the cell's one argument, a list of a collection sort, or the cell
    /// itself where `path` names no cell symbol below a list. A list whose middle is not a list
    /// of items (a variable, an unevaluated application) has no known items.
    #[must_use]
    pub fn list_len(&self, path: &[&str]) -> Option<usize> {
        list_heads(self.term, path).map(crate::term::Items::len)
    }

    /// The items of the list the cell at `path` holds ([`Self::list_len`]) from position `from`
    /// on, each element as KORE (without its `ListItem` wrapper), or `None` where there is no
    /// such list. Only those items are converted, so a log read by what was appended since its
    /// last length costs the walk down the path and the size of the new items. A `from` past the
    /// end reads none.
    #[must_use]
    pub fn list_items(&self, path: &[&str], from: usize) -> Option<Vec<kore::Pattern>> {
        let heads = list_heads(self.term, path)?;
        if from >= heads.len() {
            return Some(Vec::new());
        }
        Some(heads.range(from..).map(crate::externalize::term).collect())
    }
}

/// A point a [`Probe`] is asked about: the rule, the side and the observed state.
pub struct ProbeArrival<'a> {
    pub(crate) rule: &'a str,
    pub(crate) side: StopSide,
    pub(crate) path: ProbePath,
    pub(crate) state: ProbeState<'a>,
}

impl<'a> ProbeArrival<'a> {
    /// The path of the point ([`ProbePath::ROOT`] for a probe that does not follow paths).
    #[must_use]
    pub fn path(&self) -> ProbePath {
        self.path
    }

    /// The rule, by the name the request selected it by.
    #[must_use]
    pub fn rule(&self) -> &str {
        self.rule
    }

    /// Whether the observed state is before the rule's step or its normalized successor.
    #[must_use]
    pub fn side(&self) -> StopSide {
        self.side
    }

    /// The observed state.
    #[must_use]
    pub fn state(&self) -> &ProbeState<'a> {
        &self.state
    }
}

impl<'a> std::ops::Deref for ProbeArrival<'a> {
    type Target = ProbeState<'a>;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}

/// The leaf a path ended at, as [`Probe::ended`] is told of it.
pub struct ProbeLeaf<'a> {
    pub(crate) halt: &'a HaltReason,
    pub(crate) path: ProbePath,
    pub(crate) state: ProbeState<'a>,
}

impl<'a> ProbeLeaf<'a> {
    /// The path that ended ([`ProbePath::ROOT`] for a probe that does not follow paths).
    #[must_use]
    pub fn path(&self) -> ProbePath {
        self.path
    }

    /// The leaf's halt.
    #[must_use]
    pub fn halt(&self) -> &HaltReason {
        self.halt
    }

    /// The leaf's state: its depth and configuration.
    #[must_use]
    pub fn state(&self) -> &ProbeState<'a> {
        &self.state
    }
}

impl<'a> std::ops::Deref for ProbeLeaf<'a> {
    type Target = ProbeState<'a>;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}

/// A return of the path to an earlier state of itself, as [`Probe::cycled`] is told of it.
pub struct ProbeCycle<'a> {
    pub(crate) first: u64,
    pub(crate) rule: &'a str,
    pub(crate) path: ProbePath,
    pub(crate) state: ProbeState<'a>,
}

impl<'a> ProbeCycle<'a> {
    /// The path that returned ([`ProbePath::ROOT`]: a return is recognized only before the run's
    /// first split).
    #[must_use]
    pub fn path(&self) -> ProbePath {
        self.path
    }

    /// The depth of the earlier state equal to this one.
    #[must_use]
    pub fn first(&self) -> u64 {
        self.first
    }

    /// The rule whose step reached the state, by its label, or its `UNIQUE_ID` where it has none.
    #[must_use]
    pub fn rule(&self) -> &str {
        self.rule
    }

    /// The state: the later of the two, and its depth.
    #[must_use]
    pub fn state(&self) -> &ProbeState<'a> {
        &self.state
    }
}

impl<'a> std::ops::Deref for ProbeCycle<'a> {
    type Target = ProbeState<'a>;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}

/// The states a probed path keeps to recognize a return to one of them ([module
/// documentation](self), "Cycles").
pub(super) struct CycleWatch {
    /// The most states kept ([`Probe::cycle_states`]).
    room: usize,
    /// The probe's progress when the kept states were reached; `None` before the first state.
    progress: Option<u64>,
    /// The kept states, by configuration.
    kept: FxHashMap<Term, Vec<Kept>>,
    len: usize,
}

/// A kept state: what besides its configuration its path's continuation rests on, and its depth.
struct Kept {
    depth: u64,
    stops: (u64, u64),
    effects: EffectJournal,
    io: Option<ExecutionIoState>,
}

impl Kept {
    fn alike(&self, state: &Watched<'_>) -> bool {
        self.stops == state.stops
            && self.effects.fingerprint() == state.effects.fingerprint()
            && self.effects == *state.effects
            && match (&self.io, state.io) {
                (None, None) => true,
                (Some(kept), Some(io)) => kept.observed_alike(io),
                _ => false,
            }
    }
}

/// A state as [`CycleWatch::returns`] compares it.
pub(super) struct Watched<'s> {
    pub(super) depth: u64,
    pub(super) term: &'s Term,
    /// The stop events and the arrivals at a stop the state's path passed.
    pub(super) stops: (u64, u64),
    pub(super) effects: &'s EffectJournal,
    /// The console, where it is available to the path.
    pub(super) io: Option<&'s ExecutionIoState>,
}

impl CycleWatch {
    /// A watch keeping at most `room` states, or `None` where `room` is 0.
    pub(super) fn new(room: usize) -> Option<Self> {
        (room > 0).then(|| Self {
            room,
            progress: None,
            kept: FxHashMap::default(),
            len: 0,
        })
    }

    /// The depth of the kept state `state` returns to, given the probe's `progress` at it; where
    /// there is none, `state` is kept if there is room. A change of progress forgets every kept
    /// state first. The caller passes only a reached, normalized, ground state with no
    /// constraint, which is no initial input ([module documentation](self), "Cycles").
    pub(super) fn returns(&mut self, state: &Watched<'_>, progress: u64) -> Option<u64> {
        if self.progress != Some(progress) {
            self.kept.clear();
            self.len = 0;
            self.progress = Some(progress);
        }
        debug_assert!(state.term.attributes().variables.is_empty());
        if let Some(earlier) = self
            .kept
            .get(state.term)
            .and_then(|kept| kept.iter().find(|kept| kept.alike(state)))
        {
            return Some(earlier.depth);
        }
        if self.len < self.room {
            self.kept.entry(state.term.clone()).or_default().push(Kept {
                depth: state.depth,
                stops: state.stops,
                effects: state.effects.clone(),
                io: state.io.cloned(),
            });
            self.len += 1;
        }
        None
    }
}

/// A held cell of an observed state ([`ProbeState::cell_handle`]).
#[derive(Clone, Debug)]
pub struct CellHandle(Term);

impl CellHandle {
    /// Whether both handles hold the same term node. Equal nodes are equal cells; distinct
    /// nodes may still be equal cells, which [`Self::kore`] then tells.
    #[must_use]
    pub fn same(&self, other: &Self) -> bool {
        self.0.ptr_eq(&other.0)
    }

    /// The cell as KORE.
    #[must_use]
    pub fn kore(&self) -> kore::Pattern {
        crate::externalize::term(&self.0)
    }
}

/// The cell at `path` of `term` ([`ProbeState::cell`]).
pub(super) fn cell_term<'t>(term: &'t Term, path: &[&str]) -> Option<&'t Term> {
    let (first, below) = path.split_first()?;
    let mut current = term;
    if application_symbol(current)? != *first {
        return None;
    }
    for symbol in below {
        let TermKind::Application { arguments, .. } = current.kind() else {
            return None;
        };
        current = arguments
            .iter()
            .find(|argument| application_symbol(argument) == Some(symbol))?;
    }
    Some(current)
}

/// The items of the list the cell at `path` of `term` holds, where the list has no middle
/// ([`ProbeState::list_len`]).
fn list_heads<'t>(term: &'t Term, path: &[&str]) -> Option<&'t crate::term::Items<Term>> {
    let cell = cell_term(term, path)?;
    let list = match cell.kind() {
        TermKind::Application { arguments, .. } => match arguments.as_slice() {
            [content] => content,
            _ => return None,
        },
        _ => cell,
    };
    match list.kind() {
        TermKind::List {
            heads, rest: None, ..
        } => Some(heads),
        _ => None,
    }
}

fn application_symbol(term: &Term) -> Option<&str> {
    match term.kind() {
        TermKind::Application { symbol, .. } => Some(&symbol.name),
        _ => None,
    }
}

/// Run `ask`, an in-process caller's work, isolated from the run ([module documentation](self),
/// "Isolation"): no coverage, no diagnostic, no path fact, off the run's clock, in a proof
/// evaluation scope, outside the run's definition scope.
pub(super) fn isolated<R>(ask: impl FnOnce() -> R) -> R {
    let (answer, _) = crate::coverage::isolated(u64::MAX, || {
        let _proof =
            crate::evaluation::EvaluationScope::enter(crate::evaluation::EvaluationMode::Proof);
        crate::term::domain::outside_definition_scopes(ask)
    });
    answer
}
