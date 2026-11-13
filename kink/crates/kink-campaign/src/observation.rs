//! Observations: a campaign's runs compared by declared observation channels, so that a program
//! that never ends is still a case, and a mutant is killed by the first decided difference of a
//! finite prefix of its run ([`Observe`], [`crate::RunOptions::observe`]).
//!
//! # Declarations
//!
//! An observation declaration is a finite set of channels, stated at the K level: every rule by
//! its exact K label and every cell by its K cell name, and every content as the cell holds it
//! (there is no observer, so no function of a cell is evaluated).
//! - A point class ([`PointClass`]) names rewrite rules, each on its before or after side, a
//!   content (cells), and a stuttering mode ([`Stutter`]), which has no default. A point event is
//!   a step of a path by such a rule whose successor is defined; its observed state is the state
//!   before the step for a before rule and the normalized successor for an after rule. The class's
//!   channel is the sequence of its events' contents in path order, without an element equal to
//!   the previous one under [`Stutter::Collapse`].
//! - A log ([`Log`]) names a `List` cell and the point classes at whose events it is read (their
//!   rules and sides); it is also read where the path ends. Its channel is the concatenation of
//!   the items the cell appends, every item an element: two equal consecutive items are two
//!   elements. The baseline's cell is checked to only grow by appending: each read must hold the
//!   earlier read as a prefix, item for item, or the baseline's campaign is refused
//!   (`log-not-appended`), since its channel is then no concatenation of appended items.
//!
//! A campaign without a declaration ([`Observe::NONE`]) makes every request, key, verdict and
//! record it made before observations existed.
//!
//! # Elements, and how a channel ends
//!
//! An element is the content of one event (or one log item): a tuple of ground terms, each a
//! value of kink's terminal-value walk under the baseline's definition (free constructors,
//! normal-form injections, domain values with an injective codec, and ground natural collections
//! rebuilt canonically; kink-native `ObservationDecider::terminal_value`). An element with a part
//! that is no such value (a missing cell, a variable, an application no equation reduces) is
//! undecided. Equality of two elements is equality of their canonical values, decided on SHA-256
//! digests of their KORE text; a baseline's recorded element keeps 8 bytes of its digest, and the
//! mutant's elements are compared with those 8 bytes, so a collision can only hide a difference.
//!
//! A path that ends at a determined end (a leaf whose state slots are all values: the leaves the
//! one-sided rule reads, and the stop leaves of the truncated system) closes every channel with
//! END; a path whose every leaf is an undefined step closes them with UNDEF. A channel stays open
//! where its path was cut by a bound and at an undecided element, except under
//! [`Stutter::Count`]:
//! - under [`Stutter::Collapse`], whether a content is an element at all rests on its equality
//!   with the last element kept, which an undecided content leaves undecided, so the index of
//!   every later element is unknown;
//! - a log opens at an undecided item too. Each item is one element, so counting it as one
//!   unknown position would also be sound; the slot does not, because a log's element is in
//!   general a function of its item that may give several elements, whose number an undecided
//!   item leaves open, and one rule for every log keeps a later element function sound.
//!
//! Under [`Stutter::Count`] an undecided element is one unknown position, and the elements after
//! it stay comparable: the index is the number of events.
//!
//! What a side reads rests on the facts of its run's leaf ([`LeafFacts::of`]): its state is real
//! (not `Vacuous`, not shown to have no instance, and shown to have one, by the adapter, by the
//! bridge, or, for a leaf whose last step k-rust expanded, by k-rust's existence judgement of
//! the state) and the path has no diagnostic. A leaf a
//! bound cut is no exception: a work-bound or breadth-bound leaf's path has no real prefix as the
//! bridge reads it, but a leaf whose state is a term of free constructors, injections and domain
//! values ([`LeafFeasibility::Syntactic`]) denotes that state, so the step into it was defined, and
//! it supplies the elements read there as any other real leaf does.
//!
//! A real leaf also makes every earlier state of its path real, so an element read at an earlier
//! point is read of a state the path reached. Within one request each state's path condition
//! holds its parent's: k-rust builds a successor's constraints as its parent's conjoined with the
//! step's applicability and the result conditions it carries (a right-hand side's or `ensures`'
//! definedness left open among them), and normalizes them to an equivalent conjunction with the
//! conditions its term simplification adds. The only conjunct dropped without being valid is
//! `⌈u⌉` where `u` occurs under total symbols in the same pattern's term, which the term entails
//! (`C[u] ∧ ⌈u⌉ = C[u]`), and only in a pattern leaving the rewriter (a leaf, a payload, a
//! reported copy; k-rust-backend `simplify_leaf_pattern`), never in a state the run goes on from.
//! By the leaf contract ([`LeafFacts`]) each state's term is defined wherever its path condition
//! holds, the initial configuration's on a clean path (its open definedness is named on every
//! leaf), so an instance of a settled leaf is an instance of every state of its path, and each
//! step at it is a step of the definition, its conditions being conjuncts of the next path
//! condition. A partial residue a step
//! builds and a later step discards keeps its open `⌈u⌉` in the leaf's predicate, so a leaf of
//! free constructors under it is neither `Syntactic` nor shown to exist, and is not real.
//!
//! # Functions of an observer
//!
//! A front end that reads the definition's values can give a declaration functions of an
//! observer ([`Observe::with_functions`], [`ObservationFunctions`]): every content of a point
//! class, a filter that keeps only some of its points, and every element of a log, each a
//! function of named cells of the observed state (of the item, for a log's element), evaluated in
//! one fixed observer definition the front end chooses, never the definition being run. The
//! baseline's runs and every mutant's are evaluated alike, so a mutation changes the states
//! observed and where events fall, never what an observation computes. The declaration's value
//! names the functions' identity ([`ObserveFunctions::identity`]), so every key and record of a
//! run with them names what decides each element; a declaration without them is kink's own, as
//! above, and its value is the one it had before functions existed.
//!
//! Under functions:
//! - a point's content is the front end's ([`ObservationEvaluator::content`]), and an element is
//!   undecided where the front end says it is not known there (no value, or an evaluation stopped
//!   before its end): the function is evaluated in proof mode, decided only at a ground value;
//! - a class with a filter ([`ObservationEvaluator::holds`]) has an event only at a point where
//!   the filter is decided to hold. A filter not known at a point opens the channel there under
//!   either stuttering mode, since whether the point is an event at all is not known, so neither
//!   is the index of any later element. A log read at the class's points is read at every point
//!   of it, its filter not applying;
//! - a request the front end gives no evaluator (its observer does not load, for one) knows no
//!   function's value: every content and log element is undecided, and every filter, so a class
//!   with one opens its channel at its first point ([`ObservationFunctions::filtered`]). A class
//!   without one keeps its points, each an undecided element: under [`Stutter::Count`] each is
//!   one unknown position, so a side's END against such an element is still a decided difference,
//!   the number of points being a fact of the path;
//! - each item a log appends contributes the elements the front end gives it
//!   ([`ObservationEvaluator::elements`]), none or several, in order; an item it gives none for
//!   is one undecided element, which opens the log's channel. The baseline's append check
//!   compares items by the front end's term digest ([`ObservationEvaluator::item_digest`]),
//!   equal exactly when the two items are one term.
//!
//! The front end reads every run's cells with the baseline's declarations, so its functions'
//! cells ([`ObservationFunctions::cells`]) are read cells of the declaration for the admission of
//! a mutant (`observation-incompatible`, the runner's `observation_refusal`): no mutant is run
//! whose read cells could hold a term that denotes another value on it than on the baseline.
//! The element a reader is shown is the front end's document of it ([`Element::Evaluated`]).
//!
//! # Cycles
//!
//! A path that returns to an earlier state of itself with nothing new observed runs forever and
//! adds no element: each channel that is neither open nor past the baseline's horizon there is
//! complete, closed by the cycle ([`Closure::Cycle`]). This proves that the path diverges, which
//! a bound never does: the slot reads it as a fact of the path, not as the end of a budget.
//!
//! k-rust recognizes the return (k-rust-backend `rewrite::probe`, "Cycles"). The run keeps, up to
//! [`Observe::cycle_states`], the states of its path reached since the probe's channels last
//! changed, and compares each later state with them. Two states are one where their
//! configurations are the same ground term with no constraint and their stop counts, effects and
//! console are alike, under strategy `all`: a ground term with no constraint is one element in
//! every model, and a symbolic state is never compared, so an equality not decided in every model
//! is never a return. The definition's step of a state is a function of the state, and the path
//! left the earlier state by one successor at each state up to the later one, so it repeats those
//! steps forever. The probe's progress ([`Probe::progress`]) only grows with what it keeps
//! (elements, items read, opened or reached channels, undecided elements, an answer), so an equal
//! progress at both states says that no channel changed between them, and so none changes on any
//! later pass: each point of a pass is asked in the probe state and of the observed state it was
//! asked in and of on the first. Each log is read once more at the state of the return, which
//! holds every item the path appends, ever. A return to a state reached past the room is not
//! recognized, and no cycle is claimed for it.
//!
//! The return is read where the slot reads any answer of the probe: the leaf is the state of the
//! return, and only a settled leaf ([`LeafFacts::settled`]) with sides makes it decided, so every
//! state of the path up to it, the repeated steps included, is real and every step decided without
//! a diagnostic.
//! - On a mutant, a channel closed by a cycle has no element at its length, ever: a baseline element
//!   there, or the baseline's END or UNDEF there, is a decided difference, and the request ends at
//!   the first one; otherwise nothing more can be learned and the path ends.
//! - On the baseline, the run goes on as without the probe, which heeds nothing more of it, so its
//!   leaves, coverage and work are those of the run without a probe; its channels are recorded
//!   closed by the cycle. A mutant element past one is a difference, a mutant END or UNDEF there
//!   is a difference (the baseline never ends), a mutant closed alike at the same length agrees to
//!   the end with no horizon, and a mutant that holds all its elements and then opens agrees up to
//!   that horizon.
//!
//! # Several paths
//!
//! The meaning of a run is the set of its paths' observations: for each channel, the
//! prefix-closed set of the finite prefixes of its paths' channels, END and UNDEF being elements.
//! Two definitions differ on a program where a channel's prefix sets differ. A finite witness of
//! that is a prefix one side has and the other lacks, and it is a fact only where the side that
//! lacks it is explored completely to its length: every path of that side either holds an element
//! at each index below the length or closed earlier. A side explored less far, or a prefix past a
//! horizon, decides nothing: a bound only ends what is known. Each channel is compared on its own,
//! which is sound (a channel's difference is a difference of the tuple) and may miss a difference
//! only the tuple shows.
//!
//! The probe follows every path of its run (k-rust-backend `rewrite::probe`, "Several paths"): each
//! path keeps its own trace, forked from its parent's where the run splits, as a run of one path
//! keeps its one. A run that never splits is the run of one path above, with the record, the
//! comparison and the verdict it had before several paths were followed. A state-set run merges a
//! state into an equal one only where the probe's histories of their paths are equal (a digest of
//! every field of the trace the path's later answers rest on), so the merged path's continuation,
//! and what the probe keeps of it, are the other's; two states with different histories are both
//! explored. Until the run first splits the history is one constant: the run then has one state
//! at each depth, and every later state is deeper than the state that split, so no two states
//! whose histories it compares were read before the split.
//!
//! A path the run stops exploring with no leaf of its own (a pending state a work budget, a stop
//! that ends the run or a difference dropped) has no leaf whose facts the slot reads, so its
//! prefixes are facts only where another leaf stands for them. k-rust asks nothing of such a path
//! after its fork, since its state was never normalized, so its trace is the trace of the path it
//! was forked from as that path split. Where that path leads to a leaf of the run, every state up
//! to the split is a state of the leaf's path, real and clean where the leaf is: the dropped path's
//! prefixes are facts, and it bounds its side at its elements. A diagnostic only the dropped state
//! carries arose at the split's step, so a path it stands for shares the trace up to the split and
//! differs only at or past that bound. A dropped path asked anything since its fork, or whose fork
//! leads to no leaf, is unknown ([`LeafEnd::Unknown`]): it adds no prefix, bounds its side at 0,
//! and makes a baseline's record not real.
//!
//! A path that ends at an undefined step beside other paths closes its channels with UNDEF in its
//! side's sets, where the run's end is determined. A real `Trivial` leaf stands only for the
//! instances on which every applied candidate of the step is undefined (k-rust
//! `docs/compatibility.md`, "Trivial rule results"), which have no successor: their path is a path
//! of the definition that reaches the configuration and whose step's outcome is no configuration,
//! so its prefix closed by UNDEF is a fact of the side, not a prefix of a longer path.
//!
//! A prefix is kept as its chain: its elements folded in order, each by the 8 bytes of its digest a
//! record keeps, END and UNDEF by links of their own ([`ChannelSets`]). Equal prefixes have equal
//! chains, so a chain a set lacks is a prefix no path of the set has; a collision can only hide a
//! difference. An undecided element ends what its path can say of the chain, so it opens the
//! path's channel there under either stuttering mode.
//!
//! - The baseline's run, where it splits, records each channel's prefix set over its paths and how
//!   far every path is explored ([`PathRecord`]). A path that ended at a leaf adds its END or UNDEF
//!   where the run's end is determined; a path cut by a bound, ended undecided or left unexplored
//!   bounds the set at its elements; a path whose leaf has no instance adds its prefixes and bounds
//!   nothing. The record is complete only where every leaf of the run is clean, since a diagnostic
//!   may stand for a path the run does not hold, and real only where every leaf is real.
//! - A mutant's path is compared as its elements come, by chain, with the baseline's set, once its
//!   run splits or from the start where the baseline's did. A prefix outside the set at an index
//!   to which the baseline is explored on every path (mutant-outside) ends the request; past that
//!   index nothing more is compared on the channel. Such a difference kills where the leaf the
//!   request ended at is settled: the prefix is a fact of a path the mutant has, whatever its
//!   unexplored part holds.
//! - After the run, a prefix of a real baseline record that no path of the mutant has, at an index
//!   to which every path of the mutant is explored, kills (baseline-outside); so does a prefix read
//!   where a mutant path ended (a log item, its END or UNDEF) outside the baseline's set, where
//!   every leaf of the mutant's run is settled. Both need the mutant's run clean and judged into
//!   sides, so that no path of it is missing.
//! - Otherwise a channel agrees to its end where both sides are explored completely, and up to the
//!   baseline's horizon where the mutant is explored at least as far; a mutant explored short of
//!   the baseline leaves the slot unknown, and so does a baseline record that is not real, whose
//!   prefixes are no facts the mutant could lack.
//!
//! A difference of prefix sets names the side whose prefix the other lacks
//! ([`Position::outside`]); no capture run re-derives it, since no one baseline path holds it.
//!
//! # The slot
//!
//! A test of a campaign with a declaration has one slot more, after its end slots
//! ([`judge`]). The baseline's run records its channels ([`BaselineRecord`]); the mutant's run
//! compares its elements with the record as they come, in the probe of the one request, and the
//! request ends at the first difference. The slot distinguishes at a channel and an index at which
//! both sides' elements are decided and differ, END and UNDEF being elements unequal to every
//! content and to each other; never past either side's open point, so a bound never kills.
//!
//! The baseline's record is held to the facts a mutant's difference is held to: an element it
//! keeps was read in a real state of a path with no diagnostic ([`record`]), so no kill rests on a
//! baseline element read in a state the definition does not reach.
//!
//! A baseline run that a deterministic bound cut (its depth bound or its work bound) and that
//! is otherwise complete is a prefix program ([`BaselineRecord::prefix`]): it has no end, so its
//! end slots compare nothing, and it is admitted for its channels, each up to its horizon (the
//! number of elements it recorded before its open point), and for the crash policies of its end
//! slots, which a complete path of it that crashes still meets ([`BaselineRecord::crashed`]). A
//! mutant of it stops once every channel has reached that horizon or opened, and a mutant that
//! agrees up to it survives with that horizon ([`ObservationVerdict::horizon`]), unless every
//! horizon is 0: the prefix then observed nothing within its budget, and the slot is unknown.
//! A baseline run cut by the clock stays a timeout.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use k_rust::k_rust_backend::definition::BackendDefinition;
use k_rust::k_rust_backend::rewrite::HaltReason;
use k_rust::k_rust_backend::smt::NoSolver;
use k_rust::kore::ast::{Definition as KoreDefinition, Pattern, Sentence};
use k_rust::kore::printer::Printer;
use k_rust::names::KoreAttribute;
use kink_native::execution::{
    AdaptedLeaf, CellHandle, HaltClass, Probe, ProbeArrival, ProbeCycle, ProbeDecision, ProbeLeaf,
    ProbePath, ProbeRules, ProbeState, StopRules, StopSide,
};
use kink_native::feasibility::{LeafFeasibility, TestInitialState};
use kink_native::step_events::ObservationDecider;
use kink_patch::payload_digest;
use serde_json::{Value, json};

use crate::cells::CellLayout;
use crate::{OracleOutcome, OracleSide};
use k_rust::definition::configuration::CellMultiplicity;

/// The version of kink's observation slot ([`Observe`]): how a declaration is resolved, what an
/// element is and how two are compared, how a channel ends, which baseline runs are prefix
/// programs, which mutants are admitted, and when the slot distinguishes. A component of kink's
/// semantics identity ([`crate::identity::KINK_IDENTITY`], key `observation`). A campaign without
/// a declaration is outside all of it. v1: K-level declarations, one path per side (a channel
/// opens where its path first branches). v2: a path that returns to an earlier state of itself
/// with nothing new observed closes its channels complete and silent ([`Closure::Cycle`]), so a
/// mutant that idles forever where the baseline still emits is killed, and one that agrees with
/// a baseline closed so and returns too survives with no horizon (module documentation,
/// "Cycles"). A front end's functions of an observer ([`Observe::with_functions`]) are named by
/// the declaration's value, which a declaration without them keeps as it was, so they need no
/// version of their own: no record made without them can be read as one made with them. v3: the
/// probe follows every path of a run, and a run that splits is compared by its channels' prefix
/// sets (module documentation, "Several paths"), where v2 opened every channel at the first
/// branch; a run that never splits is compared as under v2.
/// v4: a mutant's run decided to have no start (the runner's `no_start`)
/// closes every channel by UNDEF at 0 and keeps nothing its probe read at its vacuous leaf
/// ([`Comparison::without_start`]),
/// where v3 left its channels open, the run's end undecided.
pub const OBSERVATION_VERSION: &str = "kink-campaign/observation/v4";

/// The domain of a prefix's chain ([`ChannelSets`]).
const CHAIN_DOMAIN: &str = "kink-campaign/observation/chain/v1";

/// The domain of an element's digest.
const ELEMENT_DOMAIN: &str = "kink-campaign/observation/element/v1";

/// How a point class's channel treats an element equal to the one before it. Declared per class:
/// which is meant is a property of the specification ([`PointClass::stutter`]).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stutter {
    /// An element equal to the last element kept is dropped: the number of events between two
    /// changes is not observed.
    Collapse,
    /// Every event is an element: how many events there were is observed.
    Count,
}

impl Stutter {
    /// The record name: `"collapse"` or `"count"`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Collapse => "collapse",
            Self::Count => "count",
        }
    }
}

/// A point class: rewrite rules by exact K label, on their before or after side, the cells (by K
/// cell name) whose content is each event's element, and the stuttering mode.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PointClass {
    /// The channel's name, unique among the declaration's channels.
    pub name: String,
    /// The rules whose events are observed in the state before their step.
    pub before: BTreeSet<String>,
    /// The rules whose events are observed in their normalized successor.
    pub after: BTreeSet<String>,
    /// The cells whose contents, in this order, are each event's element. Each must be a leaf
    /// cell of multiplicity 1 below cells of multiplicity 1, observable.
    pub cells: Vec<String>,
    pub stutter: Stutter,
}

/// A log: a `List` cell (by K cell name), read at the events of the named point classes and
/// where the path ends.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Log {
    /// The channel's name, unique among the declaration's channels.
    pub name: String,
    pub cell: String,
    /// The point classes at whose events (their rules and sides) the log is read.
    pub at: Vec<String>,
}

/// The channels of an [`Observe`] that declares some, and the room its runs keep to recognize a
/// return of their path ([`Observe::cycle_states`]).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct Declaration {
    points: Vec<PointClass>,
    logs: Vec<Log>,
    cycle_states: usize,
    /// The front end's functions of an observer, which give every content, filter and log
    /// element ([`Observe::with_functions`]); `None` for kink's own identity contents.
    functions: Option<ObserveFunctions>,
}

/// The number of states a run with a declaration keeps, reached since its channels last changed,
/// to recognize a return of its path to one of them ([`Observe::cycle_states`]), unless the
/// declaration sets another ([`Observe::with_cycle_states`]).
pub const CYCLE_STATES: usize = 4096;

/// A campaign's observation declaration ([module documentation](self)), held interned as
/// [`crate::Stop`] is, so that [`crate::RunOptions`] stays `Copy`: equal declarations are one
/// value, which lives as long as the process. [`Observe::NONE`] declares no channel.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Observe(Option<&'static Declaration>);

impl Observe {
    /// No channel: every run is compared by its end slots only.
    pub const NONE: Self = Self(None);

    /// The declaration of `points` and `logs`.
    ///
    /// # Errors
    ///
    /// Why it declares no observation: no channel, two channels of one name, a point class that
    /// names no rule, a log read at a class the declaration does not have, or a name that is
    /// empty.
    pub fn new(points: Vec<PointClass>, logs: Vec<Log>) -> Result<Self, String> {
        if points.is_empty() && logs.is_empty() {
            return Err("an observation declares no channel".to_owned());
        }
        let mut names = BTreeSet::new();
        for name in points
            .iter()
            .map(|point| &point.name)
            .chain(logs.iter().map(|log| &log.name))
        {
            if name.is_empty() {
                return Err("a channel has an empty name".to_owned());
            }
            if !names.insert(name.as_str()) {
                return Err(format!("two channels are named `{name}`"));
            }
        }
        for point in &points {
            if point.before.is_empty() && point.after.is_empty() {
                return Err(format!("the point class `{}` names no rule", point.name));
            }
        }
        for log in &logs {
            for class in &log.at {
                if !points.iter().any(|point| &point.name == class) {
                    return Err(format!(
                        "the log `{}` is read at `{class}`, which is no point class",
                        log.name
                    ));
                }
            }
        }
        Ok(Self::interned(Declaration {
            points,
            logs,
            cycle_states: CYCLE_STATES,
            functions: None,
        }))
    }

    /// This declaration, its runs keeping at most `states` states to recognize a return of their
    /// path ([`Self::cycle_states`]); 0 recognizes none. [`Self::NONE`] stays as it is.
    #[must_use]
    pub fn with_cycle_states(self, states: usize) -> Self {
        match self.0 {
            None => self,
            Some(declaration) => Self::interned(Declaration {
                cycle_states: states,
                ..declaration.clone()
            }),
        }
    }

    /// This declaration, its contents, filters and log elements given by `functions`, a front
    /// end's functions of an observer, in place of kink's identity contents (module
    /// documentation, "Functions of an observer"). [`Self::NONE`] stays as it is.
    #[must_use]
    pub fn with_functions(self, functions: ObserveFunctions) -> Self {
        match self.0 {
            None => self,
            Some(declaration) => Self::interned(Declaration {
                functions: Some(functions),
                ..declaration.clone()
            }),
        }
    }

    /// The front end's functions of an observer, when the declaration has them
    /// ([`Self::with_functions`]).
    #[must_use]
    pub fn functions(self) -> Option<&'static ObserveFunctions> {
        self.0
            .and_then(|declaration| declaration.functions.as_ref())
    }

    /// How many states of a run's path, reached since its channels last changed, the run keeps
    /// to recognize a return to one of them (module documentation, "Cycles"); 0 for
    /// [`Self::NONE`]. The room bounds the memory and the work, and a return to a state reached
    /// past it is not recognized: a larger room can only decide more.
    #[must_use]
    pub fn cycle_states(self) -> usize {
        self.0.map_or(0, |declaration| declaration.cycle_states)
    }

    fn interned(declaration: Declaration) -> Self {
        static INTERNED: std::sync::Mutex<BTreeSet<&'static Declaration>> =
            std::sync::Mutex::new(BTreeSet::new());
        let mut interned = INTERNED
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(existing) = interned.get(&declaration) {
            return Self(Some(existing));
        }
        let leaked: &'static Declaration = Box::leak(Box::new(declaration));
        interned.insert(leaked);
        Self(Some(leaked))
    }

    /// Whether this declares no channel.
    #[must_use]
    pub const fn is_none(self) -> bool {
        self.0.is_none()
    }

    /// The point classes; empty for [`Self::NONE`].
    #[must_use]
    pub fn points(self) -> &'static [PointClass] {
        self.0.map_or(&[], |declaration| &declaration.points)
    }

    /// The logs; empty for [`Self::NONE`].
    #[must_use]
    pub fn logs(self) -> &'static [Log] {
        self.0.map_or(&[], |declaration| &declaration.logs)
    }

    /// The names of every point class's rules, which each side must label rewrite rules with
    /// ([`StopRules::unresolved`]).
    #[must_use]
    pub fn rules(self) -> StopRules {
        let names = self
            .points()
            .iter()
            .flat_map(|point| point.before.iter().chain(&point.after))
            .cloned()
            .collect::<BTreeSet<_>>();
        StopRules {
            before: names.into_iter().collect(),
            after: Vec::new(),
        }
    }

    /// The declaration as a JSON object, `{points: [{name, before, after, cells, stutter}],
    /// logs: [{name, cell, at}]}`, with `cycle_states` where it is not [`CYCLE_STATES`] and
    /// `functions`, the identity of the front end's functions ([`ObserveFunctions::identity`]),
    /// where it has them; `None` for [`Self::NONE`]. A declaration without functions has the value
    /// it had before functions existed. Every field is destructured, so a new one does not
    /// compile until it is recorded here.
    #[must_use]
    pub fn value(self) -> Option<Value> {
        let Declaration {
            points,
            logs,
            cycle_states,
            functions,
        } = self.0?;
        let points = points
            .iter()
            .map(|point| {
                let PointClass {
                    name,
                    before,
                    after,
                    cells,
                    stutter,
                } = point;
                json!({"name": name, "before": before, "after": after, "cells": cells,
                       "stutter": stutter.name()})
            })
            .collect::<Vec<_>>();
        let logs = logs
            .iter()
            .map(|log| {
                let Log { name, cell, at } = log;
                json!({"name": name, "cell": cell, "at": at})
            })
            .collect::<Vec<_>>();
        let mut value = json!({"points": points, "logs": logs});
        if *cycle_states != CYCLE_STATES {
            value["cycle_states"] = json!(cycle_states);
        }
        if let Some(functions) = functions {
            value["functions"] = functions.identity().clone();
        }
        Some(value)
    }

    /// Why a cell of the declaration states no observation of the configuration `layout` of the
    /// definition whose KORE is `kore` ([`Self::resolve`]'s refusal), or `None`: what a front end
    /// checks before any run, so that its refusal names the cell as the campaign would.
    #[must_use]
    pub fn cell_refusal(self, layout: &CellLayout, kore: &KoreDefinition) -> Option<String> {
        self.resolve(layout, kore).err()
    }

    /// The declaration resolved on the baseline's configuration `layout` and KORE `kore`: each
    /// cell's path of KORE cell symbols from the top cell down.
    ///
    /// # Errors
    ///
    /// Why a cell states no observation: a cell the configuration does not have, one declared
    /// `unobservable` (no use of the definition may observe it), one that is not a leaf cell of
    /// multiplicity 1 below cells of multiplicity 1, or a log cell whose content is not a `List`.
    pub(crate) fn resolve(
        self,
        layout: &CellLayout,
        kore: &KoreDefinition,
    ) -> Result<Resolved, String> {
        let path = |name: &str| -> Result<Vec<String>, String> {
            let index = layout
                .cell(name)
                .ok_or_else(|| format!("the configuration has no cell `{name}`"))?;
            let cells = layout.cells();
            let cell = &cells[index];
            if cell.unobservable {
                return Err(format!("the cell `{name}` is unobservable"));
            }
            if cells.iter().any(|other| other.parent == Some(index)) {
                return Err(format!("the cell `{name}` is not a leaf cell"));
            }
            let mut symbols = vec![cell.kore_symbol.clone()];
            if cell.multiplicity != CellMultiplicity::One {
                return Err(format!("the cell `{name}` is not of multiplicity 1"));
            }
            for ancestor in layout.ancestors(index) {
                if cells[ancestor].multiplicity != CellMultiplicity::One {
                    return Err(format!(
                        "the cell `{name}` lies inside `{}`, which is not of multiplicity 1",
                        cells[ancestor].name
                    ));
                }
                symbols.push(cells[ancestor].kore_symbol.clone());
            }
            symbols.reverse();
            Ok(symbols)
        };
        let mut channels = Vec::new();
        let mut cells = BTreeSet::new();
        let mut rules = ProbeRules::default();
        for point in self.points() {
            let paths = point
                .cells
                .iter()
                .map(|cell| path(cell))
                .collect::<Result<Vec<_>, _>>()?;
            cells.extend(paths.iter().cloned());
            rules.before.extend(point.before.iter().cloned());
            rules.after.extend(point.after.iter().cloned());
            channels.push(Resolution::Point {
                before: point.before.clone(),
                after: point.after.clone(),
                cells: paths,
                stutter: point.stutter,
            });
        }
        for log in self.logs() {
            let cell = path(&log.cell)?;
            let symbol = cell.last().expect("a path names its cell");
            if !holds_list(kore, symbol) {
                return Err(format!("the log cell `{}` does not hold a List", log.cell));
            }
            cells.insert(cell.clone());
            let (mut before, mut after) = (BTreeSet::new(), BTreeSet::new());
            for class in &log.at {
                let point = self
                    .points()
                    .iter()
                    .find(|point| &point.name == class)
                    .expect("Observe::new checks every class a log is read at");
                before.extend(point.before.iter().cloned());
                after.extend(point.after.iter().cloned());
            }
            channels.push(Resolution::Log {
                cell,
                before,
                after,
            });
        }
        if let Some(functions) = self.functions() {
            cells.extend(functions.cells().iter().cloned());
        }
        let names = self
            .points()
            .iter()
            .map(|point| point.name.clone())
            .chain(self.logs().iter().map(|log| log.name.clone()))
            .collect();
        Ok(Resolved {
            names,
            channels,
            rules,
            cells: cells.into_iter().collect(),
            cycle_states: self.cycle_states(),
        })
    }
}

/// A front end's functions of an observer for a declaration ([`Observe::with_functions`]): the
/// source of every content, filter and log element of the declaration's runs, evaluated in one
/// fixed observer definition the front end chooses, never the definition being run (module
/// documentation, "Functions of an observer").
pub trait ObservationFunctions: Send + Sync {
    /// Each cell the functions read besides the declaration's own cells, as the KORE cell
    /// symbols from the configuration's top down to the cell (k-rust `ProbeState::cell`'s path).
    /// A mutant is admitted only where these cells, with the declaration's, could hold no term
    /// that denotes another value on it than on the baseline (`observation-incompatible`).
    fn cells(&self) -> &[Vec<String>];

    /// Whether the point class `class` (by position) has a filter, which keeps only some of its
    /// points ([`ObservationEvaluator::holds`]). Known without an evaluator: a request given none
    /// opens such a class's channel at its first point.
    fn filtered(&self, class: usize) -> bool;

    /// The KORE symbols of the functions that give the declaration's contents, filters and log
    /// elements, as the symbols of the definition the corpus runs name them where the observer's
    /// are those (the baseline as its own observer), or `None` where the front end does not name
    /// them. kink-flow's coverage scope takes every symbol they reach as one a run of the result
    /// records evaluates, and `None` as every function of the definition (kink-flow
    /// `coverage::scope`).
    fn functions(&self) -> Option<Vec<String>> {
        None
    }

    /// Run `body` once with the evaluator of one request, on the calling thread.
    ///
    /// # Errors
    ///
    /// Why no evaluator can be given here (its observer does not load, for example); `body` is
    /// then not run, and every content and log element of the request is undecided, and every
    /// filter: a class with one opens its channel at its first point (module documentation,
    /// "Functions of an observer").
    fn with_evaluator(
        &self,
        body: &mut dyn FnMut(&mut dyn ObservationEvaluator),
    ) -> Result<(), String>;
}

/// The evaluation of a declaration's functions for one request ([`ObservationFunctions`]). Each
/// answer must be a function of the state's configuration (of `item`, for a log's element),
/// evaluated in the observer whatever definition the request runs; `Err` says why it is not
/// known there (no value, or an evaluation stopped before its end), which the slot reads as an
/// undecided element.
pub trait ObservationEvaluator {
    /// Whether the point class `class` (by position) keeps a point at `state`: `None` for a class
    /// with no filter, which keeps every point.
    fn holds(&mut self, class: usize, state: &ProbeState<'_>) -> Option<Result<bool, String>>;

    /// The content of the point class `class` at `state`, with its value where `value`.
    ///
    /// # Errors
    ///
    /// Why the content is not known at `state`.
    fn content(
        &mut self,
        class: usize,
        state: &ProbeState<'_>,
        value: bool,
    ) -> Result<Evaluated, String>;

    /// The elements one item of the log `log` (by position among the logs) contributes, `item`
    /// as the log's cell holds it, each with its value where `value`.
    ///
    /// # Errors
    ///
    /// Why the item's elements are not known.
    fn elements(
        &mut self,
        log: usize,
        item: &Pattern,
        value: bool,
    ) -> Result<Vec<Evaluated>, String>;

    /// The digest the baseline's append check compares an item by: equal exactly when the two
    /// items are one term.
    fn item_digest(&mut self, item: &Pattern) -> [u8; 32];
}

/// One element an [`ObservationEvaluator`] gives: the digest two sides' elements are compared
/// by, and its value for a reader, a front end's document, where asked.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Evaluated {
    pub digest: [u8; 32],
    pub value: Option<Value>,
}

/// A declaration's functions of an observer: their identity, which every key and document of a
/// run with the declaration names, and the front end that evaluates them. Two are equal when
/// their identities are: the identity names the observer and the functions, which decide every
/// element.
#[derive(Clone)]
pub struct ObserveFunctions {
    identity: Value,
    canonical: String,
    oracle: std::sync::Arc<dyn ObservationFunctions>,
}

impl ObserveFunctions {
    /// The functions `oracle` evaluates, whose identity is `identity` (a JSON value that names
    /// what decides every element: for the krs front end, the observer's Definition IR digest and
    /// the declaration as written).
    #[must_use]
    pub fn new(identity: Value, oracle: std::sync::Arc<dyn ObservationFunctions>) -> Self {
        Self {
            canonical: kink_patch::canonical_json(&identity),
            identity,
            oracle,
        }
    }

    /// The identity, as documents and keys name the functions.
    #[must_use]
    pub const fn identity(&self) -> &Value {
        &self.identity
    }

    /// The cells the functions read besides the declaration's own ([`ObservationFunctions::cells`]).
    #[must_use]
    pub fn cells(&self) -> &[Vec<String>] {
        self.oracle.cells()
    }

    /// The functions the declaration evaluates ([`ObservationFunctions::functions`]).
    #[must_use]
    pub fn functions(&self) -> Option<Vec<String>> {
        self.oracle.functions()
    }
}

impl PartialEq for ObserveFunctions {
    fn eq(&self, other: &Self) -> bool {
        self.canonical == other.canonical
    }
}

impl Eq for ObserveFunctions {}

impl PartialOrd for ObserveFunctions {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ObserveFunctions {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.canonical.cmp(&other.canonical)
    }
}

impl std::hash::Hash for ObserveFunctions {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.canonical.hash(state);
    }
}

impl std::fmt::Debug for ObserveFunctions {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_tuple("ObserveFunctions")
            .field(&self.canonical)
            .finish()
    }
}

/// How one request's probe gets its contents: kink's identity contents, a front end's evaluator,
/// or none, with why and the front end's functions (every element and every filter is then
/// undecided).
pub(crate) enum Evaluation<'e> {
    Kink,
    Front(&'e mut dyn ObservationEvaluator),
    Missing(String, &'e ObserveFunctions),
}

impl<'e> Evaluation<'e> {
    /// This evaluation, for a probe that lives within `'e`.
    pub(crate) fn within<'s>(self) -> Evaluation<'s>
    where
        'e: 's,
    {
        match self {
            Self::Kink => Evaluation::Kink,
            Self::Front(evaluator) => Evaluation::Front(evaluator),
            Self::Missing(reason, functions) => Evaluation::Missing(reason, functions),
        }
    }
}

/// `body` with the evaluation of one request under `observe` ([`Evaluation`]): a front end's
/// evaluator, given on the calling thread, where the declaration has functions.
pub(crate) fn evaluating<T>(observe: Observe, body: impl FnOnce(Evaluation<'_>) -> T) -> T {
    let Some(functions) = observe.functions() else {
        return body(Evaluation::Kink);
    };
    let mut body = Some(body);
    let mut result = None;
    let given = functions.oracle.with_evaluator(&mut |evaluator| {
        if let Some(body) = body.take() {
            result = Some(body(Evaluation::Front(evaluator)));
        }
    });
    match (result, body) {
        (Some(result), _) => result,
        (None, Some(body)) => body(Evaluation::Missing(
            match given {
                Err(reason) => format!("the observer gave the run no evaluation: {reason}"),
                Ok(()) => "the observer gave the run no evaluation".to_owned(),
            },
            functions,
        )),
        (None, None) => unreachable!("a body taken gives a result"),
    }
}

/// Whether the cell symbol `symbol` of `kore` holds a `List`: its one argument sort is a hooked
/// sort with the hook `LIST.List`.
fn holds_list(kore: &KoreDefinition, symbol: &str) -> bool {
    let sentences = || kore.modules.iter().flat_map(|module| &module.sentences);
    let Some(content) = sentences().find_map(|sentence| match sentence {
        Sentence::SymbolDeclaration {
            symbol: declared,
            argument_sorts,
            ..
        } if declared.name == symbol && argument_sorts.len() == 1 => Some(&argument_sorts[0]),
        _ => None,
    }) else {
        return false;
    };
    let content = content.to_string();
    let name = content.split('{').next().unwrap_or(&content);
    sentences().any(|sentence| match sentence {
        Sentence::SortDeclaration {
            hooked: true,
            name: declared,
            attributes,
            ..
        } => {
            declared == name
                && attributes
                    .arguments(KoreAttribute::Hook)
                    .is_some_and(|hook| format!("{hook:?}").contains("LIST.List"))
        }
        _ => false,
    })
}

/// A declaration resolved on the baseline ([`Observe::resolve`]).
#[derive(Clone, Debug)]
pub(crate) struct Resolved {
    /// Each channel's name, in declaration order (the point classes, then the logs).
    names: Vec<String>,
    channels: Vec<Resolution>,
    /// Every point class's rules on their sides: the probe's rules.
    rules: ProbeRules,
    /// Every cell read, as its path of KORE cell symbols.
    cells: Vec<Vec<String>>,
    /// The room a run keeps to recognize a return of its path ([`Observe::cycle_states`]).
    cycle_states: usize,
}

impl Resolved {
    /// Every cell the declaration reads, as its path of KORE cell symbols from the top cell down.
    pub(crate) fn cells(&self) -> &[Vec<String>] {
        &self.cells
    }

    /// The number of point classes: the channels before the logs.
    fn points(&self) -> usize {
        self.channels
            .iter()
            .filter(|channel| matches!(channel, Resolution::Point { .. }))
            .count()
    }
}

#[derive(Clone, Debug)]
enum Resolution {
    Point {
        before: BTreeSet<String>,
        after: BTreeSet<String>,
        cells: Vec<Vec<String>>,
        stutter: Stutter,
    },
    Log {
        cell: Vec<String>,
        before: BTreeSet<String>,
        after: BTreeSet<String>,
    },
}

impl Resolution {
    /// Whether an element equal to the last element kept is dropped: under [`Stutter::Collapse`]
    /// only. A log's channel is the concatenation of its items, every item an element.
    const fn collapses(&self) -> bool {
        matches!(
            self,
            Self::Point {
                stutter: Stutter::Collapse,
                ..
            }
        )
    }

    /// Whether an undecided element is one unknown position, which leaves the later ones
    /// comparable: under [`Stutter::Count`] only (module documentation, "Elements").
    const fn counts(&self) -> bool {
        matches!(
            self,
            Self::Point {
                stutter: Stutter::Count,
                ..
            }
        )
    }

    fn selects(&self, rule: &str, side: StopSide) -> bool {
        let (before, after) = match self {
            Self::Point { before, after, .. } | Self::Log { before, after, .. } => (before, after),
        };
        match side {
            StopSide::Before => before.contains(rule),
            StopSide::After => after.contains(rule),
        }
    }
}

/// How one side's run ends its channels, as the slot reads it.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Closure {
    /// The path ended at a determined end.
    End,
    /// The path's last step was undefined.
    Undefined,
    /// The path returned to an earlier state of itself with nothing new observed between the two
    /// (module documentation, "Cycles"): it runs forever and adds no element, so the channel is
    /// complete and silent. Unlike END and UNDEF this is no element: the channel has no element at
    /// its length, ever.
    Cycle,
}

impl Closure {
    /// The record name: `"end"`, `"undefined"` or `"cycle"`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::End => "end",
            Self::Undefined => "undefined",
            Self::Cycle => "cycle",
        }
    }

    const fn element(self) -> Element {
        match self {
            Self::End => Element::End,
            Self::Undefined => Element::Undefined,
            Self::Cycle => Element::Cycle,
        }
    }
}

/// Why a channel opened: what ended what its side can observe of it, which says what could
/// observe more. A bound is a fact of the budget, and so may be a cycle's horizon (where the
/// mutant's path was cut); every other opening is a fact of the run, which a larger budget
/// reaches again.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Opening {
    /// A deterministic bound (the depth bound or the work bound) cut the path.
    Bound,
    /// The element there is undecided: a content with a part that is no value, under
    /// [`Stutter::Collapse`], or a log item that is no value or a log cell that holds no list of
    /// known items.
    UndecidedElement,
    /// The run has several paths: every channel of a record of such a run
    /// ([`BaselineRecord::channels`]) opens at 0 so, and the paths' prefix sets
    /// ([`BaselineRecord::paths`]) hold what was observed and how far each channel is explored.
    Branch,
    /// The path's states or its end are not decided: the leaf is not settled, its end is no
    /// value and no bound cut it, or the run gave no single leaf.
    UndecidedPath,
    /// The log's cell did not only grow by appending.
    NotAppended,
    /// Only in a survivor's horizon, never in a record: the baseline's channel is complete and
    /// silent after its path returned to an earlier state ([`Closure::Cycle`]), and the mutant's
    /// channel stopped being observed past every baseline element (its path was cut, or its
    /// channel opened) before it showed whether it emits more.
    Cycle,
}

impl Opening {
    /// The record name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Bound => "bound",
            Self::UndecidedElement => "undecided-element",
            Self::Branch => "branch",
            Self::UndecidedPath => "undecided-path",
            Self::NotAppended => "log-not-appended",
            Self::Cycle => "cycle",
        }
    }
}

/// Where and why a channel opened: the [`Opening`], and the reason in words.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Opened {
    pub opening: Opening,
    pub reason: String,
}

impl Opened {
    #[must_use]
    pub fn new(opening: Opening, reason: impl Into<String>) -> Self {
        Self {
            opening,
            reason: reason.into(),
        }
    }
}

/// Where a recorded channel ends: closed by END or UNDEF after its elements, complete and silent
/// after a return of its path ([`Closure::Cycle`]), or open there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ChannelEnd {
    Closed(Closure),
    /// The channel is open after its elements, as it opened.
    Open(Opened),
}

/// One channel of a baseline's run: its elements, each as the first 8 bytes of its digest or
/// `None` where it was undecided (only under [`Stutter::Count`]), and how it ends.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChannelRecord {
    pub name: String,
    pub elements: Vec<Option<[u8; 8]>>,
    pub end: ChannelEnd,
}

impl ChannelRecord {
    /// The number of elements before the channel's open point; `None` for a closed channel.
    #[must_use]
    pub fn horizon(&self) -> Option<usize> {
        matches!(self.end, ChannelEnd::Open(_)).then_some(self.elements.len())
    }

    /// The channel's horizon with why it opened ([`Horizon`]); `None` for a closed channel.
    #[must_use]
    pub fn open_horizon(&self) -> Option<Horizon> {
        match &self.end {
            ChannelEnd::Open(opened) => Some(Horizon {
                elements: self.elements.len(),
                opening: opened.opening,
            }),
            ChannelEnd::Closed(_) => None,
        }
    }
}

/// One channel's prefix set over a side's paths (module documentation, "Several paths"): at each
/// index `i`, the first 8 bytes of the chain of each path's prefix of length `i + 1`, END and
/// UNDEF being elements, and how far every path is explored.
///
/// A prefix's chain folds its elements in order, each as the first 8 bytes of its digest, END and
/// UNDEF as their own links ([`chain_next`]): two prefixes with equal elements have one chain, so
/// a chain missing from a set says that no path of the set has that prefix. Two prefixes that
/// differ may share a chain only by a collision, which can only hide a difference.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ChannelSets {
    pub prefixes: Vec<BTreeSet<[u8; 8]>>,
    /// The number of elements every path of the side holds or closed before: below it, every
    /// path's element at an index is in the set there, or the path closed earlier. `None` where
    /// every path is explored to its end, and so the set at every index is complete. The opening
    /// is why the path that bounds it is open there.
    pub complete_to: Option<Horizon>,
}

impl ChannelSets {
    /// Whether every path is explored past `index`: the set there holds every path's prefix of
    /// length `index + 1`.
    #[must_use]
    pub fn complete_at(&self, index: usize) -> bool {
        self.complete_to.is_none_or(|at| index < at.elements)
    }

    /// Whether some path's prefix of length `index + 1` has the chain `chain`.
    #[must_use]
    pub fn holds(&self, index: usize, chain: &[u8; 32]) -> bool {
        self.prefixes
            .get(index)
            .is_some_and(|set| set.contains(&short(chain)))
    }

    fn add(&mut self, index: usize, chain: &[u8; 32]) {
        if self.prefixes.len() <= index {
            self.prefixes.resize_with(index + 1, BTreeSet::new);
        }
        self.prefixes[index].insert(short(chain));
    }

    fn bound(&mut self, elements: usize, opening: Opening) {
        if self.complete_to.is_none_or(|at| elements < at.elements) {
            self.complete_to = Some(Horizon { elements, opening });
        }
    }
}

/// A baseline's record of a run with several paths (module documentation, "Several paths"): each
/// channel's prefix set over the run's paths.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathRecord {
    pub channels: Vec<ChannelSets>,
    /// The number of paths the sets were built from.
    pub paths: usize,
    /// Whether every leaf of the run is real and clean ([`LeafFacts::settled`]), and every path the
    /// run stopped exploring is known up to where it was left (module documentation, "Several
    /// paths"): then every prefix in the sets is a prefix of a path of the definition, and a mutant
    /// that lacks one is distinguished. Otherwise a set may hold a prefix the definition does not have, which can
    /// only hide a mutant's prefix, and no baseline prefix is held against a mutant.
    pub real: bool,
}

/// What a baseline's run records of its channels ([module documentation](self)), which every
/// mutant's run of the test is compared with.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BaselineRecord {
    pub channels: Vec<ChannelRecord>,
    /// Whether the run is a prefix program: a deterministic bound (its depth bound or its work
    /// bound) cut it, every other path of it is complete, and so it has no end. Its end slots
    /// compare nothing, and it is admitted for its channels.
    pub prefix: bool,
    /// Whether a complete path of the run ended in a semantic crash. A prefix program's end slots
    /// read no side, so its admission reads this under each slot's crash policy: a slot that
    /// rejects a crash refuses the baseline as it refuses a crashing side.
    pub crashed: bool,
    /// Why the run refuses the baseline's campaign, when it does: a log whose cell did not only
    /// grow by appending (`log-not-appended`), whose channel is no concatenation of appended
    /// items.
    pub refusal: Option<String>,
    /// Where the run split into several paths, each channel's prefix set over them (module
    /// documentation, "Several paths"); its `channels` then hold no element, each open at 0 by
    /// [`Opening::Branch`]. `None` for a run of one path.
    pub paths: Option<PathRecord>,
}

impl BaselineRecord {
    /// Whether the run observed nothing: no channel kept an element or closed by a cycle on its
    /// one path, or, for a run of several paths, no path kept a prefix of any channel. A prefix
    /// program that observed nothing can tell no mutant from it within its horizons.
    #[must_use]
    pub fn observed_nothing(&self) -> bool {
        match &self.paths {
            Some(paths) => paths
                .channels
                .iter()
                .all(|channel| channel.prefixes.iter().all(BTreeSet::is_empty)),
            None => self.channels.iter().all(|channel| {
                channel.elements.is_empty() && matches!(channel.end, ChannelEnd::Open(_))
            }),
        }
    }

    /// The record's prefix sets (module documentation, "Several paths"): a record of several
    /// paths keeps them; a record of one path is the set of its one path's prefixes, explored to
    /// its horizon, or to its end where it is closed.
    #[must_use]
    pub fn sets(&self) -> Vec<ChannelSets> {
        if let Some(paths) = &self.paths {
            return paths.channels.clone();
        }
        self.channels
            .iter()
            .map(|channel| {
                let mut sets = ChannelSets::default();
                let trace = ChannelTrace {
                    elements: channel.elements.clone(),
                    open: match &channel.end {
                        ChannelEnd::Open(opened) => Some(opened.clone()),
                        ChannelEnd::Closed(_) => None,
                    },
                    silent: channel.end == ChannelEnd::Closed(Closure::Cycle),
                    ..ChannelTrace::default()
                };
                let closure = match channel.end {
                    ChannelEnd::Closed(closure @ (Closure::End | Closure::Undefined)) => {
                        Some(closure)
                    }
                    _ => None,
                };
                add_path(&mut sets, &trace, closure, Opening::UndecidedPath);
                sets
            })
            .collect()
    }

    /// The record as a result record keeps it: `{channels: [{name, elements, closed, open}],
    /// prefix, crashed}`, each element the hex of its 8 digest bytes (null where it was undecided),
    /// `closed` `"end"`, `"undefined"` or `"cycle"` for a closed channel (else null), and `open`
    /// `{index, opening, reason}` for an open one (else null), `index` its horizon and `opening`
    /// why it opened ([`Opening::name`]). Every field is destructured, so a
    /// new one does not compile until it is recorded here.
    #[must_use]
    pub fn value(&self) -> Value {
        let Self {
            channels,
            prefix,
            crashed,
            refusal,
            paths,
        } = self;
        let channels = channels
            .iter()
            .map(|channel| {
                let ChannelRecord {
                    name,
                    elements,
                    end,
                } = channel;
                let elements = elements
                    .iter()
                    .map(|element| {
                        element.map(|bytes| {
                            bytes
                                .iter()
                                .map(|byte| format!("{byte:02x}"))
                                .collect::<String>()
                        })
                    })
                    .collect::<Vec<_>>();
                let (closed, open) = match end {
                    ChannelEnd::Closed(closure) => (json!(closure.name()), Value::Null),
                    ChannelEnd::Open(Opened { opening, reason }) => (
                        Value::Null,
                        json!({
                            "index": elements.len(),
                            "opening": opening.name(),
                            "reason": reason,
                        }),
                    ),
                };
                json!({"name": name, "elements": elements, "closed": closed, "open": open})
            })
            .collect::<Vec<_>>();
        let mut value = json!({"channels": channels, "prefix": prefix, "crashed": crashed});
        if let Some(refusal) = refusal {
            value["refusal"] = json!(refusal);
        }
        if let Some(PathRecord {
            channels,
            paths,
            real,
        }) = paths
        {
            let hex = |bytes: &[u8; 8]| {
                bytes
                    .iter()
                    .map(|byte| format!("{byte:02x}"))
                    .collect::<String>()
            };
            let channels = channels
                .iter()
                .map(
                    |ChannelSets {
                         prefixes,
                         complete_to,
                     }| {
                        json!({
                            "prefixes": prefixes
                                .iter()
                                .map(|set| set.iter().map(hex).collect::<Vec<_>>())
                                .collect::<Vec<_>>(),
                            "complete_to": complete_to.map(Horizon::value),
                        })
                    },
                )
                .collect::<Vec<_>>();
            value["paths"] = json!({"paths": paths, "real": real, "channels": channels});
        }
        value
    }
}

/// One side's element at a reported difference, as a reader is shown it
/// ([`crate::ObservedDifference`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Element {
    /// The values the element is made of: a point class's cells, in the class's order, or a log's
    /// one item.
    Content(Vec<Pattern>),
    /// The value a front end's functions gave the element ([`Observe::with_functions`]), as the
    /// front end documents it.
    Evaluated(Value),
    /// An element some part of which is no value (an element under [`Stutter::Count`], or one
    /// against a closed channel).
    Undecided,
    /// The channel is closed there by END.
    End,
    /// The channel is closed there by UNDEF.
    Undefined,
    /// The channel has no element there, ever: its path returned to an earlier state of itself
    /// with nothing new observed (module documentation, "Cycles").
    Cycle,
}

/// One element of a channel of a value run of the baseline ([`crate::observed_values`]): its
/// value, and where on the run's path it was read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValueElement {
    /// The element as a reader is shown it, in the form a capture run gives one element
    /// ([`crate::ObservedDifference::baseline`]): a content ([`Element::Content`], or
    /// [`Element::Evaluated`] under a front end's functions), or [`Element::Undecided`] where the
    /// record holds an undecided element (a class under [`Stutter::Count`]). Never a closure:
    /// how the channel ends is [`ChannelValues::end`].
    pub element: Element,
    /// The depth of the state the element was read at: the number of steps its path took to it.
    /// A before point's state is the state before its step, an after point's the step's
    /// successor, so the two points of one step are one apart.
    pub depth: u64,
    /// The rule and the side of the point the element was read at; `None` for a log item read
    /// where the path ended or where it returned to an earlier state of itself, which is no
    /// point.
    pub point: Option<(Arc<str>, StopSide)>,
}

/// One channel of a value run of the baseline ([`crate::observed_values`]): the value of every
/// element the baseline's record holds of it, in order, and how the record ends it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChannelValues {
    pub name: String,
    /// One per element of the record's channel, at its index.
    pub elements: Vec<ValueElement>,
    /// How the record ends the channel ([`ChannelRecord::end`]).
    pub end: ChannelEnd,
}

/// How a channel of a value run ends for a reader that knows two closures only, END and UNDEF
/// ([`ChannelValues::ending`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ValuesEnd {
    /// Closed by END after its elements.
    End,
    /// Closed by UNDEF after its elements.
    Undefined,
    /// Open after `index` elements. `opening` is why, as the record names it; it is
    /// [`Opening::Cycle`] for a channel the record closes by a cycle.
    Open {
        index: usize,
        opening: Opening,
        reason: String,
    },
}

impl ChannelValues {
    /// How the channel ends, a cycle's closure stated as an opening. The record's
    /// [`Closure::Cycle`] says the channel has no element past those it holds, ever; a reader
    /// without that closure is told less, that nothing is known past them, and why. That loses
    /// what an element of another side at that index would decide, and decides nothing the
    /// record does not.
    #[must_use]
    pub fn ending(&self) -> ValuesEnd {
        match &self.end {
            ChannelEnd::Closed(Closure::End) => ValuesEnd::End,
            ChannelEnd::Closed(Closure::Undefined) => ValuesEnd::Undefined,
            ChannelEnd::Closed(Closure::Cycle) => ValuesEnd::Open {
                index: self.elements.len(),
                opening: Opening::Cycle,
                reason: "the path returned to an earlier state of itself with nothing new \
                         observed: the channel is silent from here, which is stated as open"
                    .to_owned(),
            },
            ChannelEnd::Open(Opened { opening, reason }) => ValuesEnd::Open {
                index: self.elements.len(),
                opening: *opening,
                reason: reason.clone(),
            },
        }
    }
}

/// What the probe of a value run keeps beside its trace ([`ObservationProbe::with_values`]).
struct Values {
    /// Per channel, whether its elements' values are kept.
    wanted: Vec<bool>,
    /// Per channel, the value of each element its trace holds, at its index.
    taken: Vec<Vec<ValueElement>>,
    /// The names of the rules read at, each held once.
    rules: BTreeSet<Arc<str>>,
    /// The rule and side of the point being answered, while it is.
    at: Option<(Arc<str>, StopSide)>,
}

/// Where the slot found a difference: the channel, the index, and whether it was read where the
/// mutant's path ended (an END or UNDEF, or a log item appended by the last step) rather than at
/// a point.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Position {
    pub channel: String,
    pub index: usize,
    pub at_end: bool,
    /// Where a side has several paths (module documentation, "Several paths"), the side whose
    /// prefix of length `index + 1` the other side's prefix set lacks; `None` for a difference of
    /// the two sides' one paths, decided element against element.
    pub outside: Option<Outside>,
}

/// The side whose prefix the other side's prefix set lacks, at a difference of prefix sets
/// ([`Position::outside`]).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Outside {
    /// An explored path of the mutant has the prefix, and no path of the baseline has it.
    Mutant,
    /// A real path of the baseline has the prefix, and no path of the mutant has it.
    Baseline,
}

impl Outside {
    /// The record name: `"mutant"` or `"baseline"`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Mutant => "mutant",
            Self::Baseline => "baseline",
        }
    }
}

/// The observation slot's outcome for one mutant run of one test ([`judge`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObservationVerdict {
    pub outcome: OracleOutcome,
    /// The first decided difference, on `Distinguish`.
    pub position: Option<Position>,
    /// On `Agree`, each channel whose agreement rests on the baseline's prefix: its horizon, the
    /// number of elements it agrees on, with why the baseline's channel opened there. Empty when
    /// every channel agreed to its end.
    pub horizon: BTreeMap<String, Horizon>,
    /// On `Unknown`, why.
    pub cause: Option<String>,
    /// On `Distinguish`, the mutant's element at the position: the content its probe read, or
    /// END or UNDEF where its path closed the channel.
    pub element: Option<Element>,
    /// Where the mutant's path returned to an earlier state of itself, when it did (module
    /// documentation, "Cycles"): the depth of the earlier state and of the state of the return.
    pub cycle: Option<(u64, u64)>,
}

/// A channel's horizon: the number of elements its baseline's record holds before the channel's
/// open point, and why the channel opened there.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Horizon {
    pub elements: usize,
    pub opening: Opening,
}

impl Horizon {
    /// The horizon as a document gives it: `{elements, opening}`.
    #[must_use]
    pub fn value(self) -> Value {
        json!({"elements": self.elements, "opening": self.opening.name()})
    }
}

/// The facts of a run's one leaf the slot reads: whether its state is real (the path up to it
/// is a prefix of a path of the definition), and whether k-rust reported any diagnostic on it.
/// They are kept apart from whether an element read there is decided, which the probe judged
/// when it read the element.
///
/// They rest on k-rust's leaf contract and on how k-rust splits a step:
/// - a leaf's predicate implies the definedness of every partial term a `requires`, `ensures`,
///   right-hand side or simplified state relied on along its path, with the definition's
///   `total`, `functional` and `preserves-definedness` attributes as axioms (k-rust-backend
///   `ExecutionLeaf`); a mutant runs with every claim its edit leaves unbacked withdrawn
///   (the runner's module documentation), so no axiom of its run is an unbacked claim;
/// - a state's path condition holds its parent's, an obligation a step carries staying a conjunct
///   after a later step discards its term (module documentation, "Elements, and how a channel
///   ends"), so an instance of a real leaf is an instance of every state of its path: what the
///   leaf's facts say of its state they say of every state before it;
/// - a right-hand side's or `ensures`' definedness obligation that a step leaves open gives the
///   instances where it fails a leaf of their own, an undefined step (`Trivial`), beside the
///   successor, and no point of either path is asked there; so a run whose one leaf is not an
///   undefined step left no such obligation open on its path;
/// - the initial configuration's own obligations left open name the instances where they fail
///   on every leaf of the run (an `UndefinedInitialInstances` diagnostic), so such a run is not
///   clean; refuted, the run's leaf is `Vacuous`, whose state has no instance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct LeafFacts {
    real: bool,
    clean: bool,
}

impl LeafFacts {
    /// Whether the leaf's state is a real state of a path with no diagnostic: what is read
    /// there, and at every state of the path before it, is read of a state the path reached.
    pub(crate) const fn settled(self) -> bool {
        self.real && self.clean
    }

    /// Whether `leaf`'s state is shown to exist, by `exists` (kink-native
    /// `ObservationDecider::configuration_exists`, k-rust's `ground_defined` on the definition
    /// that produced the leaf, under the campaign's collection trust), asked only where
    /// [`Self::of`] reads the answer: a leaf whose last step k-rust expanded, not `Vacuous`, whose
    /// feasibility is [`LeafFeasibility::Unknown`]. `false` elsewhere, which says nothing.
    pub(crate) fn existence(leaf: &AdaptedLeaf, exists: impl FnOnce(&Pattern) -> bool) -> bool {
        Self::reads_existence(leaf) && exists(&leaf.branch.state)
    }

    /// Whether k-rust expanded the step into `leaf`'s state: every halt but a work-bound,
    /// poll-bound, breadth-bound, timed-out or cancelled one, whose state was taken from the
    /// worklist (or left on it, or stopped within its step) before its producing step's successor
    /// was normalized and split, so its
    /// predicate need not hold that step's right-hand side obligations, and no undefined step
    /// need stand beside it for the instances where they fail.
    const fn expanded(halt: HaltClass) -> bool {
        !matches!(
            halt,
            HaltClass::WorkBound
                | HaltClass::PollBound
                | HaltClass::BreadthBound
                | HaltClass::Timeout
                | HaltClass::Cancelled
        )
    }

    const fn reads_existence(leaf: &AdaptedLeaf) -> bool {
        Self::expanded(leaf.halt)
            && !matches!(leaf.halt, HaltClass::Vacuous)
            && matches!(leaf.feasibility, LeafFeasibility::Unknown)
    }

    /// The facts of `leaf`, whose state the bridge vouched for as a real prefix when `vouched`
    /// (kink-native's bridge: the path a probe cut keeps a real prefix for a state that has a
    /// terminal value or is shown to exist), and whose state is shown to exist when `existing`
    /// ([`Self::existence`]).
    ///
    /// - A `Vacuous` leaf is never real: k-rust showed its state to have no instance (its
    ///   constraints are `\bottom`, or the initial configuration's own definedness facts were
    ///   refuted, in which case k-rust returns the state unchanged, with no `\bottom` added).
    /// - A state shown to have no instance ([`LeafFeasibility::Unsat`]) is never real either.
    /// - A state the adapter showed to have an instance is real, whatever its halt: a work-bound
    ///   leaf of feasibility [`LeafFeasibility::Syntactic`] is a term of free constructors,
    ///   injections and domain values, which denotes its state.
    /// - Otherwise the leaf is real when the bridge vouched for it, or when its last step was
    ///   expanded and its state is shown to exist. The state then has an instance in every model
    ///   (its existence is a ground fact: `configuration_exists` refuses a free variable and a
    ///   conjunction, so a predicate conjunct), and by the leaf contract and the split invariant
    ///   ([`LeafFacts`]) every condition its path relied on holds there, so the path is a path of
    ///   the definition. Existence is asked of the state itself, since the predicate need not
    ///   restate it: k-rust drops `\ceil(t)` where `t` occurs under total symbols only, so a
    ///   ground state with no predicate conjunct can still owe the definedness of a partial
    ///   residue (`out(f(6))` owes `⌈f(6)⌉`), while an irreducible application of a total
    ///   symbol (`show(6)`) owes nothing. A leaf whose last step was not expanded is excluded
    ///   ([`Self::existence`]): the split invariant does not cover it.
    ///
    /// The leaf is clean when k-rust reported no diagnostic on it, which carries those of its
    /// path.
    pub(crate) fn of(leaf: &AdaptedLeaf, vouched: bool, existing: bool) -> Self {
        let real = match (leaf.halt, leaf.feasibility) {
            (HaltClass::Vacuous, _) | (_, LeafFeasibility::Unsat) => false,
            (_, LeafFeasibility::Syntactic | LeafFeasibility::Solver) => true,
            (_, LeafFeasibility::Unknown) => vouched || (Self::reads_existence(leaf) && existing),
        };
        Self {
            real,
            clean: leaf.diagnostics.is_empty()
                && leaf.candidate_diagnostics.iter().all(Vec::is_empty)
                && leaf.remainder_diagnostics.is_empty(),
        }
    }

    /// The facts of every leaf of `leaves` at once (`vouched` and `existing` as for
    /// [`Self::shared`]): real where every leaf is real by [`Self::of`], so every path of the run
    /// is a path of the definition, and clean where every leaf is. A run of several paths
    /// (module documentation, "Several paths") is read so: a prefix set holds the prefixes of
    /// every path, so it is a set of the definition's prefixes only where every path is real, and
    /// complete only where no diagnostic of the run may stand for a path it does not hold.
    pub(crate) fn every(leaves: &[AdaptedLeaf], vouched: bool, existing: &[bool]) -> Self {
        let existing = |index: usize| existing.get(index).copied().unwrap_or(false);
        let vouched = vouched && leaves.len() == 1;
        let facts = leaves
            .iter()
            .enumerate()
            .map(|(index, leaf)| Self::of(leaf, vouched, existing(index)));
        Self {
            real: !leaves.is_empty() && facts.clone().all(|facts| facts.real),
            clean: facts.clone().all(|facts| facts.clean),
        }
    }

    /// The facts of the path every leaf of `leaves` shares up to its first branching, the only
    /// part of a run a probe reads (`vouched` as for [`Self::of`], read only for one leaf, and
    /// `existing[i]` the [`Self::existence`] of leaf `i`, `false` when absent).
    ///
    /// The shared path is real when some leaf is real by [`Self::of`]: by the leaf contract
    /// ([`LeafFacts`]) that leaf's predicate implies every condition its path relied on, and its
    /// state exists, so its path is a path of the definition, of which the shared path is a
    /// prefix. An undefined step (`Trivial`) whose state exists is such a leaf: by the split
    /// invariant k-rust leaves it beside the successor of a step whose right-hand side or
    /// `ensures` obligation is open, and its state is the state before that step. A leaf that is
    /// not real adds nothing: it may stand for instances where a step past the branching is
    /// undefined or has none. The path is clean only when every leaf is, so that no diagnostic
    /// of the run is left out, whichever leaf k-rust reports it on. `None` for a run with no
    /// leaf.
    pub(crate) fn shared(leaves: &[AdaptedLeaf], vouched: bool, existing: &[bool]) -> Option<Self> {
        let existing = |index: usize| existing.get(index).copied().unwrap_or(false);
        match leaves {
            [] => None,
            [leaf] => Some(Self::of(leaf, vouched, existing(0))),
            leaves => {
                let facts = leaves
                    .iter()
                    .enumerate()
                    .map(|(index, leaf)| Self::of(leaf, false, existing(index)));
                Some(Self {
                    real: facts.clone().any(|facts| facts.real),
                    clean: facts.clone().all(|facts| facts.clean),
                })
            }
        }
    }
}

/// A mutant run's comparison with the baseline's record, as its probe made it, and the slot's
/// verdict once [`judge`] read it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Comparison {
    /// The probe's channels, boxed: a baseline's record, the other kind of observation, is small.
    pub(crate) trace: Box<Trace>,
    /// The run's one leaf, when it has exactly one; for a run of several paths, the leaf where
    /// the probe found a difference, when it found one.
    pub(crate) leaf: Option<LeafFacts>,
    /// The facts of every leaf of the run ([`LeafFacts::every`]).
    pub(crate) every: LeafFacts,
    pub verdict: Option<ObservationVerdict>,
}

impl Comparison {
    /// The comparison of a mutant's run decided to have no start
    /// (the runner's `no_start`: its initial configuration has no instance).
    /// The run reaches no configuration,
    /// so no point of it is an event and no log is read:
    /// what the probe read at its `Vacuous` leaf was read of a state with no instance,
    /// and none of it is kept.
    /// Every channel is empty and the run's one path ended before any step,
    /// an end undefined after 0 steps, which [`judge`] reads as UNDEF at 0 on every channel.
    /// That end is decided with no state to show real,
    /// so the run's facts are settled:
    /// no element of it rests on a state, and its UNDEF rests on k-rust's decision alone.
    pub(crate) fn without_start(&mut self) {
        let channels = self
            .trace
            .channels
            .iter()
            .map(|channel| ChannelTrace {
                cells: vec![None; channel.cells.len()],
                ..ChannelTrace::default()
            })
            .collect();
        *self.trace = Trace {
            channels,
            ended: true,
            ..Trace::default()
        };
        let settled = LeafFacts {
            real: true,
            clean: true,
        };
        self.leaf = Some(settled);
        self.every = settled;
    }
}

/// What a run reports of its observations ([`crate::RunNotes::observation`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Observation {
    /// A baseline's run: its record.
    Recorded(BaselineRecord),
    /// A mutant's run: its comparison with the baseline's record.
    Compared(Comparison),
}

/// One side's channel as its probe built it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct ChannelTrace {
    elements: Vec<Option<[u8; 8]>>,
    /// The full digest of the last element kept, for collapse.
    last: Option<[u8; 32]>,
    /// Why the channel opened after its elements, when it did.
    open: Option<Opened>,
    /// For a log: the items read so far (their full digests on the baseline, where each read is
    /// checked to hold them as its prefix), the number read, and the last handle on the cell.
    items: Vec<[u8; 32]>,
    read: usize,
    handle: Option<HeldHandle>,
    /// For a point class: the last handle on each cell and its value's text.
    cells: Vec<Option<(HeldHandle, Result<String, String>)>>,
    /// Compare mode: an index below the baseline's horizon at which either side's element was
    /// undecided, so the agreement is not known there.
    unknown: Option<usize>,
    /// Compare mode: the mutant emitted an element at the baseline's open point.
    reached: bool,
    /// The number of elements before the reads where the path ended, when those reads changed
    /// the channel: they read the path's last state, which is real only where its leaf is
    /// settled ([`LeafFacts::settled`]).
    at_end: Option<usize>,
    /// The path returned to an earlier state of itself while the channel was neither open nor
    /// past the baseline's horizon: it has no element past those it holds, ever.
    silent: bool,
    /// The chain of the prefix of the first elements ([`chain_next`]), and their number, as far
    /// as it was folded: compare mode against prefix sets folds it as elements come.
    chain: Option<([u8; 32], usize)>,
}

impl ChannelTrace {
    /// The number of elements before the first undecided one: a prefix's chain is known only up
    /// to there.
    fn decided(&self) -> usize {
        self.elements
            .iter()
            .position(Option::is_none)
            .unwrap_or(self.elements.len())
    }

    /// The chain of the prefix of all the channel's elements, `None` where one is undecided.
    fn chain(&mut self) -> Option<[u8; 32]> {
        let (mut chain, mut folded) = self.chain.unwrap_or((chain_start(), 0));
        for element in &self.elements[folded..] {
            chain = chain_next(&chain, Link::Content((*element)?));
            folded += 1;
        }
        self.chain = Some((chain, folded));
        Some(chain)
    }
}

/// A prefix's chain as a record's prefix sets hold it ([`ChannelSets`]), folded one element at a
/// time: what a reader of a record of several paths walks the sets by, for the elements it
/// knows. [`ChannelSets::holds`] reads it at an index.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrefixChain([u8; 32]);

impl PrefixChain {
    /// The chain of the empty prefix.
    #[must_use]
    pub fn empty() -> Self {
        Self(chain_start())
    }

    /// The chain of this prefix followed by the element whose digest's first 8 bytes are
    /// `element`.
    #[must_use]
    pub fn then(self, element: [u8; 8]) -> Self {
        Self(chain_next(&self.0, Link::Content(element)))
    }

    /// The chain's digest, as [`ChannelSets::holds`] takes it.
    #[must_use]
    pub const fn digest(&self) -> &[u8; 32] {
        &self.0
    }
}

/// One link of a prefix's chain: an element's 8 digest bytes, or the END or UNDEF that closes the
/// channel ([`ChannelSets`]).
#[derive(Clone, Copy)]
enum Link {
    Content([u8; 8]),
    Closed(Closure),
}

/// The chain of the empty prefix.
fn chain_start() -> [u8; 32] {
    *payload_digest(CHAIN_DOMAIN, &[]).as_bytes()
}

/// The chain of a prefix whose chain without its last element is `chain` and whose last element
/// is `link`. A content's link and a closure's are told apart by their first byte, so END and
/// UNDEF are unequal to every content and to each other.
fn chain_next(chain: &[u8; 32], link: Link) -> [u8; 32] {
    let mut bytes = Vec::with_capacity(41);
    bytes.extend_from_slice(chain);
    match link {
        Link::Content(element) => {
            bytes.push(0);
            bytes.extend_from_slice(&element);
        }
        Link::Closed(Closure::End) => bytes.push(1),
        Link::Closed(Closure::Undefined) => bytes.push(2),
        Link::Closed(Closure::Cycle) => bytes.push(3),
    }
    *payload_digest(CHAIN_DOMAIN, &bytes).as_bytes()
}

/// How a path of a run with several paths ended, as the probe was told of its leaf ([`Paths`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum LeafEnd {
    /// A leaf that is an end of the system: its END is decided where the run's end is
    /// ([`determined`]).
    End,
    /// An undefined step: its UNDEF is decided where the run's end is.
    Undefined,
    /// A leaf whose state has no instance: no path of the definition.
    Vacuous,
    /// The path was cut there, or its end is not decided; open at its elements.
    Open(Opened),
    /// The run stopped exploring the path, and no leaf of the run shows the facts of its states
    /// (module documentation, "Several paths"): its prefixes are no facts, it bounds its side's
    /// sets at 0, and a baseline's record with such a path is not real.
    Unknown,
}

impl LeafEnd {
    fn of(halt: &HaltReason) -> Self {
        match halt {
            HaltReason::Stuck
            | HaltReason::CutPointRule { .. }
            | HaltReason::TerminalRule { .. } => Self::End,
            HaltReason::Trivial { .. } => Self::Undefined,
            HaltReason::Vacuous { .. } => Self::Vacuous,
            HaltReason::DepthBound | HaltReason::WorkBound | HaltReason::BreadthBound => {
                Self::Open(Opened::new(Opening::Bound, "the path was cut by a bound"))
            }
            other => Self::Open(Opened::new(
                Opening::UndecidedPath,
                format!("the path ended undecided ({})", halt_name(other)),
            )),
        }
    }
}

/// A short name of a halt, for a reason.
fn halt_name(halt: &HaltReason) -> &'static str {
    match halt {
        HaltReason::Branch { .. } => "a branch",
        HaltReason::Stopped(_) => "a stop",
        _ => "an undecided end",
    }
}

/// The paths of a run that split into several, as its probe kept them (module documentation,
/// "Several paths"): each path that ended at a leaf, with how, and each path the run left
/// unexplored, open where it was left, or [`LeafEnd::Unknown`] where no leaf shows its facts. A
/// path merged into an equal state of another, with an
/// equal history, is not kept: its continuation is the other's.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Paths {
    pub(crate) paths: Vec<(Trace, LeafEnd)>,
}

/// A held handle, compared by node identity only.
#[derive(Clone, Debug)]
struct HeldHandle(CellHandle);

impl PartialEq for HeldHandle {
    fn eq(&self, other: &Self) -> bool {
        self.0.same(&other.0)
    }
}

impl Eq for HeldHandle {}

/// The answer a run's probe gave that ended it, when it gave one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Answer {
    /// A decided difference of the two sides' elements, at a point: the request ended there.
    Differs { channel: usize, index: usize },
    /// Every channel reached the baseline's horizon or opened: nothing more can be learned.
    Done,
}

/// One side's channels as its probe built them.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Trace {
    channels: Vec<ChannelTrace>,
    branched: Option<u64>,
    ended: bool,
    answer: Option<Answer>,
    /// A difference read where the path ended (a log item the last step appended): the probe
    /// cannot end the request there, so the slot reads it after the run.
    end_difference: Option<(usize, usize)>,
    /// On the baseline, why its run refuses the campaign: a log that did not only grow by
    /// appending ([`BaselineRecord::refusal`]).
    refusal: Option<String>,
    /// On a mutant, its element at the first difference its probe found (at a point, or read
    /// where the path ended), for the reader ([`ObservationVerdict::element`]).
    differing: Option<Box<Element>>,
    /// The depths of the earlier state and of the state where the path returned to it (module
    /// documentation, "Cycles"); the probe heeds nothing after it.
    cycled: Option<(u64, u64)>,
    /// Where the run split into several paths, each path's trace (module documentation, "Several
    /// paths"); the other fields then describe no path.
    paths: Option<Box<Paths>>,
}

/// The probe of one result run: records the baseline's channels, or compares a mutant's with the
/// baseline's record as they come ([module documentation](self)).
pub(crate) struct ObservationProbe<'a> {
    resolved: &'a Resolved,
    decider: ObservationDecider<'a>,
    /// Where the contents come from: kink's identity contents, or a front end's functions.
    evaluation: Evaluation<'a>,
    against: Option<&'a BaselineRecord>,
    /// The trace of the path a callback is about, while it is answered ([`Self::on`]).
    trace: Trace,
    /// The trace of each path the run has not left, by path (module documentation, "Several
    /// paths"): the root's alone until the run splits.
    live: BTreeMap<ProbePath, Trace>,
    /// Each path that ended at a leaf, with its trace and how it ended.
    ended: Vec<(Trace, LeafEnd)>,
    /// The paths that ended at a leaf the probe was told of ([`Probe::ended`]).
    ended_paths: BTreeSet<ProbePath>,
    /// The path each path was forked from ([`Probe::fork`]).
    parents: BTreeMap<ProbePath, ProbePath>,
    /// The paths the probe was asked a question of since they were forked.
    asked: BTreeSet<ProbePath>,
    /// The trace of a path the run left with no path on, kept for a run that never split.
    vanished: Option<Trace>,
    /// Whether the run split into two paths or more.
    several: bool,
    /// On a mutant, the baseline's prefix sets, which its paths are compared with by chain once
    /// the run splits, or from the start where the baseline's run split.
    sets: Option<Vec<ChannelSets>>,
    /// Each live path's history ([`Probe::history`]), with the progress it was read at.
    histories: std::cell::RefCell<BTreeMap<ProbePath, (u64, [u8; 32])>>,
    /// A capture run's target ([`Self::capturing`]): the channel and the index of the element it
    /// re-derives, and that element once read, with its recorded digest bytes.
    capture: Option<(usize, usize)>,
    captured: Option<(Element, Option<[u8; 8]>)>,
    /// A value run's values ([`Self::with_values`]): what a capture run keeps of one element,
    /// kept of every element of the channels asked for.
    values: Option<Values>,
}

static NO_SOLVER: NoSolver = NoSolver;

/// The first 8 bytes of a digest, as a baseline's record keeps them.
fn short(digest: &[u8; 32]) -> [u8; 8] {
    let mut short = [0; 8];
    short.copy_from_slice(&digest[..8]);
    short
}

impl<'a> ObservationProbe<'a> {
    /// The probe of a run of the test whose initial state is `initial`, reading values under the
    /// baseline's definition `shared` (with collections `trusted`), or through `evaluation` where
    /// the declaration has a front end's functions, comparing with `against` when it is a
    /// mutant's run.
    pub(crate) fn new(
        resolved: &'a Resolved,
        shared: &'a BackendDefinition,
        trusted: bool,
        initial: &'a Pattern,
        against: Option<&'a BaselineRecord>,
        evaluation: Evaluation<'a>,
    ) -> Self {
        let decider =
            ObservationDecider::new(shared, &NO_SOLVER, TestInitialState::of_test(initial))
                .trusting_collections(trusted);
        let channels = resolved
            .channels
            .iter()
            .map(|channel| ChannelTrace {
                cells: match channel {
                    Resolution::Point { cells, .. } => vec![None; cells.len()],
                    Resolution::Log { .. } => Vec::new(),
                },
                ..ChannelTrace::default()
            })
            .collect();
        let trace = Trace {
            channels,
            ..Trace::default()
        };
        Self {
            resolved,
            decider,
            evaluation,
            against,
            trace: Trace::default(),
            live: BTreeMap::from([(ProbePath::ROOT, trace)]),
            ended: Vec::new(),
            ended_paths: BTreeSet::new(),
            parents: BTreeMap::new(),
            asked: BTreeSet::new(),
            vanished: None,
            several: false,
            sets: against.map(BaselineRecord::sets),
            histories: std::cell::RefCell::default(),
            capture: None,
            captured: None,
            values: None,
        }
    }

    /// Answer `ask` about the path `path`, on its trace ([`Self::trace`]): the trace is taken from
    /// the live paths for the answer and put back after it.
    fn on<R>(&mut self, path: ProbePath, ask: impl FnOnce(&mut Self) -> R) -> R {
        self.asked.insert(path);
        self.trace = self.live.remove(&path).unwrap_or_else(|| self.fresh());
        let answer = ask(self);
        let trace = std::mem::take(&mut self.trace);
        self.live.insert(path, trace);
        answer
    }

    /// The trace of a path the probe was never told of: no element, every channel as it starts.
    fn fresh(&self) -> Trace {
        Trace {
            channels: self
                .resolved
                .channels
                .iter()
                .map(|channel| ChannelTrace {
                    cells: match channel {
                        Resolution::Point { cells, .. } => vec![None; cells.len()],
                        Resolution::Log { .. } => Vec::new(),
                    },
                    ..ChannelTrace::default()
                })
                .collect(),
            ..Trace::default()
        }
    }

    /// Whether the trace's channels are compared with the baseline's by prefix sets: once the
    /// run splits, or from the start where the baseline's run split.
    fn by_sets(&self) -> bool {
        self.against.is_some() && (self.several || self.against.is_some_and(|b| b.paths.is_some()))
    }

    /// The probe of a capture run of the baseline ([`crate::observed_difference`]): it records
    /// the run's channels as the baseline's probe does, and ends the path once it has read the
    /// element `index` of the channel `channel`, which it keeps with its digest bytes.
    pub(crate) fn capturing(
        resolved: &'a Resolved,
        shared: &'a BackendDefinition,
        trusted: bool,
        initial: &'a Pattern,
        evaluation: Evaluation<'a>,
        channel: usize,
        index: usize,
    ) -> Self {
        let mut probe = Self::new(resolved, shared, trusted, initial, None, evaluation);
        probe.capture = Some((channel, index));
        probe
    }

    /// The probe, also keeping the value of every element of the channels named in `channels`
    /// (a value run of the baseline, [`crate::observed_values`]), as a capture run keeps one
    /// element's. It answers every question as without them: what it keeps is read from the
    /// state after the element is taken, and nothing it answers or records reads it.
    ///
    /// It holds one [`ValueElement`] per element kept, and nothing per step or per point that
    /// keeps no element (an event a collapsing class drops, a point of a channel already open).
    /// The values are of the run's one path: where the run splits into several they are dropped
    /// ([`Self::take_values`]), since no one path holds them.
    pub(crate) fn with_values(mut self, channels: &[String]) -> Self {
        let wanted = self
            .resolved
            .names
            .iter()
            .map(|name| channels.contains(name))
            .collect::<Vec<_>>();
        self.values = Some(Values {
            taken: vec![Vec::new(); wanted.len()],
            wanted,
            rules: BTreeSet::new(),
            at: None,
        });
        self
    }

    /// A value run's values, per channel of the declaration (empty for one not asked for):
    /// `None` for a probe that keeps none, and for a run that split into several paths.
    pub(crate) fn take_values(&mut self) -> Option<Vec<Vec<ValueElement>>> {
        let values = self.values.take()?;
        (!self.several).then_some(values.taken)
    }

    /// The element a capture run read, with its digest bytes as the run recorded them: `None`
    /// when the run did not reach it.
    pub(crate) fn captured(self) -> Option<(Element, Option<[u8; 8]>)> {
        self.captured
    }

    /// The values of the point class `channel`'s cells at `state`, for a reader: an element is
    /// undecided where a part is no value. Under a front end's functions, the content's value as
    /// the front end documents it.
    fn values(&mut self, channel: usize, state: &ProbeState<'_>) -> Element {
        match &mut self.evaluation {
            Evaluation::Kink => {}
            Evaluation::Front(evaluator) => {
                return match evaluator.content(channel, state, true) {
                    Ok(Evaluated {
                        value: Some(value), ..
                    }) => Element::Evaluated(value),
                    _ => Element::Undecided,
                };
            }
            Evaluation::Missing(..) => return Element::Undecided,
        }
        let Resolution::Point { cells, .. } = &self.resolved.channels[channel] else {
            unreachable!("only a point class has a content");
        };
        cells
            .iter()
            .map(|path| {
                let symbol = path.last().map(String::as_str);
                let path = path.iter().map(String::as_str).collect::<Vec<_>>();
                // The cell's content: a handle holds the cell itself.
                let cell = state.cell_handle(&path)?.kore();
                let term = match &cell {
                    Pattern::Application {
                        symbol: head,
                        arguments,
                    } if Some(head.name.as_str()) == symbol && arguments.len() == 1 => {
                        arguments[0].clone()
                    }
                    _ => cell.clone(),
                };
                term.free_variables()
                    .is_empty()
                    .then(|| self.decider.terminal_value(&term))
                    .flatten()
            })
            .collect::<Option<Vec<_>>>()
            .map_or(Element::Undecided, Element::Content)
    }

    /// The value of the element `element` of one log item, for a reader: the item itself, or
    /// under a front end's functions the element's value as the front end documents it.
    fn item_value(&mut self, channel: usize, item: &Pattern, element: usize) -> Element {
        let log = channel - self.resolved.points();
        match &mut self.evaluation {
            Evaluation::Kink => {}
            Evaluation::Front(evaluator) => {
                return match evaluator.elements(log, item, true) {
                    Ok(elements) => match elements.into_iter().nth(element) {
                        Some(Evaluated {
                            value: Some(value), ..
                        }) => Element::Evaluated(value),
                        _ => Element::Undecided,
                    },
                    Err(_) => Element::Undecided,
                };
            }
            Evaluation::Missing(..) => return Element::Undecided,
        }
        item.free_variables()
            .is_empty()
            .then(|| self.decider.terminal_value(item))
            .flatten()
            .map_or(Element::Undecided, |value| Element::Content(vec![value]))
    }

    /// The element just taken on `channel`, which had `before` elements, read at a state of
    /// depth `depth`, is kept where the run keeps values: by a value run for every channel it was
    /// asked for ([`Self::with_values`]), and by a capture run where it is the run's target, with
    /// its recorded digest bytes. `element` gives it as a reader is shown it. Nothing is kept
    /// where the take added no element (an event a collapsing class drops, an undecided content
    /// that opened the channel).
    fn capture_taken(
        &mut self,
        channel: usize,
        before: usize,
        depth: u64,
        element: impl FnOnce(&mut Self) -> Element,
    ) {
        if self.trace.channels[channel].elements.len() != before + 1 {
            return;
        }
        if self
            .values
            .as_ref()
            .is_some_and(|values| values.wanted[channel])
            && !self.several
        {
            let element = element(self);
            let values = self.values.as_mut().expect("a value run");
            // The values follow the trace index by index: an element is kept for each one taken.
            debug_assert_eq!(values.taken[channel].len(), before);
            values.taken[channel].push(ValueElement {
                element,
                depth,
                point: values.at.clone(),
            });
            return;
        }
        let Some((target, index)) = self.capture else {
            return;
        };
        if target == channel && before == index && self.captured.is_none() {
            let digest = self.trace.channels[channel].elements[index];
            self.captured = Some((element(self), digest));
        }
    }

    /// The rules the probe observes.
    pub(crate) fn rules(&self) -> ProbeRules {
        self.resolved.rules.clone()
    }

    /// The channels as the run left them: the one path's trace where the run never split, and
    /// otherwise every path's ([`Paths`]), each ended path with how it ended and each path the
    /// run left unexplored open there.
    pub(crate) fn finish(mut self) -> Trace {
        if !self.several {
            // One path, possibly renamed: the trace of the path that ended, or is still live,
            // or else the one the run left with no path on.
            return self
                .ended
                .pop()
                .map(|(trace, _)| trace)
                .or_else(|| self.live.into_values().next())
                .or(self.vanished)
                .unwrap_or_default();
        }
        let mut paths = std::mem::take(&mut self.ended);
        // Every path on the way to a leaf of the run: the paths the probe was told ended, those
        // its own answer ended (the answer's leaf), and every path each was forked from.
        let mut toward_a_leaf = BTreeSet::new();
        let answered = self
            .live
            .iter()
            .filter(|(_, trace)| trace.answer.is_some())
            .map(|(path, _)| *path);
        for leaf in self.ended_paths.iter().copied().chain(answered) {
            let mut at = Some(leaf);
            while let Some(path) = at.filter(|path| toward_a_leaf.insert(*path)) {
                at = self.parents.get(&path).copied();
            }
        }
        for (path, trace) in self.live {
            let stopped = || {
                LeafEnd::Open(Opened::new(
                    Opening::Bound,
                    "the run stopped exploring the path",
                ))
            };
            let end = match trace.answer {
                // On a mutant, a path its probe ended past every horizon or opened.
                Some(Answer::Done) => LeafEnd::Open(Opened::new(
                    Opening::Bound,
                    "the path reached the baseline's horizon on every channel",
                )),
                Some(Answer::Differs { .. }) => stopped(),
                // A path the run stopped exploring with no leaf of its own: a pending state the
                // run dropped. Its facts are known up to its fork where nothing was asked of it
                // since and the path it was forked from leads to a leaf, whose facts the slot
                // reads; otherwise no leaf shows them.
                None if !self.asked.contains(&path)
                    && self
                        .parents
                        .get(&path)
                        .is_some_and(|parent| toward_a_leaf.contains(parent)) =>
                {
                    stopped()
                }
                None => LeafEnd::Unknown,
            };
            paths.push((trace, end));
        }
        let refusal = paths.iter().find_map(|(trace, _)| trace.refusal.clone());
        Trace {
            refusal,
            paths: Some(Box::new(Paths { paths })),
            ..Trace::default()
        }
    }

    /// The canonical KORE text of `term` when it is a ground value under the baseline's
    /// definition, or why it is not.
    fn value_text(&self, term: Option<Pattern>) -> Result<String, String> {
        let term = term.ok_or_else(|| "the state holds no such cell".to_owned())?;
        if !term.free_variables().is_empty() {
            return Err("a read cell holds a variable".to_owned());
        }
        self.decider
            .terminal_value(&term)
            .map(|value| Printer::compact().print_pattern(&value))
            .ok_or_else(|| {
                format!(
                    "a read cell holds no value: {}",
                    Printer::compact().print_pattern(&term)
                )
            })
    }

    /// The element of the point class `channel` at `state`: the digest of its cells' values, or
    /// under a front end's functions the digest of the content they give.
    fn content(&mut self, channel: usize, state: &ProbeState<'_>) -> Result<[u8; 32], String> {
        match &mut self.evaluation {
            Evaluation::Kink => {}
            Evaluation::Front(evaluator) => {
                return evaluator
                    .content(channel, state, false)
                    .map(|evaluated| evaluated.digest);
            }
            Evaluation::Missing(reason, _) => return Err(reason.clone()),
        }
        let Resolution::Point { cells, .. } = &self.resolved.channels[channel] else {
            unreachable!("only a point class has a content");
        };
        let mut payload = String::new();
        for (index, path) in cells.iter().enumerate() {
            let path = path.iter().map(String::as_str).collect::<Vec<_>>();
            let handle = state.cell_handle(&path).map(HeldHandle);
            let cached = self.trace.channels[channel].cells[index]
                .as_ref()
                .filter(|(held, _)| handle.as_ref() == Some(held))
                .map(|(_, text)| text.clone());
            let text = match cached {
                Some(text) => text,
                None => {
                    let text = self.value_text(handle.as_ref().map(|held| held.0.kore()));
                    if let Some(handle) = handle {
                        self.trace.channels[channel].cells[index] = Some((handle, text.clone()));
                    }
                    text
                }
            }?;
            payload.push_str(&text);
            payload.push('\n');
        }
        Ok(*payload_digest(ELEMENT_DOMAIN, payload.as_bytes()).as_bytes())
    }

    /// The digest of one log item.
    fn item(&self, item: Pattern) -> Result<[u8; 32], String> {
        let text = self.value_text(Some(item))?;
        Ok(*payload_digest(ELEMENT_DOMAIN, format!("{text}\n").as_bytes()).as_bytes())
    }

    /// The digest the baseline's append check compares one item of the log by: its element's
    /// under kink's identity contents, the front end's term digest under its functions; `None`
    /// where the item has none, whose element is then undecided and opens the channel.
    fn item_key(&mut self, item: &Pattern) -> Option<[u8; 32]> {
        match &mut self.evaluation {
            Evaluation::Front(evaluator) => Some(evaluator.item_digest(item)),
            Evaluation::Kink | Evaluation::Missing(..) => self.item(item.clone()).ok(),
        }
    }

    /// The elements one item of the log `channel` contributes: the item itself, or under a front
    /// end's functions each element they give it; one undecided element where they give none.
    fn item_elements(&mut self, channel: usize, item: &Pattern) -> Vec<Result<[u8; 32], String>> {
        let log = channel - self.resolved.points();
        match &mut self.evaluation {
            Evaluation::Kink => vec![self.item(item.clone())],
            Evaluation::Front(evaluator) => match evaluator.elements(log, item, false) {
                Ok(elements) => elements
                    .into_iter()
                    .map(|element| Ok(element.digest))
                    .collect(),
                Err(reason) => vec![Err(reason)],
            },
            Evaluation::Missing(reason, _) => vec![Err(reason.clone())],
        }
    }

    /// Whether the point class `channel` keeps the point at `state`: always under kink's
    /// identity contents and for a class with no filter, where its filter is decided to hold
    /// under a front end's functions. A filter not known there opens the channel, under either
    /// stuttering mode: whether the point is an event at all is not known, so neither is the
    /// index of any later element. A request the front end gave no evaluator knows no filter,
    /// so a class with one opens at its first point.
    fn keeps(&mut self, channel: usize, state: &ProbeState<'_>) -> bool {
        let holds = match &mut self.evaluation {
            Evaluation::Kink => None,
            Evaluation::Front(evaluator) => evaluator.holds(channel, state),
            Evaluation::Missing(reason, functions) => functions
                .oracle
                .filtered(channel)
                .then(|| Err(format!("its filter is not known here: {reason}"))),
        };
        match holds {
            None | Some(Ok(true)) => true,
            Some(Ok(false)) => false,
            Some(Err(reason)) => {
                let trace = &mut self.trace.channels[channel];
                let index = trace.elements.len();
                trace.open.get_or_insert_with(|| {
                    Opened::new(
                        Opening::UndecidedElement,
                        format!("undecided element at {index}: {reason}"),
                    )
                });
                false
            }
        }
    }

    /// Takes `element` on `channel`: recorded on the baseline, compared on a mutant. The index of
    /// a difference it makes.
    fn take(&mut self, channel: usize, element: Result<[u8; 32], String>) -> Option<usize> {
        let by_sets = self.by_sets();
        let resolution = &self.resolved.channels[channel];
        let trace = &mut self.trace.channels[channel];
        if let (true, Some(sets)) = (by_sets, &self.sets) {
            compare_chain(resolution, trace, &sets[channel], element)
        } else if let Some(against) = self.against {
            compare_element(resolution, trace, &against.channels[channel], element)
        } else {
            record_element(resolution, trace, element);
            None
        }
    }

    /// Reads the log `channel` at `state`, taking each item appended since the last read.
    fn read_log(&mut self, channel: usize, state: &ProbeState<'_>) -> Option<usize> {
        let Resolution::Log { cell, .. } = &self.resolved.channels[channel] else {
            unreachable!("only a log is read");
        };
        if self.trace.channels[channel].open.is_some() || self.trace.channels[channel].reached {
            return None;
        }
        let path = cell.iter().map(String::as_str).collect::<Vec<_>>();
        let handle = state.cell_handle(&path).map(HeldHandle);
        if handle.is_some() && handle == self.trace.channels[channel].handle {
            return None;
        }
        let read = self.trace.channels[channel].read;
        let Some(length) = state.list_len(&path) else {
            self.trace.channels[channel].open = Some(Opened::new(
                Opening::UndecidedElement,
                "the log cell holds no list of known items",
            ));
            return None;
        };
        if length < read {
            self.not_appended(channel, "the log shrank".to_owned());
            return None;
        }
        let new = if self.against.is_some() {
            state.list_items(&path, read).unwrap_or_default()
        } else {
            // The baseline's log must only grow by appending: every earlier item, again.
            let all = state.list_items(&path, 0).unwrap_or_default();
            for (position, item) in all.iter().take(read).enumerate() {
                if self.item_key(item) != Some(self.trace.channels[channel].items[position]) {
                    self.not_appended(channel, format!("the item at {position} was rewritten"));
                    return None;
                }
            }
            all.into_iter().skip(read).collect()
        };
        self.trace.channels[channel].handle = handle;
        'items: for item in new {
            if let Some(key) = self.item_key(&item)
                && self.against.is_none()
            {
                self.trace.channels[channel].items.push(key);
            }
            self.trace.channels[channel].read += 1;
            for (position, element) in self.item_elements(channel, &item).into_iter().enumerate() {
                let before = self.trace.channels[channel].elements.len();
                if let Some(index) = self.take(channel, element) {
                    if self.trace.differing.is_none() {
                        let value = self.item_value(channel, &item, position);
                        self.trace.differing = Some(Box::new(value));
                    }
                    return Some(index);
                }
                self.capture_taken(channel, before, state.depth(), |probe| {
                    probe.item_value(channel, &item, position)
                });
                if self.captured.is_some()
                    || self.trace.channels[channel].open.is_some()
                    || self.trace.channels[channel].reached
                {
                    break 'items;
                }
            }
        }
        None
    }

    /// The log `channel`'s cell did not only grow by appending (`why`). On a mutant the channel
    /// opens there: what it appended before is read. On the baseline the run refuses the
    /// campaign (`log-not-appended`): its channel is no concatenation of appended items, so no
    /// mutant could be compared with it.
    fn not_appended(&mut self, channel: usize, why: String) {
        if self.against.is_none() {
            self.trace.refusal.get_or_insert_with(|| {
                format!(
                    "log-not-appended: the log `{}`: {why}",
                    self.resolved.names[channel]
                )
            });
        }
        self.trace.channels[channel].open = Some(Opened::new(Opening::NotAppended, why));
    }

    /// Whether every channel reached the baseline's horizon or opened, on a mutant of a prefix
    /// program: nothing more can be learned.
    fn done(&self) -> bool {
        self.against.is_some_and(|against| against.prefix)
            && self
                .trace
                .channels
                .iter()
                .all(|channel| channel.reached || channel.open.is_some())
    }

    /// [`Probe::observe`] on the trace of the point's path.
    fn observe_here(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision {
        if self.trace.cycled.is_some() {
            return ProbeDecision::Continue;
        }
        if let Some(values) = &mut self.values {
            let rule = match values.rules.get(point.rule()) {
                Some(rule) => Arc::clone(rule),
                None => {
                    let rule = Arc::<str>::from(point.rule());
                    values.rules.insert(Arc::clone(&rule));
                    rule
                }
            };
            values.at = Some((rule, point.side()));
        }
        let decision = self.observe_point(point);
        if let Some(values) = &mut self.values {
            values.at = None;
        }
        decision
    }

    /// [`Self::observe_here`], once a value run knows the point it is asked at.
    fn observe_point(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision {
        let (rule, side) = (point.rule().to_owned(), point.side());
        for channel in 0..self.resolved.channels.len() {
            if !self.resolved.channels[channel].selects(&rule, side) {
                continue;
            }
            let difference = match self.resolved.channels[channel] {
                Resolution::Point { .. } => {
                    let open = self.trace.channels[channel].open.is_some()
                        || self.trace.channels[channel].reached;
                    if open || !self.keeps(channel, point) {
                        None
                    } else {
                        let before = self.trace.channels[channel].elements.len();
                        let element = self.content(channel, point);
                        let difference = self.take(channel, element);
                        if difference.is_some() {
                            let value = self.values(channel, point);
                            self.trace.differing = Some(Box::new(value));
                        }
                        self.capture_taken(channel, before, point.depth(), |probe| {
                            probe.values(channel, point)
                        });
                        difference
                    }
                }
                Resolution::Log { .. } => self.read_log(channel, point),
            };
            if self.captured.is_some() {
                self.trace.answer = Some(Answer::Done);
                return ProbeDecision::Done;
            }
            if let Some(index) = difference {
                self.trace.answer = Some(Answer::Differs { channel, index });
                return ProbeDecision::Differs(format!(
                    "the channel `{}` differs at {index}",
                    self.resolved.names[channel]
                ));
            }
        }
        if self.done() {
            self.trace.answer = Some(Answer::Done);
            return ProbeDecision::Done;
        }
        ProbeDecision::Continue
    }

    /// [`Probe::branched`] on the root's trace.
    fn branched_here(&mut self, depth: u64) {
        if self.trace.cycled.is_some() {
            return;
        }
        self.trace.branched = Some(depth);
        for channel in &mut self.trace.channels {
            channel.open.get_or_insert_with(|| {
                Opened::new(
                    Opening::Branch,
                    format!("the path branched at depth {depth}"),
                )
            });
        }
    }

    /// [`Probe::ended`] on the trace of the leaf's path: each log is read once more at the leaf.
    fn ended_here(&mut self, leaf: &ProbeLeaf<'_>) {
        if self.trace.cycled.is_some() {
            return;
        }
        self.trace.ended = true;
        for channel in 0..self.resolved.channels.len() {
            if !matches!(self.resolved.channels[channel], Resolution::Log { .. }) {
                continue;
            }
            let snapshot = |trace: &ChannelTrace| {
                (
                    trace.elements.len(),
                    trace.reached,
                    trace.open.is_some(),
                    trace.unknown,
                )
            };
            let before = snapshot(&self.trace.channels[channel]);
            let difference = self.read_log(channel, leaf);
            if snapshot(&self.trace.channels[channel]) != before || difference.is_some() {
                self.trace.channels[channel].at_end = Some(before.0);
            }
            if let Some(index) = difference
                && self.trace.end_difference.is_none()
            {
                self.trace.end_difference = Some((channel, index));
            }
        }
    }

    /// [`Probe::cycled`] on the trace of the returning path.
    fn cycled_here(&mut self, cycle: &ProbeCycle<'_>) -> ProbeDecision {
        if self.trace.cycled.is_some() || self.trace.answer.is_some() {
            return ProbeDecision::Continue;
        }
        self.trace.cycled = Some((cycle.first(), cycle.depth()));
        let difference = self.close_silent(cycle);
        if self.against.is_none() {
            return ProbeDecision::Continue;
        }
        if let Some((channel, index)) = difference {
            self.trace.answer = Some(Answer::Differs { channel, index });
            return ProbeDecision::Differs(format!(
                "the channel `{}` differs at {index}: the path returned at depth {} to its state at \
                 depth {}",
                self.resolved.names[channel],
                cycle.depth(),
                cycle.first()
            ));
        }
        self.trace.answer = Some(Answer::Done);
        ProbeDecision::Done
    }

    /// The path returned to an earlier state of itself with the probe's progress unchanged, at
    /// `state` (module documentation, "Cycles"): every channel neither open nor past the
    /// baseline's horizon is complete. Each log is read once more at `state`, which holds the
    /// items the path appended since its last read and appends none from here on. On a mutant,
    /// the index of the first channel's difference: an element the baseline has where the
    /// mutant's channel has none, ever, or the baseline's END or UNDEF there; the mutant's element
    /// there is [`Element::Cycle`].
    fn close_silent(&mut self, state: &ProbeState<'_>) -> Option<(usize, usize)> {
        for channel in 0..self.resolved.channels.len() {
            if matches!(self.resolved.channels[channel], Resolution::Log { .. })
                && let Some(index) = self.read_log(channel, state)
            {
                return Some((channel, index));
            }
        }
        let mut difference = None;
        for (channel, trace) in self.trace.channels.iter_mut().enumerate() {
            if trace.open.is_some() || trace.reached {
                continue;
            }
            trace.silent = true;
            let Some(against) = self.against else {
                continue;
            };
            let recorded = &against.channels[channel];
            let length = trace.elements.len();
            let differs = length < recorded.elements.len()
                || matches!(
                    recorded.end,
                    ChannelEnd::Closed(Closure::End | Closure::Undefined)
                );
            if differs && difference.is_none() {
                difference = Some((channel, length));
            }
        }
        // The mutant's element at the difference, for the reader: none there, ever.
        if difference.is_some() && self.trace.differing.is_none() {
            self.trace.differing = Some(Box::new(Element::Cycle));
        }
        difference
    }
}

/// Compares `element` on the channel `resolution`, whose trace is `trace`, with the baseline's
/// record of it `baseline` (compare mode): the index of the difference it makes, when it makes
/// one.
fn compare_element(
    resolution: &Resolution,
    trace: &mut ChannelTrace,
    baseline: &ChannelRecord,
    element: Result<[u8; 32], String>,
) -> Option<usize> {
    if trace.open.is_some() || trace.reached {
        return None;
    }
    let index = trace.elements.len();
    let element = match element {
        Ok(digest) => {
            if resolution.collapses() && trace.last == Some(digest) {
                return None;
            }
            trace.last = Some(digest);
            Some(short(&digest))
        }
        // One unknown position: the event is an element, its content undecided.
        Err(_) if resolution.counts() => {
            trace.last = None;
            None
        }
        Err(reason) => {
            trace.open = Some(Opened::new(
                Opening::UndecidedElement,
                format!("undecided element at {index}: {reason}"),
            ));
            return None;
        }
    };
    match baseline.elements.get(index) {
        Some(recorded) => {
            trace.elements.push(element);
            match (recorded, element) {
                (Some(recorded), Some(element)) if *recorded != element => Some(index),
                (Some(_), Some(_)) => None,
                _ => {
                    trace.unknown.get_or_insert(index);
                    None
                }
            }
        }
        None => match baseline.end {
            // An element, decided or not, where the baseline's channel is closed: a content
            // against END or UNDEF.
            ChannelEnd::Closed(_) => {
                trace.elements.push(element);
                Some(index)
            }
            // Past the baseline's horizon: nothing more is compared on this channel.
            ChannelEnd::Open(_) => {
                trace.reached = true;
                None
            }
        },
    }
}

/// Compares `element` on the channel `resolution`, whose trace is `trace`, with the baseline's
/// prefix set `sets` (compare mode by prefix sets, module documentation, "Several paths"): the
/// index of the difference it makes, when it makes one. The mutant's prefix up to the element is
/// outside the baseline's set where the baseline is explored past that index on every path and
/// no path's prefix there has its chain; past the index to which the baseline is explored,
/// nothing more is compared on the channel. An undecided element opens the channel under either
/// stuttering mode: the chain of every later prefix rests on it.
fn compare_chain(
    resolution: &Resolution,
    trace: &mut ChannelTrace,
    sets: &ChannelSets,
    element: Result<[u8; 32], String>,
) -> Option<usize> {
    if trace.open.is_some() || trace.reached {
        return None;
    }
    let index = trace.elements.len();
    let element = match element {
        Ok(digest) => {
            if resolution.collapses() && trace.last == Some(digest) {
                return None;
            }
            trace.last = Some(digest);
            short(&digest)
        }
        Err(reason) => {
            trace.open = Some(Opened::new(
                Opening::UndecidedElement,
                format!("undecided element at {index}: {reason}"),
            ));
            return None;
        }
    };
    if !sets.complete_at(index) {
        trace.reached = true;
        return None;
    }
    let Some(prefix) = trace.chain() else {
        // An element of the prefix was undecided before the run split.
        trace.open = Some(Opened::new(
            Opening::UndecidedElement,
            format!("undecided element before {index}"),
        ));
        return None;
    };
    trace.elements.push(Some(element));
    let chain = chain_next(&prefix, Link::Content(element));
    trace.chain = Some((chain, index + 1));
    (!sets.holds(index, &chain)).then_some(index)
}

/// Adds one path's channel `trace` to `sets`: the chain of each prefix of its decided elements,
/// and, where `closure` closes the channel after all its elements, the prefix it closes. A channel
/// left open, or past the other side's horizon (`reached`), or with an undecided element, bounds
/// how far the side is explored, at its decided elements, with `open`'s opening where the path
/// gives no other.
fn add_path(sets: &mut ChannelSets, trace: &ChannelTrace, closure: Option<Closure>, open: Opening) {
    let chain = add_prefixes(sets, trace);
    let decided = trace.decided();
    let opening = match (&trace.open, closure) {
        (Some(opened), _) => opened.opening,
        _ if decided < trace.elements.len() => Opening::UndecidedElement,
        _ if trace.reached => open,
        // Complete and silent: no element past these, ever.
        _ if trace.silent => return,
        (None, Some(closure)) => {
            sets.add(decided, &chain_next(&chain, Link::Closed(closure)));
            return;
        }
        (None, None) => open,
    };
    sets.bound(decided, opening);
}

/// Adds the chain of each prefix of `trace`'s decided elements to `sets`, and gives the chain of
/// the longest.
fn add_prefixes(sets: &mut ChannelSets, trace: &ChannelTrace) -> [u8; 32] {
    let mut chain = chain_start();
    for (index, element) in trace.elements[..trace.decided()].iter().enumerate() {
        chain = chain_next(&chain, Link::Content(element.expect("a decided element")));
        sets.add(index, &chain);
    }
    chain
}

/// The prefix sets of `paths`, one side's paths, channel by channel: each path's prefixes, its
/// END or UNDEF where `ended` (the run's end is determined) and its leaf is one, and the index to
/// which every path is explored. A path whose leaf has no instance adds its prefixes, which can
/// only hide a difference, and bounds nothing: it is no path of the definition. A path whose facts
/// no leaf shows ([`LeafEnd::Unknown`]) adds nothing and bounds every channel at 0: what it holds
/// is no fact, and what it lacks may be a path of the definition.
fn sets_of(paths: &[(Trace, LeafEnd)], channels: usize, ended: bool) -> Vec<ChannelSets> {
    (0..channels)
        .map(|channel| {
            let mut sets = ChannelSets::default();
            for (trace, end) in paths {
                let trace = &trace.channels[channel];
                let (closure, open) = match end {
                    LeafEnd::End if ended => (Some(Closure::End), Opening::UndecidedPath),
                    LeafEnd::Undefined if ended => {
                        (Some(Closure::Undefined), Opening::UndecidedPath)
                    }
                    LeafEnd::End | LeafEnd::Undefined => (None, Opening::UndecidedPath),
                    LeafEnd::Vacuous => {
                        add_prefixes(&mut sets, trace);
                        continue;
                    }
                    LeafEnd::Unknown => {
                        sets.bound(0, Opening::UndecidedPath);
                        continue;
                    }
                    LeafEnd::Open(opened) => (None, opened.opening),
                };
                add_path(&mut sets, trace, closure, open);
            }
            sets
        })
        .collect()
}

/// Records `element` on the channel `resolution`, whose trace is `trace` (record mode).
fn record_element(
    resolution: &Resolution,
    trace: &mut ChannelTrace,
    element: Result<[u8; 32], String>,
) {
    if trace.open.is_some() {
        return;
    }
    let index = trace.elements.len();
    match element {
        Ok(digest) => {
            if resolution.collapses() && trace.last == Some(digest) {
                return;
            }
            trace.last = Some(digest);
            trace.elements.push(Some(short(&digest)));
        }
        Err(_) if resolution.counts() => {
            trace.last = None;
            trace.elements.push(None);
        }
        Err(reason) => {
            trace.open = Some(Opened::new(
                Opening::UndecidedElement,
                format!("undecided element at {index}: {reason}"),
            ));
        }
    }
}

impl Probe for ObservationProbe<'_> {
    fn observe(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision {
        self.on(point.path(), |probe| probe.observe_here(point))
    }

    fn branched(&mut self, depth: u64) {
        // A probe that follows paths is told of no branch; kept for a run that does not ask it to.
        self.on(ProbePath::ROOT, |probe| probe.branched_here(depth));
    }

    fn ended(&mut self, leaf: &ProbeLeaf<'_>) {
        let path = leaf.path();
        self.on(path, |probe| probe.ended_here(leaf));
        self.asked.remove(&path);
        if let Some(trace) = self.live.remove(&path) {
            self.ended_paths.insert(path);
            self.ended.push((trace, LeafEnd::of(leaf.halt())));
        }
    }

    fn follows_paths(&self) -> bool {
        true
    }

    fn fork(&mut self, from: ProbePath, into: ProbePath) {
        let trace = self
            .live
            .get(&from)
            .cloned()
            .unwrap_or_else(|| self.fresh());
        self.live.insert(into, trace);
        self.parents.insert(into, from);
    }

    /// A split into two paths or more makes the run one of several paths; a split into one
    /// renames the path, and one into none leaves no path of the definition there.
    fn split(&mut self, path: ProbePath, _depth: u64, into: &[ProbePath]) {
        self.several |= into.len() > 1;
        if self.several
            && let Some(values) = &mut self.values
        {
            // The run has several paths: no one path holds the values kept so far.
            values.taken = Vec::new();
            values.wanted.fill(false);
        }
        self.histories.borrow_mut().remove(&path);
        self.asked.remove(&path);
        if let Some(trace) = self.live.remove(&path)
            && into.is_empty()
        {
            self.vanished = Some(trace);
        }
    }

    /// The path's continuation is an equal state's on a path with an equal history: what the
    /// probe keeps of that path is what it would keep of this one.
    fn merged(&mut self, path: ProbePath, _depth: u64) {
        self.histories.borrow_mut().remove(&path);
        self.asked.remove(&path);
        self.live.remove(&path);
    }

    /// A digest of everything the path's trace keeps that its later answers and records rest on
    /// ([`trace_digest`]), recomputed only where its progress changed; one constant until the run
    /// first splits into several paths. Before that split the run has one state at each depth,
    /// and every state after it is deeper than the state that split, so no state whose history
    /// was read before it is ever compared with another (the merge table compares states of one
    /// depth): the constant changes no merge, and spares a run that never splits a digest of its
    /// whole trace at each state.
    fn history(&self, path: ProbePath) -> [u8; 32] {
        if !self.several {
            return [0; 32];
        }
        let Some(trace) = self.live.get(&path) else {
            return [0; 32];
        };
        let progress = trace_progress(trace);
        let mut histories = self.histories.borrow_mut();
        match histories.get(&path) {
            Some((read, history)) if *read == progress => *history,
            _ => {
                let history = trace_digest(trace);
                histories.insert(path, (progress, history));
                history
            }
        }
    }

    fn cycle_states(&self) -> usize {
        self.resolved.cycle_states
    }

    /// The sum of what the probe keeps that its answers rest on, over its live paths (a return
    /// is recognized only before the run splits, so there is one): each channel's elements, items
    /// read and whether it opened, passed the baseline's horizon or met an undecided element, and
    /// whether the probe answered or refused. Each only grows, so an equal sum is an equal state:
    /// the last element kept, which collapse compares with, changes only with the elements, and
    /// the handles held only spare conversions.
    fn progress(&self) -> u64 {
        self.live
            .values()
            .map(trace_progress)
            .fold(0, u64::saturating_add)
    }

    /// The path runs forever from here and the probe sees nothing new on it, so every channel
    /// neither open nor past the baseline's horizon is complete ([`Self::close_silent`]). The
    /// baseline's run goes on as without the probe, which heeds nothing more of it; a mutant's
    /// request ends at its first difference, and its path otherwise, since nothing more can be
    /// learned.
    fn cycled(&mut self, cycle: &ProbeCycle<'_>) -> ProbeDecision {
        self.on(cycle.path(), |probe| probe.cycled_here(cycle))
    }
}

/// The progress of one path's trace ([`Probe::progress`]).
fn trace_progress(trace: &Trace) -> u64 {
    let channels = trace
        .channels
        .iter()
        .map(|channel| {
            channel.elements.len()
                + channel.read
                + usize::from(channel.open.is_some())
                + usize::from(channel.reached)
                + usize::from(channel.unknown.is_some())
        })
        .sum::<usize>();
    let answered = usize::from(trace.answer.is_some())
        + usize::from(trace.refusal.is_some())
        + usize::from(trace.end_difference.is_some());
    u64::try_from(channels + answered).unwrap_or(u64::MAX)
}

/// The history of a path ([`Probe::history`]): a digest of every field of its trace that what the
/// probe answers or keeps of the path's continuation rests on. Each channel's elements, the last
/// element kept (which collapse compares with), the items read (which the baseline's append check
/// compares with), whether and why it opened, whether it passed the baseline's horizon or met an
/// undecided element, and the reads where the path ended or a return; and the path's answer,
/// refusal and difference. The handles and the cells' texts are left out: they only spare
/// conversions. Two paths with equal histories at equal states therefore answer alike from there.
fn trace_digest(trace: &Trace) -> [u8; 32] {
    let channels = trace
        .channels
        .iter()
        .map(|channel| {
            let ChannelTrace {
                elements,
                last,
                open,
                items,
                read,
                handle: _,
                cells: _,
                unknown,
                reached,
                at_end,
                silent,
                chain: _,
            } = channel;
            json!({
                "elements": elements
                    .iter()
                    .map(|element| element.map(|bytes| short_hex(&bytes)))
                    .collect::<Vec<_>>(),
                "last": last.map(|digest| {
                    digest.iter().map(|byte| format!("{byte:02x}")).collect::<String>()
                }),
                "open": open.as_ref().map(|opened| (opened.opening.name(), opened.reason.clone())),
                "items": items
                    .iter()
                    .map(|digest| digest.iter().map(|byte| format!("{byte:02x}")).collect::<String>())
                    .collect::<Vec<_>>(),
                "read": read,
                "unknown": unknown,
                "reached": reached,
                "at_end": at_end,
                "silent": silent,
            })
        })
        .collect::<Vec<_>>();
    let answer = match &trace.answer {
        None => Value::Null,
        Some(Answer::Done) => json!("done"),
        Some(Answer::Differs { channel, index }) => json!([channel, index]),
    };
    let value = json!({
        "channels": channels,
        "answer": answer,
        "refusal": trace.refusal,
        "end_difference": trace.end_difference,
        "cycled": trace.cycled,
    });
    *payload_digest(CHAIN_DOMAIN, value.to_string().as_bytes()).as_bytes()
}

fn short_hex(bytes: &[u8; 8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Whether every state side of a run is a value or a crash: the run is complete, and its one
/// path's end is determined.
fn determined(sides: &[OracleSide]) -> bool {
    !sides.is_empty()
        && sides
            .iter()
            .all(|side| matches!(side, OracleSide::Normal(_) | OracleSide::SemanticCrash(_)))
}

/// The baseline's record of its run's channels `trace`: its sides `sides` (`None` for a run that
/// gave none), whether every complete path of it is an undefined step (`undefined`), whether a
/// complete path of it crashed (`crashed`), its leaves' halts, the halts of its incomplete paths'
/// leaves, and the facts of the path its leaves share up to their first branching
/// ([`LeafFacts::shared`]; `None` for a run with no leaf).
///
/// The record is held to what a mutant's difference is held to ([`judge`]). Every element the
/// probe kept was read at a state of that shared path, and those facts are the only facts known
/// of its states: a diagnostic may have been added at any step of it, and a state not shown real
/// may have stopped being real at any step. So where the path is not settled
/// ([`LeafFacts::settled`]) every channel opens before its first element, and no mutant is
/// distinguished by an element the definition need not reach. Otherwise every element is kept,
/// those read where the path ended included.
#[allow(clippy::too_many_arguments)]
pub(crate) fn record(
    resolved: &Resolved,
    trace: Trace,
    sides: Option<&[OracleSide]>,
    undefined: bool,
    crashed: bool,
    halts: &[HaltClass],
    incomplete: &[HaltClass],
    facts: Option<LeafFacts>,
    every: LeafFacts,
) -> BaselineRecord {
    let settled = facts.is_some_and(LeafFacts::settled);
    let bound = |halt: &HaltClass| matches!(halt, HaltClass::DepthBound | HaltClass::WorkBound);
    let ended = sides.is_some_and(determined);
    let prefix =
        sides.is_some() && !ended && !incomplete.is_empty() && incomplete.iter().all(bound);
    if let Some(paths) = trace.paths {
        return record_paths(
            resolved,
            &paths.paths,
            ended,
            every,
            prefix,
            crashed,
            trace.refusal,
        );
    }
    let closure = if trace.branched.is_some() || !trace.ended {
        None
    } else if ended {
        Some(if undefined {
            Closure::Undefined
        } else {
            Closure::End
        })
    } else {
        None
    };
    let open = |halts: &[HaltClass]| match halts {
        [halt] if bound(halt) => Opened::new(Opening::Bound, "the path was cut by a bound"),
        [halt] => Opened::new(
            Opening::UndecidedPath,
            format!("the path ended undecided ({halt:?})"),
        ),
        _ => Opened::new(Opening::UndecidedPath, "the run gave no single leaf"),
    };
    let unsettled = match facts {
        None => "the run gave no leaf",
        Some(facts) if !facts.real => "the path's states are not shown real",
        Some(_) => "k-rust reported a diagnostic on the path",
    };
    let unsettled_open = || {
        Opened::new(
            Opening::UndecidedPath,
            format!("the path is not settled: {unsettled}"),
        )
    };
    let channels = trace
        .channels
        .into_iter()
        .zip(&resolved.names)
        .map(|(mut channel, name)| {
            if !settled && !channel.elements.is_empty() {
                channel.elements.clear();
                channel.open = Some(unsettled_open());
            }
            let closure = if channel.silent {
                Some(Closure::Cycle)
            } else {
                closure
            };
            ChannelRecord {
                name: name.clone(),
                elements: channel.elements,
                end: match (channel.open, closure) {
                    (Some(opened), _) => ChannelEnd::Open(opened),
                    (None, Some(closure)) if settled => ChannelEnd::Closed(closure),
                    (None, Some(_)) => ChannelEnd::Open(unsettled_open()),
                    (None, None) => ChannelEnd::Open(open(halts)),
                },
            }
        })
        .collect();
    BaselineRecord {
        channels,
        prefix,
        crashed,
        refusal: trace.refusal,
        paths: None,
    }
}

/// The baseline's record of a run that split into several paths `paths` (module documentation,
/// "Several paths"): each channel's prefix set over them, END and UNDEF read where the run's end
/// is determined (`ended`). It is held to the facts of every leaf (`every`): where a leaf has a
/// diagnostic, a path may be missing from the sets, so no channel is known to be explored
/// anywhere; where a leaf is not shown real, or a path the run stopped exploring is one whose
/// facts no leaf shows ([`LeafEnd::Unknown`]), a set may hold a prefix the definition does not
/// have, so the record is not [`PathRecord::real`].
fn record_paths(
    resolved: &Resolved,
    paths: &[(Trace, LeafEnd)],
    ended: bool,
    every: LeafFacts,
    prefix: bool,
    crashed: bool,
    refusal: Option<String>,
) -> BaselineRecord {
    let mut sets = sets_of(paths, resolved.names.len(), ended);
    if !every.clean {
        for sets in &mut sets {
            sets.bound(0, Opening::UndecidedPath);
        }
    }
    let channels = resolved
        .names
        .iter()
        .map(|name| ChannelRecord {
            name: name.clone(),
            elements: Vec::new(),
            end: ChannelEnd::Open(Opened::new(
                Opening::Branch,
                "the run has several paths: its channels are compared by prefix sets",
            )),
        })
        .collect();
    BaselineRecord {
        channels,
        prefix,
        crashed,
        refusal,
        paths: Some(PathRecord {
            channels: sets,
            paths: paths.len(),
            real: every.settled() && paths.iter().all(|(_, end)| *end != LeafEnd::Unknown),
        }),
    }
}

/// The observation slot of one test ([module documentation](self), "The slot"): the baseline's
/// record `baseline`, the mutant's comparison `comparison`, and the mutant's sides `sides` as its
/// pair judged them (`None` when the run gave none), with whether every complete path of it is an
/// undefined step (`undefined`).
///
/// - A difference the probe found, at a point or where the path ended, rests on two facts,
///   judged apart. The prefix up to the observed state is real ([`LeafFacts::of`]): the leaf is
///   not `Vacuous`, its state is not shown to have no instance, it is shown to have one (by the
///   adapter, by the bridge, which keeps a real prefix for a state with a terminal value or shown
///   to exist, or by k-rust's existence judgement where k-rust expanded the step into it), k-rust
///   reported no diagnostic on it, and the run gave sides (no exclusion over the part it explored, which ends
///   there). And the answer is decided: both elements at the index were values when the probe
///   read them, and their digests differ. Where either fails the difference is not decided and
///   the slot is unknown. A point exists only where its step's successor is defined, and k-rust
///   asks a before point only once the successor's normalization has shown it defined, the leaf
///   the answer makes carrying the diagnostics of that step and normalization. So at a clean
///   before point the step is taken and the mutant's element at the index is the content read,
///   decided against every baseline element there, UNDEF included.
/// - A difference read where the path ended is also decided when every state side of the run is
///   a value or a crash, and so is the END or UNDEF of the path (the one-sided rule's leaf
///   conditions: the path's end is final in every model). The channel it is read on never agrees:
///   its element at the index differs from the baseline's, decided or not.
/// - A difference the probe found where the mutant's path returned to an earlier state (module
///   documentation, "Cycles") rests on the same two facts: the leaf is the state of the return,
///   and a settled leaf makes every state and step of the path up to it real and decided, the
///   steps between the two equal states included. The channel is then complete, so a baseline
///   element at its length, or the baseline's END or UNDEF there, is a decided difference.
/// - Without a decided difference, a channel agrees when the two sides close it alike at the same
///   index (END, UNDEF, or complete and silent after a return), and agrees up to a horizon when
///   the baseline's channel is open and the mutant reached that point, closed it there or later,
///   or opened there or later, or when the baseline's channel is complete and silent and the
///   mutant holds all its elements and opened after them; anything else is not known. The slot
///   agrees when every channel does, with the horizons of those that agree on a prefix, except on
///   a prefix program with no channel closed alike and every horizon 0: it observed nothing
///   within its budget, so an agreement would be agreement on nothing, and the slot is unknown.
pub(crate) fn judge(
    baseline: &BaselineRecord,
    comparison: &Comparison,
    sides: Option<&[OracleSide]>,
    undefined: bool,
) -> ObservationVerdict {
    if baseline.paths.is_some() || comparison.trace.paths.is_some() {
        return judge_sets(baseline, comparison, sides, undefined);
    }
    let trace = &comparison.trace;
    let name = |channel: usize| baseline.channels[channel].name.clone();
    let distinguish =
        |channel: usize, index: usize, at_end: bool, element: Option<Element>| ObservationVerdict {
            outcome: OracleOutcome::Distinguish,
            position: Some(Position {
                channel: name(channel),
                index,
                at_end,
                outside: None,
            }),
            horizon: BTreeMap::new(),
            cause: None,
            element,
            cycle: trace.cycled,
        };
    let unknown = |cause: String| ObservationVerdict {
        outcome: OracleOutcome::Unknown,
        position: None,
        horizon: BTreeMap::new(),
        cause: Some(cause),
        element: None,
        cycle: trace.cycled,
    };
    let settled = comparison.leaf.is_some_and(LeafFacts::settled);
    let real = settled && sides.is_some();
    match trace.answer {
        Some(Answer::Differs { channel, index }) => {
            return if real {
                distinguish(channel, index, false, trace.differing.as_deref().cloned())
            } else {
                unknown(format!(
                    "the channel `{}` differs at {index} in a state that is not decided",
                    name(channel)
                ))
            };
        }
        Some(Answer::Done) if !real => {
            return unknown("the run's last state is not decided".to_owned());
        }
        _ => {}
    }
    // The path's own end, decided by the one-sided rule's leaf conditions.
    let closure = (trace.answer.is_none() && trace.ended && trace.branched.is_none())
        .then_some(())
        .and(sides)
        .filter(|sides| determined(sides))
        .map(|_| {
            if undefined {
                Closure::Undefined
            } else {
                Closure::End
            }
        });
    if let Some((channel, index)) = trace.end_difference {
        return if closure.is_some() || real {
            distinguish(channel, index, true, trace.differing.as_deref().cloned())
        } else {
            unknown(format!(
                "the channel `{}` differs at {index} where the path ended, in a state that is not \
                 decided",
                name(channel)
            ))
        };
    }
    let mut horizon = BTreeMap::new();
    let mut open = None;
    let mut closed_alike = false;
    for (channel, (mutant, recorded)) in trace.channels.iter().zip(&baseline.channels).enumerate() {
        let recorded_length = recorded.elements.len();
        if let Some(length) = mutant.at_end
            && !settled
        {
            open.get_or_insert_with(|| {
                format!(
                    "the channel `{}` is open at {length}: the path's last state is not settled",
                    name(channel)
                )
            });
            continue;
        }
        let emitted = mutant.elements.len();
        if let Some(index) = mutant.unknown {
            open.get_or_insert_with(|| {
                format!("the channel `{}` is not decided at {index}", name(channel))
            });
            continue;
        }
        // A complete and silent baseline channel has no element past its own: a mutant that holds
        // them all and opened after them agrees with it up to the mutant's own open point.
        let agrees_to_horizon = matches!(
            recorded.end,
            ChannelEnd::Open(_) | ChannelEnd::Closed(Closure::Cycle)
        );
        // Where the mutant's channel ends.
        let mutant_closure = if mutant.silent {
            Some(Closure::Cycle)
        } else if mutant.open.is_some() || mutant.reached {
            None
        } else {
            closure
        };
        match mutant_closure {
            Some(kind) if emitted < recorded_length => {
                // END or UNDEF against an element, a content whether decided or not.
                return distinguish(channel, emitted, true, Some(kind.element()));
            }
            Some(kind) => match recorded.end {
                ChannelEnd::Closed(other) if other == kind => closed_alike = true,
                ChannelEnd::Closed(_) => {
                    return distinguish(channel, emitted, true, Some(kind.element()));
                }
                ChannelEnd::Open(_) => {
                    horizon.extend(recorded.open_horizon().map(|at| (name(channel), at)));
                }
            },
            // `reached` is set only against an open channel. Against a complete and silent one
            // the comparison stops where the mutant's channel stopped being observed, past every
            // baseline element: the horizon's opening is the baseline's cycle.
            None if mutant.reached || (agrees_to_horizon && emitted >= recorded_length) => {
                let at = recorded.open_horizon().unwrap_or(Horizon {
                    elements: recorded_length,
                    opening: Opening::Cycle,
                });
                horizon.insert(name(channel), at);
            }
            None => {
                open.get_or_insert_with(|| {
                    format!(
                        "the channel `{}` is open at {emitted}: {}",
                        name(channel),
                        mutant
                            .open
                            .as_ref()
                            .map_or("the mutant's path has no decided end", |opened| {
                                opened.reason.as_str()
                            })
                    )
                });
            }
        }
    }
    if open.is_none()
        && baseline.prefix
        && !closed_alike
        && horizon.values().all(|at| at.elements == 0)
    {
        open = Some(
            "every channel's horizon is 0: the baseline's prefix observed nothing within its \
             budget"
                .to_owned(),
        );
    }
    match open {
        Some(cause) => unknown(cause),
        None => ObservationVerdict {
            outcome: OracleOutcome::Agree,
            position: None,
            horizon,
            cause: None,
            element: None,
            cycle: trace.cycled,
        },
    }
}

/// The observation slot where either side's run split into several paths (module
/// documentation, "Several paths"): the two sides' prefix sets are compared ([`judge`] reads the
/// same arguments).
///
/// - A mutant's prefix the probe found outside the baseline's set, at a point, kills where the
///   leaf the request ended at is settled and the run gave sides, as a difference of one path
///   does: the prefix is real, each element decided, and the baseline is explored past that index
///   on every path, so no path of the baseline in any model has it.
/// - Everything else rests on the mutant's whole run: it must have given sides and every leaf
///   must be clean, so that no path is missing from what it explored. A prefix read where a path
///   ended (a log item, or its END or UNDEF where the run's end is determined) outside the
///   baseline's set kills where every leaf of the run is settled.
/// - A baseline's prefix outside the mutant's set kills where the baseline's record is real (each
///   prefix is the definition's) and the mutant is explored past that index on every path.
/// - Otherwise each channel agrees up to the lesser of the indices to which the two sides are
///   explored, and to its end where both are explored completely; that needs a real baseline
///   record, since a baseline prefix not shown real is no fact the mutant could lack. A prefix
///   program whose every horizon is 0 observed nothing within its budget, and the slot is
///   unknown.
fn judge_sets(
    baseline: &BaselineRecord,
    comparison: &Comparison,
    sides: Option<&[OracleSide]>,
    undefined: bool,
) -> ObservationVerdict {
    let trace = &comparison.trace;
    let name = |channel: usize| baseline.channels[channel].name.clone();
    let distinguish =
        |channel: usize, index: usize, at_end: bool, outside: Outside, element: Option<Element>| {
            ObservationVerdict {
                outcome: OracleOutcome::Distinguish,
                position: Some(Position {
                    channel: name(channel),
                    index,
                    at_end,
                    outside: Some(outside),
                }),
                horizon: BTreeMap::new(),
                cause: None,
                element,
                cycle: trace.cycled,
            }
        };
    let unknown = |cause: String| ObservationVerdict {
        outcome: OracleOutcome::Unknown,
        position: None,
        horizon: BTreeMap::new(),
        cause: Some(cause),
        element: None,
        cycle: trace.cycled,
    };
    let ended = sides.is_some_and(determined);
    // The mutant's paths: its several, or its one, ended as its run's end says.
    let one;
    let paths: &[(Trace, LeafEnd)] = match &trace.paths {
        Some(paths) => &paths.paths,
        None => {
            let end = if trace.answer.is_none() && trace.ended && trace.branched.is_none() {
                if undefined {
                    LeafEnd::Undefined
                } else {
                    LeafEnd::End
                }
            } else {
                LeafEnd::Open(Opened::new(
                    Opening::UndecidedPath,
                    "the mutant's path has no decided end",
                ))
            };
            one = [(trace.as_ref().clone(), end)];
            &one
        }
    };
    let real = comparison.leaf.is_some_and(LeafFacts::settled) && sides.is_some();
    for (path, _) in paths {
        if let Some(Answer::Differs { channel, index }) = path.answer {
            return if real {
                distinguish(
                    channel,
                    index,
                    false,
                    Outside::Mutant,
                    path.differing.as_deref().cloned(),
                )
            } else {
                unknown(format!(
                    "the channel `{}` differs at {index} in a state that is not decided",
                    name(channel)
                ))
            };
        }
    }
    if sides.is_none() {
        return unknown("the mutant's run gave no sides".to_owned());
    }
    if !comparison.every.clean {
        return unknown(
            "k-rust reported a diagnostic on the mutant's run, which may then miss a path"
                .to_owned(),
        );
    }
    let settled = comparison.every.settled();
    let sets = baseline.sets();
    // A prefix read where a path ended, outside the baseline's set.
    for (path, _) in paths {
        if let Some((channel, index)) = path.end_difference {
            return if settled {
                distinguish(
                    channel,
                    index,
                    true,
                    Outside::Mutant,
                    path.differing.as_deref().cloned(),
                )
            } else {
                unknown(format!(
                    "the channel `{}` differs at {index} where a path ended, in a state that is \
                     not decided",
                    name(channel)
                ))
            };
        }
    }
    // A path's END or UNDEF, outside the baseline's set.
    if ended && settled {
        for (path, end) in paths {
            let closure = match end {
                LeafEnd::End => Closure::End,
                LeafEnd::Undefined => Closure::Undefined,
                _ => continue,
            };
            for (channel, mutant) in path.channels.iter().enumerate() {
                let mut mutant = mutant.clone();
                let index = mutant.elements.len();
                if mutant.open.is_some() || mutant.reached || mutant.silent {
                    continue;
                }
                let Some(prefix) = mutant.chain() else {
                    continue;
                };
                let chain = chain_next(&prefix, Link::Closed(closure));
                if sets[channel].complete_at(index) && !sets[channel].holds(index, &chain) {
                    return distinguish(
                        channel,
                        index,
                        true,
                        Outside::Mutant,
                        Some(closure.element()),
                    );
                }
            }
        }
    }
    let baseline_real = baseline.paths.as_ref().is_none_or(|paths| paths.real);
    let mutant_sets = sets_of(paths, sets.len(), ended && settled);
    // A baseline's prefix outside the mutant's set, where the mutant is explored past its index.
    if baseline_real {
        for (channel, (recorded, mutant)) in sets.iter().zip(&mutant_sets).enumerate() {
            for (index, prefixes) in recorded.prefixes.iter().enumerate() {
                if !mutant.complete_at(index) {
                    break;
                }
                let held = mutant.prefixes.get(index);
                if !prefixes
                    .iter()
                    .all(|prefix| held.is_some_and(|held| held.contains(prefix)))
                {
                    return distinguish(channel, index, false, Outside::Baseline, None);
                }
            }
        }
    }
    if !baseline_real {
        return unknown(
            "a leaf of the baseline's run is not shown real, so no baseline prefix is held against \
             the mutant"
                .to_owned(),
        );
    }
    // Each channel agrees to its end where both sides are explored completely, and up to the
    // baseline's horizon where the mutant is explored at least that far; a mutant explored short
    // of the baseline leaves the channel unknown, as a bound never decides.
    let mut horizon = BTreeMap::new();
    let mut complete = false;
    for (channel, (recorded, mutant)) in sets.iter().zip(&mutant_sets).enumerate() {
        match (recorded.complete_to, mutant.complete_to) {
            (None, None) => complete = true,
            (Some(at), None) => {
                horizon.insert(name(channel), at);
            }
            (Some(at), Some(explored)) if explored.elements >= at.elements => {
                horizon.insert(name(channel), at);
            }
            (_, Some(explored)) => {
                return unknown(format!(
                    "the channel `{}` is explored to {} on the mutant ({}), short of the \
                     baseline's {}",
                    name(channel),
                    explored.elements,
                    explored.opening.name(),
                    recorded
                        .complete_to
                        .map_or("end".to_owned(), |at| at.elements.to_string())
                ));
            }
        }
    }
    if baseline.prefix && !complete && horizon.values().all(|at| at.elements == 0) {
        return unknown(
            "every channel's horizon is 0: the baseline's prefix observed nothing within its \
             budget"
                .to_owned(),
        );
    }
    ObservationVerdict {
        outcome: OracleOutcome::Agree,
        position: None,
        horizon,
        cause: None,
        element: None,
        cycle: trace.cycled,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn point(name: &str, rule: &str) -> PointClass {
        PointClass {
            name: name.to_owned(),
            before: BTreeSet::from([rule.to_owned()]),
            after: BTreeSet::new(),
            cells: vec!["n".to_owned()],
            stutter: Stutter::Collapse,
        }
    }

    /// A declaration names at least one channel, each once, each point class names a rule, and
    /// a log is read only at the declaration's classes; equal declarations are one value.
    #[test]
    fn a_declaration_is_checked_and_interned() {
        assert!(Observe::new(Vec::new(), Vec::new()).is_err());
        assert!(Observe::new(vec![point("a", "r"), point("a", "s")], Vec::new()).is_err());
        let mut empty = point("a", "r");
        empty.before.clear();
        assert!(Observe::new(vec![empty], Vec::new()).is_err());
        let log = |at: &str| Log {
            name: "out".to_owned(),
            cell: "out".to_owned(),
            at: vec![at.to_owned()],
        };
        assert!(Observe::new(vec![point("a", "r")], vec![log("b")]).is_err());
        let one = Observe::new(vec![point("a", "r")], vec![log("a")]).unwrap();
        let two = Observe::new(vec![point("a", "r")], vec![log("a")]).unwrap();
        assert_eq!(one, two);
        assert!(std::ptr::eq(one.0.unwrap(), two.0.unwrap()));
        assert_eq!(
            one.value().unwrap()["points"][0]["stutter"],
            json!("collapse")
        );
        assert_eq!(Observe::NONE.value(), None);
    }

    fn digest(item: u8) -> [u8; 32] {
        [item; 32]
    }

    fn element(item: u8) -> Option<[u8; 8]> {
        Some(short(&digest(item)))
    }

    fn log() -> Resolution {
        Resolution::Log {
            cell: Vec::new(),
            before: BTreeSet::new(),
            after: BTreeSet::new(),
        }
    }

    fn class(stutter: Stutter) -> Resolution {
        Resolution::Point {
            before: BTreeSet::from(["r".to_owned()]),
            after: BTreeSet::new(),
            cells: Vec::new(),
            stutter,
        }
    }

    /// The channel `resolution` records of `items`, on the baseline.
    fn recorded(resolution: &Resolution, items: &[u8]) -> ChannelTrace {
        let mut trace = ChannelTrace::default();
        for item in items {
            record_element(resolution, &mut trace, Ok(digest(*item)));
        }
        trace
    }

    fn channel(name: &str, elements: &[u8], end: ChannelEnd) -> ChannelRecord {
        ChannelRecord {
            name: name.to_owned(),
            elements: elements.iter().map(|item| element(*item)).collect(),
            end,
        }
    }

    fn cut() -> ChannelEnd {
        ChannelEnd::Open(Opened::new(Opening::Bound, "the path was cut by a bound"))
    }

    fn at(elements: usize, opening: Opening) -> Horizon {
        Horizon { elements, opening }
    }

    fn baseline(channels: Vec<ChannelRecord>, prefix: bool) -> BaselineRecord {
        BaselineRecord {
            channels,
            prefix,
            crashed: false,
            refusal: None,
            paths: None,
        }
    }

    /// A mutant's channel that emitted `items`, each compared, and `reached` the horizon.
    fn emitted(items: &[u8], reached: bool) -> ChannelTrace {
        ChannelTrace {
            elements: items.iter().map(|item| element(*item)).collect(),
            reached,
            ..ChannelTrace::default()
        }
    }

    fn trace(channels: Vec<ChannelTrace>) -> Trace {
        Trace {
            channels,
            branched: None,
            ended: false,
            answer: None,
            end_difference: None,
            refusal: None,
            differing: None,
            cycled: None,
            paths: None,
        }
    }

    const SETTLED: LeafFacts = LeafFacts {
        real: true,
        clean: true,
    };

    fn compared(trace: Trace, leaf: LeafFacts) -> Comparison {
        Comparison {
            trace: Box::new(trace),
            leaf: Some(leaf),
            every: leaf,
            verdict: None,
        }
    }

    /// A run judged into sides whose end is not determined (a bound cut it).
    const UNDETERMINED: &[OracleSide] = &[OracleSide::Unknown];

    fn determined_end() -> Vec<OracleSide> {
        vec![OracleSide::SemanticCrash(
            k_rust::kore::parser::parse_pattern(r"\top{SortBool{}}()").unwrap(),
        )]
    }

    fn position(channel: &str, index: usize, at_end: bool) -> Option<Position> {
        Some(Position {
            channel: channel.to_owned(),
            index,
            at_end,
            outside: None,
        })
    }

    /// A log's channel is the concatenation of its items: two equal consecutive items are two
    /// elements, on the baseline and on a mutant, as under `count`; only `collapse` drops one.
    /// The baseline appends 1, 1, 2 and the mutant 1, 2: the mutant's item 1 is 2 against the
    /// baseline's 1, a decided difference at a settled point.
    #[test]
    fn a_log_keeps_equal_consecutive_items() {
        assert_eq!(recorded(&log(), &[1, 1, 2]).elements.len(), 3);
        assert_eq!(
            recorded(&class(Stutter::Count), &[1, 1, 2]).elements.len(),
            3
        );
        assert_eq!(
            recorded(&class(Stutter::Collapse), &[1, 1, 2])
                .elements
                .len(),
            2
        );
        let record = ChannelRecord {
            name: "out".to_owned(),
            elements: recorded(&log(), &[1, 1, 2]).elements,
            end: cut(),
        };
        let mut mutant = ChannelTrace::default();
        assert_eq!(
            compare_element(&log(), &mut mutant, &record, Ok(digest(1))),
            None
        );
        assert_eq!(
            compare_element(&log(), &mut mutant, &record, Ok(digest(2))),
            Some(1)
        );
        let mut differs = trace(vec![mutant]);
        differs.answer = Some(Answer::Differs {
            channel: 0,
            index: 1,
        });
        let verdict = judge(
            &baseline(vec![record], true),
            &compared(differs, SETTLED),
            Some(UNDETERMINED),
            false,
        );
        assert_eq!(verdict.outcome, OracleOutcome::Distinguish);
        assert_eq!(verdict.position, position("out", 1, false));
    }

    /// A log item the last step appended, read where the mutant's path ended (here cut by a
    /// bound, so its end is not determined), that differs from the baseline's at the index is a
    /// decided difference when the leaf is settled, whether it is the baseline's last recorded
    /// element (index 1 of 2) or an earlier one (index 0); on a leaf not shown real it is not
    /// decided, and the channel never agrees.
    #[test]
    fn an_item_read_where_the_path_ended_is_never_an_agreement() {
        let record = baseline(vec![channel("out", &[1, 2], cut())], true);
        for (items, index) in [(&[1, 3][..], 1), (&[3][..], 0)] {
            let mut ended = trace(vec![ChannelTrace {
                at_end: Some(0),
                ..emitted(items, false)
            }]);
            ended.ended = true;
            ended.end_difference = Some((0, index));
            let killed = judge(
                &record,
                &compared(ended.clone(), SETTLED),
                Some(UNDETERMINED),
                false,
            );
            assert_eq!(killed.outcome, OracleOutcome::Distinguish, "{index}");
            assert_eq!(killed.position, position("out", index, true));
            let unreal = LeafFacts {
                real: false,
                clean: true,
            };
            let open = judge(&record, &compared(ended, unreal), Some(UNDETERMINED), false);
            assert_eq!(open.outcome, OracleOutcome::Unknown, "{index}");
        }
    }

    /// k-rust asks a before point only once its step's successor is shown defined, so a content
    /// at a clean before point against a baseline that closed the channel with UNDEF at that
    /// index is a decided difference.
    #[test]
    fn content_against_a_baseline_undef_is_decided() {
        let record = baseline(
            vec![channel(
                "clock",
                &[1],
                ChannelEnd::Closed(Closure::Undefined),
            )],
            false,
        );
        let mut differs = trace(vec![emitted(&[1, 2], false)]);
        differs.answer = Some(Answer::Differs {
            channel: 0,
            index: 1,
        });
        let verdict = judge(
            &record,
            &compared(differs, SETTLED),
            Some(UNDETERMINED),
            false,
        );
        assert_eq!(verdict.outcome, OracleOutcome::Distinguish);
        assert_eq!(verdict.position, position("clock", 1, false));
    }

    /// A mutant of a prefix program survives with each channel's horizon: when its probe ended
    /// the request once every channel reached it (`Done`), and when a bound cut it after it
    /// reached one channel's horizon and emitted the other's. A mutant of a program that ended
    /// whose channel the baseline left open reaches it and runs on to its own end: it agrees up to
    /// that horizon too.
    #[test]
    fn a_survivor_carries_its_horizons() {
        let record = baseline(vec![channel("clock", &[1, 2], cut())], true);
        let mut done = trace(vec![emitted(&[1, 2], true)]);
        done.answer = Some(Answer::Done);
        let verdict = judge(&record, &compared(done, SETTLED), Some(UNDETERMINED), false);
        assert_eq!(verdict.outcome, OracleOutcome::Agree);
        assert_eq!(
            verdict.horizon,
            BTreeMap::from([("clock".to_owned(), at(2, Opening::Bound))])
        );

        let two = baseline(
            vec![channel("clock", &[1], cut()), channel("out", &[2], cut())],
            true,
        );
        let mut bounded = trace(vec![emitted(&[1], true), emitted(&[2], false)]);
        bounded.ended = true;
        let verdict = judge(&two, &compared(bounded, SETTLED), Some(UNDETERMINED), false);
        assert_eq!(verdict.outcome, OracleOutcome::Agree);
        assert_eq!(
            verdict.horizon,
            BTreeMap::from([
                ("clock".to_owned(), at(1, Opening::Bound)),
                ("out".to_owned(), at(1, Opening::Bound))
            ])
        );

        let undecided = ChannelEnd::Open(Opened::new(
            Opening::UndecidedElement,
            "undecided element at 1: no value",
        ));
        let ending = baseline(vec![channel("clock", &[1], undecided)], false);
        let mut reached = trace(vec![emitted(&[1], true)]);
        reached.ended = true;
        let end = determined_end();
        let verdict = judge(&ending, &compared(reached, SETTLED), Some(&end), false);
        assert_eq!(verdict.outcome, OracleOutcome::Agree);
        // The horizon says the channel opened at an undecided element, on a baseline that ended:
        // no bound cut it.
        assert_eq!(
            verdict.horizon,
            BTreeMap::from([("clock".to_owned(), at(1, Opening::UndecidedElement))])
        );
    }

    /// A channel complete and silent after a return: the baseline's prefix program holds 1, 2
    /// and then never another element.
    /// - A mutant whose channel is silent after the same elements agrees with it to its end,
    ///   with no horizon, even with no element at all on either side: two silent channels agree
    ///   on everything.
    /// - A mutant whose path ended (END) after them is distinguished: the baseline never ends.
    /// - A mutant cut by a bound after them agrees up to 2, its own open point; one cut before
    ///   them is open, and the slot unknown.
    #[test]
    fn a_complete_and_silent_channel_agrees_only_with_silence() {
        let silent = ChannelEnd::Closed(Closure::Cycle);
        let record = baseline(vec![channel("clock", &[1, 2], silent.clone())], true);
        let quiet = |items: &[u8]| ChannelTrace {
            silent: true,
            ..emitted(items, false)
        };
        let verdict = judge(
            &record,
            &compared(trace(vec![quiet(&[1, 2])]), SETTLED),
            Some(UNDETERMINED),
            false,
        );
        assert_eq!(verdict.outcome, OracleOutcome::Agree);
        assert!(verdict.horizon.is_empty());
        let nothing = baseline(vec![channel("clock", &[], silent)], true);
        let verdict = judge(
            &nothing,
            &compared(trace(vec![quiet(&[])]), SETTLED),
            Some(UNDETERMINED),
            false,
        );
        assert_eq!(verdict.outcome, OracleOutcome::Agree);
        let ended = Trace {
            ended: true,
            ..trace(vec![emitted(&[1, 2], false)])
        };
        let end = determined_end();
        let verdict = judge(&record, &compared(ended, SETTLED), Some(&end), false);
        assert_eq!(verdict.outcome, OracleOutcome::Distinguish);
        assert_eq!(verdict.position, position("clock", 2, true));
        let cut_after = trace(vec![emitted(&[1, 2], false)]);
        let verdict = judge(
            &record,
            &compared(cut_after, SETTLED),
            Some(UNDETERMINED),
            false,
        );
        assert_eq!(verdict.outcome, OracleOutcome::Agree);
        assert_eq!(
            verdict.horizon,
            BTreeMap::from([("clock".to_owned(), at(2, Opening::Cycle))])
        );
        let cut_before = trace(vec![emitted(&[1], false)]);
        let verdict = judge(
            &record,
            &compared(cut_before, SETTLED),
            Some(UNDETERMINED),
            false,
        );
        assert_eq!(verdict.outcome, OracleOutcome::Unknown);
    }

    /// A prefix program whose every horizon is 0 observed nothing within its budget: a mutant
    /// that agrees with it agrees on nothing, and the slot is unknown, naming the empty horizon.
    /// A program that ended is judged by its end slots too, so its open channel's horizon of 0
    /// is an agreement of the observation slot, as without a declaration.
    #[test]
    fn a_prefix_that_observed_nothing_is_unknown() {
        let mut done = trace(vec![emitted(&[], true)]);
        done.answer = Some(Answer::Done);
        let empty = baseline(vec![channel("clock", &[], cut())], true);
        let verdict = judge(
            &empty,
            &compared(done.clone(), SETTLED),
            Some(UNDETERMINED),
            false,
        );
        assert_eq!(verdict.outcome, OracleOutcome::Unknown);
        assert!(verdict.cause.unwrap().contains("horizon is 0"));
        let ended = baseline(vec![channel("clock", &[], cut())], false);
        let mut reached = trace(vec![emitted(&[], true)]);
        reached.ended = true;
        let end = determined_end();
        let verdict = judge(&ended, &compared(reached, SETTLED), Some(&end), false);
        assert_eq!(verdict.outcome, OracleOutcome::Agree);
    }

    fn resolved(names: &[&str]) -> Resolved {
        Resolved {
            names: names.iter().map(|name| (*name).to_owned()).collect(),
            channels: names.iter().map(|_| class(Stutter::Count)).collect(),
            rules: ProbeRules::default(),
            cells: Vec::new(),
            cycle_states: CYCLE_STATES,
        }
    }

    /// A baseline that ends closes its channels with END, or with UNDEF where every complete
    /// path is an undefined step; a mutant that closes a channel alike at the same index agrees
    /// with no horizon, and one that closes it otherwise, or with a content against the closure,
    /// is distinguished there.
    #[test]
    fn a_baseline_that_ends_closes_its_channels() {
        let resolved = resolved(&["clock"]);
        let end = determined_end();
        let ran = || {
            let mut ran = trace(vec![recorded(&class(Stutter::Count), &[1])]);
            ran.ended = true;
            ran
        };
        let halts = [HaltClass::Stuck];
        let ends = record(
            &resolved,
            ran(),
            Some(&end),
            false,
            false,
            &halts,
            &[],
            Some(SETTLED),
            SETTLED,
        );
        assert!(!ends.prefix);
        assert_eq!(ends.channels[0].end, ChannelEnd::Closed(Closure::End));
        assert_eq!(ends.channels[0].elements, vec![element(1)]);
        let undefined = record(
            &resolved,
            ran(),
            Some(&end),
            true,
            false,
            &halts,
            &[],
            Some(SETTLED),
            SETTLED,
        );
        assert_eq!(
            undefined.channels[0].end,
            ChannelEnd::Closed(Closure::Undefined)
        );

        let mut alike = trace(vec![emitted(&[1], false)]);
        alike.ended = true;
        let verdict = judge(&ends, &compared(alike.clone(), SETTLED), Some(&end), false);
        assert_eq!(verdict.outcome, OracleOutcome::Agree);
        assert!(verdict.horizon.is_empty());
        let verdict = judge(&undefined, &compared(alike, SETTLED), Some(&end), false);
        assert_eq!(verdict.outcome, OracleOutcome::Distinguish);
        assert_eq!(verdict.position, position("clock", 1, true));
        let mut early = trace(vec![emitted(&[], false)]);
        early.ended = true;
        let verdict = judge(&ends, &compared(early, SETTLED), Some(&end), false);
        assert_eq!(verdict.position, position("clock", 0, true));
    }

    /// The baseline's record is held to the facts a mutant's difference is held to: where the
    /// path its leaves share is not settled (a diagnostic, or a state not shown real), every
    /// channel opens before its first element, so no kill rests on an element the definition
    /// need not reach; where it is, every element is kept. A complete path that crashed and a
    /// log that was not appended reach the record for admission.
    #[test]
    fn the_baseline_record_rests_on_its_path() {
        let resolved = resolved(&["clock"]);
        let ran = || trace(vec![recorded(&class(Stutter::Count), &[1, 2])]);
        let cut = [HaltClass::DepthBound];
        let kept = record(
            &resolved,
            ran(),
            Some(UNDETERMINED),
            false,
            true,
            &cut,
            &cut,
            Some(SETTLED),
            SETTLED,
        );
        assert!(kept.prefix && kept.crashed);
        assert_eq!(kept.channels[0].elements.len(), 2);
        assert_eq!(kept.channels[0].horizon(), Some(2));
        for (facts, why) in [
            (
                LeafFacts {
                    real: true,
                    clean: false,
                },
                "diagnostic",
            ),
            (
                LeafFacts {
                    real: false,
                    clean: true,
                },
                "not shown real",
            ),
        ] {
            let opened = record(
                &resolved,
                ran(),
                Some(UNDETERMINED),
                false,
                false,
                &cut,
                &cut,
                Some(facts),
                SETTLED,
            );
            assert_eq!(opened.channels[0].horizon(), Some(0), "{why}");
            let ChannelEnd::Open(opened) = &opened.channels[0].end else {
                panic!("{why}: the channel opens");
            };
            assert_eq!(opened.opening, Opening::UndecidedPath, "{why}");
            assert!(opened.reason.contains(why), "{}", opened.reason);
        }
        let mut rewritten = ran();
        rewritten.refusal =
            Some("log-not-appended: the log `out`: the item at 0 was rewritten".to_owned());
        let refused = record(
            &resolved,
            rewritten,
            Some(UNDETERMINED),
            false,
            false,
            &cut,
            &cut,
            Some(SETTLED),
            SETTLED,
        );
        assert!(refused.refusal.unwrap().starts_with("log-not-appended"));
    }

    /// A leaf of halt `halt` and state `state`, which the adapter did not decide.
    fn leaf(halt: HaltClass, state: &Pattern) -> AdaptedLeaf {
        AdaptedLeaf {
            halt,
            branch: kink_native::observation::AdaptedBranch {
                identity: Vec::new(),
                state: state.clone(),
                depth: 3,
                trace: Vec::new(),
            },
            feasibility: LeafFeasibility::Unknown,
            cause: None,
            diagnostics: Vec::new(),
            candidate_diagnostics: Vec::new(),
            remainder_diagnostics: Vec::new(),
            undefined_rule: None,
            contradicted_total: None,
            proposal: None,
            probe: None,
        }
    }

    /// A leaf's state is real by k-rust's existence judgement of it
    /// (`ObservationDecider::configuration_exists`), never by its shape: `out(f(a))` is ground
    /// with no predicate conjunct, yet owes `⌈f(a)⌉` (`f` partial, no equation reduces it), so a
    /// stuck leaf there is not real; `out(show(a))` owes nothing (`show` total), so a stuck leaf
    /// there is real, while the element read of it is undecided (it has no terminal value). A
    /// `Vacuous` leaf is never real, whatever its state, its feasibility or the bridge says of it,
    /// and neither is a leaf whose last step k-rust did not expand; existence is not asked of
    /// either.
    #[test]
    fn a_leaf_is_real_by_the_existence_of_its_state_where_k_rust_expanded_it() {
        let definition = BackendDefinition::internalize(
            &k_rust::kore::parser::parse_definition(
                r"[]
                module MAIN
                    sort SortS{} []
                    symbol Lbla{}() : SortS{} [constructor{}()]
                    symbol Lblout{}(SortS{}) : SortS{} [constructor{}()]
                    symbol Lblshow{}(SortS{}) : SortS{} [function{}(), total{}()]
                    symbol Lblf{}(SortS{}) : SortS{} [function{}()]
                endmodule []",
            )
            .unwrap(),
            "MAIN",
        )
        .unwrap();
        let parse = |text: &str| k_rust::kore::parser::parse_pattern(text).unwrap();
        let owing = parse(r"Lblout{}(Lblf{}(Lbla{}()))");
        let residue = parse(r"Lblout{}(Lblshow{}(Lbla{}()))");
        let decider =
            ObservationDecider::new(&definition, &NoSolver, TestInitialState::of_test(&residue));
        let exists = |term: &Pattern| decider.configuration_exists(term);
        let facts = |leaf: &AdaptedLeaf, vouched: bool| {
            LeafFacts::of(leaf, vouched, LeafFacts::existence(leaf, exists))
        };
        let stuck = leaf(HaltClass::Stuck, &owing);
        assert!(!facts(&stuck, false).real);
        assert!(!facts(&stuck, false).settled());
        let stuck = leaf(HaltClass::Stuck, &residue);
        assert!(facts(&stuck, false).settled());
        assert_eq!(decider.terminal_value(&residue), None);
        let unasked = |_: &Pattern| -> bool { panic!("existence is not asked") };
        for halt in [
            HaltClass::Vacuous,
            HaltClass::WorkBound,
            HaltClass::PollBound,
            HaltClass::BreadthBound,
            HaltClass::Timeout,
            HaltClass::Cancelled,
        ] {
            let unexpanded = leaf(halt, &residue);
            assert!(!LeafFacts::existence(&unexpanded, unasked), "{halt:?}");
            assert!(!LeafFacts::of(&unexpanded, false, true).real, "{halt:?}");
        }
        let mut vacuous = leaf(HaltClass::Vacuous, &residue);
        assert!(!LeafFacts::of(&vacuous, true, true).real);
        vacuous.feasibility = LeafFeasibility::Syntactic;
        assert!(!LeafFacts::of(&vacuous, true, true).real);
        // A shared path is real when one of its leaves is: an undefined step whose pre-step
        // state exists beside a successor that owes `⌈f(a)⌉`.
        let leaves = [
            leaf(HaltClass::Stuck, &owing),
            leaf(HaltClass::Trivial, &residue),
        ];
        let existing = leaves
            .iter()
            .map(|leaf| LeafFacts::existence(leaf, exists))
            .collect::<Vec<_>>();
        assert_eq!(existing, [false, true]);
        assert!(
            LeafFacts::shared(&leaves, false, &existing)
                .unwrap()
                .settled()
        );
        assert!(!LeafFacts::shared(&leaves, false, &[]).unwrap().real);
    }

    /// Several paths (module documentation, "Several paths"): a side's record and comparison
    /// built from its paths, each holding the channel `out`.
    mod several_paths {
        use super::*;

        /// A path whose channel holds `items`, each decided, ended as `end`.
        fn path(items: &[u8], end: LeafEnd) -> (Trace, LeafEnd) {
            (trace(vec![emitted(items, false)]), end)
        }

        fn stopped() -> LeafEnd {
            LeafEnd::Open(Opened::new(
                Opening::Bound,
                "the run stopped exploring the path",
            ))
        }

        /// The baseline's record of `paths`, every leaf with the facts `every`, its end
        /// determined.
        fn record_of(paths: &[(Trace, LeafEnd)], every: LeafFacts) -> BaselineRecord {
            record_paths(&resolved(&["out"]), paths, true, every, false, false, None)
        }

        /// A mutant's comparison of a run of the paths `paths`, every leaf with the facts
        /// `every`, its probe having found no difference.
        fn compared_paths(paths: Vec<(Trace, LeafEnd)>, every: LeafFacts) -> Comparison {
            Comparison {
                trace: Box::new(Trace {
                    paths: Some(Box::new(Paths { paths })),
                    ..trace(Vec::new())
                }),
                leaf: None,
                every,
                verdict: None,
            }
        }

        fn judged(baseline: &BaselineRecord, mutant: &Comparison) -> ObservationVerdict {
            judge(baseline, mutant, Some(&determined_end()), false)
        }

        const NOT_REAL: LeafFacts = LeafFacts {
            real: false,
            clean: true,
        };

        const DIAGNOSED: LeafFacts = LeafFacts {
            real: true,
            clean: false,
        };

        /// The baseline's paths end after 1 and after 2; the mutant's only after 1. Where every
        /// baseline leaf is real, its prefix [2], which no mutant path has, kills; where one is
        /// not, a prefix of the record is no fact the mutant could lack, and the slot is unknown.
        #[test]
        fn a_baseline_record_that_is_not_real_leaves_the_slot_unknown() {
            let baseline = [path(&[1], LeafEnd::End), path(&[2], LeafEnd::End)];
            let mutant = || compared_paths(vec![path(&[1], LeafEnd::End)], SETTLED);
            let real = record_of(&baseline, SETTLED);
            assert!(real.paths.as_ref().unwrap().real);
            let killed = judged(&real, &mutant());
            assert_eq!(killed.outcome, OracleOutcome::Distinguish);
            assert_eq!(
                killed.position.and_then(|at| at.outside),
                Some(Outside::Baseline)
            );
            let unreal = record_of(&baseline, NOT_REAL);
            assert!(!unreal.paths.as_ref().unwrap().real);
            let verdict = judged(&unreal, &mutant());
            assert_eq!(verdict.outcome, OracleOutcome::Unknown, "{verdict:?}");
            assert!(verdict.cause.unwrap().contains("not shown real"));
        }

        /// A diagnostic on a baseline leaf may stand for a path the run does not hold, so the
        /// record is explored to no index (`complete_to` 0), and a mutant prefix outside its set
        /// is no kill; a diagnostic on a mutant leaf leaves the slot unknown, as a mutant path may
        /// be missing.
        #[test]
        fn a_diagnostic_bounds_its_side_at_zero() {
            let baseline = [path(&[1], LeafEnd::End), path(&[2], LeafEnd::End)];
            let diagnosed = record_of(&baseline, DIAGNOSED);
            let sets = &diagnosed.paths.as_ref().unwrap().channels[0];
            assert_eq!(sets.complete_to, Some(at(0, Opening::UndecidedPath)));
            assert!(!sets.complete_at(0));
            let third = compared_paths(
                vec![path(&[1], LeafEnd::End), path(&[3], LeafEnd::End)],
                SETTLED,
            );
            assert_eq!(judged(&diagnosed, &third).outcome, OracleOutcome::Unknown);
            let clean = record_of(&baseline, SETTLED);
            let verdict = judged(
                &clean,
                &compared_paths(vec![path(&[1], LeafEnd::End)], DIAGNOSED),
            );
            assert_eq!(verdict.outcome, OracleOutcome::Unknown);
            assert!(verdict.cause.unwrap().contains("diagnostic"));
        }

        /// After the run, a mutant path's END or UNDEF outside the baseline's set kills, where
        /// the baseline is explored past its index and every mutant leaf is settled: the
        /// baseline's paths end after [1] and after [2, 3]; a mutant path ending after [2]
        /// closes there by END, and one taking an undefined step there by UNDEF, neither of which
        /// any baseline path has at index 1.
        #[test]
        fn a_mutant_end_or_undef_outside_the_baseline_set_kills_after_the_run() {
            let baseline = record_of(
                &[path(&[1], LeafEnd::End), path(&[2, 3], LeafEnd::End)],
                SETTLED,
            );
            for (end, element) in [
                (LeafEnd::End, Element::End),
                (LeafEnd::Undefined, Element::Undefined),
            ] {
                let mutant =
                    compared_paths(vec![path(&[1], LeafEnd::End), path(&[2], end)], SETTLED);
                let verdict = judged(&baseline, &mutant);
                assert_eq!(verdict.outcome, OracleOutcome::Distinguish, "{verdict:?}");
                assert_eq!(
                    verdict.position,
                    Some(Position {
                        channel: "out".to_owned(),
                        index: 1,
                        at_end: true,
                        outside: Some(Outside::Mutant),
                    })
                );
                assert_eq!(verdict.element, Some(element));
                // A mutant leaf that is not settled decides no end.
                let unsettled = compared_paths(
                    vec![path(&[1], LeafEnd::End), path(&[2], LeafEnd::End)],
                    NOT_REAL,
                );
                assert_ne!(
                    judged(&baseline, &unsettled).outcome,
                    OracleOutcome::Distinguish
                );
            }
        }

        /// A `Vacuous` leaf among several paths is no path of the definition: its prefixes join
        /// the set, which can only hide a mutant's prefix, it bounds nothing, and it makes the
        /// run's leaves not real, so the record holds no baseline prefix against a mutant.
        #[test]
        fn a_vacuous_leaf_among_several_paths_hides_and_bounds_nothing() {
            let state = k_rust::kore::parser::parse_pattern(r"\top{SortBool{}}()").unwrap();
            let mut vacuous = leaf(HaltClass::Vacuous, &state);
            vacuous.feasibility = LeafFeasibility::Syntactic;
            let mut stuck = leaf(HaltClass::Stuck, &state);
            stuck.feasibility = LeafFeasibility::Syntactic;
            let every = LeafFacts::every(&[stuck, vacuous], false, &[]);
            assert!(!every.real && every.clean);
            let paths = [path(&[1], LeafEnd::End), path(&[9], LeafEnd::Vacuous)];
            let sets = &sets_of(&paths, 1, true)[0];
            assert_eq!(sets.complete_to, None);
            assert!(sets.holds(
                0,
                &chain_next(&chain_start(), Link::Content(short(&digest(9))))
            ));
            let record = record_of(&paths, every);
            assert!(!record.paths.as_ref().unwrap().real);
            // The mutant lacks the vacuous prefix [9] and has the baseline's real one: no kill.
            let mutant = compared_paths(vec![path(&[1], LeafEnd::End)], SETTLED);
            assert_eq!(judged(&record, &mutant).outcome, OracleOutcome::Unknown);
        }

        /// A path the run stopped exploring is known up to where it was left only where a leaf
        /// stands for it (module documentation, "Several paths"): as known, it bounds its side at
        /// its elements; as unknown, it adds no prefix, bounds its side at 0 and makes the record
        /// not real, so neither a mutant prefix outside the set nor a baseline prefix the mutant
        /// lacks kills.
        #[test]
        fn a_path_the_run_stopped_exploring_bounds_its_side() {
            let known = record_of(&[path(&[1], LeafEnd::End), path(&[2], stopped())], SETTLED);
            let paths = known.paths.as_ref().unwrap();
            assert!(paths.real);
            assert_eq!(paths.channels[0].complete_to, Some(at(1, Opening::Bound)));
            let unknown = record_of(
                &[path(&[1], LeafEnd::End), path(&[2], LeafEnd::Unknown)],
                SETTLED,
            );
            let paths = unknown.paths.as_ref().unwrap();
            assert!(!paths.real);
            assert_eq!(
                paths.channels[0].complete_to,
                Some(at(0, Opening::UndecidedPath))
            );
            assert_eq!(paths.channels[0].prefixes[0].len(), 1);
            for mutant in [
                vec![path(&[3], LeafEnd::End)],
                vec![path(&[1], LeafEnd::End), path(&[3], LeafEnd::End)],
            ] {
                let verdict = judged(&unknown, &compared_paths(mutant, SETTLED));
                assert_eq!(verdict.outcome, OracleOutcome::Unknown, "{verdict:?}");
            }
            // An unknown mutant path leaves the mutant explored to no index: the baseline's
            // prefix [2], which no other mutant path has, does not kill.
            let baseline = record_of(
                &[path(&[1], LeafEnd::End), path(&[2], LeafEnd::End)],
                SETTLED,
            );
            let mutant = compared_paths(
                vec![path(&[1], LeafEnd::End), path(&[], LeafEnd::Unknown)],
                SETTLED,
            );
            assert_eq!(judged(&baseline, &mutant).outcome, OracleOutcome::Unknown);
        }
    }
}
