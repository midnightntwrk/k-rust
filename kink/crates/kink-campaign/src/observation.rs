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
//! where its path was cut by a bound, where the path first branched (only one path is compared),
//! and at an undecided element, except under [`Stutter::Count`]:
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

use k_rust::k_rust_backend::definition::BackendDefinition;
use k_rust::k_rust_backend::smt::NoSolver;
use k_rust::kore::ast::{Definition as KoreDefinition, Pattern, Sentence};
use k_rust::kore::printer::Printer;
use k_rust::names::KoreAttribute;
use kink_native::execution::{
    AdaptedLeaf, CellHandle, HaltClass, Probe, ProbeArrival, ProbeCycle, ProbeDecision, ProbeLeaf,
    ProbeRules, ProbeState, StopRules, StopSide,
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
/// "Cycles").
pub const OBSERVATION_VERSION: &str = "kink-campaign/observation/v2";

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
    /// logs: [{name, cell, at}]}`, with `cycle_states` where it is not [`CYCLE_STATES`]; `None`
    /// for [`Self::NONE`]. Every field is destructured, so a new one does not compile until it is
    /// recorded here.
    #[must_use]
    pub fn value(self) -> Option<Value> {
        let Declaration {
            points,
            logs,
            cycle_states,
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

/// Where a recorded channel ends: closed by END or UNDEF after its elements, complete and silent
/// after a return of its path ([`Closure::Cycle`]), or open there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ChannelEnd {
    Closed(Closure),
    /// The channel is open after its elements, for this reason (a bound, a branch, an undecided
    /// element or end).
    Open(String),
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
}

impl BaselineRecord {
    /// The record as a result record keeps it: `{channels: [{name, elements, closed, open}],
    /// prefix, crashed}`, each element the hex of its 8 digest bytes (null where it was undecided),
    /// `closed` `"end"`, `"undefined"` or `"cycle"` for a closed channel (else null), and `open` `{index,
    /// reason}` for an open one (else null), `index` its horizon. Every field is destructured, so a
    /// new one does not compile until it is recorded here.
    #[must_use]
    pub fn value(&self) -> Value {
        let Self {
            channels,
            prefix,
            crashed,
            refusal,
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
                    ChannelEnd::Open(reason) => (
                        Value::Null,
                        json!({"index": elements.len(), "reason": reason}),
                    ),
                };
                json!({"name": name, "elements": elements, "closed": closed, "open": open})
            })
            .collect::<Vec<_>>();
        let mut value = json!({"channels": channels, "prefix": prefix, "crashed": crashed});
        if let Some(refusal) = refusal {
            value["refusal"] = json!(refusal);
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

/// Where the slot found a difference: the channel, the index, and whether it was read where the
/// mutant's path ended (an END or UNDEF, or a log item appended by the last step) rather than at
/// a point.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Position {
    pub channel: String,
    pub index: usize,
    pub at_end: bool,
}

/// The observation slot's outcome for one mutant run of one test ([`judge`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObservationVerdict {
    pub outcome: OracleOutcome,
    /// The first decided difference, on `Distinguish`.
    pub position: Option<Position>,
    /// On `Agree`, each channel whose agreement rests on the baseline's prefix: the number of
    /// elements it agrees on, its horizon. Empty when every channel agreed to its end.
    pub horizon: BTreeMap<String, usize>,
    /// On `Unknown`, why.
    pub cause: Option<String>,
    /// On `Distinguish`, the mutant's element at the position: the content its probe read, or
    /// END or UNDEF where its path closed the channel.
    pub element: Option<Element>,
    /// Where the mutant's path returned to an earlier state of itself, when it did (module
    /// documentation, "Cycles"): the depth of the earlier state and of the state of the return.
    pub cycle: Option<(u64, u64)>,
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
    /// breadth-bound, timed-out or cancelled one, whose state was taken from the worklist (or
    /// left on it) before its producing step's successor was normalized and split, so its
    /// predicate need not hold that step's right-hand side obligations, and no undefined step
    /// need stand beside it for the instances where they fail.
    const fn expanded(halt: HaltClass) -> bool {
        !matches!(
            halt,
            HaltClass::WorkBound
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
    /// The run's one leaf, when it has exactly one.
    pub(crate) leaf: Option<LeafFacts>,
    pub verdict: Option<ObservationVerdict>,
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
    open: Option<String>,
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
#[derive(Clone, Debug, Eq, PartialEq)]
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
}

/// The probe of one result run: records the baseline's channels, or compares a mutant's with the
/// baseline's record as they come ([module documentation](self)).
pub(crate) struct ObservationProbe<'a> {
    resolved: &'a Resolved,
    decider: ObservationDecider<'a>,
    against: Option<&'a BaselineRecord>,
    trace: Trace,
    /// A capture run's target ([`Self::capturing`]): the channel and the index of the element it
    /// re-derives, and that element once read, with its recorded digest bytes.
    capture: Option<(usize, usize)>,
    captured: Option<(Element, Option<[u8; 8]>)>,
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
    /// baseline's definition `shared` (with collections `trusted`), comparing with `against`
    /// when it is a mutant's run.
    pub(crate) fn new(
        resolved: &'a Resolved,
        shared: &'a BackendDefinition,
        trusted: bool,
        initial: &'a Pattern,
        against: Option<&'a BaselineRecord>,
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
        Self {
            resolved,
            decider,
            against,
            trace: Trace {
                channels,
                branched: None,
                ended: false,
                answer: None,
                end_difference: None,
                refusal: None,
                differing: None,
                cycled: None,
            },
            capture: None,
            captured: None,
        }
    }

    /// The probe of a capture run of the baseline ([`crate::observed_difference`]): it records
    /// the run's channels as the baseline's probe does, and ends the path once it has read the
    /// element `index` of the channel `channel`, which it keeps with its digest bytes.
    pub(crate) fn capturing(
        resolved: &'a Resolved,
        shared: &'a BackendDefinition,
        trusted: bool,
        initial: &'a Pattern,
        channel: usize,
        index: usize,
    ) -> Self {
        let mut probe = Self::new(resolved, shared, trusted, initial, None);
        probe.capture = Some((channel, index));
        probe
    }

    /// The element a capture run read, with its digest bytes as the run recorded them: `None`
    /// when the run did not reach it.
    pub(crate) fn captured(self) -> Option<(Element, Option<[u8; 8]>)> {
        self.captured
    }

    /// The values of the point class `channel`'s cells at `state`, for a reader: an element is
    /// undecided where a part is no value.
    fn values(&self, channel: usize, state: &ProbeState<'_>) -> Element {
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

    /// The value of one log item, for a reader.
    fn item_value(&self, item: &Pattern) -> Element {
        item.free_variables()
            .is_empty()
            .then(|| self.decider.terminal_value(item))
            .flatten()
            .map_or(Element::Undecided, |value| Element::Content(vec![value]))
    }

    /// Whether the element just taken on `channel`, which had `before` elements, is a capture
    /// run's target: it is then kept, as `element` gives it, with its recorded digest bytes.
    fn capture_taken(
        &mut self,
        channel: usize,
        before: usize,
        element: impl FnOnce(&Self) -> Element,
    ) {
        let Some((target, index)) = self.capture else {
            return;
        };
        let trace = &self.trace.channels[channel];
        if target == channel
            && before == index
            && trace.elements.len() == index + 1
            && self.captured.is_none()
        {
            let digest = trace.elements[index];
            self.captured = Some((element(self), digest));
        }
    }

    /// The rules the probe observes.
    pub(crate) fn rules(&self) -> ProbeRules {
        self.resolved.rules.clone()
    }

    /// The channels as the run left them.
    pub(crate) fn finish(self) -> Trace {
        self.trace
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

    /// The element of the point class `channel` at `state`: the digest of its cells' values.
    fn content(&mut self, channel: usize, state: &ProbeState<'_>) -> Result<[u8; 32], String> {
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

    /// Takes `element` on `channel`: recorded on the baseline, compared on a mutant. The index of
    /// a difference it makes.
    fn take(&mut self, channel: usize, element: Result<[u8; 32], String>) -> Option<usize> {
        let resolution = &self.resolved.channels[channel];
        let trace = &mut self.trace.channels[channel];
        if let Some(against) = self.against {
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
            self.trace.channels[channel].open =
                Some("the log cell holds no list of known items".to_owned());
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
                if self.item(item.clone()).ok()
                    != Some(self.trace.channels[channel].items[position])
                {
                    self.not_appended(channel, format!("the item at {position} was rewritten"));
                    return None;
                }
            }
            all.into_iter().skip(read).collect()
        };
        self.trace.channels[channel].handle = handle;
        for item in new {
            let element = self.item(item.clone());
            if let Ok(digest) = &element
                && self.against.is_none()
            {
                self.trace.channels[channel].items.push(*digest);
            }
            self.trace.channels[channel].read += 1;
            let before = self.trace.channels[channel].elements.len();
            if let Some(index) = self.take(channel, element) {
                if self.trace.differing.is_none() {
                    self.trace.differing = Some(Box::new(self.item_value(&item)));
                }
                return Some(index);
            }
            self.capture_taken(channel, before, |probe| probe.item_value(&item));
            if self.captured.is_some()
                || self.trace.channels[channel].open.is_some()
                || self.trace.channels[channel].reached
            {
                break;
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
        self.trace.channels[channel].open = Some(why);
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
            trace.open = Some(format!("undecided element at {index}: {reason}"));
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
        Err(reason) => trace.open = Some(format!("undecided element at {index}: {reason}")),
    }
}

impl Probe for ObservationProbe<'_> {
    fn observe(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision {
        if self.trace.cycled.is_some() {
            return ProbeDecision::Continue;
        }
        let (rule, side) = (point.rule().to_owned(), point.side());
        for channel in 0..self.resolved.channels.len() {
            if !self.resolved.channels[channel].selects(&rule, side) {
                continue;
            }
            let difference = match self.resolved.channels[channel] {
                Resolution::Point { .. } => {
                    let open = self.trace.channels[channel].open.is_some()
                        || self.trace.channels[channel].reached;
                    if open {
                        None
                    } else {
                        let before = self.trace.channels[channel].elements.len();
                        let element = self.content(channel, point);
                        let difference = self.take(channel, element);
                        if difference.is_some() {
                            self.trace.differing = Some(Box::new(self.values(channel, point)));
                        }
                        self.capture_taken(channel, before, |probe| probe.values(channel, point));
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

    fn branched(&mut self, depth: u64) {
        if self.trace.cycled.is_some() {
            return;
        }
        self.trace.branched = Some(depth);
        for channel in &mut self.trace.channels {
            channel
                .open
                .get_or_insert_with(|| format!("the path branched at depth {depth}"));
        }
    }

    fn ended(&mut self, leaf: &ProbeLeaf<'_>) {
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

    fn cycle_states(&self) -> usize {
        self.resolved.cycle_states
    }

    /// The sum of what the probe keeps that its answers rest on: each channel's elements, items
    /// read and whether it opened, passed the baseline's horizon or met an undecided element, and
    /// whether the probe answered or refused. Each only grows, so an equal sum is an equal state:
    /// the last element kept, which collapse compares with, changes only with the elements, and
    /// the handles held only spare conversions.
    fn progress(&self) -> u64 {
        let channels = self
            .trace
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
        let answered =
            usize::from(self.trace.answer.is_some()) + usize::from(self.trace.refusal.is_some());
        u64::try_from(channels + answered).unwrap_or(u64::MAX)
    }

    /// The path runs forever from here and the probe sees nothing new on it, so every channel
    /// neither open nor past the baseline's horizon is complete ([`Self::close_silent`]). The
    /// baseline's run goes on as without the probe, which heeds nothing more of it; a mutant's
    /// request ends at its first difference, and its path otherwise, since nothing more can be
    /// learned.
    fn cycled(&mut self, cycle: &ProbeCycle<'_>) -> ProbeDecision {
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
) -> BaselineRecord {
    let settled = facts.is_some_and(LeafFacts::settled);
    let bound = |halt: &HaltClass| matches!(halt, HaltClass::DepthBound | HaltClass::WorkBound);
    let ended = sides.is_some_and(determined);
    let prefix =
        sides.is_some() && !ended && !incomplete.is_empty() && incomplete.iter().all(bound);
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
        [halt] if bound(halt) => "the path was cut by a bound".to_owned(),
        [halt] => format!("the path ended undecided ({halt:?})"),
        _ => "the run gave no single leaf".to_owned(),
    };
    let unsettled = match facts {
        None => "the run gave no leaf",
        Some(facts) if !facts.real => "the path's states are not shown real",
        Some(_) => "k-rust reported a diagnostic on the path",
    };
    let channels = trace
        .channels
        .into_iter()
        .zip(&resolved.names)
        .map(|(mut channel, name)| {
            if !settled && !channel.elements.is_empty() {
                channel.elements.clear();
                channel.open = Some(format!("the path is not settled: {unsettled}"));
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
                    (Some(reason), _) => ChannelEnd::Open(reason),
                    (None, Some(closure)) if settled => ChannelEnd::Closed(closure),
                    (None, Some(_)) => {
                        ChannelEnd::Open(format!("the path is not settled: {unsettled}"))
                    }
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
    let trace = &comparison.trace;
    let name = |channel: usize| baseline.channels[channel].name.clone();
    let distinguish =
        |channel: usize, index: usize, at_end: bool, element: Option<Element>| ObservationVerdict {
            outcome: OracleOutcome::Distinguish,
            position: Some(Position {
                channel: name(channel),
                index,
                at_end,
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
                // END or UNDEF against a content element.
                return distinguish(channel, emitted, true, Some(kind.element()));
            }
            Some(kind) => match recorded.end {
                ChannelEnd::Closed(other) if other == kind => closed_alike = true,
                ChannelEnd::Closed(_) => {
                    return distinguish(channel, emitted, true, Some(kind.element()));
                }
                ChannelEnd::Open(_) => {
                    horizon.insert(name(channel), recorded_length);
                }
            },
            None if mutant.reached || (agrees_to_horizon && emitted >= recorded_length) => {
                horizon.insert(name(channel), recorded_length);
            }
            None => {
                open.get_or_insert_with(|| {
                    format!(
                        "the channel `{}` is open at {emitted}: {}",
                        name(channel),
                        mutant
                            .open
                            .as_deref()
                            .unwrap_or("the mutant's path has no decided end")
                    )
                });
            }
        }
    }
    if open.is_none()
        && baseline.prefix
        && !closed_alike
        && horizon.values().all(|length| *length == 0)
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
        ChannelEnd::Open("the path was cut by a bound".to_owned())
    }

    fn baseline(channels: Vec<ChannelRecord>, prefix: bool) -> BaselineRecord {
        BaselineRecord {
            channels,
            prefix,
            crashed: false,
            refusal: None,
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
        assert_eq!(verdict.horizon, BTreeMap::from([("clock".to_owned(), 2)]));

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
            BTreeMap::from([("clock".to_owned(), 1), ("out".to_owned(), 1)])
        );

        let undecided = ChannelEnd::Open("undecided element at 1: no value".to_owned());
        let ending = baseline(vec![channel("clock", &[1], undecided)], false);
        let mut reached = trace(vec![emitted(&[1], true)]);
        reached.ended = true;
        let end = determined_end();
        let verdict = judge(&ending, &compared(reached, SETTLED), Some(&end), false);
        assert_eq!(verdict.outcome, OracleOutcome::Agree);
        assert_eq!(verdict.horizon, BTreeMap::from([("clock".to_owned(), 1)]));
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
        assert_eq!(verdict.horizon, BTreeMap::from([("clock".to_owned(), 2)]));
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
            );
            assert_eq!(opened.channels[0].horizon(), Some(0), "{why}");
            let ChannelEnd::Open(reason) = &opened.channels[0].end else {
                panic!("{why}: the channel opens");
            };
            assert!(reason.contains(why), "{reason}");
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
}
