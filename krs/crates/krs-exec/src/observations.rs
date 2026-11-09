//! Observations: a run's meaning as sequences of declared observations along its path, beside
//! its end ([`ObservationSpec`], [`crate::RunOptions::observe`]).
//!
//! # Channels
//!
//! A declaration is a finite set of *channels*, each a sequence of elements a run emits along
//! its path.
//!
//! - A *point class* names rewrite rules, as a stop names them ([`crate::StopRules`]), on the
//!   before or the after side of their step. A *point* is a step of the path by such a rule whose
//!   successor is defined; its *observed state* is the state before the step for a before rule and
//!   the normalized successor for an after rule (k-rust's probe, docs/compatibility.md, "Probes
//!   (in-process)"). At each point the class emits its *content*: a tuple of components, each a
//!   leaf cell's value ([`PointClass::cells`]) or a function of named cells evaluated in the
//!   observer ([`PointClass::views`], [`PointClass::components`]). A filter
//!   ([`PointClass::when`]) keeps only the points where it is decided true. Which rule of the
//!   class fired, and the relative order of two classes' points, are not observed: a point is a
//!   place to sample at, not content.
//! - A *log* names a `List` cell. Its channel is the concatenation, in append order, of an element
//!   function's values ([`LogChannel::element`], `Item -> List<_>`, the identity by default) on
//!   the items the cell holds. The cell is read at the points of the classes the log names
//!   ([`LogChannel::at`], their filters not applying) and at the path's end; a recording run
//!   checks that each read's items begin with the previous read's, exactly, and refuses the
//!   program's log otherwise (`log-not-appended`).
//!
//! # Stuttering
//!
//! A class declares what two equal consecutive contents are ([`Stutter`]): under `collapse` an
//! element equal to the last element kept is dropped, so the number of points is not observed;
//! under `count` nothing is dropped, so it is. Both are sound (a kill under either is a
//! difference of one function of the path, evaluated alike for both sides); which one a
//! specification promises is the author's statement, so the class must say it.
//!
//! # How a channel ends
//!
//! A channel is *closed* by the run's end: by `end` where the path ends at a determined end (no
//! rule applies, or a stop of the run's stop rules), by `undefined` where its last step is
//! undefined. Otherwise it stays *open* at the index where the run stopped knowing it: a bound,
//! the path's first state with several successors, or an element whose value is undecided.
//! An element is a function of a finite prefix of the path, so a bound only ends what is known.
//!
//! # Undefined and undecided elements
//!
//! An element can fail two ways. It has *no value* where a read cell holds no data (a variable,
//! an unevaluated application, a part with no KRS description) or the observer gives the function
//! no value; it is *undecided* where an evaluation spent its budget of polls or the solver
//! answered `Unknown`. A recording run for `krs run` refuses an element with no value
//! ([`crate::ExecError::Observation`]), naming the point, the rule, the steps and the cell, and
//! keeps an undecided element as unknown; a run that compares, or that records a baseline for a
//! comparison ([`RecordOptions::refuse_no_value`] false), keeps either as unknown. An unknown
//! element opens a log's channel and a `collapse` class's (its index rests on decided equalities
//! of earlier elements), and under `count` leaves the later elements comparable: the index is
//! the number of points. An unknown filter opens the class's channel in either mode.
//!
//! # Digests
//!
//! Elements are told apart by SHA-256 digests of a canonical encoding of their terms: a leaf
//! cell's content as the run's definition holds it, a function's value as the observer encodes
//! it, with `Map` and `Set` elements ordered by their own encodings (`ValueIndex`'s canonical
//! KORE). Equal terms have equal digests; distinct terms have distinct digests under the
//! collision resistance of SHA-256. A digest truncated to a prefix ([`ElementDigest::truncated`])
//! only tells two elements apart where the prefixes differ, so a truncation can hide a difference
//! and never make one. A leaf cell's component is digested from its content without a round trip
//! through the observer, and a cell the backend did not rewrite since the last point (the same
//! term node, [`k_rust::backend::CellHandle`]) is not converted again.
//!
//! # Recording and comparing
//!
//! [`ObservationOracle`] is the backend's probe of a run with observations. Recording
//! ([`ObservationOracle::record`]) keeps every element, with its value where asked; comparing
//! ([`ObservationOracle::compare`]) checks each element against a recorded baseline as it is
//! emitted, ends the run at the first decided difference, and ends the path once every channel
//! has opened or passed the baseline's horizon. [`compare_records`] is the one comparison of two
//! records, which reads the channels' ends too: their first difference ([`first_difference`]),
//! or how far each channel agrees and what stopped it.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::sync::Arc;

use k_rust::backend::{
    CellHandle, Probe, ProbeArrival, ProbeDecision, ProbeLeaf, ProbeRules, ProbeState, StopSide,
};
use k_rust::kore::ast::Pattern;
use krs_ir::BuiltinSort;
use serde::ser::{SerializeMap, SerializeStruct};
use serde::{Serialize, Serializer};
use serde_json::Value as Json;
use sha2::{Digest as _, Sha256};

use crate::condition::{
    ObservationError, ObservedState, ReadCell, ResolvedCondition, Use, leaf_content,
};
use crate::inputs::InputType;
use crate::report::StopAt;
use crate::values::{Decl, SortRef, Value, ValueIndex};
use crate::{ExecError, Semantics};

/// The format name of an observation document ([`Observations::document`]).
pub const OBSERVATIONS_FORMAT: &str = "krs-observations/1";

/// A run's declared observations ([module documentation](self)). An empty declaration observes
/// nothing, and a run under it is the run without it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ObservationSpec {
    /// The point classes, in declaration order.
    pub points: Vec<PointClass>,
    /// The logs, in declaration order.
    pub logs: Vec<LogChannel>,
    /// The definition the functions are evaluated in, `PACKAGE:DEFINITION` as an observer is
    /// named; `None` for the run's own definition. A front end resolves the name and passes the
    /// definition to [`Semantics::observations`] and [`crate::Observers::observations`].
    pub observer: Option<String>,
}

impl ObservationSpec {
    /// Whether the declaration has no channel.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.points.is_empty() && self.logs.is_empty()
    }

    /// Whether it declares a function, which is evaluated in an observer: a view, a component, a
    /// filter or an element function.
    #[must_use]
    pub fn declares_function(&self) -> bool {
        self.points.iter().any(|class| {
            !class.views.is_empty() || !class.components.is_empty() || class.when.is_some()
        }) || self.logs.iter().any(|log| log.element.is_some())
    }
}

/// A point class ([module documentation](self), "Channels").
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PointClass {
    /// The channel's name, unique among the declaration's channels.
    pub name: String,
    /// The rules whose steps are before points, named as a stop names them.
    pub before: Vec<String>,
    /// The rules whose steps are after points, named as a stop names them.
    pub after: Vec<String>,
    /// What two equal consecutive contents are ([`Stutter`]); there is no default.
    pub stutter: Stutter,
    /// Leaf cells, by Rust field path, each a component named by its path: its value, or the
    /// value of its view ([`Self::views`]).
    pub cells: Vec<String>,
    /// A view per cell of [`Self::cells`]: a function of one parameter, evaluated in the
    /// observer, whose value is the cell's component.
    pub views: BTreeMap<String, String>,
    /// Further components, each a function of named cells, after the cells.
    pub components: Vec<Component>,
    /// The filter: a point is an event only where it is decided true at the observed state.
    pub when: Option<Filter>,
}

/// What a class's equal consecutive contents are ([module documentation](self), "Stuttering").
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Stutter {
    /// An element equal to the last element kept is dropped.
    Collapse,
    /// Every event is an element.
    Count,
}

impl Stutter {
    /// The declaration's spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Collapse => "collapse",
            Self::Count => "count",
        }
    }

    /// The mode a declaration spells `text`, if any.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        match text {
            "collapse" => Some(Self::Collapse),
            "count" => Some(Self::Count),
            _ => None,
        }
    }
}

/// A component of a class's content that is a function of named cells.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Component {
    /// The component's name, unique among the class's components and cells.
    pub name: String,
    /// The leaf cells it reads, by Rust field path, in the order of its parameters.
    pub cells: Vec<String>,
    /// The function, by a KRS path as [`crate::ValueIndex::decl`] reads one (`crate::` and its
    /// path for the root package's, its full path, or a `::`-aligned suffix of it).
    pub function: String,
}

/// A class's filter: a function of named cells of result sort `Bool`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Filter {
    /// The function, by a KRS path as [`crate::ValueIndex::decl`] reads one (`crate::` and its
    /// path for the root package's, its full path, or a `::`-aligned suffix of it).
    pub function: String,
    /// The leaf cells it reads, by Rust field path, in the order of its parameters.
    pub cells: Vec<String>,
}

/// A log ([module documentation](self), "Channels").
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LogChannel {
    /// The channel's name, unique among the declaration's channels.
    pub name: String,
    /// The `List` leaf cell, by Rust field path.
    pub cell: String,
    /// The element function, `Item -> List<_>`, evaluated in the observer on each appended
    /// item; `None` for the identity, each item an element.
    pub element: Option<String>,
    /// The point classes at whose points the cell is read, besides the path's end.
    pub at: Vec<String>,
}

/// A channel's kind.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ChannelKind {
    /// A point class's channel.
    Point,
    /// A log's channel.
    Log,
}

/// A component of a resolved class.
#[derive(Clone, Debug)]
enum ResolvedComponent {
    /// A leaf cell's value, digested from its content.
    Cell {
        name: String,
        cell: ReadCell,
        declared: InputType,
    },
    /// A function of named cells, evaluated in the observer.
    Function {
        name: String,
        function: ResolvedCondition,
    },
}

impl ResolvedComponent {
    fn name(&self) -> &str {
        match self {
            Self::Cell { name, .. } | Self::Function { name, .. } => name,
        }
    }
}

#[derive(Clone, Debug)]
struct ResolvedClass {
    name: String,
    stutter: Stutter,
    before: BTreeSet<String>,
    after: BTreeSet<String>,
    components: Vec<ResolvedComponent>,
    filter: Option<ResolvedCondition>,
}

impl ResolvedClass {
    fn selects(&self, rule: &str, side: StopSide) -> bool {
        match side {
            StopSide::Before => self.before.contains(rule),
            StopSide::After => self.after.contains(rule),
        }
    }
}

/// A log's element function, resolved in the observer.
#[derive(Clone, Debug)]
struct ElementFunction {
    decl: Decl,
    parameter: Arc<str>,
    /// The type of each element of its result.
    element: InputType,
}

#[derive(Clone, Debug)]
struct ResolvedLog {
    name: String,
    cell: ReadCell,
    /// The declared type of an item.
    item: InputType,
    element: Option<ElementFunction>,
    /// The classes it is read at, by position.
    at: BTreeSet<usize>,
}

/// A declaration resolved for runs of one definition, its functions in one observer
/// ([`Semantics::observations`]).
#[derive(Clone, Debug)]
pub struct ResolvedObservations {
    spec: ObservationSpec,
    classes: Vec<ResolvedClass>,
    logs: Vec<ResolvedLog>,
    subject: Arc<ValueIndex>,
    observer: Arc<ValueIndex>,
    functions: bool,
}

impl ResolvedObservations {
    /// The declaration as it was resolved.
    #[must_use]
    pub const fn spec(&self) -> &ObservationSpec {
        &self.spec
    }

    /// The rules whose steps the probe observes, by `UNIQUE_ID`, on each side: every class's,
    /// a log's classes among them.
    #[must_use]
    pub fn probe_rules(&self) -> ProbeRules {
        let mut rules = ProbeRules::default();
        for class in &self.classes {
            rules.before.extend(class.before.iter().cloned());
            rules.after.extend(class.after.iter().cloned());
        }
        rules
    }

    /// Whether some component, filter or element function is evaluated in the observer, so a
    /// run needs one.
    #[must_use]
    pub const fn needs_observer(&self) -> bool {
        self.functions
    }

    /// Every cell the declaration reads, without repeats: each class's cells, the cells of its
    /// components and of its filter, and each log's cell, as the cell symbols from the
    /// configuration's top down to the cell (the path [`ProbeState::cell`] follows). A front end
    /// that evaluates the declaration on another engine's runs ([`ObservationOracle::evaluator`])
    /// checks that these cells can hold no term read otherwise on the definitions it reads with
    /// the declaration's subject.
    #[must_use]
    pub fn read_cells(&self) -> Vec<Vec<String>> {
        let mut cells = BTreeSet::new();
        for class in &self.classes {
            for component in &class.components {
                match component {
                    ResolvedComponent::Cell { cell, .. } => {
                        cells.insert(cell.symbols.clone());
                    }
                    ResolvedComponent::Function { function, .. } => {
                        cells.extend(function.cell_symbols().map(<[String]>::to_vec));
                    }
                }
            }
            if let Some(filter) = &class.filter {
                cells.extend(filter.cell_symbols().map(<[String]>::to_vec));
            }
        }
        for log in &self.logs {
            cells.insert(log.cell.symbols.clone());
        }
        cells.into_iter().collect()
    }

    /// The channels' names and kinds, in channel order: the classes, then the logs.
    pub fn channels(&self) -> impl Iterator<Item = (&str, ChannelKind)> {
        self.classes
            .iter()
            .map(|class| (class.name.as_str(), ChannelKind::Point))
            .chain(
                self.logs
                    .iter()
                    .map(|log| (log.name.as_str(), ChannelKind::Log)),
            )
    }
}

const COMPONENT: Use = Use {
    what: "an observation",
    noun: "an observation",
};
const VIEW: Use = Use {
    what: "a view of an observation",
    noun: "a view",
};
const FUNCTION: Use = Use {
    what: "an observation's component",
    noun: "a component",
};
const FILTER: Use = Use {
    what: "a filter",
    noun: "a filter",
};
const LOG: Use = Use {
    what: "a log",
    noun: "a log",
};

impl Semantics {
    /// Resolve the observations `spec` for runs of this definition, its functions in
    /// `observer`, the definition they are evaluated in (this definition itself, or another
    /// one composing it; a declaration with no function needs none, and this definition may be
    /// passed) ([module documentation](crate::observations)).
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Observe`] naming the channel and the cause: a channel's name that is
    /// empty or not unique; a class with no rule, or a rule name that selects no rewrite rule
    /// (an unknown name, an equation, several labels by suffix, items of several packages); a
    /// cell that is unknown, unobservable, a group cell, or at or below a repeated or optional
    /// cell; a cell named twice, a component name that is not unique, a view of a cell the class
    /// does not read; a function the observer does not hold, evaluated in an instance,
    /// parametric, or whose parameters are not one per cell each of a sort admitting its cell's
    /// (a view's arity or sort); a filter whose result is not `Bool`; a log whose cell is not a
    /// `List`, whose element function is not `Item -> List<_>`, or that is read at a class the
    /// declaration does not have.
    pub fn observations(
        &self,
        observer: &Self,
        spec: &ObservationSpec,
    ) -> Result<ResolvedObservations, ExecError> {
        let mut names = BTreeSet::new();
        for name in spec
            .points
            .iter()
            .map(|point| &point.name)
            .chain(spec.logs.iter().map(|log| &log.name))
        {
            if name.is_empty() {
                return Err(ExecError::Observe(
                    "an observation channel has an empty name".to_owned(),
                ));
            }
            if !names.insert(name.as_str()) {
                return Err(ExecError::Observe(format!(
                    "the observation channel `{name}` is declared twice; each channel has a name of its own"
                )));
            }
        }
        let mut functions = false;
        let classes = spec
            .points
            .iter()
            .map(|point| {
                self.resolve_class(observer, point, &mut functions)
                    .map_err(|message| {
                        ExecError::Observe(format!("the point class `{}`: {message}", point.name))
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let logs = spec
            .logs
            .iter()
            .map(|log| {
                self.resolve_log(observer, log, spec, &mut functions)
                    .map_err(|message| {
                        ExecError::Observe(format!("the log `{}`: {message}", log.name))
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ResolvedObservations {
            spec: spec.clone(),
            classes,
            logs,
            subject: Arc::clone(&self.values),
            observer: Arc::clone(&observer.values),
            functions,
        })
    }

    fn resolve_class(
        &self,
        observer: &Self,
        point: &PointClass,
        functions: &mut bool,
    ) -> Result<ResolvedClass, String> {
        if point.before.is_empty() && point.after.is_empty() {
            return Err(
                "names no rule; a point class names the rules whose steps it observes".to_owned(),
            );
        }
        let resolve = |names: &[String]| {
            let mut ids = BTreeSet::new();
            for name in names {
                ids.extend(
                    self.rules
                        .resolve_stop(name)
                        .map_err(|error| error.to_string())?,
                );
            }
            Ok::<_, String>(ids)
        };
        let before = resolve(&point.before)?;
        let after = resolve(&point.after)?;
        let mut components = Vec::new();
        let mut component_names = BTreeSet::new();
        for path in &point.cells {
            if !component_names.insert(path.as_str()) {
                return Err(format!("reads the cell `{path}` twice"));
            }
            components.push(if let Some(view) = point.views.get(path) {
                *functions = true;
                ResolvedComponent::Function {
                    name: path.clone(),
                    function: self.cell_function(
                        observer,
                        view,
                        std::slice::from_ref(path),
                        VIEW,
                    )?,
                }
            } else {
                let (cell, declared) = self.read_leaf_cell(path, COMPONENT)?;
                ResolvedComponent::Cell {
                    name: path.clone(),
                    cell,
                    declared,
                }
            });
        }
        if let Some(cell) = point.views.keys().find(|cell| !point.cells.contains(cell)) {
            return Err(format!(
                "has a view of the cell `{cell}`, which it does not read; a view replaces a cell's component"
            ));
        }
        for component in &point.components {
            if component.name.is_empty() {
                return Err("has a component with an empty name".to_owned());
            }
            if !component_names.insert(component.name.as_str()) {
                return Err(format!(
                    "has two components named `{}`; a cell's component is named by its path",
                    component.name
                ));
            }
            *functions = true;
            components.push(ResolvedComponent::Function {
                name: component.name.clone(),
                function: self
                    .cell_function(observer, &component.function, &component.cells, FUNCTION)
                    .map_err(|message| format!("the component `{}`: {message}", component.name))?,
            });
        }
        let filter = point
            .when
            .as_ref()
            .map(|filter| {
                *functions = true;
                let resolved = self
                    .cell_function(observer, &filter.function, &filter.cells, FILTER)
                    .map_err(|message| format!("the filter `{}`: {message}", filter.function))?;
                match &resolved.result {
                    Some(InputType {
                        sort: SortRef::Builtin(BuiltinSort::Bool),
                        ..
                    }) => Ok(resolved),
                    _ => Err(format!(
                        "the filter `{}`: `{}` does not return Bool; a filter holds or does not at a state",
                        filter.function,
                        resolved.function_path()
                    )),
                }
            })
            .transpose()?;
        Ok(ResolvedClass {
            name: point.name.clone(),
            stutter: point.stutter,
            before,
            after,
            components,
            filter,
        })
    }

    fn resolve_log(
        &self,
        observer: &Self,
        log: &LogChannel,
        spec: &ObservationSpec,
        functions: &mut bool,
    ) -> Result<ResolvedLog, String> {
        let (cell, declared) = self.read_leaf_cell(&log.cell, LOG)?;
        if declared.sort != SortRef::Builtin(BuiltinSort::List) {
            return Err(format!(
                "the cell `{}` is of sort {}, not a List; a log reads a List cell",
                log.cell,
                ValueIndex::sort_name(&declared.sort)
            ));
        }
        let item = declared.element(0);
        let element = log
            .element
            .as_ref()
            .map(|function| {
                *functions = true;
                element_function(observer, function, &item)
                    .map_err(|message| format!("the element function `{function}`: {message}"))
            })
            .transpose()?;
        let mut at = BTreeSet::new();
        for name in &log.at {
            let Some(position) = spec.points.iter().position(|point| &point.name == name) else {
                return Err(format!(
                    "is read at `{name}`, which is no point class of the declaration"
                ));
            };
            at.insert(position);
        }
        Ok(ResolvedLog {
            name: log.name.clone(),
            cell,
            item,
            element,
            at,
        })
    }
}

/// The element function `function` of a log whose items are of type `item`, resolved in
/// `observer`: a function of one parameter admitting the items, with a `List` result.
fn element_function(
    observer: &Semantics,
    function: &str,
    item: &InputType,
) -> Result<ElementFunction, String> {
    let decl = observer
        .values
        .function_decl(function)
        .map_err(|error| error.to_string())?;
    let Some(info) = observer.values.info(&decl) else {
        return Err(format!("`{decl}` has no production"));
    };
    if !observer.values.is_loaded(&decl) {
        return Err(format!(
            "`{decl}` is declared by a package whose module the observer's main module does not import, so the observer does not hold it"
        ));
    }
    if let Some(reason) = observer
        .values
        .instance_function(&decl, "an element function")
    {
        return Err(reason);
    }
    if info.parameters != 0 {
        return Err(format!(
            "`{decl}` is a parametric function; an element function maps an item to a List of elements"
        ));
    }
    let ([parameter], [parameter_type]) = (info.fields.as_slice(), info.field_types.as_slice())
    else {
        return Err(format!(
            "`{decl}` takes {} parameters; an element function takes one, the item",
            info.fields.len()
        ));
    };
    let Some(InputType {
        sort: parameter_sort,
        ..
    }) = parameter_type
    else {
        return Err(format!(
            "the parameter `{parameter}` of `{decl}` has a sort with no KRS declaration"
        ));
    };
    if item.is_untyped() {
        if *parameter_sort != SortRef::Builtin(BuiltinSort::KSequence) {
            return Err(format!(
                "the log's cell declares no item sort, so only a parameter of sort K admits its items, and `{parameter}` of `{decl}` is of sort {}",
                ValueIndex::sort_name(parameter_sort)
            ));
        }
    } else {
        match observer.values.is_subsort(&item.sort, parameter_sort) {
            Some(true) => {}
            Some(false) => {
                return Err(format!(
                    "the parameter `{parameter}` of `{decl}` is of sort {}, which does not admit the log's items, of sort {}",
                    ValueIndex::sort_name(parameter_sort),
                    ValueIndex::sort_name(&item.sort)
                ));
            }
            None => {
                return Err(format!(
                    "the observer does not declare the sort {} of the log's items",
                    ValueIndex::sort_name(&item.sort)
                ));
            }
        }
    }
    match &info.result {
        Some(result) if result.sort == SortRef::Builtin(BuiltinSort::List) => Ok(ElementFunction {
            element: result.element(0),
            parameter: parameter.clone(),
            decl,
        }),
        _ => Err(format!(
            "`{decl}` does not return a List; an element function maps an item to a List of elements"
        )),
    }
}

/// A SHA-256 digest of an element's canonical encoding, or a prefix of one
/// ([module documentation](self), "Digests").
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ElementDigest {
    bytes: [u8; 32],
    len: u8,
}

impl ElementDigest {
    /// The digest of `bytes`.
    #[must_use]
    pub fn of(bytes: &[u8]) -> Self {
        Self {
            bytes: Sha256::digest(bytes).into(),
            len: 32,
        }
    }

    /// The digest `bytes` writes, a whole digest or a prefix of one of 1 to 32 bytes.
    #[must_use]
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let len = u8::try_from(bytes.len())
            .ok()
            .filter(|len| (1..=32).contains(len))?;
        let mut whole = [0; 32];
        whole[..bytes.len()].copy_from_slice(bytes);
        Some(Self { bytes: whole, len })
    }

    /// The digest's bytes.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }

    /// The digest's first `len` bytes (at most its own length).
    #[must_use]
    pub fn truncated(self, len: u8) -> Self {
        let len = len.clamp(1, self.len);
        let mut bytes = [0; 32];
        bytes[..usize::from(len)].copy_from_slice(&self.bytes[..usize::from(len)]);
        Self { bytes, len }
    }

    /// Whether the two digests agree on the bytes both have: a disagreement shows two distinct
    /// elements; an agreement shows two equal elements up to a collision of the shorter prefix.
    #[must_use]
    pub fn agrees(&self, other: &Self) -> bool {
        let len = usize::from(self.len.min(other.len));
        self.bytes[..len] == other.bytes[..len]
    }
}

/// How a channel ends ([module documentation](self), "How a channel ends").
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Closure {
    /// The path ended at a determined end.
    End,
    /// The path's last step is undefined.
    Undefined,
}

/// Where a channel stopped being known: the elements before `index` are facts of the path, and
/// nothing is known from there on.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Open {
    /// The index of the first element not known.
    pub index: u64,
    /// Why.
    pub reason: String,
    /// Whether it opened where another run may know more: at an undecided element (an
    /// evaluation that spent its budget, or that the solver left undecided), or at an
    /// inconclusive halt of the run.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub undecided: bool,
    /// The point's depth and side it opened at, for cutting a record back.
    #[serde(skip)]
    at: Option<(u64, Option<StopAt>)>,
}

/// One element of a channel.
#[derive(Clone, Debug, PartialEq)]
pub struct Element {
    /// The steps from the run's start to the observed state (to the read state, for a log).
    pub depth: u64,
    /// The point's rule: as a report names it in a run's record, by `UNIQUE_ID` in the oracle's;
    /// `None` for an element a log's read at the path's end appended.
    pub rule: Option<String>,
    /// The point's side; `None` for an element of the read at the path's end.
    pub side: Option<StopAt>,
    /// The element's digest; `None` for an unknown element (under `count`).
    pub digest: Option<ElementDigest>,
    /// The element's value in the typed encoding, where the record keeps values: an object of a
    /// point's components by name, a log's element.
    pub value: Option<Json>,
    /// Why the element is unknown, where it is.
    pub undecided: Option<String>,
}

impl Element {
    /// The element's document at `index`, as [`Observations::document`] writes it: `{"index",
    /// "depth", "rule", "side", "value"}`, with `undecided` (its reason) in place of `value` for
    /// an unknown element.
    #[must_use]
    pub fn document(&self, index: u64) -> Json {
        let mut object = serde_json::Map::new();
        object.insert("index".to_owned(), Json::from(index));
        object.insert("depth".to_owned(), Json::from(self.depth));
        object.insert(
            "rule".to_owned(),
            self.rule.clone().map_or(Json::Null, Json::String),
        );
        object.insert(
            "side".to_owned(),
            self.side.map_or(Json::Null, |side| {
                serde_json::to_value(side).unwrap_or(Json::Null)
            }),
        );
        match &self.undecided {
            Some(reason) => {
                object.insert("undecided".to_owned(), Json::String(reason.clone()));
            }
            None => {
                object.insert("value".to_owned(), self.value.clone().unwrap_or(Json::Null));
            }
        }
        Json::Object(object)
    }
}

/// One channel of a record.
#[derive(Clone, Debug, PartialEq)]
pub struct Channel {
    /// The channel's name.
    pub name: String,
    /// The channel's kind.
    pub kind: ChannelKind,
    /// The elements, in path order: element `i` at position `i`.
    pub elements: Vec<Element>,
    /// How the run's end closed it, where it did.
    pub closed: Option<Closure>,
    /// Where it stopped being known, where it did.
    pub open: Option<Open>,
}

impl Channel {
    fn stopped(&self) -> bool {
        self.open.is_some() || self.closed.is_some()
    }

    fn open_at(&mut self, reason: String, undecided: bool, at: Option<(u64, Option<StopAt>)>) {
        if self.stopped() {
            return;
        }
        self.open = Some(Open {
            index: self.elements.len() as u64,
            reason,
            undecided,
            at,
        });
    }

    /// Append `element` under `stutter` (`None` for a log, which drops nothing); whether it
    /// was kept.
    fn emit(&mut self, stutter: Option<Stutter>, element: Element) -> bool {
        if self.stopped() {
            return false;
        }
        if stutter == Some(Stutter::Collapse)
            && let (Some(last), Some(digest)) = (
                self.elements.last().and_then(|last| last.digest),
                element.digest,
            )
            && last.agrees(&digest)
        {
            return false;
        }
        self.elements.push(element);
        true
    }
}

/// A run's observations: each channel's elements and how it ended
/// ([module documentation](self)).
///
/// A run report serializes a summary of it (each channel's name, kind, number of elements,
/// closure and open point); [`Self::document`] writes every element.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Observations {
    /// The channels, in declaration order: the classes, then the logs.
    pub channels: Vec<Channel>,
    /// How many times the record converted a read cell or a log's items from the backend's term
    /// to KORE: a cell the backend did not rewrite since its last conversion is not converted
    /// again ([module documentation](self), "Digests").
    pub conversions: u64,
}

impl Observations {
    /// Whether some element is unknown or some channel opened at an undecided element: the
    /// record does not answer what the observation is, since another run may decide it.
    #[must_use]
    pub fn undecided(&self) -> bool {
        self.channels.iter().any(|channel| {
            channel.open.as_ref().is_some_and(|open| open.undecided)
                || channel
                    .elements
                    .iter()
                    .any(|element| element.undecided.is_some())
        })
    }

    /// The `krs-observations/1` document of the record ([`OBSERVATIONS_FORMAT`]): `{"schema",
    /// "channels": [{"name", "kind", "elements": [{"index", "depth", "rule", "side", "value"}],
    /// "closed", "open"}]}`. `rule` and `side` are `null` for an element a log's read at the
    /// path's end appended; an unknown element has `undecided` (its reason) in place of
    /// `value`; `closed` is `"end"`, `"undefined"` or `null`, and `open` is `{"index", "reason"}`
    /// (with `"undecided": true` where an undecided element opened it) or `null`.
    #[must_use]
    pub fn document(&self) -> Json {
        let channels = self
            .channels
            .iter()
            .map(|channel| {
                let elements = channel
                    .elements
                    .iter()
                    .enumerate()
                    .map(|(index, element)| element.document(index as u64))
                    .collect::<Vec<_>>();
                serde_json::json!({
                    "name": channel.name,
                    "kind": channel.kind,
                    "elements": elements,
                    "closed": channel.closed,
                    "open": channel.open,
                })
            })
            .collect::<Vec<_>>();
        serde_json::json!({ "schema": OBSERVATIONS_FORMAT, "channels": channels })
    }

    /// The record a `krs-observations/1` document states ([`Self::document`]), as a run's
    /// record or another producer writes it: each channel's elements by their values (or as
    /// unknown, by their reason), with no digests, and how each channel ends.
    ///
    /// The document is read exactly: it holds `schema` and `channels` alone; each channel holds
    /// `name` (distinct), `kind` (`point` or `log`), `elements`, `closed` and `open`, exactly one
    /// of the last two not null; each element holds `index` (its position), `depth`, `rule` and
    /// `side` (each a string or null, `side` `before` or `after`), and either `value` or
    /// `undecided`; an `open` holds `index` (the number of elements), `reason` and optionally
    /// `undecided`.
    ///
    /// # Errors
    ///
    /// Returns the first part that is not of that shape, named by its position
    /// (`channels[1].elements[3]`).
    pub fn from_document(document: &Json) -> Result<Self, String> {
        let top = document_object(document, "the document", &["schema", "channels"])?;
        match top.get("schema") {
            Some(Json::String(schema)) if schema == OBSERVATIONS_FORMAT => {}
            _ => {
                return Err(format!(
                    "at `schema`: an observation document's `schema` is `{OBSERVATIONS_FORMAT}`"
                ));
            }
        }
        let Json::Array(listed) = document_key(&top, "the document", "channels")? else {
            return Err("at `channels`: an array of channels".to_owned());
        };
        let mut channels = Vec::<Channel>::new();
        for (position, listed) in listed.iter().enumerate() {
            let at = format!("channels[{position}]");
            let channel = channel_from_document(listed, &at)?;
            if channels.iter().any(|other| other.name == channel.name) {
                return Err(format!("at `{at}`: a second channel `{}`", channel.name));
            }
            channels.push(channel);
        }
        Ok(Self {
            channels,
            conversions: 0,
        })
    }

    /// Rename each element's rule by `name` (a `UNIQUE_ID` to a report's name).
    pub(crate) fn rename_rules(&mut self, name: impl Fn(&str) -> String) {
        for channel in &mut self.channels {
            for element in &mut channel.elements {
                if let Some(rule) = &mut element.rule {
                    *rule = name(rule);
                }
            }
        }
    }
}

/// The object `value` is, at `at` of a document, holding only `keys`.
fn document_object(
    value: &Json,
    at: &str,
    keys: &[&str],
) -> Result<serde_json::Map<String, Json>, String> {
    let Json::Object(object) = value else {
        return Err(format!("at `{at}`: not an object"));
    };
    if let Some(key) = object.keys().find(|key| !keys.contains(&key.as_str())) {
        return Err(format!(
            "at `{at}`: unknown key `{key}`; it has the keys {}",
            keys.iter()
                .map(|key| format!("`{key}`"))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    Ok(object.clone())
}

/// The member `key` of `object`, at `at` of a document, which it must hold.
fn document_key(
    object: &serde_json::Map<String, Json>,
    at: &str,
    key: &str,
) -> Result<Json, String> {
    object
        .get(key)
        .cloned()
        .ok_or_else(|| format!("at `{at}`: no `{key}`"))
}

/// The channel `listed` states at `at` of an observation document
/// ([`Observations::from_document`]).
fn channel_from_document(listed: &Json, at: &str) -> Result<Channel, String> {
    let channel = document_object(listed, at, &["name", "kind", "elements", "closed", "open"])?;
    let name = match document_key(&channel, at, "name")? {
        Json::String(name) if !name.is_empty() => name,
        _ => return Err(format!("at `{at}`: `name` is the channel's name")),
    };
    let kind = match document_key(&channel, at, "kind")?.as_str() {
        Some("point") => ChannelKind::Point,
        Some("log") => ChannelKind::Log,
        _ => return Err(format!("at `{at}`: `kind` is `point` or `log`")),
    };
    let Json::Array(listed_elements) = document_key(&channel, at, "elements")? else {
        return Err(format!("at `{at}`: `elements` is an array of elements"));
    };
    let elements = listed_elements
        .iter()
        .enumerate()
        .map(|(index, listed)| {
            element_from_document(listed, &format!("{at}.elements[{index}]"), index)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let closed = match document_key(&channel, at, "closed")? {
        Json::Null => None,
        Json::String(closure) if closure == "end" => Some(Closure::End),
        Json::String(closure) if closure == "undefined" => Some(Closure::Undefined),
        _ => return Err(format!("at `{at}`: `closed` is `end`, `undefined` or null")),
    };
    let open = match document_key(&channel, at, "open")? {
        Json::Null => None,
        listed => {
            let at = format!("{at}.open");
            let open = document_object(&listed, &at, &["index", "reason", "undecided"])?;
            let count = elements.len();
            if document_key(&open, &at, "index")?.as_u64() != Some(count as u64) {
                return Err(format!(
                    "at `{at}`: `index` is where the channel opened, after its {count} element{}",
                    if count == 1 { "" } else { "s" }
                ));
            }
            let Json::String(reason) = document_key(&open, &at, "reason")? else {
                return Err(format!("at `{at}`: `reason` is why the channel opened"));
            };
            let undecided = match open.get("undecided") {
                None => false,
                Some(Json::Bool(undecided)) => *undecided,
                Some(_) => return Err(format!("at `{at}`: `undecided` is true or false")),
            };
            Some(Open {
                index: count as u64,
                reason,
                undecided,
                at: None,
            })
        }
    };
    if closed.is_some() == open.is_some() {
        return Err(format!(
            "at `{at}`: a channel is closed (`closed`) or open (`open`) where its elements end, one of the two"
        ));
    }
    Ok(Channel {
        name,
        kind,
        elements,
        closed,
        open,
    })
}

/// The element `listed` states at `at` of an observation document, the `index`th of its channel.
fn element_from_document(listed: &Json, at: &str, index: usize) -> Result<Element, String> {
    let element = document_object(
        listed,
        at,
        &["index", "depth", "rule", "side", "value", "undecided"],
    )?;
    if document_key(&element, at, "index")?.as_u64() != Some(index as u64) {
        return Err(format!(
            "at `{at}`: `index` is the element's position, {index}"
        ));
    }
    let depth = document_key(&element, at, "depth")?
        .as_u64()
        .ok_or_else(|| format!("at `{at}`: `depth` is a number of steps"))?;
    let rule = match document_key(&element, at, "rule")? {
        Json::Null => None,
        Json::String(rule) => Some(rule),
        _ => return Err(format!("at `{at}`: `rule` is a rule's name or null")),
    };
    let side = match document_key(&element, at, "side")? {
        Json::Null => None,
        Json::String(side) if side == "before" => Some(StopAt::Before),
        Json::String(side) if side == "after" => Some(StopAt::After),
        _ => return Err(format!("at `{at}`: `side` is `before`, `after` or null")),
    };
    let (value, undecided) = match (element.get("value"), element.get("undecided")) {
        (Some(value), None) => (Some(value.clone()), None),
        (None, Some(Json::String(reason))) => (None, Some(reason.clone())),
        (None, Some(_)) => {
            return Err(format!(
                "at `{at}`: `undecided` is why the element is unknown"
            ));
        }
        _ => {
            return Err(format!(
                "at `{at}`: an element holds its `value`, or why it is unknown (`undecided`), not both"
            ));
        }
    };
    Ok(Element {
        depth,
        rule,
        side,
        digest: None,
        value,
        undecided,
    })
}

/// The run report's summary of a record.
impl Serialize for Observations {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        struct Summary<'a>(&'a Channel);
        impl Serialize for Summary<'_> {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                let mut map = serializer.serialize_map(Some(5))?;
                map.serialize_entry("name", &self.0.name)?;
                map.serialize_entry("kind", &self.0.kind)?;
                map.serialize_entry("elements", &self.0.elements.len())?;
                map.serialize_entry("closed", &self.0.closed)?;
                map.serialize_entry("open", &self.0.open)?;
                map.end()
            }
        }
        let mut object = serializer.serialize_struct("Observations", 1)?;
        object.serialize_field(
            "channels",
            &self.channels.iter().map(Summary).collect::<Vec<_>>(),
        )?;
        object.end()
    }
}

/// What a channel holds at an index, as [`compare_records`] reads it.
#[derive(Clone, Debug, PartialEq)]
pub enum Observed {
    /// An element.
    Element(Element),
    /// The channel was closed there by the path's end.
    End,
    /// The channel was closed there by an undefined last step.
    Undefined,
}

impl Observed {
    /// What the channel holds at `index`, as a document writes it: the element's document
    /// ([`Element::document`]), or `"end"` or `"undefined"` for a closure.
    #[must_use]
    pub fn document(&self, index: u64) -> Json {
        match self {
            Self::Element(element) => element.document(index),
            Self::End => Json::String("end".to_owned()),
            Self::Undefined => Json::String("undefined".to_owned()),
        }
    }
}

/// The first decided difference of two records ([`first_difference`]).
#[derive(Clone, Debug, PartialEq)]
pub struct ObservationDifference {
    /// The channel's name.
    pub channel: String,
    /// The index both sides hold something decided at, and differ.
    pub index: u64,
    /// The left record's element or closure there.
    pub left: Observed,
    /// The right record's.
    pub right: Observed,
    /// Where inside the two values they first differ (`regs.a`, `[2]`), where both carry values
    /// that differ below their top.
    pub path: Option<String>,
}

/// A side of a comparison of two records ([`compare_records`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum RecordSide {
    /// The first record.
    Left,
    /// The second record.
    Right,
}

impl RecordSide {
    /// The side's name, `left` or `right`.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Left => "left",
            Self::Right => "right",
        }
    }
}

/// What a side holds where the comparison of a channel stopped ([`ChannelAgreement`]).
#[derive(Clone, Debug, PartialEq)]
pub enum Reach {
    /// The channel is closed there, as it is on the other side.
    Closed(Closure),
    /// The channel is open there: nothing from there on is known on this side.
    Open(Open),
    /// The side knows the index; the other side's open point stopped the comparison.
    Known,
}

/// An index at which two records' elements were not compared ([`ChannelAgreement::uncompared`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Uncompared {
    /// The index.
    pub index: u64,
    /// The side whose element is unknown there; `None` where both are known and have neither a
    /// value nor a digest in common.
    pub side: Option<RecordSide>,
    /// Why.
    pub reason: String,
}

/// A channel on which two records do not differ ([`compare_records`]): how far they were
/// compared, and what stopped the comparison.
#[derive(Clone, Debug, PartialEq)]
pub struct ChannelAgreement {
    /// The channel's name.
    pub channel: String,
    /// The index the comparison stopped at. Each earlier index was compared and the two agree
    /// there, except at an index [`Self::uncompared`] names.
    pub through: u64,
    /// What the left record holds at `through`.
    pub left: Reach,
    /// What the right record holds at `through`.
    pub right: Reach,
    /// The first earlier index at which the two elements were not compared, where there is one.
    pub uncompared: Option<Uncompared>,
}

impl ChannelAgreement {
    /// Where the agreement answers nothing yet, because another record of an open side may still
    /// differ: the side, the index and why. That is so at an index [`Self::uncompared`] names,
    /// and where a side is open at `through` as undecided ([`Open::undecided`]) while the other
    /// side is not open there for another reason. A side open at a bound or a split ends the
    /// comparison at `through` whatever the other side may still learn, so the agreement is
    /// then bounded, and decided up to `through`.
    #[must_use]
    pub fn undecided(&self) -> Option<(Option<RecordSide>, u64, &str)> {
        fn undecided(reach: &Reach) -> Option<&str> {
            match reach {
                Reach::Open(open) if open.undecided => Some(open.reason.as_str()),
                _ => None,
            }
        }
        if let Some(uncompared) = &self.uncompared {
            return Some((uncompared.side, uncompared.index, &uncompared.reason));
        }
        let bounded = |reach: &Reach| matches!(reach, Reach::Open(open) if !open.undecided);
        if let Some(reason) = undecided(&self.left)
            && !bounded(&self.right)
        {
            return Some((Some(RecordSide::Left), self.through, reason));
        }
        if let Some(reason) = undecided(&self.right)
            && !bounded(&self.left)
        {
            return Some((Some(RecordSide::Right), self.through, reason));
        }
        None
    }

    /// Whether some side is open at `through`, so the agreement holds up to a horizon rather
    /// than to both sides' closure.
    #[must_use]
    pub const fn bounded(&self) -> bool {
        matches!(self.left, Reach::Open(_)) || matches!(self.right, Reach::Open(_))
    }
}

/// How two records of the same declaration compare ([`compare_records`]).
#[derive(Clone, Debug, PartialEq)]
pub enum RecordComparison {
    /// They differ, first here ([`first_difference`]).
    Differs(Box<ObservationDifference>),
    /// They do not differ: each channel both have, compared up to where it stopped, in the left
    /// record's order.
    Agree(Vec<ChannelAgreement>),
}

/// Compare two records of the same declaration: the first decided difference, or else how far
/// each channel agrees.
///
/// A difference is a channel and an index at which both sides hold a decided element or a
/// closure, and the two differ (an `end` and an `undefined` closure differ from each other and
/// from every element). Nothing past a side's open point, nor at an unknown element, is read, so
/// an open record differs only where it is known.
///
/// Two elements are compared by their values where both carry one, and otherwise by their
/// digests on the bytes both have ([`ElementDigest::agrees`]); two elements with neither in
/// common are not compared. Channels are matched by name; a channel only one side has is not
/// compared.
///
/// Where several channels differ, the difference reported is the one the right side reached
/// first: the least depth of its element there (a closure after every element), then the
/// earlier channel in the left side's order.
#[must_use]
pub fn compare_records(left: &Observations, right: &Observations) -> RecordComparison {
    let mut best: Option<(u64, Box<ObservationDifference>)> = None;
    let mut agreements = Vec::new();
    for channel in &left.channels {
        let Some(other) = right
            .channels
            .iter()
            .find(|other| other.name == channel.name)
        else {
            continue;
        };
        let difference = match channel_comparison(channel, other) {
            Ok(agreement) => {
                agreements.push(agreement);
                continue;
            }
            Err(difference) => difference,
        };
        let reached = match &difference.right {
            Observed::Element(element) => element.depth,
            Observed::End | Observed::Undefined => u64::MAX,
        };
        if best.as_ref().is_none_or(|(depth, _)| reached < *depth) {
            best = Some((reached, difference));
        }
    }
    match best {
        Some((_, difference)) => RecordComparison::Differs(difference),
        None => RecordComparison::Agree(agreements),
    }
}

/// The first decided difference between two records of the same declaration
/// ([`compare_records`]).
#[must_use]
pub fn first_difference(
    left: &Observations,
    right: &Observations,
) -> Option<ObservationDifference> {
    match compare_records(left, right) {
        RecordComparison::Differs(difference) => Some(*difference),
        RecordComparison::Agree(_) => None,
    }
}

/// What `channel` holds at `index`: `None` at or past its open point, or past its elements where
/// no closure follows them.
fn held(channel: &Channel, index: usize) -> Option<Observed> {
    if let Some(open) = &channel.open
        && index as u64 >= open.index
    {
        return None;
    }
    match channel.elements.get(index) {
        Some(element) => Some(Observed::Element(element.clone())),
        None if index == channel.elements.len() => match channel.closed {
            Some(Closure::End) => Some(Observed::End),
            Some(Closure::Undefined) => Some(Observed::Undefined),
            None => None,
        },
        None => None,
    }
}

/// What `channel` holds where the comparison stopped at `index`, `held` there.
fn reach(channel: &Channel, index: usize, held: Option<&Observed>) -> Reach {
    if held.is_some() {
        return Reach::Known;
    }
    channel.open.clone().map_or_else(
        || {
            Reach::Open(Open {
                index: index as u64,
                reason: "the record states nothing past its last element".to_owned(),
                undecided: false,
                at: None,
            })
        },
        Reach::Open,
    )
}

fn channel_comparison(
    left: &Channel,
    right: &Channel,
) -> Result<ChannelAgreement, Box<ObservationDifference>> {
    let mut uncompared = None;
    let mut index = 0;
    loop {
        let (left_at, right_at) = (held(left, index), held(right, index));
        let (Some(left_held), Some(right_held)) = (&left_at, &right_at) else {
            return Ok(ChannelAgreement {
                channel: left.name.clone(),
                through: index as u64,
                left: reach(left, index, left_at.as_ref()),
                right: reach(right, index, right_at.as_ref()),
                uncompared,
            });
        };
        let differs = match (left_held, right_held) {
            (Observed::Element(left_element), Observed::Element(right_element)) => {
                match elements_compared(left_element, right_element) {
                    Pair::Differ(path) => Some(path),
                    Pair::Agree => None,
                    Pair::Uncompared(side, reason) => {
                        uncompared.get_or_insert(Uncompared {
                            index: index as u64,
                            side,
                            reason,
                        });
                        None
                    }
                }
            }
            (Observed::End, Observed::End) | (Observed::Undefined, Observed::Undefined) => {
                let closure = if matches!(left_held, Observed::End) {
                    Closure::End
                } else {
                    Closure::Undefined
                };
                return Ok(ChannelAgreement {
                    channel: left.name.clone(),
                    through: index as u64,
                    left: Reach::Closed(closure),
                    right: Reach::Closed(closure),
                    uncompared,
                });
            }
            _ => Some(None),
        };
        if let Some(path) = differs {
            return Err(Box::new(ObservationDifference {
                channel: left.name.clone(),
                index: index as u64,
                left: left_held.clone(),
                right: right_held.clone(),
                path,
            }));
        }
        index += 1;
    }
}

/// How two elements at one index compare.
enum Pair {
    /// They differ, with the path inside their values where both carry values that differ below
    /// their top.
    Differ(Option<String>),
    /// They agree.
    Agree,
    /// They are not compared: the side whose element is unknown (`None` where both are known
    /// and have nothing in common), and why.
    Uncompared(Option<RecordSide>, String),
}

fn elements_compared(left: &Element, right: &Element) -> Pair {
    for (side, element) in [(RecordSide::Left, left), (RecordSide::Right, right)] {
        if let Some(reason) = &element.undecided {
            return Pair::Uncompared(Some(side), reason.clone());
        }
    }
    if let (Some(left), Some(right)) = (&left.value, &right.value) {
        return if left == right {
            Pair::Agree
        } else {
            Pair::Differ(json_path(left, right, String::new()))
        };
    }
    match (left.digest, right.digest) {
        (Some(left), Some(right)) if left.agrees(&right) => Pair::Agree,
        (Some(_), Some(_)) => Pair::Differ(None),
        _ => Pair::Uncompared(
            None,
            "the two elements have neither a value nor a digest in common".to_owned(),
        ),
    }
}

/// The first path inside two unequal element values, as documents of the typed encoding, at
/// which they differ (`pc`, `regs.a`, `[2]`), as a comparison of two records names it
/// ([`ObservationDifference::path`]); `None` where they differ at their top.
#[must_use]
pub fn value_path(left: &Json, right: &Json) -> Option<String> {
    json_path(left, right, String::new())
}

/// The first path at which two unequal JSON values differ, `None` at their top.
fn json_path(left: &Json, right: &Json, prefix: String) -> Option<String> {
    match (left, right) {
        (Json::Object(left), Json::Object(right)) => {
            let keys = left.keys().chain(right.keys()).collect::<BTreeSet<_>>();
            for key in keys {
                let path = if prefix.is_empty() {
                    key.clone()
                } else {
                    format!("{prefix}.{key}")
                };
                match (left.get(key), right.get(key)) {
                    (Some(left), Some(right)) if left == right => {}
                    (Some(left), Some(right)) => {
                        return json_path(left, right, path.clone()).or(Some(path));
                    }
                    _ => return Some(path),
                }
            }
            None
        }
        (Json::Array(left), Json::Array(right)) => {
            for index in 0..left.len().max(right.len()) {
                let path = format!("{prefix}[{index}]");
                match (left.get(index), right.get(index)) {
                    (Some(left), Some(right)) if left == right => {}
                    (Some(left), Some(right)) => {
                        return json_path(left, right, path.clone()).or(Some(path));
                    }
                    _ => return Some(path),
                }
            }
            None
        }
        _ => (!prefix.is_empty()).then_some(prefix),
    }
}

/// A state the oracle reads: a probe's observed state, or a state a run reached, as KORE.
pub(crate) trait Reading: ObservedState {
    /// A handle on the cell at `path`, where the state has term nodes to hold.
    fn handle(&self, path: &[&str]) -> Option<CellHandle>;
    /// The items of the `List` the cell at `path` holds from position `from` on, or `None`
    /// where it holds no list of known items.
    fn list_items(&self, path: &[&str], from: usize) -> Option<Vec<Pattern>>;
    /// The number of those items.
    fn list_len(&self, path: &[&str]) -> Option<usize>;
}

impl Reading for ProbeState<'_> {
    fn handle(&self, path: &[&str]) -> Option<CellHandle> {
        self.cell_handle(path)
    }

    fn list_items(&self, path: &[&str], from: usize) -> Option<Vec<Pattern>> {
        ProbeState::list_items(self, path, from)
    }

    fn list_len(&self, path: &[&str]) -> Option<usize> {
        ProbeState::list_len(self, path)
    }
}

/// A state a run reached, as KORE: its configuration, beside its constraints.
pub(crate) struct KoreState<'a> {
    pub(crate) pattern: &'a Pattern,
    pub(crate) subject: &'a ValueIndex,
}

impl KoreState<'_> {
    fn cell_pattern(&self, path: &[&str]) -> Option<&Pattern> {
        fn head(pattern: &Pattern) -> Option<&str> {
            match pattern {
                Pattern::Application { symbol, .. }
                | Pattern::AssociativeApplication { symbol, .. } => Some(&symbol.name),
                _ => None,
            }
        }
        let (first, below) = path.split_first()?;
        let mut pending = vec![self.pattern];
        let mut current = None;
        while let Some(pattern) = pending.pop() {
            match pattern {
                Pattern::And { arguments, .. } => pending.extend(arguments.iter()),
                _ if head(pattern) == Some(first) => current = Some(pattern),
                _ => {}
            }
        }
        let mut current = current?;
        for symbol in below {
            let (Pattern::Application { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. }) = current
            else {
                return None;
            };
            current = arguments
                .iter()
                .find(|argument| head(argument) == Some(symbol))?;
        }
        Some(current)
    }
}

impl ObservedState for KoreState<'_> {
    fn cell(&self, path: &[&str]) -> Option<Pattern> {
        self.cell_pattern(path).cloned()
    }
}

impl Reading for KoreState<'_> {
    fn handle(&self, _: &[&str]) -> Option<CellHandle> {
        None
    }

    fn list_items(&self, path: &[&str], from: usize) -> Option<Vec<Pattern>> {
        let items = self
            .subject
            .list_items(leaf_content(self.cell_pattern(path)?)?)?;
        Some(items.into_iter().skip(from).cloned().collect())
    }

    fn list_len(&self, path: &[&str]) -> Option<usize> {
        Some(
            self.subject
                .list_items(leaf_content(self.cell_pattern(path)?)?)?
                .len(),
        )
    }
}

/// An element whose value has no observation, as the oracle recorded it: the run's error names
/// the channel, the point and the reason ([`ExecError::Observation`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObservationRefusal {
    /// The channel.
    pub channel: String,
    /// The point's rule, by `UNIQUE_ID`; `None` at the path's end.
    pub rule: Option<String>,
    /// The point's side; `None` at the path's end.
    pub side: Option<StopAt>,
    /// The steps from the run's start to the observed state.
    pub depth: u64,
    /// Why, naming the cell or the evaluation.
    pub reason: String,
}

/// What a recording keeps ([`ObservationOracle::record`]).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RecordOptions {
    /// Keep each element's value in the typed encoding beside its digest.
    pub values: bool,
    /// Refuse an element with no value ([`ObservationOracle::refusal`]) rather than keep it as
    /// unknown ([module documentation](self), "Undefined and undecided elements").
    pub refuse_no_value: bool,
    /// The budget of polls of each evaluation in the observer; `None` for no bound.
    pub budget: Option<u64>,
}

enum Mode<'o> {
    Record { values: bool, refuse_no_value: bool },
    Compare(&'o Observations),
}

/// A piece of an element: a component's or a log element's digest, and its value where kept.
#[derive(Clone, Debug)]
struct Piece {
    digest: ElementDigest,
    value: Option<Json>,
}

/// The digest of a class's content made of `pieces`: their number, then each piece's digest, in
/// the class's order.
fn content_digest(pieces: &[(&str, Piece)]) -> ElementDigest {
    let mut bytes = Vec::with_capacity(8 + 32 * pieces.len());
    bytes.extend_from_slice(&(pieces.len() as u64).to_le_bytes());
    for (_, piece) in pieces {
        bytes.extend_from_slice(piece.digest.as_bytes());
    }
    ElementDigest::of(&bytes)
}

/// The value of a class's content made of `pieces`: an object of each component's value by its
/// name.
fn content_value(pieces: &[(&str, Piece)]) -> Json {
    Json::Object(
        pieces
            .iter()
            .map(|(name, piece)| {
                (
                    (*name).to_owned(),
                    piece.value.clone().unwrap_or(Json::Null),
                )
            })
            .collect(),
    )
}

/// The key of the value an evaluating oracle keeps for a part that has no document in the
/// typed encoding (a parametric constructor's application, for one, which no form of the
/// encoding writes): `{"$undocumented": {"kore": TEXT, "reason": WHY}}`, the part's canonical
/// KORE, the text its digest is taken of, and why it has no document. The typed encoding writes
/// no `$undocumented` form, so no document reads as one. Its element's digest is the one a
/// documented part would have, so a comparison is decided as for any element; only what a reader
/// is shown differs.
pub const UNDOCUMENTED: &str = "$undocumented";

/// One element an evaluating oracle gives a front end that keeps its own channels
/// ([`ObservationOracle::evaluator`]): its digest, and its value in the typed encoding where the
/// oracle keeps values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Evaluated {
    /// The element's digest, as a recording keeps it.
    pub digest: ElementDigest,
    /// The element's value in the typed encoding, where the oracle keeps values: an object of a
    /// class's components by name, or a log's element; a part with no document is shown by its
    /// KORE text ([`UNDOCUMENTED`]).
    pub value: Option<Json>,
}

/// A log's reading state.
#[derive(Default)]
struct LogState {
    /// The digest of each item read so far, with the point it was read at.
    items: Vec<(ElementDigest, u64, Option<StopAt>)>,
    /// The cell at the last read, where the state had a node to hold.
    handle: Option<CellHandle>,
    /// The pieces of each item read, by the item's digest.
    memo: HashMap<ElementDigest, Vec<Piece>>,
}

/// The point being observed.
#[derive(Clone, Copy)]
struct At<'a> {
    rule: Option<&'a str>,
    side: Option<StopAt>,
    depth: u64,
}

impl At<'_> {
    /// Where a channel opened here opened, so cutting the record back past it reopens nothing.
    const fn place(&self) -> (u64, Option<StopAt>) {
        (self.depth, self.side)
    }
}

/// Why an element is not known: no value, or undecided.
struct Unknown {
    reason: String,
    undecided: bool,
}

impl From<ObservationError> for Unknown {
    fn from(error: ObservationError) -> Self {
        Self {
            undecided: error.is_undecided(),
            reason: error.to_string(),
        }
    }
}

/// The backend's probe of a run with observations ([module documentation](self), "Recording
/// and comparing"): it records each channel's elements, and, comparing, checks them against a
/// baseline as they are emitted. A caller that runs another backend under the observations
/// (kink's runs of a definition and its mutants) passes it as the request's probe with
/// [`ResolvedObservations::probe_rules`], and reads the record with [`Self::finish`].
pub struct ObservationOracle<'o> {
    resolved: &'o ResolvedObservations,
    observer: Option<&'o mut Semantics>,
    budget: Option<u64>,
    mode: Mode<'o>,
    offset: u64,
    channels: Vec<Channel>,
    logs: Vec<LogState>,
    cells: HashMap<Vec<String>, (CellHandle, Piece)>,
    functions: HashMap<(usize, usize), (Vec<CellHandle>, Piece)>,
    conversions: u64,
    refusal: Option<ObservationRefusal>,
    difference: Option<String>,
    read_end: bool,
    /// Whether a kept value with no document in the typed encoding is shown by its KORE text
    /// ([`UNDOCUMENTED`]) rather than make its element have no value: an evaluating oracle's,
    /// whose front end decides on digests and shows the values only to a reader.
    shows_undocumented: bool,
}

impl<'o> ObservationOracle<'o> {
    /// A recording oracle of `resolved`, its functions evaluated in `observer`, the definition
    /// they were resolved in, which a declaration with a function needs.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Observe`] when the declaration has a function and no observer is
    /// given, or the observer is not the definition the declaration was resolved in.
    pub fn record(
        resolved: &'o ResolvedObservations,
        observer: Option<&'o mut Semantics>,
        options: RecordOptions,
    ) -> Result<Self, ExecError> {
        Self::new(
            resolved,
            observer,
            options.budget,
            Mode::Record {
                values: options.values,
                refuse_no_value: options.refuse_no_value,
            },
        )
    }

    /// A comparing oracle of `resolved` against `baseline`, a record of the same declaration
    /// (of the baseline definition, resolved on its own): it ends the request at the first
    /// element that differs from the baseline's (`probe-difference`), and the path once every
    /// channel has opened or passed the baseline's horizon while the baseline did not end
    /// (`probe-done`). An element with no value is kept as unknown.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::record`] does, and with [`ExecError::Observe`] when `baseline`'s
    /// channels are not the declaration's, by name and kind in order.
    pub fn compare(
        resolved: &'o ResolvedObservations,
        observer: Option<&'o mut Semantics>,
        baseline: &'o Observations,
        budget: Option<u64>,
    ) -> Result<Self, ExecError> {
        let theirs = baseline
            .channels
            .iter()
            .map(|channel| (channel.name.as_str(), channel.kind));
        if !theirs.eq(resolved.channels()) {
            return Err(ExecError::Observe(
                "the baseline's record is not of the declaration compared: its channels differ"
                    .to_owned(),
            ));
        }
        Self::new(resolved, observer, budget, Mode::Compare(baseline))
    }

    fn new(
        resolved: &'o ResolvedObservations,
        observer: Option<&'o mut Semantics>,
        budget: Option<u64>,
        mode: Mode<'o>,
    ) -> Result<Self, ExecError> {
        match &observer {
            None if resolved.functions => {
                return Err(ExecError::Observe(
                    "the observations are evaluated in an observer definition, and none was given"
                        .to_owned(),
                ));
            }
            Some(observer) if !Arc::ptr_eq(&resolved.observer, observer.values()) => {
                return Err(ExecError::Observe(
                    "the observations are evaluated in a definition other than the observer they were resolved in".to_owned(),
                ));
            }
            _ => {}
        }
        let channels = resolved
            .channels()
            .map(|(name, kind)| Channel {
                name: name.to_owned(),
                kind,
                elements: Vec::new(),
                closed: None,
                open: None,
            })
            .collect();
        Ok(Self {
            resolved,
            observer,
            budget,
            mode,
            offset: 0,
            channels,
            logs: resolved.logs.iter().map(|_| LogState::default()).collect(),
            cells: HashMap::new(),
            functions: HashMap::new(),
            conversions: 0,
            refusal: None,
            difference: None,
            read_end: false,
            shows_undocumented: false,
        })
    }

    /// The rules whose steps the oracle observes, the request's probe rules
    /// ([`ResolvedObservations::probe_rules`]).
    #[must_use]
    pub fn probe_rules(&self) -> ProbeRules {
        self.resolved.probe_rules()
    }

    /// The element with no value that a recording refused, once one did: the request ended
    /// there (`probe-difference`).
    #[must_use]
    pub const fn refusal(&self) -> Option<&ObservationRefusal> {
        self.refusal.as_ref()
    }

    /// The difference from the baseline a comparison found, once it did: the request ended
    /// there (`probe-difference`).
    #[must_use]
    pub fn difference(&self) -> Option<&str> {
        self.difference.as_deref()
    }

    /// An oracle of `resolved` that keeps no channel of its own and evaluates elements one at a
    /// time for a front end that runs the declaration under another engine and keeps the
    /// channels by its own rule (kink's runs of a definition and its mutants): whether a class's
    /// filter holds at a state ([`Self::holds`]), a class's content there ([`Self::content`]),
    /// and the elements one item of a log contributes ([`Self::item_elements`]), each as a
    /// recording of this oracle takes it, its digest and, under [`Self::keep_values`], its
    /// value. The functions are evaluated in `observer` as [`Self::record`] evaluates them,
    /// within `budget` polls each. A kept part with no document in the typed encoding is shown
    /// by its KORE text ([`UNDOCUMENTED`]), its element keeping its digest.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::record`] does.
    pub fn evaluator(
        resolved: &'o ResolvedObservations,
        observer: Option<&'o mut Semantics>,
        budget: Option<u64>,
    ) -> Result<Self, ExecError> {
        let mut oracle = Self::new(
            resolved,
            observer,
            budget,
            Mode::Record {
                values: false,
                refuse_no_value: false,
            },
        )?;
        oracle.shows_undocumented = true;
        Ok(oracle)
    }

    /// Whether the elements this evaluating oracle gives carry their values in the typed
    /// encoding ([`Evaluated::value`]); without, only their digests, which is what a comparison
    /// needs.
    pub fn keep_values(&mut self, values: bool) {
        if let Mode::Record {
            refuse_no_value, ..
        } = self.mode
        {
            self.mode = Mode::Record {
                values,
                refuse_no_value,
            };
        }
    }

    /// Whether the filter of the class `class` (by its position in the declaration) holds at
    /// `state`: `None` for a class with no filter, which every point of keeps; why it is not known
    /// otherwise (no value, or an evaluation stopped before its end).
    pub fn holds(&mut self, class: usize, state: &ProbeState<'_>) -> Option<Result<bool, String>> {
        let resolved = self.resolved;
        let filter = resolved.classes.get(class)?.filter.as_ref()?;
        Some(
            self.filter(filter, state)
                .map_err(|unknown| format!("its filter is not known here: {}", unknown.reason)),
        )
    }

    /// The content of the class `class` (by its position in the declaration) at `state`, the
    /// element a recording takes at a point of the class there.
    ///
    /// # Errors
    ///
    /// Why a component has no value there, naming it.
    ///
    /// # Panics
    ///
    /// When the declaration has no class `class`.
    pub fn content(&mut self, class: usize, state: &ProbeState<'_>) -> Result<Evaluated, String> {
        let pieces = self
            .pieces(class, state)
            .map_err(|unknown| unknown.reason)?;
        Ok(Evaluated {
            digest: content_digest(&pieces),
            value: self.keeps_values().then(|| content_value(&pieces)),
        })
    }

    /// The elements one item of the log `log` (by its position among the declaration's logs)
    /// contributes to its channel, `item` as the log's cell holds it: the item itself, or each
    /// element of its element function's value.
    ///
    /// # Errors
    ///
    /// Why the item, or its element function there, has no value.
    ///
    /// # Panics
    ///
    /// When the declaration has no log `log`.
    pub fn item_elements(&mut self, log: usize, item: &Pattern) -> Result<Vec<Evaluated>, String> {
        let resolved = self.resolved;
        let pieces = self
            .item_pieces(&resolved.logs[log], item)
            .map_err(|unknown| unknown.reason)?;
        let values = self.keeps_values();
        Ok(pieces
            .into_iter()
            .map(|piece| Evaluated {
                digest: piece.digest,
                value: piece.value.filter(|_| values),
            })
            .collect())
    }

    /// The digest of an item of a log's cell as a recording checks that the cell only grows by
    /// appending: of the item's canonical KORE under the declaration's subject, so two items have
    /// one digest exactly when they are one term.
    #[must_use]
    pub fn item_digest(&self, item: &Pattern) -> ElementDigest {
        let mut bytes = Vec::new();
        self.resolved.subject.canonical_kore(item, &mut bytes);
        ElementDigest::of(&bytes)
    }

    /// Count the depths of the request's points from `offset` steps: the steps the run took
    /// before the request's start.
    pub(crate) const fn set_offset(&mut self, offset: u64) {
        self.offset = offset;
    }

    /// The record, its channels not yet closed or open ended as `end` says: closed by the
    /// path's `end` or `undefined` last step, or open with `end`'s reason at the run's last
    /// element. A log's channel that was not read at the path's end is open there, since the
    /// items appended after its last read are not known.
    pub fn finish(&mut self, end: &ChannelEnd) -> Observations {
        let read_end = self.read_end;
        let mut channels = std::mem::take(&mut self.channels);
        for channel in &mut channels {
            if channel.stopped() {
                continue;
            }
            match end {
                ChannelEnd::End | ChannelEnd::Undefined
                    if channel.kind == ChannelKind::Log && !read_end =>
                {
                    channel.open_at(
                        "the log's cell was not read at the path's end".to_owned(),
                        false,
                        None,
                    );
                }
                ChannelEnd::End => channel.closed = Some(Closure::End),
                ChannelEnd::Undefined => channel.closed = Some(Closure::Undefined),
                ChannelEnd::Open(reason) => channel.open_at(reason.clone(), false, None),
                ChannelEnd::Undecided(reason) => channel.open_at(reason.clone(), true, None),
            }
        }
        Observations {
            channels,
            conversions: self.conversions,
        }
    }

    /// Observe a point of the path: `rule`'s step on `side`, the observed state `state` at
    /// `depth` steps from the run's start.
    fn point(
        &mut self,
        rule: &str,
        side: StopSide,
        depth: u64,
        state: &dyn Reading,
    ) -> ProbeDecision {
        if self.refusal.is_some() || self.difference.is_some() {
            return ProbeDecision::Continue;
        }
        let at = At {
            rule: Some(rule),
            side: Some(match side {
                StopSide::Before => StopAt::Before,
                StopSide::After => StopAt::After,
            }),
            depth,
        };
        let resolved = self.resolved;
        let mut logs = BTreeSet::new();
        for (index, class) in resolved.classes.iter().enumerate() {
            if !class.selects(rule, side) {
                continue;
            }
            if let Err(refusal) = self.event(index, at, state) {
                return self.refuse(refusal);
            }
            for (log, resolved_log) in resolved.logs.iter().enumerate() {
                if resolved_log.at.contains(&index) {
                    logs.insert(log);
                }
            }
        }
        for log in logs {
            if let Err(refusal) = self.read_log(log, at, state) {
                return self.refuse(refusal);
            }
        }
        if let Some(difference) = &self.difference {
            return ProbeDecision::Differs(difference.clone());
        }
        if let Mode::Compare(baseline) = &self.mode
            && !self.channels.is_empty()
            && self.channels.iter().all(|channel| channel.open.is_some())
            && baseline
                .channels
                .iter()
                .all(|channel| channel.closed.is_none())
        {
            return ProbeDecision::Done;
        }
        ProbeDecision::Continue
    }

    fn refuse(&mut self, refusal: ObservationRefusal) -> ProbeDecision {
        let reason = format!("the observation `{}`: {}", refusal.channel, refusal.reason);
        self.refusal = Some(refusal);
        ProbeDecision::Differs(reason)
    }

    fn refuses_no_value(&self) -> bool {
        matches!(
            self.mode,
            Mode::Record {
                refuse_no_value: true,
                ..
            }
        )
    }

    fn keeps_values(&self) -> bool {
        matches!(self.mode, Mode::Record { values: true, .. })
    }

    /// The refusal of `unknown` on `channel` at `at`, where the recording refuses an element
    /// with no value; `None` where it keeps it as unknown.
    fn refusal_of(
        &self,
        channel: usize,
        at: At<'_>,
        unknown: &Unknown,
    ) -> Option<ObservationRefusal> {
        (!unknown.undecided && self.refuses_no_value()).then(|| ObservationRefusal {
            channel: self.channels[channel].name.clone(),
            rule: at.rule.map(str::to_owned),
            side: at.side,
            depth: at.depth,
            reason: unknown.reason.clone(),
        })
    }

    /// A class's event at `at`, if its filter holds there.
    fn event(
        &mut self,
        class: usize,
        at: At<'_>,
        state: &dyn Reading,
    ) -> Result<(), ObservationRefusal> {
        if self.channels[class].stopped() {
            return Ok(());
        }
        let resolved = self.resolved;
        let class_spec = &resolved.classes[class];
        if let Some(filter) = &class_spec.filter {
            match self.filter(filter, state) {
                Ok(true) => {}
                Ok(false) => return Ok(()),
                Err(unknown) => {
                    if let Some(refusal) = self.refusal_of(class, at, &unknown) {
                        return Err(refusal);
                    }
                    self.channels[class].open_at(
                        format!("its filter is not known here: {}", unknown.reason),
                        unknown.undecided,
                        Some(at.place()),
                    );
                    return Ok(());
                }
            }
        }
        let element = match self.pieces(class, state) {
            Err(unknown) => {
                if let Some(refusal) = self.refusal_of(class, at, &unknown) {
                    return Err(refusal);
                }
                if class_spec.stutter == Stutter::Collapse {
                    self.channels[class].open_at(
                        unknown.reason,
                        unknown.undecided,
                        Some(at.place()),
                    );
                    return Ok(());
                }
                Element {
                    depth: at.depth,
                    rule: at.rule.map(str::to_owned),
                    side: at.side,
                    digest: None,
                    value: None,
                    undecided: Some(unknown.reason),
                }
            }
            Ok(pieces) => {
                let value = self.keeps_values().then(|| content_value(&pieces));
                Element {
                    depth: at.depth,
                    rule: at.rule.map(str::to_owned),
                    side: at.side,
                    digest: Some(content_digest(&pieces)),
                    value,
                    undecided: None,
                }
            }
        };
        if self.channels[class].emit(Some(class_spec.stutter), element) {
            self.compare_last(class);
        }
        Ok(())
    }

    /// The pieces of the class `class`'s content at `state`, each with its component's name, in
    /// the class's order; why a component has no value otherwise.
    fn pieces(
        &mut self,
        class: usize,
        state: &dyn Reading,
    ) -> Result<Vec<(&'o str, Piece)>, Unknown> {
        let resolved = self.resolved;
        let class_spec = &resolved.classes[class];
        let mut pieces = Vec::with_capacity(class_spec.components.len());
        for (index, component) in class_spec.components.iter().enumerate() {
            match self.component(class, index, component, state) {
                Ok(piece) => pieces.push((component.name(), piece)),
                Err(unknown) => {
                    return Err(Unknown {
                        reason: format!("the component `{}`: {}", component.name(), unknown.reason),
                        undecided: unknown.undecided,
                    });
                }
            }
        }
        Ok(pieces)
    }

    /// Check a comparison's last element of `channel` against the baseline's at its index.
    fn compare_last(&mut self, channel: usize) {
        let Mode::Compare(baseline) = &self.mode else {
            return;
        };
        let theirs = &baseline.channels[channel];
        let ours = &mut self.channels[channel];
        let index = ours.elements.len() - 1;
        if let Some(open) = &theirs.open
            && index as u64 >= open.index
        {
            let element = ours.elements.pop();
            ours.open_at(
                format!(
                    "the baseline's channel is known up to its element {} ({})",
                    open.index, open.reason
                ),
                false,
                element.map(|element| (element.depth, element.side)),
            );
            return;
        }
        if let Some(their) = theirs.elements.get(index) {
            if let (Some(theirs_digest), Some(ours_digest)) =
                (their.digest, ours.elements[index].digest)
                && !theirs_digest.agrees(&ours_digest)
            {
                self.difference = Some(format!(
                    "the channel `{}` differs from the baseline's at its element {index}",
                    ours.name
                ));
            }
        } else {
            {
                let closure = match theirs.closed {
                    Some(Closure::End) => "the path's end",
                    Some(Closure::Undefined) => "an undefined step",
                    None => "nothing known",
                };
                self.difference = Some(format!(
                    "the channel `{}` has an element {index} where the baseline's has {closure}",
                    ours.name
                ));
            }
        }
    }

    /// A filter's answer at `state`.
    fn filter(&mut self, filter: &ResolvedCondition, state: &dyn Reading) -> Result<bool, Unknown> {
        let observer = self
            .observer
            .as_deref_mut()
            .expect("a declaration with a function has an observer");
        self.conversions += filter.cells().len() as u64;
        match filter.evaluate(observer, state, self.budget)? {
            Value::Bool(holds) => Ok(holds),
            other => Err(Unknown {
                reason: format!("`{}` gives no Bool here: {other:?}", filter.function()),
                undecided: false,
            }),
        }
    }

    /// A component's piece at `state`.
    fn component(
        &mut self,
        class: usize,
        index: usize,
        component: &ResolvedComponent,
        state: &dyn Reading,
    ) -> Result<Piece, Unknown> {
        match component {
            ResolvedComponent::Cell { cell, declared, .. } => {
                self.cell_piece(cell, declared, state)
            }
            ResolvedComponent::Function { function, .. } => {
                let handles = function
                    .cells()
                    .iter()
                    .map(|cell| state.handle(&cell.symbol_path()))
                    .collect::<Option<Vec<_>>>();
                if let (Some(handles), Some((held, piece))) =
                    (&handles, self.functions.get(&(class, index)))
                    && handles.iter().zip(held).all(|(now, then)| now.same(then))
                    && (piece.value.is_some() || !self.keeps_values())
                {
                    return Ok(piece.clone());
                }
                let observer = self
                    .observer
                    .as_deref_mut()
                    .expect("a declaration with a function has an observer");
                self.conversions += function.cells().len() as u64;
                let value = function.evaluate(observer, state, self.budget)?;
                let piece =
                    self.value_piece(function.observer_values(), &value, function.result.as_ref())?;
                if let Some(handles) = handles {
                    self.functions
                        .insert((class, index), (handles, piece.clone()));
                }
                Ok(piece)
            }
        }
    }

    /// A leaf cell's piece at `state`, digested from its content.
    fn cell_piece(
        &mut self,
        cell: &ReadCell,
        declared: &InputType,
        state: &dyn Reading,
    ) -> Result<Piece, Unknown> {
        let path = cell.symbol_path();
        let handle = state.handle(&path);
        if let (Some(handle), Some((held, piece))) = (&handle, self.cells.get(&cell.symbols))
            && handle.same(held)
            && (piece.value.is_some() || !self.keeps_values())
        {
            return Ok(piece.clone());
        }
        let refuse = |reason: String| Unknown {
            reason: format!("the cell `{}` {reason}", cell.path),
            undecided: false,
        };
        self.conversions += 1;
        let pattern = state
            .cell(&path)
            .ok_or_else(|| refuse("is not held by the state".to_owned()))?;
        let content = leaf_content(&pattern)
            .ok_or_else(|| refuse("is not a leaf cell of the state".to_owned()))?;
        let subject = &self.resolved.subject;
        let piece = self
            .term_piece(subject, content, declared)
            .map_err(refuse)?;
        if let Some(handle) = handle {
            self.cells
                .insert(cell.symbols.clone(), (handle, piece.clone()));
        }
        Ok(piece)
    }

    /// The piece of `pattern`, a term of the definition `index` holds at type `declared`; the
    /// reason it has no value otherwise.
    fn term_piece(
        &self,
        index: &ValueIndex,
        pattern: &Pattern,
        declared: &InputType,
    ) -> Result<Piece, String> {
        let value = index
            .decode(pattern)
            .map_err(|error| format!("holds no term of the definition: {error}"))?;
        if let Some(part) = crate::views::opaque_part(index, &value) {
            return Err(format!(
                "holds {part}, which has no KRS description to observe"
            ));
        }
        let mut bytes = Vec::new();
        index.canonical_kore(pattern, &mut bytes);
        let value = self
            .keeps_values()
            .then(|| {
                crate::encode::encode(index, &value, declared).or_else(|error| {
                    self.undocumented(
                        &bytes,
                        format!("has no document in the typed encoding: {error}"),
                    )
                })
            })
            .transpose()?;
        Ok(Piece {
            digest: ElementDigest::of(&bytes),
            value,
        })
    }

    /// The value kept for a part whose canonical KORE is `kore` and which has no document in the
    /// typed encoding, `reason` saying why: shown by its KORE text where this oracle shows such a
    /// part ([`UNDOCUMENTED`]); `reason` otherwise, which leaves its element with no value.
    fn undocumented(&self, kore: &[u8], reason: String) -> Result<Json, String> {
        if !self.shows_undocumented {
            return Err(reason);
        }
        let mut body = serde_json::Map::new();
        body.insert(
            "kore".to_owned(),
            Json::String(String::from_utf8_lossy(kore).into_owned()),
        );
        body.insert("reason".to_owned(), Json::String(reason));
        let mut shown = serde_json::Map::new();
        shown.insert(UNDOCUMENTED.to_owned(), Json::Object(body));
        Ok(Json::Object(shown))
    }

    /// The piece of `value`, a value of the observer `index` at type `declared`.
    fn value_piece(
        &self,
        index: &ValueIndex,
        value: &Value,
        declared: Option<&InputType>,
    ) -> Result<Piece, Unknown> {
        let unknown = |reason: String| Unknown {
            reason,
            undecided: false,
        };
        let pattern = index
            .encode(value)
            .map_err(|error| unknown(format!("its value is no term of the observer: {error}")))?;
        let mut bytes = Vec::new();
        index.canonical_kore(&pattern, &mut bytes);
        let value = self
            .keeps_values()
            .then(|| {
                crate::encode::encode(
                    index,
                    value,
                    &declared.cloned().unwrap_or_else(InputType::untyped),
                )
                .or_else(|error| {
                    self.undocumented(
                        &bytes,
                        format!("its value has no document in the typed encoding: {error}"),
                    )
                    .map_err(unknown)
                })
            })
            .transpose()?;
        Ok(Piece {
            digest: ElementDigest::of(&bytes),
            value,
        })
    }

    /// Read a log at `at`: the items appended since its last read, each through its element
    /// function, after the recording's exact check that the earlier items are still there.
    fn read_log(
        &mut self,
        log: usize,
        at: At<'_>,
        state: &dyn Reading,
    ) -> Result<(), ObservationRefusal> {
        let channel = self.resolved.classes.len() + log;
        if self.channels[channel].stopped() {
            return Ok(());
        }
        let resolved = self.resolved;
        let spec = &resolved.logs[log];
        let path = spec.cell.symbol_path();
        let handle = state.handle(&path);
        if let (Some(handle), Some(held)) = (&handle, &self.logs[log].handle)
            && handle.same(held)
        {
            return Ok(());
        }
        let Some(items) = self.appended(log, channel, at, state)? else {
            return Ok(());
        };
        for item in items {
            let mut bytes = Vec::new();
            resolved.subject.canonical_kore(&item, &mut bytes);
            let digest = ElementDigest::of(&bytes);
            self.logs[log].items.push((digest, at.depth, at.side));
            let pieces = match self.logs[log].memo.get(&digest) {
                Some(pieces) => pieces.clone(),
                None => match self.item_pieces(spec, &item) {
                    Ok(pieces) => {
                        self.logs[log].memo.insert(digest, pieces.clone());
                        pieces
                    }
                    Err(failure) => {
                        let failure = Unknown {
                            reason: format!(
                                "the item at position {}: {}",
                                self.logs[log].items.len() - 1,
                                failure.reason
                            ),
                            undecided: failure.undecided,
                        };
                        return self.log_unknown(channel, at, &failure);
                    }
                },
            };
            for piece in pieces {
                let element = Element {
                    depth: at.depth,
                    rule: at.rule.map(str::to_owned),
                    side: at.side,
                    digest: Some(piece.digest),
                    value: piece.value,
                    undecided: None,
                };
                if self.channels[channel].emit(None, element) {
                    self.compare_last(channel);
                }
                if self.difference.is_some() || self.channels[channel].stopped() {
                    return Ok(());
                }
            }
        }
        self.logs[log].handle = handle;
        Ok(())
    }

    /// The items of a log's cell appended since its last read: in a recording, after the exact
    /// check that the earlier items are still there (a refusal otherwise); in a comparison,
    /// after the check that the cell did not shrink. `None` where the channel opened instead.
    fn appended(
        &mut self,
        log: usize,
        channel: usize,
        at: At<'_>,
        state: &dyn Reading,
    ) -> Result<Option<Vec<Pattern>>, ObservationRefusal> {
        let resolved = self.resolved;
        let spec = &resolved.logs[log];
        let path = spec.cell.symbol_path();
        let read = self.logs[log].items.len();
        let unknown = |reason: String| Unknown {
            reason: format!("the cell `{}` {reason}", spec.cell.path),
            undecided: false,
        };
        if matches!(self.mode, Mode::Record { .. }) {
            self.conversions += 1;
            let Some(items) = state.list_items(&path, 0) else {
                return self.log_unknown_none(
                    channel,
                    at,
                    &unknown("holds no list of known items".to_owned()),
                );
            };
            let rewritten = if items.len() < read {
                Some(format!(
                    "held {read} items at its previous read and holds {} here",
                    items.len()
                ))
            } else {
                items[..read]
                    .iter()
                    .zip(&self.logs[log].items)
                    .position(|(item, (digest, _, _))| {
                        let mut bytes = Vec::new();
                        resolved.subject.canonical_kore(item, &mut bytes);
                        ElementDigest::of(&bytes) != *digest
                    })
                    .map(|position| {
                        format!(
                            "holds another item at position {position} than at its previous read"
                        )
                    })
            };
            if let Some(rewritten) = rewritten {
                return Err(ObservationRefusal {
                    channel: spec.name.clone(),
                    rule: at.rule.map(str::to_owned),
                    side: at.side,
                    depth: at.depth,
                    reason: format!(
                        "log-not-appended: the cell `{}` {rewritten}; a log's cell only grows by appending",
                        spec.cell.path
                    ),
                });
            }
            Ok(Some(items.into_iter().skip(read).collect()))
        } else {
            match state.list_len(&path) {
                None => self.log_unknown_none(
                    channel,
                    at,
                    &unknown("holds no list of known items".to_owned()),
                ),
                Some(len) if len < read => self.log_unknown_none(
                    channel,
                    at,
                    &unknown(format!(
                        "held {read} items at its previous read and holds {len} here"
                    )),
                ),
                Some(_) => {
                    self.conversions += 1;
                    Ok(Some(state.list_items(&path, read).unwrap_or_default()))
                }
            }
        }
    }

    fn log_unknown_none(
        &mut self,
        channel: usize,
        at: At<'_>,
        unknown: &Unknown,
    ) -> Result<Option<Vec<Pattern>>, ObservationRefusal> {
        self.log_unknown(channel, at, unknown).map(|()| None)
    }

    fn log_unknown(
        &mut self,
        channel: usize,
        at: At<'_>,
        unknown: &Unknown,
    ) -> Result<(), ObservationRefusal> {
        if let Some(refusal) = self.refusal_of(channel, at, unknown) {
            return Err(refusal);
        }
        self.channels[channel].open_at(unknown.reason.clone(), unknown.undecided, Some(at.place()));
        Ok(())
    }

    /// The pieces an item contributes to its log's channel: itself, or each element of its
    /// element function's value.
    fn item_pieces(&mut self, spec: &ResolvedLog, item: &Pattern) -> Result<Vec<Piece>, Unknown> {
        let subject = Arc::clone(&self.resolved.subject);
        let Some(function) = &spec.element else {
            return self
                .term_piece(&subject, item, &spec.item)
                .map(|piece| vec![piece])
                .map_err(|reason| Unknown {
                    reason,
                    undecided: false,
                });
        };
        let value = subject.decode(item).map_err(|error| Unknown {
            reason: format!("holds no term of the definition: {error}"),
            undecided: false,
        })?;
        if let Some(part) = crate::views::opaque_part(&subject, &value) {
            return Err(Unknown {
                reason: format!(
                    "holds {part}, which has no KRS description to carry to an observer"
                ),
                undecided: false,
            });
        }
        let observer = self
            .observer
            .as_deref_mut()
            .expect("a declaration with a function has an observer");
        let result = observer
            .evaluate_within(
                function.decl.path(),
                vec![(&*function.parameter, value)],
                self.budget,
            )
            .map_err(|error| Unknown::from(ObservationError::Evaluation(error)))?;
        let Value::List(elements) = result else {
            return Err(Unknown {
                reason: format!("`{}` gives no List here: {result:?}", function.decl),
                undecided: false,
            });
        };
        let observer_values = Arc::clone(&self.resolved.observer);
        elements
            .iter()
            .map(|element| self.value_piece(&observer_values, element, Some(&function.element)))
            .collect()
    }

    /// Read every log at the path's end, `state` at `depth` steps.
    fn read_end(&mut self, depth: u64, state: &dyn Reading) {
        if self.refusal.is_some() {
            return;
        }
        let at = At {
            rule: None,
            side: None,
            depth,
        };
        for log in 0..self.resolved.logs.len() {
            if let Err(refusal) = self.read_log(log, at, state) {
                self.refusal = Some(refusal);
                return;
            }
        }
        self.read_end = true;
    }

    /// Observe the points of a step the run took before its request: `rule`'s step from `before`
    /// (the run's start) to `after` (the request's start).
    pub(crate) fn taken_step(
        &mut self,
        rule: &str,
        before: &Pattern,
        after: &Pattern,
    ) -> ProbeDecision {
        let subject = Arc::clone(&self.resolved.subject);
        for (side, pattern, depth) in [(StopSide::Before, before, 0), (StopSide::After, after, 1)] {
            let state = KoreState {
                pattern,
                subject: &subject,
            };
            let decision = self.point(rule, side, depth, &state);
            if decision != ProbeDecision::Continue {
                return decision;
            }
        }
        ProbeDecision::Continue
    }

    /// Read every log at the path's end, `pattern` at `depth` steps: a run's end the request's
    /// probe was not told of.
    pub(crate) fn end_at(&mut self, depth: u64, pattern: &Pattern) {
        let subject = Arc::clone(&self.resolved.subject);
        self.read_end(
            depth,
            &KoreState {
                pattern,
                subject: &subject,
            },
        );
    }

    /// Cut the record back to a path that ends at `depth` steps, at `pattern`: the states past it
    /// have no value, so the steps into them are undefined and have no point. The elements and
    /// log items of a later point, a before point at `depth` included, are dropped, a channel
    /// opened there is open no more, and every log is read again at the new end.
    pub(crate) fn cut_back(&mut self, depth: u64, pattern: &Pattern) {
        let past = |at: u64, side: Option<StopAt>| {
            at > depth || (at == depth && side == Some(StopAt::Before))
        };
        for channel in &mut self.channels {
            channel
                .elements
                .retain(|element| !past(element.depth, element.side));
            if let Some(Open {
                at: Some((at, side)),
                ..
            }) = &channel.open
                && past(*at, *side)
            {
                channel.open = None;
            }
            // A channel opened at a point the cut keeps, or at a split, keeps its index
            // only where its elements still reach it.
            if let Some(open) = &mut channel.open {
                open.index = open.index.min(channel.elements.len() as u64);
            }
        }
        for log in &mut self.logs {
            log.items.retain(|(_, at, side)| !past(*at, *side));
            log.handle = None;
        }
        self.read_end = false;
        self.end_at(depth, pattern);
    }
}

/// How a run's end leaves the channels not already open ([`ObservationOracle::finish`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ChannelEnd {
    /// Closed by a determined end.
    End,
    /// Closed by an undefined last step.
    Undefined,
    /// Open there, for this reason: a bound, which ends only what is known.
    Open(String),
    /// Open there as undecided ([`Open::undecided`]), for this reason: an inconclusive halt,
    /// which another run may take further.
    Undecided(String),
}

impl Probe for ObservationOracle<'_> {
    fn observe(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision {
        let depth = point.depth().saturating_add(self.offset);
        self.point(point.rule(), point.side(), depth, point.state())
    }

    fn branched(&mut self, depth: u64) {
        let depth = depth.saturating_add(self.offset);
        for channel in &mut self.channels {
            channel.open_at(
                format!(
                    "the path splits at the state after {depth} step{}",
                    if depth == 1 { "" } else { "s" }
                ),
                false,
                None,
            );
        }
    }

    fn ended(&mut self, leaf: &ProbeLeaf<'_>) {
        let depth = leaf.depth().saturating_add(self.offset);
        self.read_end(depth, leaf.state());
    }
}

impl fmt::Display for ObservationRefusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "the observation `{}`: {}",
            self.channel, self.reason
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn element(depth: u64, digest: &[u8], value: Option<Json>) -> Element {
        Element {
            depth,
            rule: Some("tick".to_owned()),
            side: Some(StopAt::Before),
            digest: Some(ElementDigest::of(digest)),
            value,
            undecided: None,
        }
    }

    fn unknown(depth: u64) -> Element {
        Element {
            depth,
            rule: Some("tick".to_owned()),
            side: Some(StopAt::Before),
            digest: None,
            value: None,
            undecided: Some("spent".to_owned()),
        }
    }

    fn channel(
        name: &str,
        elements: Vec<Element>,
        closed: Option<Closure>,
        open: Option<u64>,
    ) -> Channel {
        Channel {
            name: name.to_owned(),
            kind: ChannelKind::Point,
            open: open.map(|index| Open {
                index,
                reason: "depth-bound".to_owned(),
                undecided: false,
                at: None,
            }),
            elements,
            closed,
        }
    }

    fn record(channels: Vec<Channel>) -> Observations {
        Observations {
            channels,
            conversions: 0,
        }
    }

    fn empty(name: &str) -> Channel {
        channel(name, Vec::new(), None, None)
    }

    /// Under `collapse` an element equal to the last one kept is dropped, so the count of equal
    /// consecutive contents is not observed; under `count` every event is an element. An unknown
    /// element is kept under `count` and never collapses an equal neighbour.
    #[test]
    fn collapse_drops_equal_consecutive_contents_and_count_keeps_them() {
        let contents: [&[u8]; 5] = [b"a", b"a", b"b", b"b", b"a"];
        let mut collapsed = empty("c");
        let mut counted = empty("c");
        for (depth, content) in contents.iter().enumerate() {
            collapsed.emit(
                Some(Stutter::Collapse),
                element(depth as u64, content, None),
            );
            counted.emit(Some(Stutter::Count), element(depth as u64, content, None));
        }
        let digests = |channel: &Channel| {
            channel
                .elements
                .iter()
                .map(|element| element.digest.unwrap())
                .collect::<Vec<_>>()
        };
        let of = |bytes: &[u8]| ElementDigest::of(bytes);
        assert_eq!(digests(&collapsed), [of(b"a"), of(b"b"), of(b"a")]);
        assert_eq!(digests(&counted).len(), 5);
        assert_eq!(
            collapsed
                .elements
                .iter()
                .map(|element| element.depth)
                .collect::<Vec<_>>(),
            [0, 2, 4]
        );
        counted.emit(Some(Stutter::Count), unknown(5));
        counted.emit(Some(Stutter::Count), element(6, b"a", None));
        assert_eq!(counted.elements.len(), 7);
        // A log drops nothing.
        let mut log = empty("l");
        log.emit(None, element(0, b"x", None));
        log.emit(None, element(0, b"x", None));
        assert_eq!(log.elements.len(), 2);
    }

    /// A channel that stopped (opened or closed) takes no element.
    #[test]
    fn a_stopped_channel_takes_no_element() {
        let mut open = empty("c");
        open.open_at("undecided".to_owned(), true, None);
        assert!(!open.emit(Some(Stutter::Count), element(0, b"a", None)));
        assert_eq!(open.open.as_ref().unwrap().index, 0);
    }

    /// The first difference of two records: the first index at which both are decided and differ,
    /// END and UNDEF being elements; nothing past an open point or at an unknown element is read.
    #[test]
    fn first_difference_of_two_records() {
        let same = record(vec![channel(
            "c",
            vec![element(1, b"a", None), element(2, b"b", None)],
            Some(Closure::End),
            None,
        )]);
        assert_eq!(first_difference(&same, &same.clone()), None);
        // A differing element.
        let other = record(vec![channel(
            "c",
            vec![element(1, b"a", None), element(3, b"c", None)],
            Some(Closure::End),
            None,
        )]);
        let difference = first_difference(&same, &other).unwrap();
        assert_eq!((difference.channel.as_str(), difference.index), ("c", 1));
        // An end against an element.
        let short = record(vec![channel(
            "c",
            vec![element(1, b"a", None)],
            Some(Closure::End),
            None,
        )]);
        let difference = first_difference(&same, &short).unwrap();
        assert_eq!((difference.index, &difference.right), (1, &Observed::End));
        // An end against an undefined step.
        let undefined = record(vec![channel(
            "c",
            vec![element(1, b"a", None), element(2, b"b", None)],
            Some(Closure::Undefined),
            None,
        )]);
        assert_eq!(first_difference(&same, &undefined).unwrap().index, 2);
        // Nothing past an open point: a bound never makes a difference.
        let bounded = record(vec![channel(
            "c",
            vec![element(1, b"a", None)],
            None,
            Some(1),
        )]);
        assert_eq!(first_difference(&same, &bounded), None);
        assert_eq!(first_difference(&bounded, &same), None);
        // An unknown element is skipped, and a later decided one still differs.
        let unknown_first = record(vec![channel(
            "c",
            vec![unknown(1), element(3, b"c", None)],
            Some(Closure::End),
            None,
        )]);
        assert_eq!(first_difference(&same, &unknown_first).unwrap().index, 1);
        let unknown_only = record(vec![channel(
            "c",
            vec![unknown(1), element(2, b"b", None)],
            Some(Closure::End),
            None,
        )]);
        assert_eq!(first_difference(&same, &unknown_only), None);
    }

    /// Of several differing channels, the one the right side reached first is reported, and
    /// values are compared where both carry them, naming the path inside them.
    #[test]
    fn the_difference_reported_is_the_right_side_s_first() {
        let left = record(vec![
            channel("a", vec![element(5, b"x", None)], None, Some(1)),
            channel(
                "b",
                vec![element(
                    2,
                    b"p",
                    Some(serde_json::json!({"regs": {"a": 1, "b": 2}})),
                )],
                None,
                Some(1),
            ),
        ]);
        let right = record(vec![
            channel("a", vec![element(5, b"y", None)], None, Some(1)),
            channel(
                "b",
                vec![element(
                    3,
                    b"p",
                    Some(serde_json::json!({"regs": {"a": 1, "b": 3}})),
                )],
                None,
                Some(1),
            ),
        ]);
        let difference = first_difference(&left, &right).unwrap();
        assert_eq!(difference.channel, "b");
        assert_eq!(difference.path.as_deref(), Some("regs.b"));
    }

    /// A truncated digest agrees with every digest it is a prefix of, so a truncation can hide a
    /// difference and never make one.
    #[test]
    fn a_truncated_digest_agrees_with_its_whole() {
        let whole = ElementDigest::of(b"element");
        let short = whole.truncated(8);
        assert_eq!(short.as_bytes().len(), 8);
        assert!(short.agrees(&whole) && whole.agrees(&short));
        assert!(!short.agrees(&ElementDigest::of(b"other")));
        assert_eq!(ElementDigest::from_bytes(short.as_bytes()), Some(short));
        assert_eq!(ElementDigest::from_bytes(&[]), None);
    }

    /// The document of a record writes every element with its index, and the run report's
    /// summary counts them.
    #[test]
    fn the_document_and_the_summary() {
        let observations = record(vec![
            channel(
                "c",
                vec![
                    element(1, b"a", Some(serde_json::json!({"n": 1}))),
                    unknown(2),
                ],
                None,
                Some(2),
            ),
            Channel {
                kind: ChannelKind::Log,
                ..channel("l", vec![], Some(Closure::End), None)
            },
        ]);
        let document = observations.document();
        assert_eq!(document["schema"], OBSERVATIONS_FORMAT);
        assert_eq!(document["channels"][0]["elements"][0]["value"]["n"], 1);
        assert_eq!(document["channels"][0]["elements"][1]["index"], 1);
        assert_eq!(document["channels"][0]["elements"][1]["undecided"], "spent");
        assert_eq!(document["channels"][0]["open"]["index"], 2);
        assert_eq!(document["channels"][1]["closed"], "end");
        assert_eq!(document["channels"][1]["kind"], "log");
        let summary = serde_json::to_value(&observations).unwrap();
        assert_eq!(summary["channels"][0]["elements"], 2);
        assert!(observations.undecided());
    }

    /// Two records that do not differ agree channel by channel: to both sides' closure, up to a
    /// horizon where a side is open at a bound, and with no answer where an element was not
    /// compared or a side is open as undecided while the other side still knows the index.
    #[test]
    fn how_far_two_records_agree() {
        let closed = record(vec![channel(
            "c",
            vec![element(1, b"a", None), element(2, b"b", None)],
            Some(Closure::End),
            None,
        )]);
        let RecordComparison::Agree(agreements) = compare_records(&closed, &closed.clone()) else {
            panic!("equal records differ");
        };
        assert_eq!(agreements[0].through, 2);
        assert_eq!(agreements[0].left, Reach::Closed(Closure::End));
        assert!(!agreements[0].bounded() && agreements[0].undecided().is_none());
        let bounded = record(vec![channel(
            "c",
            vec![element(1, b"a", None)],
            None,
            Some(1),
        )]);
        let RecordComparison::Agree(agreements) = compare_records(&bounded, &closed) else {
            panic!("a bound made a difference");
        };
        assert_eq!(agreements[0].through, 1);
        assert!(matches!(agreements[0].left, Reach::Open(_)));
        assert_eq!(agreements[0].right, Reach::Known);
        assert!(agreements[0].bounded() && agreements[0].undecided().is_none());
        // An unknown element is not compared, so the agreement answers nothing.
        let unknown_first = record(vec![channel(
            "c",
            vec![unknown(1), element(2, b"b", None)],
            Some(Closure::End),
            None,
        )]);
        let RecordComparison::Agree(agreements) = compare_records(&closed, &unknown_first) else {
            panic!("an unknown element made a difference");
        };
        assert_eq!(
            agreements[0].undecided(),
            Some((Some(RecordSide::Right), 0, "spent"))
        );
        // A side open as undecided where the other side knows the index answers nothing; where
        // the other side is open at a bound there, the agreement is bounded.
        let mut undecided = bounded.clone();
        undecided.channels[0].open.as_mut().unwrap().undecided = true;
        let RecordComparison::Agree(agreements) = compare_records(&undecided, &closed) else {
            panic!("an undecided open point made a difference");
        };
        assert_eq!(
            agreements[0].undecided(),
            Some((Some(RecordSide::Left), 1, "depth-bound"))
        );
        let RecordComparison::Agree(agreements) = compare_records(&undecided, &bounded) else {
            panic!("two open points made a difference");
        };
        assert_eq!(agreements[0].undecided(), None);
        // Elements with neither a value nor a digest in common are not compared.
        let mut valued = closed.clone();
        for element in &mut valued.channels[0].elements {
            element.digest = None;
            element.value = Some(serde_json::json!(1));
        }
        let RecordComparison::Agree(agreements) = compare_records(&closed, &valued) else {
            panic!("elements with nothing in common differ");
        };
        assert_eq!(
            agreements[0]
                .undecided()
                .map(|(side, index, _)| (side, index)),
            Some((None, 0))
        );
    }

    /// A record's document reads back as the record, with values in place of digests, so the
    /// two compare alike; a part of another shape is refused, naming its position.
    #[test]
    fn a_document_reads_back_as_its_record() {
        let observations = record(vec![
            channel(
                "c",
                vec![
                    element(1, b"a", Some(serde_json::json!({"n": 1}))),
                    unknown(2),
                ],
                None,
                Some(2),
            ),
            Channel {
                kind: ChannelKind::Log,
                ..channel(
                    "l",
                    vec![Element {
                        rule: None,
                        side: None,
                        ..element(3, b"x", Some(serde_json::json!({"Out": {"n": 2}})))
                    }],
                    Some(Closure::End),
                    None,
                )
            },
        ]);
        let document = observations.document();
        let read = Observations::from_document(&document).unwrap();
        assert_eq!(read.document(), document);
        assert!(read.channels[0].elements[0].digest.is_none());
        assert_eq!(first_difference(&observations, &read), None);
        let refused = |edit: &dyn Fn(&mut Json)| {
            let mut edited = document.clone();
            edit(&mut edited);
            Observations::from_document(&edited).unwrap_err()
        };
        for (edit, expected) in [
            (
                &(|document: &mut Json| document["schema"] = Json::from("krs-observations/0"))
                    as &dyn Fn(&mut Json),
                "at `schema`: an observation document's `schema` is `krs-observations/1`",
            ),
            (
                &|document: &mut Json| document["extra"] = Json::from(1),
                "at `the document`: unknown key `extra`",
            ),
            (
                &|document: &mut Json| document["channels"][1]["name"] = Json::from("c"),
                "at `channels[1]`: a second channel `c`",
            ),
            (
                &|document: &mut Json| {
                    document["channels"][0]["elements"][1]["index"] = Json::from(5);
                },
                "at `channels[0].elements[1]`: `index` is the element's position, 1",
            ),
            (
                &|document: &mut Json| {
                    document["channels"][0]["elements"][0]["undecided"] = Json::from("x");
                },
                "at `channels[0].elements[0]`: an element holds its `value`",
            ),
            (
                &|document: &mut Json| {
                    document["channels"][1]["open"] = document["channels"][0]["open"].clone();
                },
                "at `channels[1].open`: `index` is where the channel opened, after its 1 element",
            ),
            (
                &|document: &mut Json| document["channels"][1]["closed"] = Json::Null,
                "at `channels[1]`: a channel is closed (`closed`) or open (`open`)",
            ),
        ] {
            let message = refused(edit);
            assert!(
                message.starts_with(expected),
                "{expected:?} is not the start of {message:?}"
            );
        }
    }
}
