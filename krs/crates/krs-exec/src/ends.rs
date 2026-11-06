//! Ends of runs and their comparison at the KRS level: cells by Rust field path, values as
//! their canonical documents ([`crate::encode()`]).
//!
//! # Ends
//!
//! An *end* is how a complete run ended ([`EndClass`]: its halt word, and for `stopped` the KRS
//! item of the stop rule, with the package that declares it) and the content of its cells
//! ([`EndCells`]), read from the final state by the configuration's declaration: a leaf cell
//! holds a value, a group cell its cells, an optional cell its content or nothing, and a repeated
//! cell its instances. The instances of a `List`
//! cell collection are in the collection's order; those of a `Set` or `Map` collection are a
//! set, kept in the order of their canonical text (instances with equal texts, which only values
//! with no document can have, in the order of the values), each once, so that two ends holding
//! the same instances are equal. A `Map` collection is a map from key to instance: an instance's
//! key is its first cell, which is the instance's identity, so an end holds at most one instance
//! per key, and two ends' instances with one key are the same instance, compared cell by cell.
//!
//! [`Semantics::end_of`] reads a run's end and [`Semantics::ends_of`] a final-state search's
//! ends. A run that halted inconclusively (`indeterminate`, `timeout`, `interrupted`,
//! `unsupported-hook`, `simplification-error`) has no end: nothing is known of where the
//! definition takes the program, so its set of ends is empty and incomplete ([`Ends`]). A state
//! that carries a constraint denotes the set of configurations that satisfy it, which a
//! comparison of values does not decide, so it is no end either. An `undefined` end has no
//! cells: its state is `\bottom`.
//!
//! [`Semantics::read_configuration`] reads an end of a given class from a configuration that
//! another comparison of configurations projected (kink's kill evidence, which leaves out the
//! cells its slot does not compare): the cells it names are not stated, as an end document that
//! omits them does not state them.
//!
//! # End documents
//!
//! An end is written and read as a document of the typed encoding (the normative statement of
//! values is [`crate::inputs`], "The canonical document of a value"):
//!
//! ```json
//! {"halt": "stopped", "rule": "crate::machine::boundary", "cells": {"pc": 257, "cpu": {"ime": true}}}
//! ```
//!
//! - `halt` is the halt word of a complete run (`stuck`, `depth-bound`, `undefined`, `stopped`);
//!   `rule` names the stop rule's KRS item when, and only when, `halt` is `stopped`.
//!   An expectation's end is never `depth-bound` ("Results", below).
//!   It is any name a stop accepts ([`crate::StopRules`], `--stop-before`): the item's Rust path
//!   with `crate::` for an item of the definition's main package
//!   (`crate::machine::boundary`), with its crate's name for an item of a dependency
//!   (`lang::step`), or a K label of one of its rules.
//!   The name must select rewrite rules of the definition, and all of one item:
//!   a rule the definition does not have stops none of its runs,
//!   and a stopped end's class is one item, so a name that selects two items' rules is refused.
//!   The class holds the item, which [`Semantics::end_document`] writes by one name of it: its
//!   path with `crate::` or its crate's name where that selects its rules alone, else the first
//!   label of its rules that does. So two packages' items at one path are two classes, and the
//!   name a document writes reads back as the item.
//!   A stopped end whose class names no item has no end document.
//! - `cells` nests by group field as [`crate::StateView`] paths do (`cpu.regs` is
//!   `cells.cpu.regs`; TOML dotted keys give it); a leaf cell holds its value's document at the
//!   cell's declared type; an optional cell is `[]` (absent) or `[content]`; a repeated cell is
//!   the array of its instances' contents (each a table of the instance's cells, or a document
//!   for a repeated leaf cell), read as a list for a `List` collection and as a set otherwise.
//!   An `undefined` end states no cell.
//!
//! A document may state any subset of the cells ([`Semantics::read_end`]): a stated cell is
//! decoded at its declared type, and a path the configuration does not declare is refused,
//! listing the cells there. Two instances of a `Map` collection that state one key are refused,
//! naming the key: a map holds one instance per key. Whether a document states enough is a
//! property of a comparison: a compared cell it does not state is refused, naming the cell and
//! its type, and a cell it states that is not compared (an unobservable cell, or one a narrowing
//! leaves out) is never read again. The refusal names an instance as a difference does: an
//! instance of a `List` collection by its index, one of a `Map` collection by its key
//! (`procs.process[1].ticks`), and one of a `Set` collection by its canonical text
//! (`objects.obj{{}}.oid`), as is a `Map` instance that does not state its key: an end is a value,
//! which keeps no position in the document it was read from, and a set's instances have none.
//! [`Semantics::end_document`] writes an end's document, which reads back as the end.
//!
//! # Compared cells
//!
//! By default a comparison compares the class and every leaf cell that is not unobservable and
//! not inside an unobservable cell (`#[k::cell(unobservable)]`: no use of the definition may
//! observe it). [`Comparison::compare`] narrows the compared cells to the ones it names by
//! declared path (fields joined by `.`, through repeated cells without an index:
//! `threads.thread.count`); a group's path names its leaves, the unobservable ones excepted.
//! Naming an unobservable cell, or one inside an unobservable cell, is refused: such a cell has no
//! observation to compare. The computation cell is a cell like any other.
//!
//! A comparison that compares a cell of a `Map` collection's instances compares the whole of
//! their key, the instance's first cell: instances are paired by key, so without the key two
//! instances could not be told apart, and their projections could merge into one. A comparison
//! that compares some of an instance's cells but not all of its key is refused, naming the key,
//! as one is whose key is, or holds, an unobservable cell, and so is a view at or inside a key,
//! which could give two instances one key.
//!
//! An end *projected* onto the compared cells keeps its class and those cells: an optional cell
//! holding a compared cell keeps whether it is present, and a repeated cell holding one keeps its
//! instances, each projected, a set collection's instances as a set of projections.
//!
//! A comparison may apply *views* to compared leaf cells ([`Comparison::views`]; the normative
//! statement is [`crate::views`]). The projected end then holds, at each viewed cell, the view's
//! value at the cell's value instead of the cell's value, written at the view's declared result
//! type, element types included, by the definition that declares the view; everything below compares and shows projected ends, so a
//! difference at a viewed cell is between viewed values and its path descends into them, and the
//! difference lists the views it applied (`views`). A set collection's instances are then the set
//! of their viewed projections.
//!
//! # Results
//!
//! A comparison is [`Compared::Equal`], [`Compared::Differs`] with the first [`Difference`], or
//! [`Compared::Inconclusive`] with the reason: a side has no end (an inconclusive run), a side's
//! set of ends is incomplete where completeness decides, or a stopped end does not name its stop
//! rule. Inconclusive is never a difference: "no end to compare" and "ends differ" call for
//! different actions.
//!
//! - An expectation (one end `x`, usually partial) against a run's ends `E`
//!   ([`Semantics::check_expectation`]) is met when every end of `E` agrees with `x` on the class
//!   and the compared cells: the expectation states what the definition computes for the case,
//!   and one disagreeing end of a nondeterministic definition is a result it can produce. The
//!   first disagreeing end in the order of the canonical text of the projected end documents is
//!   reported, so the report is a function of the set of ends, not of the order a producer gave
//!   them in. When every end agrees but `E` is incomplete, or empty, the result is inconclusive.
//!   The ends of `E` are the ends the definition reaches ([`Ends::reached`]): a `depth-bound`
//!   end is a state at which a step budget ended a run or a search, which took no step from it,
//!   so it is not known to be an end of the definition, which may take the state further; it is
//!   not compared and makes `E` incomplete, whether or not the state has a successor. A run that
//!   reaches its budget is therefore inconclusive against an expectation, never met or unmet. So
//!   no end meets an expectation of a `depth-bound` end, which is refused: the depth counts the
//!   compiled definition's steps, the heating and cooling steps of strictness and contexts
//!   included, so the state after N steps changes with how the definition is compiled and is no
//!   fact about the definition. An expectation of the state at a point of a run states a stop at
//!   a named rule and a stop count instead (`stopped`, its `rule`). The arrivals at a rule the
//!   author wrote are that rule's steps, which the compilation does not change; the arrivals at
//!   a context or a strict production are the heating and cooling steps the compilation
//!   generates for it, which change with the compilation as the depth does.
//! - Two sets of ends `L` and `R` ([`Semantics::compare_ends`]) are equal when their sets of projected
//!   ends are. Otherwise the difference is between the first end of `R` outside `L` (in the order
//!   of the canonical text of the projected end documents) and its nearest end of `L`, which
//!   needs `L` complete for the end to be outside it; else the first end of `L` outside `R` and
//!   its nearest end of `R`, which needs `R` complete. The nearest end is the one with the fewest
//!   differing compared leaves, the first in order among equals; differing classes count one.
//!   A leaf held by both ends counts one when its values differ, a map's differing entries
//!   counted one by one, and two instances of a `Map` collection with one key are compared as two
//!   instances of a `List` collection at one index are, by their leaves; content only one end holds
//!   (an optional cell's, an instance of a `List` collection past the other's last, an instance of
//!   a `Map` collection at a key the other does not hold, an instance of a `Set` collection the
//!   other does not hold) counts each compared leaf in it, since no leaf of the other end stands
//!   at its position.
//!   With no such end and both sets complete, they are equal; else the result is inconclusive.
//!
//! # The first difference
//!
//! The class is compared first. Then the compared cells, in declaration order (pre-order of the
//! cell tree): the first that differs is the difference's `cell`, and every other compared cell
//! that differs is listed in `also_differ`, so that declaration order does not hide them. The
//! instances of a `List` collection are compared index by index (`threads.thread[0].count`, the
//! whole instance for an index past one side's end); those of a `Map` collection key by key, in
//! the order of the keys' canonical texts, each key written as a value map's key is
//! (`procs.process[1].ticks`, `harts.hart["boot"].pc`, the whole instance for a key one side
//! lacks), so `[2]` is a key in a `Map` collection as it is a position in a `List` collection;
//! in a `Set` collection the difference is the first instance, by canonical text, that one side
//! holds and the other does not (`objects.obj{<instance text>}`). An optional cell present on
//! one side only differs as `[]` against `[content]`.
//!
//! Inside a leaf's value the difference descends while both sides are the same constructor (to
//! its first differing field, named as a position of the value's document names it, the
//! constructor's name and the field's: `.Flags.zf`, `.Pair.0`, `$ctor(Pair).a` where the document
//! writes the tagged form, and no further where the value has no document there), both maps (to
//! the first differing key in the order of its canonical text at the key type, `["B"]` or
//! `[49152]`, a side lacking the key showing null), both lists or both K sequences (to the first
//! differing index, `[2]`, null past a side's end), and both sets (to the first element, by
//! canonical text, that one holds and the other does not, `{<element text>}`, which ends the
//! descent). The path is the cell's Rust field path followed by those segments: `f.Flags.zf`,
//! `bus[2]`, `bus[0].Write.value`, `memory[5]`, `regs["B"]`. A path thus names what each part
//! belongs to, and a segment is read by the declared type of the position it descends into, so a
//! difference is read with its definition.
//!
//! Each side's value is shown as its canonical document at the type of its position; a value with
//! no document there (an `Opaque` part, a parametric application) is shown whole as K text
//! (`rendering: "k"`, or KORE when the printer warns), never as a document with K text inside it.
//! Its `opaque` names the part that has no document by its position inside the shown value, in
//! the notation of [`crate::InputError`]'s positions, empty for the whole value: the difference's
//! `path` locates the shown value, and `opaque` the part inside it (`.count` in an instance of
//! `threads.thread`, `[0].seen` in a present optional group, `.Run.log$list[2]` in a value).
//!
//! A shown text longer than [`VALUE_CAP`] characters is cut: when the two texts first differ at
//! character `d`, at least `VALUE_CAP / 2` characters in, both are cut to the `VALUE_CAP`
//! characters from `d - VALUE_CAP / 2`, so the two shown texts differ; otherwise each to its
//! first `VALUE_CAP`. A cut value carries its window of the canonical text (`text`) instead of the document,
//! `truncated`, and the characters cut before the window (`offset`).

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::ops::Deref;
use std::sync::Arc;

use k_rust::kore::ast::{Pattern, Symbol};
use krs_ir::{CellCollectionType, CellMultiplicity};
use serde::Serialize;
use serde_json::{Map as JsonMap, Value as Json};

use crate::encode::{EncodeError, canonical_text, encode, field_position};
use crate::inputs::{InputFiles, InputType, NoFiles, decode_value_in, input_type};
use crate::report::{Halt, RunReport, SearchReport};
use crate::values::{CellNode, SortRef, Value, ValueError, ValueIndex};
use crate::view::{self, View, cell_symbols, cells_below};
use crate::views::CellViews;
use crate::{SearchMode, SearchOptions, Semantics};
use krs_ir::BuiltinSort;

/// The format of a [`Difference`] document.
///
/// A side's class names a stopped end's rule by a name a stop accepts ([`EndClass::rule`]:
/// `crate::finish`, `lang::step`, or a K label); a `krs-difference/1` document named it by the
/// item's Rust path below its crate root (`finish`). A reader of `krs-difference/1` would read
/// `crate::finish` as a path through a module `crate`, so the format took a version of its own.
///
/// `krs-difference/3` reads `path`, `cell` and `segments` differently from `krs-difference/2` in
/// two places ([module documentation](crate::ends#the-first-difference)): a constructor's field
/// is named with the constructor, as a position of the value's document names it (`f.Flags.zf`,
/// `bus[0].Idles.count`, where version 2 wrote `f.zf` and `bus[0].count`); and an instance of a
/// `Map` collection is named by its key and paired with the other side's instance of that key
/// (`procs.process[1].ticks`, where version 2 wrote the instance's whole text and compared the
/// instances as a set's). A reader of version 2 would take `.Flags` for a field and `[1]` for a
/// `List` position, so the format takes the next version.
pub const DIFFERENCE_FORMAT: &str = "krs-difference/3";

/// The most characters of one value's text a [`Difference`] shows.
pub const VALUE_CAP: usize = 2000;

/// How a complete run ended: its halt word, and for [`Halt::Stopped`] the stop rule's KRS item.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct EndClass {
    /// The halt: [`Halt::is_complete`] holds of it.
    pub halt: Halt,
    /// The stop rule's KRS item for a stopped end, by the one name of it that selects its rules
    /// alone ([module documentation](crate::ends#end-documents)): `crate::machine::boundary`
    /// for an item of the definition's main package, `lang::step` for a dependency's, a K label
    /// where neither selects the item alone. Two classes name one item exactly when their names
    /// are equal. `None` for every other end, and for a stopped run that does not name its rule
    /// ([`crate::Stop::rule`]) or whose rule's item no name selects alone.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule: Option<String>,
}

/// The content of one cell of an end.
///
/// Its order (`Ord`) is a total order consistent with equality, which orders the instances of a
/// set collection that have the same canonical text.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum EndCell {
    /// A leaf cell's value.
    Leaf(Value),
    /// A group cell's cells.
    Group(EndCells),
    /// An optional cell: absent, or its content (a [`Self::Leaf`] or a [`Self::Group`]).
    Optional(Option<Box<EndCell>>),
    /// A repeated cell's instances, each a [`Self::Group`] (a [`Self::Leaf`] for a repeated leaf
    /// cell): in the collection's order for a `List` collection, otherwise in the order of their
    /// canonical text, each once.
    Repeated(Vec<EndCell>),
}

/// The cells of an end below one root (the configuration, a group, an instance), by Rust field,
/// in declaration order. An end read from a document may lack cells it does not state.
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct EndCells(Vec<(String, EndCell)>);

impl EndCells {
    /// The cell declared by `field`, if stated.
    #[must_use]
    pub fn get(&self, field: &str) -> Option<&EndCell> {
        self.0
            .iter()
            .find_map(|(name, cell)| (name == field).then_some(cell))
    }

    /// The stated cells, by field, in declaration order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &EndCell)> {
        self.0.iter().map(|(field, cell)| (field.as_str(), cell))
    }

    /// Whether no cell is stated.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// One end: its class and its cells.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct End {
    /// How the run ended.
    pub class: EndClass,
    /// The cells; none for an `undefined` end.
    pub cells: EndCells,
}

impl End {
    /// The value of the leaf cell at `path` (fields joined by `.`, through groups and present
    /// optional cells, as [`crate::StateView::value`] reads it); `None` when the end does not
    /// state it, an optional cell on the way is absent, or the path passes through a repeated
    /// cell.
    #[must_use]
    pub fn value(&self, path: &str) -> Option<&Value> {
        let mut cells = &self.cells;
        let mut segments = path.split('.').peekable();
        while let Some(segment) = segments.next() {
            let mut cell = cells.get(segment)?;
            if let EndCell::Optional(content) = cell {
                cell = content.as_deref()?;
            }
            match (cell, segments.peek()) {
                (EndCell::Leaf(value), None) => return Some(value),
                (EndCell::Group(inner), Some(_)) => cells = inner,
                _ => return None,
            }
        }
        None
    }
}

/// The ends of one producer: a run's (at most one) or a search's final states.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Ends {
    /// The ends, in the producer's order.
    pub ends: Vec<End>,
    /// Why the set may lack ends of the definition from the same input (`None` when it is
    /// complete): an inconclusive halt, a constrained state, a search cut by its bounds.
    pub incomplete: Option<String>,
}

impl Ends {
    /// The complete set of one end, as an end document states.
    #[must_use]
    pub fn one(end: End) -> Self {
        Self {
            ends: vec![end],
            incomplete: None,
        }
    }

    /// The empty, incomplete set: no end is known, for `reason`.
    #[must_use]
    pub fn none(reason: impl Into<String>) -> Self {
        Self {
            ends: Vec::new(),
            incomplete: Some(reason.into()),
        }
    }

    /// The ends of this set that the definition reaches, which an expectation is checked
    /// against ([module documentation](crate::ends#results)): every end but a `depth-bound`
    /// one, a state at which a step budget ended the run or the search before any step from it,
    /// and from which the definition may go on. Leaving one out makes the set incomplete, for that reason unless it
    /// already was. Borrowed when the set holds no `depth-bound` end.
    #[must_use]
    pub fn reached(&self) -> Cow<'_, Self> {
        if self
            .ends
            .iter()
            .all(|end| end.class.halt != Halt::DepthBound)
        {
            return Cow::Borrowed(self);
        }
        Cow::Owned(Self {
            ends: self
                .ends
                .iter()
                .filter(|end| end.class.halt != Halt::DepthBound)
                .cloned()
                .collect(),
            incomplete: Some(self.incomplete.clone().unwrap_or_else(|| {
                "a step budget ended the run at a `depth-bound` state, from which it took no \
                 step, so the state is not known to be an end of the definition: it may go on \
                 from there"
                    .to_owned()
            })),
        })
    }
}

/// One cell the configuration declares ([`Semantics::cells`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellInfo {
    /// Its declared path: the Rust fields from the configuration joined by `.`, through repeated
    /// cells without an index (`threads.thread.count`).
    pub path: String,
    /// `None` for a cell that occurs once in its parent, else optional or repeated.
    pub multiplicity: Option<CellMultiplicity>,
    /// A repeated cell's collection type.
    pub collection: Option<CellCollectionType>,
    /// A leaf cell's declared type (the position its value's document is written at); `None` for
    /// a group cell.
    pub ty: Option<InputType>,
    /// Whether the cell, or a cell holding it, carries `unobservable`.
    pub unobservable: bool,
    /// The KORE symbol of the cell's label (`Lbl'-LT-'pc'-GT-'`), which a configuration's
    /// application of the cell is headed by.
    pub symbol: String,
}

/// What a comparison compares ([module documentation](crate::ends#compared-cells)).
#[derive(Clone, Debug, Default)]
pub struct Comparison {
    /// The compared cells by declared path; `None` compares every leaf cell that is not
    /// unobservable.
    pub compare: Option<Vec<String>>,
    /// The views applied to compared cells, resolved ([`Semantics::cell_views`]) and evaluated
    /// at the ends compared ([`CellViews::evaluate`]); none by default
    /// ([module documentation](crate::views)).
    pub views: CellViews,
}

/// One side of a comparison: a name for reports (`expected`/`actual`, `left`/`right`,
/// `baseline`/`mutant`) and its ends.
#[derive(Clone, Copy, Debug)]
pub struct Side<'a> {
    /// The name a difference shows for the side.
    pub name: &'a str,
    /// Its ends.
    pub ends: &'a Ends,
}

/// The result of a comparison.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Compared {
    /// The sides agree on the class and every compared cell.
    Equal,
    /// They do not, first here.
    Differs(Box<Difference>),
    /// Nothing can be concluded, for this reason: no end to compare, an incomplete set where
    /// completeness decides, or a stopped end that does not name its stop rule.
    Inconclusive(String),
}

/// Where a difference is.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum DifferenceAt {
    /// The ends' classes differ.
    Class,
    /// A compared cell differs.
    Cell,
}

/// A value as a difference shows it ([module documentation](crate::ends#the-first-difference)).
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Rendered {
    /// `document` (its canonical document), `k` (K text), or `kore` (KORE, where the printer
    /// warns).
    pub rendering: &'static str,
    /// The canonical document, when it is shown whole.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub document: Option<Json>,
    /// The text: the K or KORE text, or the window of a cut document's canonical text.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub text: Option<String>,
    /// For K or KORE text, the position of the part with no document inside the shown value, in
    /// the notation of [`crate::InputError`]'s positions; empty for the whole value.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub opaque: Option<String>,
    /// Whether the text was cut to [`VALUE_CAP`] characters.
    pub truncated: bool,
    /// The characters cut before the shown text.
    pub offset: usize,
}

/// One side of a [`Difference`].
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DifferenceSide {
    /// The side's name.
    pub name: String,
    /// How many ends the side has.
    pub ends: usize,
    /// Whether its set of ends is complete.
    pub complete: bool,
    /// The class of the side's end the difference shows.
    pub class: EndClass,
    /// Its value at the difference's path; `None` at the class, and for a side that lacks the
    /// position (a map key, a list index, an instance, a set element the other side holds).
    pub value: Option<Rendered>,
}

/// The first difference between two ends, in the format [`DIFFERENCE_FORMAT`].
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Difference {
    /// [`DIFFERENCE_FORMAT`].
    pub format: &'static str,
    /// Whether the classes or a cell differ.
    pub at: DifferenceAt,
    /// The differing cell's path, instances indexed (`threads.thread[0].count`) or keyed
    /// (`procs.process[1].ticks`); `None` at the class.
    pub cell: Option<String>,
    /// The cell's path followed by the segments; `None` at the class.
    pub path: Option<String>,
    /// The segments inside the cell's value (`.Flags.zf`, `[2]`, `["B"]`, `{<text>}`).
    pub segments: Vec<String>,
    /// The side whose end is outside the other's set (for an expectation, the actual side).
    pub outside: String,
    /// The other compared cells that differ, in declaration order.
    pub also_differ: Vec<String>,
    /// The compared leaf cells, by declared path.
    pub compared: Vec<String>,
    /// The leaf cells not compared, by declared path.
    pub not_compared: Vec<String>,
    /// The views applied: the function by declared cell path.
    pub views: BTreeMap<String, String>,
    /// The first side.
    pub left: DifferenceSide,
    /// The second side.
    pub right: DifferenceSide,
}

/// Why ends cannot be read, written or compared.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EndError {
    /// A document or a comparison names a cell the configuration does not declare.
    UnknownCell {
        /// The path as written.
        path: String,
        /// The declared paths there.
        known: Vec<String>,
    },
    /// A comparison names an unobservable cell, or one inside an unobservable cell.
    Unobservable {
        /// The path as written.
        path: String,
    },
    /// A comparison compares cells of a `Map` collection's instances but not the whole of their
    /// key ([module documentation](crate::ends#compared-cells)).
    UncomparedKey {
        /// The collection's declared path.
        collection: String,
        /// The key cell's declared path.
        key: String,
        /// Whether the key is, or holds, an unobservable cell, which no comparison compares.
        unobservable: bool,
    },
    /// An end does not state a compared cell.
    MissingCell {
        /// The side's name.
        side: String,
        /// The cell's path, instances indexed or keyed.
        path: String,
        /// The cell's declared type, or what kind of cell it is.
        what: String,
    },
    /// A document, or a part of one, is no end of the definition.
    Document {
        /// Where: `halt`, `cells.cpu.regs`, `cells.threads.thread[1].id`.
        position: String,
        /// Why.
        message: String,
    },
    /// A view that cannot be applied: its cell or function does not fit, or it has no value at
    /// an end ([module documentation](crate::views)).
    View {
        /// The viewed cell's declared path.
        cell: String,
        /// The view's function as named.
        function: String,
        /// Why.
        message: String,
    },
    /// A view whose evaluation at an end stopped before it ended, for the caller's budget or
    /// another stop of the backend, or ended short of a value after the solver answered
    /// `Unknown` ([`CellViews::evaluate_within`]): whether it has a value there is not known, so a
    /// comparison under it is inconclusive, not refused, when no view refuses at another value.
    ViewStopped {
        /// The viewed cell's declared path.
        cell: String,
        /// The view's function as named.
        function: String,
        /// Where, and the budget.
        message: String,
    },
    /// A state that is no configuration of the definition, or results that are no ends.
    State(String),
}

impl fmt::Display for EndError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownCell { path, known } => write!(
                formatter,
                "no cell has the path `{path}`; the cells are {}",
                known.join(", ")
            ),
            Self::Unobservable { path } => write!(
                formatter,
                "the cell `{path}` is unobservable: no use of the definition may observe it, so it is never compared"
            ),
            Self::UncomparedKey {
                collection,
                key,
                unobservable,
            } => {
                write!(
                    formatter,
                    "the comparison compares cells of the Map collection `{collection}` but not the whole of its key `{key}`: a Map collection's instances are paired by their key, the instance's first cell and its identity, so a comparison of their cells compares the key"
                )?;
                if *unobservable {
                    formatter.write_str(
                        ", and the key is, or holds, an unobservable cell, which no comparison compares; leave the collection's cells out of the comparison",
                    )
                } else {
                    write!(formatter, "; compare `{key}` too")
                }
            }
            Self::MissingCell { side, path, what } => write!(
                formatter,
                "the {side} end does not state the compared cell `{path}` ({what})"
            ),
            Self::Document { position, message } if position.is_empty() => {
                formatter.write_str(message)
            }
            Self::Document { position, message } => write!(formatter, "`{position}`: {message}"),
            Self::View {
                cell,
                function,
                message,
            }
            | Self::ViewStopped {
                cell,
                function,
                message,
            } => write!(
                formatter,
                "the view `{function}` of the cell `{cell}`: {message}"
            ),
            Self::State(message) => formatter.write_str(message),
        }
    }
}

impl std::error::Error for EndError {}

impl From<ValueError> for EndError {
    fn from(error: ValueError) -> Self {
        Self::State(error.to_string())
    }
}

/// Which cells a comparison compares, parallel to the cell tree: whether a compared leaf is at or
/// below each cell.
#[derive(Clone, Debug)]
struct Selection {
    compared: bool,
    children: Vec<Selection>,
}

/// A part of one side at a differing cell.
#[derive(Clone, Copy)]
enum Part<'e> {
    /// A leaf's value at its type.
    Value(&'e Value),
    /// An optional cell, shown as `[]` or `[content]`.
    Optional(&'e CellNode, &'e EndCell),
    /// An instance of a repeated cell.
    Instance(&'e CellNode, &'e EndCell),
}

/// A compared cell at which two ends differ.
struct Unit<'e> {
    cell: String,
    segments: Vec<String>,
    ty: InputType,
    /// The value index that writes the cell's values: the observer's for a viewed cell.
    index: &'e ValueIndex,
    left: Option<Part<'e>>,
    right: Option<Part<'e>>,
    /// The compared leaves that differ there ([module documentation](crate::ends#results)).
    weight: usize,
}

/// A part of a cell's content with no document: its position inside the content, in the
/// notation of [`crate::InputError`]'s positions, and the encoder's refusal.
struct Refused {
    position: String,
    error: EncodeError,
}

impl Refused {
    /// The refusal seen from the content that holds this one at `segment`.
    fn under(mut self, segment: &str) -> Self {
        self.position.insert_str(0, segment);
        self
    }
}

/// The compared leaves in a projected cell's content: its leaves, since projection keeps only
/// compared cells.
fn leaves(content: &EndCell) -> usize {
    match content {
        EndCell::Leaf(_) => 1,
        EndCell::Group(cells) => cells.iter().map(|(_, cell)| leaves(cell)).sum(),
        EndCell::Optional(content) => content.as_deref().map_or(0, leaves),
        EndCell::Repeated(instances) => instances.iter().map(leaves).sum(),
    }
}

fn declared_paths(nodes: &[CellNode], prefix: &str, output: &mut Vec<String>) {
    for node in nodes {
        let path = format!("{prefix}{}", node.field);
        output.push(path.clone());
        declared_paths(&node.children, &format!("{path}."), output);
    }
}

fn leaf_type(index: &ValueIndex, node: &CellNode) -> Option<InputType> {
    node.content.as_ref().map(|(sort, arguments)| {
        input_type(index, sort, arguments).unwrap_or_else(InputType::untyped)
    })
}

/// What a cell is, for a refusal that names it: a leaf's type, or its kind.
fn describe(index: &ValueIndex, node: &CellNode) -> String {
    match (node.multiplicity, leaf_type(index, node)) {
        (Some(CellMultiplicity::Star), _) => "a repeated cell".to_owned(),
        (Some(CellMultiplicity::Optional), Some(ty)) => format!("an optional cell of {ty}"),
        (Some(CellMultiplicity::Optional), None) => "an optional group cell".to_owned(),
        (None, Some(ty)) => ty.to_string(),
        (None, None) => "a group cell".to_owned(),
    }
}

const fn is_list(node: &CellNode) -> bool {
    matches!(node.collection, Some(CellCollectionType::List))
}

/// The key cell of the instances of `node` when it is a `Map` collection: the instance's first
/// cell, its identity; `None` for any other cell, and for a repeated leaf cell, which has no cell
/// of its own (KRS declares every repeated cell as a group, and a repeated leaf cell's instances
/// compare as a set's).
fn map_key(node: &CellNode) -> Option<&CellNode> {
    match (node.multiplicity, node.collection) {
        (Some(CellMultiplicity::Star), Some(CellCollectionType::Map)) => node.children.first(),
        _ => None,
    }
}

/// The key of `instance`, an instance of the cell `node`: its key cell's content, where `node`
/// is a `Map` collection and the instance states its key.
fn instance_key<'e>(node: &CellNode, instance: &'e EndCell) -> Option<&'e EndCell> {
    let key = map_key(node)?;
    let EndCell::Group(cells) = instance else {
        return None;
    };
    cells.get(&key.field)
}

/// Whether the selection of `node` compares every leaf at or below it.
fn whole(selection: &Selection, node: &CellNode) -> bool {
    if node.children.is_empty() {
        selection.compared
    } else {
        selection
            .children
            .iter()
            .zip(&node.children)
            .all(|(selection, child)| whole(selection, child))
    }
}

/// Whether `node` is, or holds, an unobservable cell.
fn holds_unobservable(node: &CellNode) -> bool {
    node.unobservable || node.children.iter().any(holds_unobservable)
}

/// Refuse a selection that compares a cell of a `Map` collection's instances but not the whole of
/// their key ([module documentation](crate::ends#compared-cells)).
fn check_keys(nodes: &[CellNode], selection: &[Selection], prefix: &str) -> Result<(), EndError> {
    for (node, selected) in nodes.iter().zip(selection) {
        let path = format!("{prefix}{}", node.field);
        if selected.compared
            && let Some(key) = map_key(node)
            && !whole(&selected.children[0], key)
        {
            return Err(EndError::UncomparedKey {
                key: format!("{path}.{}", key.field),
                collection: path,
                unobservable: holds_unobservable(key),
            });
        }
        check_keys(&node.children, &selected.children, &format!("{path}."))?;
    }
    Ok(())
}

fn tagged(name: &str, body: Json) -> Json {
    let mut object = JsonMap::new();
    object.insert(name.to_owned(), body);
    Json::Object(object)
}

/// The first end of `from` that `to` does not hold.
fn outside<'s>(from: &'s [(String, End)], to: &[(String, End)]) -> Option<&'s End> {
    from.iter()
        .map(|(_, end)| end)
        .find(|end| !to.iter().any(|(_, other)| other == *end))
}

/// The first index at which two character sequences differ (the shorter's length when one is a
/// prefix of the other).
fn first_difference(left: &[char], right: &[char]) -> usize {
    left.iter()
        .zip(right)
        .position(|(a, b)| a != b)
        .unwrap_or_else(|| left.len().min(right.len()))
}

/// The window of `text` from character `start`, at most [`VALUE_CAP`] characters: the text,
/// whether it was cut, and the characters cut before it.
fn window(text: &[char], start: usize) -> (String, bool, usize) {
    let start = start.min(text.len());
    let end = (start + VALUE_CAP).min(text.len());
    (
        text[start..end].iter().collect(),
        start > 0 || end < text.len(),
        start,
    )
}

/// The compared definition seen through a comparison's views: a viewed leaf cell holds the
/// view's value, written at the view's result type by the observer's value index.
struct Lens<'s> {
    semantics: &'s Semantics,
    views: &'s CellViews,
}

impl Deref for Lens<'_> {
    type Target = Semantics;

    fn deref(&self) -> &Semantics {
        self.semantics
    }
}

impl Semantics {
    const fn lens<'s>(&'s self, views: &'s CellViews) -> Lens<'s> {
        Lens {
            semantics: self,
            views,
        }
    }
}

/// Cut two shown texts by the rule of the
/// [module documentation](crate::ends#the-first-difference).
fn cut(left: Option<&str>, right: Option<&str>) -> [Option<(String, bool, usize)>; 2] {
    let left = left.map(|text| text.chars().collect::<Vec<_>>());
    let right = right.map(|text| text.chars().collect::<Vec<_>>());
    let start = match (&left, &right) {
        (Some(left), Some(right)) if left.len() > VALUE_CAP || right.len() > VALUE_CAP => {
            first_difference(left, right).saturating_sub(VALUE_CAP / 2)
        }
        _ => 0,
    };
    [
        left.map(|text| window(&text, start)),
        right.map(|text| window(&text, start)),
    ]
}

impl Semantics {
    /// Every cell the configuration declares, in pre-order of the cell tree (a group before its
    /// cells, a repeated cell before its instances' cells).
    #[must_use]
    pub fn cells(&self) -> Vec<CellInfo> {
        fn walk(
            index: &ValueIndex,
            nodes: &[CellNode],
            prefix: &str,
            unobservable: bool,
            output: &mut Vec<CellInfo>,
        ) {
            for node in nodes {
                let path = format!("{prefix}{}", node.field);
                let unobservable = unobservable || node.unobservable;
                output.push(CellInfo {
                    path: path.clone(),
                    multiplicity: node.multiplicity,
                    collection: node.collection,
                    ty: leaf_type(index, node),
                    unobservable,
                    symbol: node.symbol.clone(),
                });
                walk(
                    index,
                    &node.children,
                    &format!("{path}."),
                    unobservable,
                    output,
                );
            }
        }
        let mut output = Vec::new();
        walk(&self.values, self.values.cells(), "", false, &mut output);
        output
    }

    /// The end of a run: none, in an incomplete set, for an inconclusive halt or a constrained
    /// state.
    ///
    /// # Errors
    ///
    /// Returns [`EndError::State`] for a state that is not one configuration of this definition.
    pub fn end_of(&self, report: &RunReport) -> Result<Ends, EndError> {
        let halt = report.halt;
        if !halt.is_complete() {
            return Ok(Ends::none(format!(
                "the run halted `{}`, which is no end of the definition",
                halt.as_str()
            )));
        }
        let rule = (halt == Halt::Stopped)
            .then(|| {
                report
                    .stop
                    .as_ref()
                    .and_then(|stop| stop.rule.as_ref())
                    .and_then(|rule| self.rules.class_name(&rule.rule_id))
            })
            .flatten();
        let class = EndClass { halt, rule };
        if halt == Halt::Undefined {
            return Ok(Ends::one(End {
                class,
                cells: EndCells::default(),
            }));
        }
        let views = view::views(&self.values, report.state.kore())?;
        let [View::State(state)] = views.as_slice() else {
            return Err(EndError::State(format!(
                "a `{}` run ends in one configuration, not {} states",
                halt.as_str(),
                views.len()
            )));
        };
        if !state.constraints().is_empty() {
            return Ok(Ends::none(
                "the run's end carries a constraint: it denotes the configurations that satisfy it, which a comparison of values does not decide",
            ));
        }
        let cells = self.read_state(state.term())?;
        Ok(Ends::one(End { class, cells }))
    }

    /// The ends of a final-state search (`=>!`): each solution, `depth-bound` where it is at the
    /// search's depth bound, whether or not it has a successor, and `stuck` otherwise, `undefined` for `\bottom`; incomplete when the
    /// search did not explore every path within its bounds or dropped solutions.
    ///
    /// # Errors
    ///
    /// Returns [`EndError::State`] for a search of another mode, whose states are not ends, and
    /// for a state that is not a configuration of this definition.
    pub fn ends_of(
        &self,
        report: &SearchReport,
        options: &SearchOptions,
    ) -> Result<Ends, EndError> {
        if options.mode != SearchMode::Final {
            return Err(EndError::State(format!(
                "a search of mode `{}` returns reachable states, not ends; search with mode `final`",
                options.mode.as_str()
            )));
        }
        let mut ends = Vec::new();
        let mut constrained = false;
        for solution in &report.solutions {
            let halt = if options.depth.is_some_and(|bound| solution.depth >= bound) {
                Halt::DepthBound
            } else {
                Halt::Stuck
            };
            for state in view::views(&self.values, solution.state.kore())? {
                match state {
                    View::Bottom => ends.push(End {
                        class: EndClass {
                            halt: Halt::Undefined,
                            rule: None,
                        },
                        cells: EndCells::default(),
                    }),
                    View::State(state) if !state.constraints().is_empty() => constrained = true,
                    View::State(state) => ends.push(End {
                        class: EndClass { halt, rule: None },
                        cells: self.read_state(state.term())?,
                    }),
                }
            }
        }
        let incomplete = if constrained {
            Some("a final state of the search carries a constraint, which a comparison of values does not decide".to_owned())
        } else if report.complete {
            None
        } else {
            Some("the search did not explore every path within its bounds, or dropped solutions past its limit".to_owned())
        };
        Ok(Ends { ends, incomplete })
    }

    fn read_state(&self, configuration: &Pattern) -> Result<EndCells, EndError> {
        self.read_stated(configuration, &BTreeSet::new())
    }

    /// The cells of `configuration`, except the cells whose symbols are in `unstated`, which the
    /// result does not state.
    fn read_stated(
        &self,
        configuration: &Pattern,
        unstated: &BTreeSet<&str>,
    ) -> Result<EndCells, EndError> {
        let mut symbols = Vec::new();
        cell_symbols(self.values.cells(), &mut symbols);
        self.read_cells(self.values.cells(), configuration, &symbols, unstated)
    }

    /// The end of class `class` whose cells are `configuration`'s, a configuration of this
    /// definition, as a comparison of configurations that leaves some cells out holds it: each
    /// cell whose symbol is in `unstated` is not stated, whatever the configuration holds at its
    /// position (the comparison replaced it by a placeholder such as `\top` of its sort, which
    /// denotes every content and so states none), as an end document that omits the cell does
    /// not state it. Every other cell is read as [`Self::end_of`] reads a run's state.
    ///
    /// # Errors
    ///
    /// Returns [`EndError::State`] for a configuration whose stated cells are not this
    /// definition's: a cell missing or repeated against its multiplicity, a content that does
    /// not decode.
    pub fn read_configuration(
        &self,
        configuration: &Pattern,
        class: EndClass,
        unstated: &BTreeSet<&str>,
    ) -> Result<End, EndError> {
        Ok(End {
            class,
            cells: self.read_stated(configuration, unstated)?,
        })
    }

    fn read_cells(
        &self,
        nodes: &[CellNode],
        parent: &Pattern,
        symbols: &[&str],
        unstated: &BTreeSet<&str>,
    ) -> Result<EndCells, EndError> {
        let below = cells_below(parent, symbols);
        let mut cells = Vec::with_capacity(nodes.len());
        for node in nodes {
            if unstated.contains(node.symbol.as_str()) {
                continue;
            }
            let mut found = below
                .iter()
                .filter(|pattern| {
                    matches!(pattern, Pattern::Application { symbol, .. } if symbol.name == node.symbol)
                })
                .map(|pattern| self.read_content(node, pattern, symbols, unstated))
                .collect::<Result<Vec<_>, _>>()?;
            let count = found.len();
            let cell = match (node.multiplicity, found.pop()) {
                (Some(CellMultiplicity::Star), last) => {
                    found.extend(last);
                    EndCell::Repeated(self.lens(&CellViews::default()).instances(node, found))
                }
                (Some(CellMultiplicity::Optional), last) if found.is_empty() => {
                    EndCell::Optional(last.map(Box::new))
                }
                (None, Some(cell)) if found.is_empty() => cell,
                (multiplicity, _) => {
                    return Err(EndError::State(format!(
                        "the state holds {count} cells `{}`, not {}",
                        node.field,
                        if multiplicity.is_some() {
                            "at most one"
                        } else {
                            "one"
                        }
                    )));
                }
            };
            cells.push((node.field.clone(), cell));
        }
        Ok(EndCells(cells))
    }

    /// A cell application's content: a leaf's value, or a group's cells.
    fn read_content(
        &self,
        node: &CellNode,
        pattern: &Pattern,
        symbols: &[&str],
        unstated: &BTreeSet<&str>,
    ) -> Result<EndCell, EndError> {
        if node.children.is_empty() {
            let Pattern::Application { arguments, .. } = pattern else {
                unreachable!("cells are found as applications")
            };
            let [content] = arguments.as_slice() else {
                return Err(EndError::State(format!("{pattern} is not a leaf cell")));
            };
            Ok(EndCell::Leaf(self.values.decode(content)?))
        } else {
            Ok(EndCell::Group(self.read_cells(
                &node.children,
                pattern,
                symbols,
                unstated,
            )?))
        }
    }
}

impl Semantics {
    /// The path of `instance`, the instance at `position` of an end's instances of the repeated
    /// cell `node` at the path `path`, as a difference names it: a `List` collection's by its
    /// index, a `Map` collection's by its key, a set collection's (and a `Map` instance that
    /// does not state its key) by its canonical text. The instance is the end's own, not
    /// viewed, so it is named without the views.
    pub(crate) fn instance_path(
        &self,
        node: &CellNode,
        path: &str,
        position: usize,
        instance: &EndCell,
    ) -> String {
        let no_views = CellViews::default();
        let unviewed = self.lens(&no_views);
        if is_list(node) {
            format!("{path}[{position}]")
        } else if let Some(key) = instance_key(node, instance) {
            format!("{path}[{}]", unviewed.key_text(node, key))
        } else {
            format!("{path}{{{}}}", unviewed.order_text(node, instance))
        }
    }
}

impl Lens<'_> {
    /// A repeated cell's instances in their order: the collection's for a `List` collection, the
    /// order of their canonical text otherwise, each once.
    fn instances(&self, node: &CellNode, instances: Vec<EndCell>) -> Vec<EndCell> {
        if is_list(node) {
            return instances;
        }
        let mut keyed = instances
            .into_iter()
            .map(|instance| (self.order_text(node, &instance), instance))
            .collect::<Vec<_>>();
        keyed.sort_by(|(x, left), (y, right)| {
            x.as_bytes().cmp(y.as_bytes()).then_with(|| left.cmp(right))
        });
        keyed.dedup_by(|(_, left), (_, right)| left == right);
        keyed.into_iter().map(|(_, instance)| instance).collect()
    }

    /// The text that orders an instance (or, with the configuration's root, an end) and names it
    /// in a path: the canonical text of its document, where a value with no document is written
    /// `{"$kore": <its KORE>}`, a form no document has. Distinct values with no document may share
    /// a text (one whose KORE cannot be written is written as the reason), so the order breaks
    /// ties by the content itself ([`Self::instances`]).
    fn order_text(&self, node: &CellNode, content: &EndCell) -> String {
        canonical_text(
            &self
                .content_document(node, content, false)
                .unwrap_or(Json::Null),
        )
    }

    /// The text that names an instance of the `Map` collection `node` by its key `key` in a path
    /// and orders it among the collection's keys (`2`, `"boot"`): a leaf key's text as a value
    /// map's key segment writes it, at the key cell's declared type; a group key's canonical text.
    fn key_text(&self, node: &CellNode, key: &EndCell) -> String {
        let Some(key_node) = map_key(node) else {
            unreachable!("only a Map collection's instances have keys")
        };
        match key {
            EndCell::Leaf(value) => {
                let (index, ty) = self.leaf(key_node);
                self.value_text(index, value, &ty)
            }
            content => self.order_text(key_node, content),
        }
    }
}

impl Semantics {
    /// Read an end document ([module documentation](crate::ends#end-documents)): every stated
    /// cell decoded at its declared type, the stop rule resolved among the definition's rewrite
    /// rules. Which cells it must state is a comparison's question.
    ///
    /// # Errors
    ///
    /// Returns [`EndError::UnknownCell`] for a path the configuration does not declare (listing
    /// the cells there), and [`EndError::Document`] for anything else that is no end document, a
    /// `rule` that names no rewrite rule of the definition included.
    pub fn read_end(&self, document: &Json) -> Result<End, EndError> {
        self.read_end_in(document, None, &mut NoFiles)
    }

    /// Read an end document as [`Self::read_end`] does, where its values may name files
    /// (`$file`, `$data-file`): `files` reads each, its path relative to the document that holds
    /// the end, the file `from` (the resolved name an earlier read of `files` returned), or the top
    /// document (`None`).
    ///
    /// # Errors
    ///
    /// Fails as [`Self::read_end`] does, and with [`EndError::Document`] at a value whose file
    /// cannot be read or includes itself.
    pub fn read_end_in(
        &self,
        document: &Json,
        from: Option<&str>,
        files: &mut dyn InputFiles,
    ) -> Result<End, EndError> {
        let refuse = |position: &str, message: String| EndError::Document {
            position: position.to_owned(),
            message,
        };
        let Json::Object(object) = document else {
            return Err(refuse(
                "",
                "an end document is a table of `halt`, `rule` and `cells`".to_owned(),
            ));
        };
        if let Some(key) = object
            .keys()
            .find(|key| !matches!(key.as_str(), "halt" | "rule" | "cells"))
        {
            return Err(refuse(
                key,
                "an end document holds `halt`, `rule` and `cells` only".to_owned(),
            ));
        }
        let words = [
            Halt::Stuck,
            Halt::DepthBound,
            Halt::Undefined,
            Halt::Stopped,
        ];
        let halt = match object.get("halt") {
            Some(Json::String(word)) => words
                .into_iter()
                .find(|halt| halt.as_str() == word)
                .ok_or_else(|| {
                    refuse(
                        "halt",
                        format!(
                            "`{word}` is not the halt of an end; an end halts {}",
                            words.map(Halt::as_str).join(", ")
                        ),
                    )
                })?,
            Some(_) => return Err(refuse("halt", "the halt is a string".to_owned())),
            None => return Err(refuse("halt", "an end states its halt".to_owned())),
        };
        let rule = match (object.get("rule"), halt) {
            (Some(Json::String(rule)), Halt::Stopped) => Some(
                self.rules
                    .stop_item(rule)
                    .map_err(|message| refuse("rule", message))?,
            ),
            (Some(_), Halt::Stopped) => {
                return Err(refuse(
                    "rule",
                    "the rule is a name a stop accepts, a string".to_owned(),
                ));
            }
            (None, Halt::Stopped) => {
                return Err(refuse(
                    "rule",
                    "a stopped end names the stop rule's KRS item".to_owned(),
                ));
            }
            (Some(_), _) => {
                return Err(refuse("rule", "only a stopped end names a rule".to_owned()));
            }
            (None, _) => None,
        };
        let cells = match object.get("cells") {
            None => EndCells::default(),
            Some(Json::Object(cells)) if halt == Halt::Undefined && !cells.is_empty() => {
                return Err(refuse(
                    "cells",
                    "an undefined end has no cells: its state is \\bottom".to_owned(),
                ));
            }
            Some(Json::Object(cells)) => {
                self.read_document_cells(self.values.cells(), cells, "", from, files)?
            }
            Some(_) => {
                return Err(refuse(
                    "cells",
                    "the cells are a table by Rust field".to_owned(),
                ));
            }
        };
        Ok(End {
            class: EndClass { halt, rule },
            cells,
        })
    }

    fn read_document_cells(
        &self,
        nodes: &[CellNode],
        object: &JsonMap<String, Json>,
        prefix: &str,
        from: Option<&str>,
        files: &mut dyn InputFiles,
    ) -> Result<EndCells, EndError> {
        if let Some(field) = object
            .keys()
            .find(|field| !nodes.iter().any(|node| &node.field == *field))
        {
            let mut known = Vec::new();
            for node in nodes {
                known.push(format!("{prefix}{}", node.field));
            }
            return Err(EndError::UnknownCell {
                path: format!("{prefix}{field}"),
                known,
            });
        }
        let mut cells = Vec::new();
        for node in nodes {
            let Some(document) = object.get(&node.field) else {
                continue;
            };
            let path = format!("{prefix}{}", node.field);
            let refuse = |message: &str| EndError::Document {
                position: format!("cells.{path}"),
                message: message.to_owned(),
            };
            let cell = match node.multiplicity {
                None => self.read_document_content(node, document, &path, from, files)?,
                Some(CellMultiplicity::Optional) => match document {
                    Json::Array(items) if items.is_empty() => EndCell::Optional(None),
                    Json::Array(items) if items.len() == 1 => {
                        EndCell::Optional(Some(Box::new(self.read_document_content(
                            node,
                            &items[0],
                            &format!("{path}[0]"),
                            from,
                            files,
                        )?)))
                    }
                    _ => {
                        return Err(refuse(
                            "an optional cell is `[]` (absent) or `[content]` (present)",
                        ));
                    }
                },
                Some(CellMultiplicity::Star) => {
                    let Json::Array(items) = document else {
                        return Err(refuse("a repeated cell is the array of its instances"));
                    };
                    let instances = items
                        .iter()
                        .enumerate()
                        .map(|(position, item)| {
                            self.read_document_content(
                                node,
                                item,
                                &format!("{path}[{position}]"),
                                from,
                                files,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let no_views = CellViews::default();
                    let lens = self.lens(&no_views);
                    for (position, instance) in instances.iter().enumerate() {
                        let Some(key) = instance_key(node, instance) else {
                            continue;
                        };
                        if let Some(first) = instances[..position]
                            .iter()
                            .position(|other| instance_key(node, other) == Some(key))
                        {
                            return Err(EndError::Document {
                                position: format!("cells.{path}[{position}]"),
                                message: format!(
                                    "the instance has the key {} of the instance at [{first}]: a Map collection holds one instance per key, its first cell `{}`",
                                    lens.key_text(node, key),
                                    node.children[0].field
                                ),
                            });
                        }
                    }
                    EndCell::Repeated(lens.instances(node, instances))
                }
            };
            cells.push((node.field.clone(), cell));
        }
        Ok(EndCells(cells))
    }

    /// One cell's (or instance's) content in a document: a leaf's value at its declared type, or
    /// a group's table.
    fn read_document_content(
        &self,
        node: &CellNode,
        document: &Json,
        path: &str,
        from: Option<&str>,
        files: &mut dyn InputFiles,
    ) -> Result<EndCell, EndError> {
        match leaf_type(&self.values, node) {
            Some(ty) => decode_value_in(&self.values, files, from, document, &ty)
                .map(EndCell::Leaf)
                .map_err(|error| EndError::Document {
                    position: format!("cells.{path}"),
                    message: error.to_string(),
                }),
            None => match document {
                Json::Object(object) => Ok(EndCell::Group(self.read_document_cells(
                    &node.children,
                    object,
                    &format!("{path}."),
                    from,
                    files,
                )?)),
                _ => Err(EndError::Document {
                    position: format!("cells.{path}"),
                    message: "a group cell is a table of its cells by Rust field".to_owned(),
                }),
            },
        }
    }

    /// The end document of `end` ([module documentation](crate::ends#end-documents)), which
    /// [`Self::read_end`] reads back as `end`.
    ///
    /// # Errors
    ///
    /// Returns [`EndError::Document`] at `rule` for a stopped end whose class names no item
    /// ([`EndClass::rule`] is `None`), since a stopped end's document names its stop rule's item
    /// and no name would read back as this end's class; else naming the first cell whose value has
    /// no document at its type, with the encoder's reason.
    pub fn end_document(&self, end: &End) -> Result<Json, EndError> {
        self.lens(&CellViews::default()).end_json(end, true)
    }
}

impl<'s> Lens<'s> {
    /// The value index that writes the values of the leaf cell `node`, and the type they are
    /// written at: the observer's and the view's result type for a viewed cell, else this
    /// definition's and the cell's declared type.
    fn leaf(&self, node: &CellNode) -> (&'s ValueIndex, InputType) {
        match self.views.lens(node) {
            Some((index, ty)) => (index, ty.clone()),
            None => (
                self.semantics.values.as_ref(),
                leaf_type(&self.semantics.values, node).unwrap_or_else(InputType::untyped),
            ),
        }
    }

    fn end_json(&self, end: &End, strict: bool) -> Result<Json, EndError> {
        let mut object = JsonMap::new();
        object.insert(
            "halt".to_owned(),
            Json::String(end.class.halt.as_str().to_owned()),
        );
        if let Some(rule) = &end.class.rule {
            object.insert("rule".to_owned(), Json::String(rule.clone()));
        } else if strict && end.class.halt == Halt::Stopped {
            return Err(EndError::Document {
                position: "rule".to_owned(),
                message: "a stopped end names the stop rule's KRS item, and this end's class names none: the run did not name the rule it stopped at, or no name selects that rule's item alone".to_owned(),
            });
        }
        if end.class.halt != Halt::Undefined || !end.cells.is_empty() {
            let cells = self
                .cells_document(self.values.cells(), &end.cells, strict)
                .map_err(|refused| EndError::Document {
                    position: format!("cells{}", refused.position),
                    message: EncodeError {
                        position: String::new(),
                        ..refused.error
                    }
                    .to_string(),
                })?;
            object.insert("cells".to_owned(), cells);
        }
        Ok(Json::Object(object))
    }

    /// The table of the stated `cells` declared by `nodes`.
    fn cells_document(
        &self,
        nodes: &[CellNode],
        cells: &EndCells,
        strict: bool,
    ) -> Result<Json, Box<Refused>> {
        let mut object = JsonMap::new();
        for node in nodes {
            let Some(cell) = cells.get(&node.field) else {
                continue;
            };
            let document = self
                .content_document(node, cell, strict)
                .map_err(|refused| Box::new(refused.under(&format!(".{}", node.field))))?;
            object.insert(node.field.clone(), document);
        }
        Ok(Json::Object(object))
    }

    /// The document of the content of the cell `node` declares
    /// ([module documentation](crate::ends#end-documents)): a leaf's value, a group's table, an
    /// optional cell's `[]` or `[content]`, a repeated cell's array of instances. Not `strict`, a value with no document is written
    /// `{"$kore": <its KORE>}`, for ordering only; `strict`, it is refused, positioned inside the
    /// content.
    fn content_document(
        &self,
        node: &CellNode,
        content: &EndCell,
        strict: bool,
    ) -> Result<Json, Box<Refused>> {
        match content {
            EndCell::Leaf(value) => {
                let (index, ty) = self.leaf(node);
                match encode(index, value, &ty) {
                    Ok(document) => Ok(document),
                    Err(error) if strict => Err(Box::new(Refused {
                        position: error.position.clone(),
                        error,
                    })),
                    Err(_) => {
                        Ok(tagged(
                            "$kore",
                            Json::String(index.encode(value).map_or_else(
                                |error| error.to_string(),
                                |pattern| pattern.to_string(),
                            )),
                        ))
                    }
                }
            }
            EndCell::Group(cells) => self.cells_document(&node.children, cells, strict),
            EndCell::Optional(content) => Ok(Json::Array(match content {
                Some(content) => vec![
                    self.content_document(node, content, strict)
                        .map_err(|refused| Box::new(refused.under("[0]")))?,
                ],
                None => Vec::new(),
            })),
            EndCell::Repeated(instances) => Ok(Json::Array(
                instances
                    .iter()
                    .enumerate()
                    .map(|(position, instance)| {
                        self.content_document(node, instance, strict)
                            .map_err(|refused| Box::new(refused.under(&format!("[{position}]"))))
                    })
                    .collect::<Result<_, _>>()?,
            )),
        }
    }
}

impl Semantics {
    /// Which cells `comparison` compares, checked against the declaration.
    fn selection(&self, comparison: &Comparison) -> Result<Vec<Selection>, EndError> {
        fn build(
            nodes: &[CellNode],
            chosen: &[Vec<usize>],
            chain: &mut Vec<usize>,
            selected: bool,
            unobservable: bool,
        ) -> Vec<Selection> {
            nodes
                .iter()
                .enumerate()
                .map(|(position, node)| {
                    chain.push(position);
                    let selected = selected || chosen.iter().any(|path| path == chain);
                    let unobservable = unobservable || node.unobservable;
                    let selection = if node.children.is_empty() {
                        Selection {
                            compared: selected && !unobservable,
                            children: Vec::new(),
                        }
                    } else {
                        let children = build(&node.children, chosen, chain, selected, unobservable);
                        Selection {
                            compared: children.iter().any(|child| child.compared),
                            children,
                        }
                    };
                    chain.pop();
                    selection
                })
                .collect()
        }
        let nodes = self.values.cells();
        let chosen = match &comparison.compare {
            None => None,
            Some(paths) => Some(
                paths
                    .iter()
                    .map(|path| self.resolve_cell(path))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        };
        let selected = chosen.is_none();
        let selection = build(
            nodes,
            chosen.as_deref().unwrap_or(&[]),
            &mut Vec::new(),
            selected,
            false,
        );
        check_keys(nodes, &selection, "")?;
        Ok(selection)
    }

    /// [`Self::selection`] of `comparison`, whose views must have been resolved for this
    /// definition and must each apply to a compared cell: a view of a cell the comparison does
    /// not compare would change nothing it decides.
    fn viewed_selection(&self, comparison: &Comparison) -> Result<Vec<Selection>, EndError> {
        let selection = self.selection(comparison)?;
        if comparison.views.is_empty() {
            return Ok(selection);
        }
        if !comparison
            .views
            .subject()
            .is_some_and(|subject| Arc::ptr_eq(subject, &self.values))
        {
            return Err(EndError::State(
                "the comparison's views were resolved for another definition than the one comparing".to_owned(),
            ));
        }
        let (compared, _) = Self::compared_paths(&selection, self.values.cells());
        let named = comparison.views.named();
        if let Some((cell, function)) = named.iter().find(|(cell, _)| !compared.contains(cell)) {
            return Err(EndError::View {
                cell: cell.clone(),
                function: function.clone(),
                message: "the comparison does not compare the cell, so the view would change nothing it decides".to_owned(),
            });
        }
        for (cell, function) in &named {
            if let Some(collection) = self.keyed_by(cell)? {
                return Err(EndError::View {
                    cell: cell.clone(),
                    function: function.clone(),
                    message: format!(
                        "the cell is, or is inside, the key of the Map collection `{collection}`, its instances' identity: the instances are paired by key, and a view of the key could give two instances one key"
                    ),
                });
            }
        }
        Ok(selection)
    }

    /// The declared path of the `Map` collection whose key the cell at the declared `path` is, or
    /// is inside, if any.
    fn keyed_by(&self, path: &str) -> Result<Option<String>, EndError> {
        let chain = self.resolve_cell(path)?;
        let mut nodes = self.values.cells();
        let mut fields = Vec::new();
        for (depth, position) in chain.iter().enumerate() {
            let node = &nodes[*position];
            fields.push(node.field.as_str());
            if map_key(node).is_some() && chain.get(depth + 1) == Some(&0) {
                return Ok(Some(fields.join(".")));
            }
            nodes = &node.children;
        }
        Ok(None)
    }

    /// The positions in the cell tree of the cell at the declared `path`.
    pub(crate) fn resolve_cell(&self, path: &str) -> Result<Vec<usize>, EndError> {
        let unknown = || {
            let mut known = Vec::new();
            declared_paths(self.values.cells(), "", &mut known);
            EndError::UnknownCell {
                path: path.to_owned(),
                known,
            }
        };
        let mut nodes = self.values.cells();
        let mut chain = Vec::new();
        let mut unobservable = false;
        for segment in path.split('.') {
            let position = nodes
                .iter()
                .position(|node| node.field == segment)
                .ok_or_else(unknown)?;
            unobservable |= nodes[position].unobservable;
            chain.push(position);
            nodes = &nodes[position].children;
        }
        if unobservable {
            return Err(EndError::Unobservable {
                path: path.to_owned(),
            });
        }
        Ok(chain)
    }

    /// The compared and the other leaf cells, by declared path.
    fn compared_paths(selection: &[Selection], nodes: &[CellNode]) -> (Vec<String>, Vec<String>) {
        fn walk(
            selection: &[Selection],
            nodes: &[CellNode],
            prefix: &str,
            output: &mut (Vec<String>, Vec<String>),
        ) {
            for (selected, node) in selection.iter().zip(nodes) {
                let path = format!("{prefix}{}", node.field);
                if node.children.is_empty() {
                    if selected.compared {
                        output.0.push(path);
                    } else {
                        output.1.push(path);
                    }
                } else {
                    walk(
                        &selected.children,
                        &node.children,
                        &format!("{path}."),
                        output,
                    );
                }
            }
        }
        let mut output = (Vec::new(), Vec::new());
        walk(selection, nodes, "", &mut output);
        output
    }
}

impl Lens<'_> {
    /// `end` projected onto the selected cells
    /// ([module documentation](crate::ends#compared-cells)).
    fn project(&self, selection: &[Selection], end: &End, side: &str) -> Result<End, EndError> {
        let cells = if end.class.halt == Halt::Undefined {
            EndCells::default()
        } else {
            self.project_cells(self.values.cells(), selection, &end.cells, side, "")?
        };
        Ok(End {
            class: end.class.clone(),
            cells,
        })
    }

    fn project_cells(
        &self,
        nodes: &[CellNode],
        selection: &[Selection],
        cells: &EndCells,
        side: &str,
        prefix: &str,
    ) -> Result<EndCells, EndError> {
        let mut projected = Vec::new();
        for (node, selected) in nodes.iter().zip(selection) {
            if !selected.compared {
                continue;
            }
            let path = format!("{prefix}{}", node.field);
            let cell = cells
                .get(&node.field)
                .ok_or_else(|| EndError::MissingCell {
                    side: side.to_owned(),
                    path: path.clone(),
                    what: describe(&self.values, node),
                })?;
            let cell = match (node.multiplicity, cell) {
                (Some(CellMultiplicity::Optional), EndCell::Optional(content)) => {
                    EndCell::Optional(match content {
                        Some(content) => Some(Box::new(
                            self.project_content(node, selected, content, side, &path)?,
                        )),
                        None => None,
                    })
                }
                (Some(CellMultiplicity::Star), EndCell::Repeated(instances)) => {
                    let instances = instances
                        .iter()
                        .enumerate()
                        .map(|(position, instance)| {
                            let at = self
                                .semantics
                                .instance_path(node, &path, position, instance);
                            self.project_content(node, selected, instance, side, &at)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    EndCell::Repeated(self.instances(node, instances))
                }
                (None, content) => self.project_content(node, selected, content, side, &path)?,
                _ => return Err(Self::shape(side, &path)),
            };
            projected.push((node.field.clone(), cell));
        }
        Ok(EndCells(projected))
    }

    fn project_content(
        &self,
        node: &CellNode,
        selected: &Selection,
        content: &EndCell,
        side: &str,
        path: &str,
    ) -> Result<EndCell, EndError> {
        match content {
            EndCell::Leaf(value) if node.children.is_empty() => {
                Ok(EndCell::Leaf(self.views.apply(node, value)?))
            }
            EndCell::Group(cells) if !node.children.is_empty() => {
                Ok(EndCell::Group(self.project_cells(
                    &node.children,
                    &selected.children,
                    cells,
                    side,
                    &format!("{path}."),
                )?))
            }
            _ => Err(Self::shape(side, path)),
        }
    }

    fn shape(side: &str, path: &str) -> EndError {
        EndError::State(format!(
            "the {side} end's cell `{path}` does not have the shape the configuration declares"
        ))
    }

    /// Every compared cell at which two projected cell sets differ, in declaration order.
    fn units<'e>(
        &'e self,
        nodes: &'e [CellNode],
        left: &'e EndCells,
        right: &'e EndCells,
        prefix: &str,
        output: &mut Vec<Unit<'e>>,
    ) {
        for node in nodes {
            let (Some(a), Some(b)) = (left.get(&node.field), right.get(&node.field)) else {
                continue;
            };
            if a == b {
                continue;
            }
            let path = format!("{prefix}{}", node.field);
            match (a, b) {
                (EndCell::Optional(Some(a)), EndCell::Optional(Some(b))) => {
                    self.content_units(node, a, b, path, output);
                }
                (EndCell::Optional(_), EndCell::Optional(_)) => output.push(Unit {
                    cell: path,
                    segments: Vec::new(),
                    ty: InputType::untyped(),
                    index: self.semantics.values.as_ref(),
                    left: Some(Part::Optional(node, a)),
                    right: Some(Part::Optional(node, b)),
                    weight: leaves(a) + leaves(b),
                }),
                (EndCell::Repeated(a), EndCell::Repeated(b)) if is_list(node) => {
                    for position in 0..a.len().max(b.len()) {
                        let path = format!("{path}[{position}]");
                        match (a.get(position), b.get(position)) {
                            (Some(a), Some(b)) if a == b => {}
                            (Some(a), Some(b)) => self.content_units(node, a, b, path, output),
                            (a, b) => output.push(Unit {
                                cell: path,
                                segments: Vec::new(),
                                ty: InputType::untyped(),
                                index: self.semantics.values.as_ref(),
                                left: a.map(|a| Part::Instance(node, a)),
                                right: b.map(|b| Part::Instance(node, b)),
                                weight: a.or(b).map_or(0, leaves),
                            }),
                        }
                    }
                }
                (EndCell::Repeated(a), EndCell::Repeated(b)) => match self.paired(node, a, b) {
                    Some(pairs) => {
                        for (text, a, b) in pairs {
                            let path = format!("{path}[{text}]");
                            match (a, b) {
                                (Some(a), Some(b)) => self.content_units(node, a, b, path, output),
                                (a, b) => output.push(Unit {
                                    cell: path,
                                    segments: Vec::new(),
                                    ty: InputType::untyped(),
                                    index: self.semantics.values.as_ref(),
                                    left: a.map(|a| Part::Instance(node, a)),
                                    right: b.map(|b| Part::Instance(node, b)),
                                    weight: a.or(b).map_or(0, leaves),
                                }),
                            }
                        }
                    }
                    None => self.set_units(node, a, b, path, output),
                },
                (a, b) => self.content_units(node, a, b, path, output),
            }
        }
    }

    /// The differing instances of two sides of the `Map` collection `node`, paired by key, in the
    /// order of the keys' texts (keys with equal texts in the order of the keys), each with its
    /// key's text and the instance each side holds there; `None` where `node` is no `Map`
    /// collection of groups, or an instance does not state its key, or a side holds two
    /// instances with one key, which a projected end of the definition does not.
    #[expect(
        clippy::type_complexity,
        reason = "a key's text and the instance each side holds there"
    )]
    fn paired<'e>(
        &self,
        node: &CellNode,
        left: &'e [EndCell],
        right: &'e [EndCell],
    ) -> Option<Vec<(String, Option<&'e EndCell>, Option<&'e EndCell>)>> {
        map_key(node)?;
        let keyed = |side: &'e [EndCell]| {
            let map = side
                .iter()
                .map(|instance| Some((instance_key(node, instance)?, instance)))
                .collect::<Option<BTreeMap<_, _>>>()?;
            (map.len() == side.len()).then_some(map)
        };
        let (left, right) = (keyed(left)?, keyed(right)?);
        let mut pairs = left
            .keys()
            .chain(right.keys().filter(|key| !left.contains_key(*key)))
            .filter_map(|key| {
                let (a, b) = (left.get(key).copied(), right.get(key).copied());
                (a != b).then(|| (self.key_text(node, key), *key, a, b))
            })
            .collect::<Vec<_>>();
        pairs.sort_by(|(x, xk, ..), (y, yk, ..)| {
            x.as_bytes().cmp(y.as_bytes()).then_with(|| xk.cmp(yk))
        });
        Some(
            pairs
                .into_iter()
                .map(|(text, _, a, b)| (text, a, b))
                .collect(),
        )
    }

    /// The difference of two sides of the set collection `node`: the first instance, by canonical
    /// text, that one side holds and the other does not.
    fn set_units<'e>(
        &'e self,
        node: &'e CellNode,
        a: &'e [EndCell],
        b: &'e [EndCell],
        path: String,
        output: &mut Vec<Unit<'e>>,
    ) {
        let alone = a
            .iter()
            .filter(|instance| !b.contains(instance))
            .chain(b.iter().filter(|instance| !a.contains(instance)))
            .collect::<Vec<_>>();
        let weight = alone.iter().map(|instance| leaves(instance)).sum();
        let only = alone
            .into_iter()
            .map(|instance| (self.order_text(node, instance), instance))
            .min_by(|(x, xi), (y, yi)| x.as_bytes().cmp(y.as_bytes()).then_with(|| xi.cmp(yi)));
        if let Some((text, instance)) = only {
            let held = |side: &[EndCell]| {
                side.contains(instance)
                    .then_some(Part::Instance(node, instance))
            };
            output.push(Unit {
                cell: path,
                segments: vec![format!("{{{text}}}")],
                ty: InputType::untyped(),
                index: self.semantics.values.as_ref(),
                left: held(a),
                right: held(b),
                weight,
            });
        }
    }

    fn content_units<'e>(
        &'e self,
        node: &'e CellNode,
        left: &'e EndCell,
        right: &'e EndCell,
        path: String,
        output: &mut Vec<Unit<'e>>,
    ) {
        match (left, right) {
            (EndCell::Group(a), EndCell::Group(b)) => {
                self.units(&node.children, a, b, &format!("{path}."), output);
            }
            (EndCell::Leaf(a), EndCell::Leaf(b)) => output.push(Unit {
                cell: path,
                segments: Vec::new(),
                ty: self.leaf(node).1,
                index: self.leaf(node).0,
                left: Some(Part::Value(a)),
                right: Some(Part::Value(b)),
                weight: match (a, b) {
                    (Value::Map(a), Value::Map(b)) => a
                        .keys()
                        .chain(b.keys().filter(|key| !a.contains_key(*key)))
                        .filter(|key| a.get(*key) != b.get(*key))
                        .count(),
                    _ => 1,
                },
            }),
            // Projection leaves no other pair of different shapes.
            _ => output.push(Unit {
                cell: path,
                segments: Vec::new(),
                ty: InputType::untyped(),
                index: self.semantics.values.as_ref(),
                left: Some(Part::Instance(node, left)),
                right: Some(Part::Instance(node, right)),
                weight: leaves(left) + leaves(right),
            }),
        }
    }

    /// The differing cells of two projected ends, none when either is undefined (it has no cells).
    fn end_units<'e>(&'e self, left: &'e End, right: &'e End) -> Vec<Unit<'e>> {
        let mut units = Vec::new();
        if left.class.halt != Halt::Undefined && right.class.halt != Halt::Undefined {
            self.units(
                self.values.cells(),
                &left.cells,
                &right.cells,
                "",
                &mut units,
            );
        }
        units
    }

    /// The distance of two projected ends: their differing compared leaves, and one for
    /// differing classes ([module documentation](crate::ends#results)).
    fn distance(&self, left: &End, right: &End) -> usize {
        let cells: usize = self
            .end_units(left, right)
            .iter()
            .map(|unit| unit.weight)
            .sum();
        cells + usize::from(left.class != right.class)
    }

    /// The text of a value at `ty` that orders it and names it in a segment: its canonical text,
    /// or its K text where it has no document.
    fn value_text(&self, index: &ValueIndex, value: &Value, ty: &InputType) -> String {
        match encode(index, value, ty) {
            Ok(document) => canonical_text(&document),
            Err(_) => self.k_text(index, value).0,
        }
    }

    /// A value `index` writes as K text, or its KORE where the printer warns: the text and its
    /// rendering. A viewed value is printed by the observer's printer, since its sort may be
    /// declared by the observer alone.
    fn k_text(&self, index: &ValueIndex, value: &Value) -> (String, &'static str) {
        match index.encode(value) {
            Ok(pattern) => self.pattern_text(self.views.printer(index), &pattern),
            Err(error) => (error.to_string(), "kore"),
        }
    }

    /// `pattern` printed by `unparser`, by default this definition's printer.
    fn pattern_text(
        &self,
        unparser: Option<&krs_unparse::Unparser>,
        pattern: &Pattern,
    ) -> (String, &'static str) {
        let printed = unparser.unwrap_or(self.unparser()).print_kore(
            pattern,
            &krs_unparse::Options::new(krs_unparse::Mode::Pretty),
        );
        if printed.warnings.is_empty() {
            (printed.text, "k")
        } else {
            (pattern.to_string(), "kore")
        }
    }

    /// Descend into two differing values
    /// ([module documentation](crate::ends#the-first-difference)): the segments, the two sides
    /// there (`None` for a side lacking the position) and the type there.
    fn descend<'v>(
        &self,
        index: &ValueIndex,
        mut left: &'v Value,
        mut right: &'v Value,
        mut ty: InputType,
        segments: &mut Vec<String>,
    ) -> (Option<&'v Value>, Option<&'v Value>, InputType) {
        let at = |ty: &InputType, builtin: BuiltinSort| ty.sort == SortRef::Builtin(builtin);
        loop {
            match (left, right) {
                (Value::Ctor(a), Value::Ctor(b))
                    if a.decl() == b.decl()
                        && a.sort_args() == b.sort_args()
                        && a.fields().len() == b.fields().len() =>
                {
                    let Some(position) = a
                        .fields()
                        .iter()
                        .zip(b.fields())
                        .position(|((_, x), (_, y))| x != y)
                    else {
                        break;
                    };
                    // The field is named as a position of the value's document names it; a value
                    // with no document there has no such position, and is shown whole.
                    let Some(segment) = field_position(index, left, &ty, position) else {
                        break;
                    };
                    let field_type = index
                        .info(a.decl())
                        .and_then(|info| info.field_types.get(position).cloned().flatten());
                    segments.push(segment);
                    ty = field_type.unwrap_or_else(InputType::untyped);
                    left = &a.fields()[position].1;
                    right = &b.fields()[position].1;
                }
                (Value::Map(a), Value::Map(b)) => {
                    let (key_type, value_type) = if at(&ty, BuiltinSort::Map) {
                        (ty.element(0), ty.element(1))
                    } else {
                        (InputType::untyped(), InputType::untyped())
                    };
                    let Some((text, key)) = a
                        .keys()
                        .chain(b.keys().filter(|key| !a.contains_key(*key)))
                        .filter(|key| a.get(*key) != b.get(*key))
                        .map(|key| (self.value_text(index, key, &key_type), key))
                        .min_by(|(x, xk), (y, yk)| x.as_bytes().cmp(y.as_bytes()).then(xk.cmp(yk)))
                    else {
                        break;
                    };
                    segments.push(format!("[{text}]"));
                    match (a.get(key), b.get(key)) {
                        (Some(a), Some(b)) => {
                            left = a;
                            right = b;
                            ty = value_type;
                        }
                        (a, b) => return (a, b, value_type),
                    }
                }
                (Value::List(a), Value::List(b)) | (Value::Seq(a), Value::Seq(b)) => {
                    let element = if matches!(left, Value::List(_)) && at(&ty, BuiltinSort::List) {
                        ty.element(0)
                    } else {
                        InputType::untyped()
                    };
                    let position = a
                        .iter()
                        .zip(b)
                        .position(|(x, y)| x != y)
                        .unwrap_or_else(|| a.len().min(b.len()));
                    segments.push(format!("[{position}]"));
                    match (a.get(position), b.get(position)) {
                        (Some(a), Some(b)) => {
                            left = a;
                            right = b;
                            ty = element;
                        }
                        (a, b) => return (a, b, element),
                    }
                }
                (Value::Set(a), Value::Set(b)) => {
                    let element = if at(&ty, BuiltinSort::Set) {
                        ty.element(0)
                    } else {
                        InputType::untyped()
                    };
                    let Some((text, item)) = a
                        .symmetric_difference(b)
                        .map(|item| (self.value_text(index, item, &element), item))
                        .min_by(|(x, xi), (y, yi)| x.as_bytes().cmp(y.as_bytes()).then(xi.cmp(yi)))
                    else {
                        break;
                    };
                    segments.push(format!("{{{text}}}"));
                    return (
                        a.contains(item).then_some(item),
                        b.contains(item).then_some(item),
                        element,
                    );
                }
                _ => break,
            }
        }
        (Some(left), Some(right), ty)
    }

    /// The shown text of a part: its document, and else its K text with the position, inside the
    /// part, of what has no document.
    fn part_text(&self, index: &ValueIndex, part: Part<'_>, ty: &InputType) -> Shown {
        let document = match part {
            Part::Value(value) => encode(index, value, ty).map_err(|error| error.position),
            Part::Optional(node, cell) | Part::Instance(node, cell) => self
                .content_document(node, cell, true)
                .map_err(|refused| refused.position),
        };
        let position = match document {
            Ok(document) => {
                return Shown {
                    text: canonical_text(&document),
                    document: Some(document),
                    rendering: "document",
                    opaque: None,
                };
            }
            Err(position) => position,
        };
        let content = match part {
            Part::Value(value) => return k_shown(self.k_text(index, value), position),
            Part::Optional(node, EndCell::Optional(content)) => {
                content.as_deref().map(|c| (node, c))
            }
            Part::Optional(node, content) | Part::Instance(node, content) => Some((node, content)),
        };
        // An absent optional cell has a document, `[]`, so a refused part holds content. A cell
        // that holds a viewed value is printed by the observer's printer, whose grammar holds
        // this definition's too.
        let shown = content
            .and_then(|(node, content)| {
                let printer = if self.views.holds_view(node) {
                    self.views.observer_printer()
                } else {
                    None
                };
                Some((printer, self.cell_pattern(node, content)?))
            })
            .map_or_else(
                || (String::new(), "kore"),
                |(printer, pattern)| self.pattern_text(printer, &pattern),
            );
        k_shown(shown, position)
    }

    /// The KORE of a cell's content as its cell application, for showing it as K text.
    fn cell_pattern(&self, node: &CellNode, content: &EndCell) -> Option<Pattern> {
        let arguments = match content {
            EndCell::Leaf(value) => vec![self.leaf(node).0.encode(value).ok()?],
            EndCell::Group(cells) => node
                .children
                .iter()
                .filter_map(|child| match cells.get(&child.field)? {
                    EndCell::Optional(None) | EndCell::Repeated(_) => None,
                    EndCell::Optional(Some(content)) => Some(self.cell_pattern(child, content)),
                    content => Some(self.cell_pattern(child, content)),
                })
                .collect::<Option<Vec<_>>>()?,
            EndCell::Optional(_) | EndCell::Repeated(_) => return None,
        };
        Some(Pattern::Application {
            symbol: Symbol {
                name: node.symbol.clone(),
                sort_parameters: Vec::new(),
            },
            arguments,
        })
    }

    /// The difference between the ends `from` (of the side named `outside`) and `near`, each
    /// projected, oriented as `left` and `right`.
    fn difference(
        &self,
        selection: &[Selection],
        left: (Side<'_>, &End),
        right: (Side<'_>, &End),
        outside: &str,
    ) -> Difference {
        let (compared, not_compared) = Semantics::compared_paths(selection, self.values.cells());
        let units = self.end_units(left.1, right.1);
        let side = |(side, end): (Side<'_>, &End), value: Option<Rendered>| DifferenceSide {
            name: side.name.to_owned(),
            ends: side.ends.ends.len(),
            complete: side.ends.incomplete.is_none(),
            class: end.class.clone(),
            value,
        };
        if left.1.class != right.1.class {
            return Difference {
                format: DIFFERENCE_FORMAT,
                at: DifferenceAt::Class,
                cell: None,
                path: None,
                segments: Vec::new(),
                outside: outside.to_owned(),
                also_differ: units.into_iter().map(|unit| unit.cell).collect(),
                compared,
                not_compared,
                views: self.views.named(),
                left: side(left, None),
                right: side(right, None),
            };
        }
        let mut units = units.into_iter();
        let Some(first) = units.next() else {
            unreachable!(
                "two projected ends that differ, with one class, differ in a compared cell: their set collections' instances are in one total order"
            )
        };
        let also_differ = units.map(|unit| unit.cell).collect();
        let mut segments = first.segments;
        let (left_part, right_part, ty) = match (first.left, first.right) {
            (Some(Part::Value(a)), Some(Part::Value(b))) => {
                let (a, b, ty) = self.descend(first.index, a, b, first.ty, &mut segments);
                (a.map(Part::Value), b.map(Part::Value), ty)
            }
            (a, b) => (a, b, first.ty),
        };
        let shown = [
            left_part.map(|part| self.part_text(first.index, part, &ty)),
            right_part.map(|part| self.part_text(first.index, part, &ty)),
        ];
        let [left_cut, right_cut] = cut(
            shown[0].as_ref().map(|shown| shown.text.as_str()),
            shown[1].as_ref().map(|shown| shown.text.as_str()),
        );
        let [left_shown, right_shown] = shown;
        let render = |shown: Option<Shown>, cut: Option<(String, bool, usize)>| {
            let (shown, (text, truncated, offset)) = shown.zip(cut)?;
            Some(Rendered {
                rendering: shown.rendering,
                document: if truncated {
                    None
                } else {
                    shown.document.clone()
                },
                text: if shown.document.is_some() && !truncated {
                    None
                } else {
                    Some(text)
                },
                opaque: shown.opaque,
                truncated,
                offset,
            })
        };
        Difference {
            format: DIFFERENCE_FORMAT,
            at: DifferenceAt::Cell,
            path: Some(format!("{}{}", first.cell, segments.concat())),
            cell: Some(first.cell),
            segments,
            outside: outside.to_owned(),
            also_differ,
            compared,
            not_compared,
            views: self.views.named(),
            left: side(left, render(left_shown, left_cut)),
            right: side(right, render(right_shown, right_cut)),
        }
    }

    /// Why an end's class cannot be compared: a stopped end that does not name its stop rule.
    fn unnamed_stop(side: Side<'_>) -> Option<String> {
        side.ends
            .ends
            .iter()
            .any(|end| end.class.halt == Halt::Stopped && end.class.rule.is_none())
            .then(|| {
                format!(
                    "an end of the {} side stopped at a rule it does not name, so its class cannot be compared",
                    side.name
                )
            })
    }

    /// A side's ends projected onto the selected cells, in the order of the canonical text of
    /// their documents (ends with equal texts, which only values with no document can have, in
    /// the order the producer gave them), each once.
    fn projected(
        &self,
        selection: &[Selection],
        side: Side<'_>,
    ) -> Result<Vec<(String, End)>, EndError> {
        let mut ends = side
            .ends
            .ends
            .iter()
            .map(|end| {
                let end = self.project(selection, end, side.name)?;
                Ok((canonical_text(&self.end_json(&end, false)?), end))
            })
            .collect::<Result<Vec<_>, EndError>>()?;
        ends.sort_by(|(x, _), (y, _)| x.as_bytes().cmp(y.as_bytes()));
        let mut unique: Vec<(String, End)> = Vec::with_capacity(ends.len());
        for (text, end) in ends {
            let held = unique
                .iter()
                .rev()
                .take_while(|(other_text, _)| *other_text == text)
                .any(|(_, other)| *other == end);
            if !held {
                unique.push((text, end));
            }
        }
        Ok(unique)
    }
}

impl Semantics {
    /// Check `comparison` against the declaration, as every comparison under it does, without
    /// an end: a caller refuses a comparison that names no cell, an unobservable cell, or a view
    /// of a cell it does not compare, before it runs what it compares.
    ///
    /// # Errors
    ///
    /// Returns [`EndError::UnknownCell`] and [`EndError::Unobservable`] for a compared path that
    /// names no observable cell, and [`EndError::View`] for a view of a cell it does not compare.
    pub fn check_comparison(&self, comparison: &Comparison) -> Result<(), EndError> {
        self.viewed_selection(comparison).map(|_| ())
    }

    /// Check that `end` states every cell `comparison` compares, as any comparison of the end
    /// does, without comparing it: a caller refuses a partial end before it runs what the end is
    /// compared with. `side` names the end in a refusal.
    ///
    /// # Errors
    ///
    /// Returns a refusal of `comparison`'s cells ([`EndError::UnknownCell`],
    /// [`EndError::Unobservable`]), [`EndError::View`] for a view of a cell it does not compare,
    /// and [`EndError::MissingCell`] for a compared cell `end` does not state.
    pub fn check_stated(
        &self,
        comparison: &Comparison,
        end: &End,
        side: &str,
    ) -> Result<(), EndError> {
        let selection = self.viewed_selection(comparison)?;
        self.lens(&CellViews::default())
            .project(&selection, end, side)
            .map(|_| ())
    }

    /// Whether `actual`'s ends meet the expectation `expected` (one end), and else the first end
    /// that does not ([module documentation](crate::ends#results)). Only the ends the
    /// definition reaches are compared ([`Ends::reached`]): a `depth-bound` end of `actual`
    /// makes its set incomplete instead.
    ///
    /// # Errors
    ///
    /// Returns [`EndError::State`] when `expected` holds other than one end, or a `depth-bound`
    /// end, a refusal of `comparison`'s cells ([`EndError::UnknownCell`],
    /// [`EndError::Unobservable`]), and [`EndError::MissingCell`] for a compared cell an end
    /// does not state.
    pub fn check_expectation(
        &self,
        comparison: &Comparison,
        expected: Side<'_>,
        actual: Side<'_>,
    ) -> Result<Compared, EndError> {
        let [expected_end] = expected.ends.ends.as_slice() else {
            return Err(EndError::State(format!(
                "an expectation is one end, not {}",
                expected.ends.ends.len()
            )));
        };
        if expected_end.class.halt == Halt::DepthBound {
            return Err(EndError::State(
                "an expectation's end is never `depth-bound`, which is where a step budget ended \
                 a run, not an end of the definition"
                    .to_owned(),
            ));
        }
        // Callers that evaluate views over `actual` first (krs-cli's `check`) pass the ends
        // `reached` already gave, so this is then a borrowed no-op; it stays so that every caller
        // compares only the ends the definition reaches.
        let reached = actual.ends.reached();
        let actual = Side {
            name: actual.name,
            ends: &reached,
        };
        let selection = self.viewed_selection(comparison)?;
        let lens = self.lens(&comparison.views);
        let x = lens.project(&selection, expected_end, expected.name)?;
        let projected = lens.projected(&selection, actual)?;
        if let Some(reason) = Lens::unnamed_stop(expected).or_else(|| Lens::unnamed_stop(actual)) {
            return Ok(Compared::Inconclusive(reason));
        }
        if let Some((_, end)) = projected.iter().find(|(_, end)| *end != x) {
            return Ok(Compared::Differs(Box::new(lens.difference(
                &selection,
                (expected, &x),
                (actual, end),
                actual.name,
            ))));
        }
        // No end agrees with nothing: a side without ends is inconclusive for that, whatever
        // made it incomplete.
        Ok(match (projected.is_empty(), &actual.ends.incomplete) {
            (true, Some(reason)) => {
                Compared::Inconclusive(format!("the {} side has no end: {reason}", actual.name))
            }
            (true, None) => Compared::Inconclusive(format!("the {} side has no end", actual.name)),
            (false, Some(reason)) => Compared::Inconclusive(format!(
                "every end the {} side has meets the expectation, but it may have others: {reason}",
                actual.name
            )),
            (false, None) => Compared::Equal,
        })
    }

    /// Compare two sets of ends ([module documentation](crate::ends#results)).
    ///
    /// The sets are the projected ends, ordered by the canonical text of their documents.
    ///
    /// # Errors
    ///
    /// Returns a refusal of `comparison`'s cells ([`EndError::UnknownCell`],
    /// [`EndError::Unobservable`]), and [`EndError::MissingCell`] for a compared cell an end does
    /// not state.
    pub fn compare_ends(
        &self,
        comparison: &Comparison,
        left: Side<'_>,
        right: Side<'_>,
    ) -> Result<Compared, EndError> {
        let selection = self.viewed_selection(comparison)?;
        let lens = self.lens(&comparison.views);
        let left_ends = lens.projected(&selection, left)?;
        let right_ends = lens.projected(&selection, right)?;
        for (side, ends) in [(left, &left_ends), (right, &right_ends)] {
            if ends.is_empty() {
                return Ok(Compared::Inconclusive(match &side.ends.incomplete {
                    Some(reason) => format!("the {} side has no end: {reason}", side.name),
                    None => format!("the {} side has no end", side.name),
                }));
            }
        }
        if let Some(reason) = Lens::unnamed_stop(left).or_else(|| Lens::unnamed_stop(right)) {
            return Ok(Compared::Inconclusive(reason));
        }
        let nearest = |end: &End, set: &[(String, End)]| {
            set.iter()
                .map(|(_, other)| other)
                .min_by_key(|other| lens.distance(end, other))
                .cloned()
                .unwrap_or_else(|| end.clone())
        };
        if left.ends.incomplete.is_none()
            && let Some(end) = outside(&right_ends, &left_ends)
        {
            let near = nearest(end, &left_ends);
            return Ok(Compared::Differs(Box::new(lens.difference(
                &selection,
                (left, &near),
                (right, end),
                right.name,
            ))));
        }
        if right.ends.incomplete.is_none()
            && let Some(end) = outside(&left_ends, &right_ends)
        {
            let near = nearest(end, &right_ends);
            return Ok(Compared::Differs(Box::new(lens.difference(
                &selection,
                (left, end),
                (right, &near),
                left.name,
            ))));
        }
        Ok(match (&left.ends.incomplete, &right.ends.incomplete) {
            (None, None) => Compared::Equal,
            (Some(reason), _) => Compared::Inconclusive(format!(
                "the {} side's ends are incomplete: {reason}",
                left.name
            )),
            (None, Some(reason)) => Compared::Inconclusive(format!(
                "the {} side's ends are incomplete: {reason}",
                right.name
            )),
        })
    }
}

/// A part's shown text before it is cut.
struct Shown {
    text: String,
    document: Option<Json>,
    rendering: &'static str,
    opaque: Option<String>,
}

/// A part shown as K (or KORE) text, `position` naming what inside it has no document.
fn k_shown((text, rendering): (String, &'static str), position: String) -> Shown {
    Shown {
        text,
        document: None,
        rendering,
        opaque: Some(position),
    }
}

#[cfg(test)]
mod tests {
    use super::{VALUE_CAP, cut};

    fn shown(text: &str) -> String {
        text.to_owned()
    }

    #[test]
    fn short_texts_are_shown_whole() {
        assert_eq!(
            cut(Some("[1]"), None),
            [Some((shown("[1]"), false, 0)), None]
        );
        assert_eq!(
            cut(Some("1"), Some("2")),
            [Some((shown("1"), false, 0)), Some((shown("2"), false, 0))]
        );
    }

    #[test]
    fn long_texts_are_cut_around_their_first_difference() {
        let head = "a".repeat(3 * VALUE_CAP);
        let left = format!("{head}x");
        let right = format!("{head}y");
        let [Some((left, true, offset)), Some((right, true, same))] =
            cut(Some(&left), Some(&right))
        else {
            panic!("both are cut");
        };
        assert_eq!(offset, 3 * VALUE_CAP - VALUE_CAP / 2);
        assert_eq!(same, offset);
        assert_eq!(left.chars().count(), VALUE_CAP / 2 + 1);
        assert!(left.ends_with('x') && right.ends_with('y'));
        // A difference in the first half of the cap keeps the start.
        let long = format!("x{head}");
        let [Some((text, true, 0)), Some((short, false, 0))] = cut(Some(&long), Some("y")) else {
            panic!("only the long text is cut");
        };
        assert_eq!(text.chars().count(), VALUE_CAP);
        assert_eq!(short, "y");
    }
}
