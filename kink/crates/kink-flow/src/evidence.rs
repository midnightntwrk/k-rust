//! Kill evidence and end summaries (CF-16): where a kill's ends differ, printed for a reader, and
//! what each end of a run is (its computation head and its class).
//!
//! Nothing here reads or changes a verdict: a kill is the campaign runner's proved `Distinguish`
//! (README 7.5.3), and the evidence only says, for a reader, where the two sides' ends differ.
//!
//! # The ends compared
//!
//! A test's whole-term slot compares two sets of ends: each side's final configurations with the
//! `<generatedCounter>` content erased (k-rust `counter_erased`, the whole-term projection); a
//! `cells` slot compares them with each cell it leaves out replaced by `\top` of its sort
//! (kink-campaign `CellProjection`), and everything below holds of those projected ends. The
//! baseline set `B` is the baseline side's whole-term value (a comparable program's side is always
//! a value). The mutant set `M` is the mutant side's whole-term value when it is one (`complete`),
//! and otherwise, for a one-sided kill (kink-campaign `OneSided`: the mutant's run reached its work
//! budget), the erased ends of the run's kept one-sided terminals (kink-campaign
//! `TestEvidence::one_sided_ends`, `complete: false`): the clean, ground, stuck ends of explored
//! complete paths that the one-sided rule reads. The whole-term slot distinguishes one-sidedly
//! exactly when one of them, erased, is outside `B`, so an end of `M` outside `B` is an end that
//! killed: every completion of the run has it among its ends, whatever the unexplored part holds.
//! The run's other explored ends are not in `M`, since none of them killed.
//!
//! # The pair of ends
//!
//! The evidence is one pair of ends, chosen deterministically:
//!
//! 1. when some end of `M` is not in `B`, the first such end in `M`'s order (the order of
//!    `Pattern`, which orders the sets) and its nearest end of `B` (`outside: "mutant"`);
//! 2. otherwise, when `M` is complete (so `M` is a strict subset of `B`), the first end of `B`
//!    not in `M` and its nearest end of `M` (`outside: "baseline"`).
//!
//! The nearest end of a set to an end `e` is the end `f` of the set with the least cell distance
//! from `e`, the first in the set's order among equals. The cell distance of two terms is 0 when
//! they are equal; for two applications of one cell symbol with the same arity it is the sum of
//! their children's distances; for two concrete maps it is the number of keys whose entries
//! differ (a key in one map only counts once); otherwise it is 1. It counts the leaf cells (and
//! map entries) in which two configurations differ, so the nearest end is the one that agrees
//! with `e` in the most places. A side with no end (every path of its run is an undefined step,
//! kink27 R1-UNDEF) has no nearest end: its `end` and `value` are null, and the `path` is null
//! too.
//!
//! # The first differing cell path
//!
//! From the top of the two ends, while both terms are applications of the same cell symbol (a
//! production with the `cell` attribute in the compiled definition) with the same arity, the
//! cell's label joins the path and the walk enters the first child at which they differ, while
//! that child is the same cell on both sides. The two contents of the last cell entered are the
//! values. The walk then goes on into collections, while both values are concrete maps or both
//! are concrete lists:
//!
//! - two concrete maps (applications of the definition's `MAP.concat`, `MAP.element` and
//!   `MAP.unit` symbols, with distinct keys): the first key, in `Pattern` order, whose entry
//!   differs; `[key]` (the key printed as K text) joins the path, and the values are the entries'
//!   values there, null for a side whose map lacks the key;
//! - two concrete lists (applications of its `LIST.concat`, `LIST.element` and `LIST.unit`
//!   symbols): the first index, from 0, whose element differs; `[i]` joins the path, and the
//!   values are the elements there, null for a side whose list is shorter.
//!
//! The two ends differ, so some cell does.
//!
//! # Printing
//!
//! A value is printed as K text through krs-unparse (`Mode::Pretty`, the printer of `krs run`'s
//! configurations, with aliases not reversed, so the text writes the term itself, and maps sorted
//! by their printed items, as K prints them), on one line. When the printer cannot be built, warns
//! (a symbol without a printable production, an instance its text does not fix, a bracket the
//! grammar lacks, ...), or the term has more than [`PRINT_NODES`] nodes, the value is printed as
//! KORE instead (`rendering: "kore"`, with the printer's warnings in `note`). Each print is cut to
//! a fixed number of characters ([`VALUE_CAP`], [`HEAD_CAP`]) and says whether it was cut, so the
//! evidence is bounded: it is stored in the tier-1 outcome record (outside the key) and in the
//! result record.
//!
//! The two values of a difference are cut around their first differing character, so the two
//! texts shown differ: when the printed texts first differ at character `d`, at least
//! [`VALUE_CAP`]` / 2` characters in, and one of them is longer than [`VALUE_CAP`], both are cut
//! to the [`VALUE_CAP`] characters from `d - VALUE_CAP / 2`. A value's `offset` is the number of
//! characters cut before its `text` (0 when it starts at the start).
//!
//! # An end's summary
//!
//! An end's computation head is the first item of its computation cell, or the cell's content
//! when that is not a sequence of items (`.K` for an empty one), printed as K text as above. The
//! computation cell is the first cell, in pre-order over the end's cells, whose production has
//! the `maincell` attribute (k-rust gives it to a cell named `k`; a configuration may declare it
//! on a cell of another name, `<code maincell="">`). The head is null when the end has no such
//! cell. Its class is the class the exit-stop slot projects it to: the flow's classifier's answer
//! for it (`results::classify`, the classifier of every campaign call of the flow, digest
//! `CLASSIFIER`), `normal` for every end.
//!
//! The ends of a run with a stop (`[stop]`) also say how the run reached them, `halt`: `stop`
//! where some path of the run reached the end at its last stop, `own` where every path that
//! reached it ended on its own (stuck, or an end of the definition). It is evidence for a reader,
//! never compared: the slot compares ends of the truncated system whichever way a path reached
//! them, and a state set that merges a stopped path with a stuck one at the same configuration
//! keeps one leaf of the two, so which halt the run reports for such an end can depend on the
//! order the run explored them.
//!
//! # Observation evidence
//!
//! Under `[observe]` a test can be killed by its observation slot alone (a prefix program's end
//! slots compare nothing). Its evidence is the difference the slot reported: `{format, position:
//! {channel, index, at_end}, baseline: {element}, mutant: {element}}`
//! ([`EndReader::observation_difference`]). An element is `{cells: {<cell>: value}}` for a point
//! class's content, by the class's cells in order, `{item: value}` for a log's, each value printed
//! as above and cut at [`VALUE_CAP`], or `"end"`, `"undefined"` or `"undecided"`. The baseline's
//! record keeps no values, so its element is re-derived by a capture run of the baseline's request
//! that ends the path at the reported element, whose digest must be the recorded one
//! (kink-campaign `observed_difference`); the mutant's is its probe's. A test whose ends also
//! distinguished keeps its end evidence, and its observation slot still shows its position. An
//! element a front end's functions of an observer gave is `{value}`, its document as the front
//! end wrote it. A front end whose renderer writes observation evidence
//! ([`EndRenderer::observation_format`]) gives its own document of the same difference in its
//! format; where it shows none, kink's own is given with `note` saying why, as for ends.
//!
//! # A query witness
//!
//! A hit's witness (`query`, [`crate::pattern::rendered_witness`]) is printed for a reader with the
//! same printer, shortened by structure rather than cut at a character count, so the cells the
//! pattern is about are never lost behind a large cell it says nothing about. The cells a pattern
//! names are those its compiled target gives a content of its own: a cell application with an
//! argument that is neither a cell nor a variable the compiler generated (k-rust completes the
//! cells a pattern leaves out, and the contents it leaves open, with such variables), so `<k>
//! done </k>`, `<mem> 7 |-> V </mem>` and `<regs> R </regs>` name their cells, while `<regs> <a>
//! 1 </a> </regs>` names `<a>` and not `<regs>`, whose other cells it leaves out.
//!
//! The state is listed by its cells, in pre-order, each `{path, named, value}`, `path` the cell
//! labels from the top cell to it. A cell the pattern names is one entry, its content printed in
//! full (`value` is `{text, rendering, truncated}` as above, never cut). A cell whose arguments
//! are all cells is entered. Every other cell is one entry, shortened: a concrete collection of
//! more than [`WITNESS_ITEMS`] elements is `{collection, length, last}` for a list (its last
//! [`WITNESS_ITEMS`] elements, in order: a list a run appends to shows what it appended last) or
//! `{collection, length, first}` for a map or a set (its first [`WITNESS_ITEMS`] entries in printed
//! order, by their printed keys, a map's entry `{key, value}`), each element printed and cut at
//! [`HEAD_CAP`]; any other content is printed and cut at [`HEAD_CAP`]. A binding's value is a
//! long collection shortened so, and otherwise printed in full: the author wrote the variable.
//! The rendering is a function of the state and the pattern alone.
//!
//! # The format of the evidence
//!
//! Every kill evidence object names its format, `format`. kink's own evidence, above, is
//! [`K_EVIDENCE_VERSION`] (`kink-k/1`): cells by K label and values as K text, the terms of the
//! K definition kink judges. A front end that reads the definition's ends at its own level sets an
//! [`EndRenderer`] on the manifest (`FlowManifest::with_end_renderer`), and the evidence of a kill
//! is then the renderer's document, in the renderer's format (the krs front end's is
//! `krs-difference/3`, the document of krs-exec's comparison of ends: cells by Rust field path
//! and values as their canonical documents). The renderer is given what kink's own evidence
//! compares: the two sets of projected ends, whether the mutant's is complete, and the cells the
//! slot leaves out, whose positions hold the projection's placeholder and so state nothing. It
//! chooses its pair of ends by its own order, under the rule above: an end outside the other set
//! (a mutant end first, which needs only the baseline's set complete), with its nearest end of
//! that set.
//!
//! The renderer judges no kill: the slot did. Its ends are the slot's ends, and a front end whose
//! values are equal exactly when their terms are finds a difference wherever the slot did, but it
//! may not: a difference only in a cell the front end does not declare, an end it cannot read.
//! kink then gives its own evidence, with `note` saying why the front end's has none, so a kill
//! never loses its evidence. A side with no end (every path an undefined step) has no end for a
//! front end to show, so its evidence is kink's own without a note.
//!
//! A `killed` record of the outcome store keeps its evidence, and serves it in place of a
//! recomputation, so the tier-1 context must name every input of the document. The ends are the
//! record's own; kink's build (`kink_build`, the running executable) fixes the renderer's code;
//! the execution digest names the K definition, up to positions. A front end's documents can
//! depend on more than that K: the krs front end names cells, constructors and fields by the
//! Definition IR's Rust names, and a constructor's field names never reach the K it emits. So
//! the renderer states its format and the further inputs its documents depend on
//! ([`EndRenderer::identity`]), and both enter the context as `evidence`
//! (`digest::outcome_context`, [`Renderer::evidence`]): a store never serves a document that
//! another renderer, or the same renderer over other names, would not write.
//!
//! The renderer writes kill evidence only. A program row's end summaries ([`EndReader::summary`],
//! `programs[i].ends`) stay kink's under a front end too, K text heads cut to [`HEAD_CAP`]: a
//! summary is a bounded listing of a program's ends for orientation, while a front end's
//! document of an end (krs-exec's is the whole end, every cell as its canonical document) has no
//! bound, and the evidence of a kill, the one place the ends are compared, carries the front
//! end's reading of the cells that differ.

use k_rust::{
    backend::counter_erased,
    definition::{AttributeKey, Sentence},
    kast::identifier::{encode, label_or_name},
    kore::{ast::Pattern, walk},
};
use kink_campaign::{
    CellProjection, Element, FinalResult, ObservedDifference, OracleSide, OracleValue, SideRun,
    TestEvidence,
};
use kink_native::ValidatedDefinition;
use krs_unparse::{ListSpelling, Mode, Options, Unparser};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

/// The most characters of one printed value the evidence keeps.
pub const VALUE_CAP: usize = 2000;
/// The most characters of one printed computation head or map key.
pub const HEAD_CAP: usize = 200;
/// The most nodes of a term printed as K text; a larger one is printed as KORE (the printer is
/// recursive, and the text would be cut anyway).
pub const PRINT_NODES: usize = 100_000;
/// The most elements of a long collection a query witness shows (module documentation, "A query
/// witness").
pub const WITNESS_ITEMS: usize = 8;
/// The KORE names of K's computation sequence.
const KSEQ: &str = "kseq";
/// The format of kink's own kill evidence (module documentation, "The format of the evidence"):
/// cells by K label, values as K text.
pub const K_EVIDENCE_VERSION: &str = "kink-k/1";

/// The format of kink's evidence of a difference of the two sides' prefix sets
/// ([`EndReader::observation_set_difference`]).
pub const K_SET_EVIDENCE_VERSION: &str = "kink-k-sets/1";

/// A front end's evidence of a kill at its own level (module documentation, "The format of the
/// evidence"); kink never reads it. The krs front end implements it with krs-exec's comparison of
/// ends.
pub trait EndRenderer {
    /// The format of the documents [`Self::difference`] writes, which each names as `format`.
    fn format(&self) -> &'static str;

    /// Every input of the documents [`Self::difference`] writes besides the ends, the K
    /// definition the execution digest names (up to positions) and the running executable
    /// (`kink_build`), as a JSON value that differs whenever such an input does (module
    /// documentation, "The format of the evidence"); `null` when there is none. It enters the
    /// tier-1 context with the format, so a stored document is served only where this renderer
    /// would write it again.
    ///
    /// # Errors
    ///
    /// When the renderer cannot state its inputs: tier 1 is then off for the command, as for an
    /// unknown build, since no key would name what a stored document depends on.
    fn identity(&self) -> Result<Value, String>;

    /// The evidence of a kill whose slot distinguished the ends `baseline` (complete) and
    /// `mutant` (complete when `mutant_complete`, else the one-sided ends that killed): each end
    /// a final configuration of the K definition kink judges as the slot compared it, with
    /// `<generatedCounter>`'s content erased and each cell of `not_compared` (by K cell name,
    /// `scratch` for `<scratch>`) replaced by `\top` of its sort. Neither set is empty. `Err`
    /// says why the renderer shows no difference (none found, an end it cannot read); kink then
    /// gives its own evidence with that reason.
    ///
    /// # Errors
    ///
    /// When the renderer finds no difference between the two sets, or cannot read an end.
    fn difference(
        &self,
        baseline: &BTreeSet<Pattern>,
        mutant: &BTreeSet<Pattern>,
        mutant_complete: bool,
        not_compared: &[String],
    ) -> Result<Value, String>;

    /// The format of the documents [`Self::observation_difference`] writes, which each names as
    /// `format`; `None` for a renderer that reads ends only, whose observation evidence is then
    /// kink's own. Where it is `Some`, it enters the tier-1 context beside [`Self::format`]
    /// ([`Renderer::evidence`]), so a stored document of an observation difference is served only
    /// where this renderer would write it again.
    fn observation_format(&self) -> Option<&'static str> {
        None
    }

    /// The evidence of a kill whose observation slot distinguished `difference` (the channel,
    /// the index and both sides' elements, each re-derived from its side's values), under the
    /// declaration `observe` (the manifest's, as the front end bound it). `Err` says why the
    /// renderer shows no difference; kink then gives its own evidence with that reason. The
    /// default shows none: a renderer that reads ends only.
    ///
    /// # Errors
    ///
    /// When the renderer cannot show the difference.
    fn observation_difference(
        &self,
        difference: &ObservedDifference,
        observe: Option<&crate::manifest::ObserveSection>,
    ) -> Result<Value, String> {
        let _ = (difference, observe);
        Err(format!(
            "the front end's renderer ({}) reads ends only",
            self.format()
        ))
    }

    /// Reads a case's expectation, its `expect` table as written ([`crate::expect`]), refusing
    /// one that is no expectation of the definition; `files` reads the files it names, relative
    /// to the file the case is written in. Admission calls it for every program with `expect`.
    /// The default refuses every expectation: a renderer that reads none.
    ///
    /// # Errors
    ///
    /// Why the table is no expectation of the definition, which admission reports as the
    /// refusal's detail (`inputs`/`expectation-value`).
    fn read_expectation(
        &self,
        expect: &toml::Table,
        files: &mut dyn crate::admit::InputFiles,
    ) -> Result<(), String> {
        let _ = (expect, files);
        Err(format!(
            "the front end's ends ({}) read no expectation",
            self.format()
        ))
    }

    /// Checks a case's expectation against the ends of its baseline run ([`crate::expect`]).
    /// The default checks none.
    ///
    /// # Errors
    ///
    /// Why the expectation cannot be checked, which the row reports as an inconclusive
    /// verdict's detail.
    fn check_expectation(
        &self,
        check: crate::expect::ExpectationCheck<'_>,
    ) -> Result<crate::expect::CheckedExpectation, String> {
        let _ = check;
        Err(format!(
            "the front end's ends ({}) check no expectation",
            self.format()
        ))
    }
}

/// A front end's [`EndRenderer`], or none. Two are equal when both are absent or both are the
/// same renderer value.
#[derive(Clone, Default)]
pub struct Renderer(pub Option<Arc<dyn EndRenderer + Send + Sync>>);

impl Renderer {
    /// The renderer, when a front end set one.
    #[must_use]
    pub fn get(&self) -> Option<&(dyn EndRenderer + Send + Sync)> {
        self.0.as_deref()
    }

    /// The tier-1 context's `evidence` member: the format of a front end's evidence and its
    /// further inputs ([`EndRenderer::identity`]), `{format, identity}`, with `observations`, the
    /// format of its observation evidence, when it writes some
    /// ([`EndRenderer::observation_format`]); `Ok(None)` for kink's own evidence
    /// ([`K_EVIDENCE_VERSION`]), which depends on nothing the context does not name.
    ///
    /// # Errors
    ///
    /// When the front end's renderer cannot state its inputs ([`EndRenderer::identity`]).
    pub fn evidence(&self) -> Result<Option<Value>, String> {
        self.get()
            .map(|renderer| {
                let mut evidence = json!({
                    "format": renderer.format(),
                    "identity": renderer.identity()?,
                });
                if let Some(format) = renderer.observation_format() {
                    evidence["observations"] = json!(format);
                }
                Ok(evidence)
            })
            .transpose()
    }
}

impl fmt::Debug for Renderer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.get() {
            Some(renderer) => write!(f, "Renderer(Some({}))", renderer.format()),
            None => f.write_str("Renderer(None)"),
        }
    }
}

impl PartialEq for Renderer {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            _ => false,
        }
    }
}

impl Eq for Renderer {}

/// What kill evidence and end summaries read from the compiled definition: its printer, its cell
/// symbols (and which are main cells), and its map and list symbols. Built once per command
/// ([`crate::results::BaselineRunner`]).
pub struct EndReader {
    /// The second slot's cell projection, when it leaves some cell out: the one-sided ends that
    /// killed are projected with it, as the slot projected them ([`Self::test_difference`]).
    projection: Option<CellProjection>,
    /// The front end's renderer of kill evidence and the cells the slot leaves out, by K name
    /// ([`Self::rendering`]).
    renderer: Renderer,
    not_compared: Vec<String>,
    printer: Result<Unparser, String>,
    cells: BTreeSet<String>,
    main_cells: BTreeSet<String>,
    map: Collection,
    list: Collection,
    set: Collection,
}

/// The KORE names of one collection's hooked symbols: its concatenation, element and unit.
#[derive(Default)]
struct Collection {
    concat: BTreeSet<String>,
    element: BTreeSet<String>,
    unit: BTreeSet<String>,
}

impl Collection {
    /// The collection of the hooks `concat`, `element` and `unit` (`MAP` or `LIST`).
    fn read(&mut self, hook: &str, prefix: &str, symbol: &str) {
        let Some(operation) = hook
            .strip_prefix(prefix)
            .and_then(|rest| rest.strip_prefix('.'))
        else {
            return;
        };
        match operation {
            "concat" => self.concat.insert(symbol.to_owned()),
            "element" => self.element.insert(symbol.to_owned()),
            "unit" => self.unit.insert(symbol.to_owned()),
            _ => false,
        };
    }

    /// The elements (each an element application's arguments) of a concrete collection, in
    /// order; `None` for any other term.
    fn elements<'t>(&self, term: &'t Pattern) -> Option<Vec<&'t [Pattern]>> {
        let mut elements = Vec::new();
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            match term {
                Pattern::Application { symbol, arguments }
                | Pattern::AssociativeApplication {
                    symbol, arguments, ..
                } if self.concat.contains(&symbol.name) => {
                    pending.extend(arguments.iter().rev());
                }
                Pattern::Application { symbol, arguments }
                    if self.element.contains(&symbol.name) =>
                {
                    elements.push(arguments.as_slice());
                }
                Pattern::Application { symbol, arguments }
                    if self.unit.contains(&symbol.name) && arguments.is_empty() => {}
                _ => return None,
            }
        }
        Some(elements)
    }
}

impl EndReader {
    /// The reader of the compiled specification `compiled`.
    pub fn of(compiled: &ValidatedDefinition) -> Self {
        let artifacts = compiled.artifacts();
        let printer =
            Unparser::from_kore(&artifacts.syntax_definition_kore, &artifacts.macros_kore)
                .map(|printer| printer.with_program_grammar(compiled.definition()))
                .map_err(|error| error.to_string());
        let mut reader = Self {
            projection: None,
            renderer: Renderer::default(),
            not_compared: Vec::new(),
            printer,
            cells: BTreeSet::new(),
            main_cells: BTreeSet::new(),
            map: Collection::default(),
            list: Collection::default(),
            set: Collection::default(),
        };
        for module in &artifacts.execution_definition.modules {
            for sentence in &module.local_sentences {
                let Sentence::Production {
                    label: Some(label),
                    attributes,
                    ..
                } = sentence.as_ref()
                else {
                    continue;
                };
                let symbol = format!("Lbl{}", encode(&label.name));
                if attributes.has(AttributeKey::Cell) {
                    reader.cells.insert(symbol.clone());
                    if attributes.has(AttributeKey::Maincell) {
                        reader.main_cells.insert(symbol.clone());
                    }
                }
                if let Some(hook) = attributes.string(AttributeKey::Hook) {
                    reader.map.read(hook, "MAP", &symbol);
                    reader.list.read(hook, "LIST", &symbol);
                    reader.set.read(hook, "SET", &symbol);
                }
            }
        }
        reader
    }

    /// This reader for a specification whose second slot leaves cells out by `projection`
    /// (`None`: it compares the whole final term).
    #[must_use]
    pub fn projecting(mut self, projection: Option<CellProjection>) -> Self {
        self.projection = projection;
        self
    }

    /// This reader with kill evidence rendered by `renderer` when it holds one (module
    /// documentation, "The format of the evidence"), for a slot that leaves out the cells
    /// `not_compared` (by K name; `ResultProjection::not_compared`).
    #[must_use]
    pub fn rendering(mut self, renderer: Renderer, not_compared: Vec<String>) -> Self {
        self.renderer = renderer;
        self.not_compared = not_compared;
        self
    }

    /// A reader with no printer and the given cell, main cell, map and list symbols (KORE names;
    /// each collection's concatenation, element and unit), for tests.
    #[cfg(test)]
    pub(crate) fn with_symbols(
        cells: &[&str],
        main_cells: &[&str],
        map: [&str; 3],
        list: [&str; 3],
    ) -> Self {
        let collection = |[concat, element, unit]: [&str; 3]| Collection {
            concat: BTreeSet::from([concat.to_owned()]),
            element: BTreeSet::from([element.to_owned()]),
            unit: BTreeSet::from([unit.to_owned()]),
        };
        Self {
            projection: None,
            renderer: Renderer::default(),
            not_compared: Vec::new(),
            printer: Err("no printer".into()),
            cells: cells.iter().map(|cell| (*cell).to_owned()).collect(),
            main_cells: main_cells.iter().map(|cell| (*cell).to_owned()).collect(),
            map: collection(map),
            list: collection(list),
            set: Collection::default(),
        }
    }

    /// `term` printed for a reader: `{text, rendering, truncated}` (and `note` when the K text
    /// was refused), `text` cut at `cap` characters (module documentation, "Printing").
    pub fn print(&self, term: &Pattern, cap: usize) -> Value {
        let printed = self.render(term);
        let chars = printed.text.chars().collect::<Vec<_>>();
        let mut value = printed.window(&chars, 0, cap);
        value.as_object_mut().map(|object| object.remove("offset"));
        value
    }

    /// The two values of a difference printed for a reader, each `{text, rendering, truncated,
    /// offset}` (and `note`), cut around their first differing character (module documentation,
    /// "Printing").
    fn print_values(
        &self,
        left: Option<&Pattern>,
        right: Option<&Pattern>,
    ) -> (Option<Value>, Option<Value>) {
        let left = left.map(|term| self.render(term));
        let right = right.map(|term| self.render(term));
        let chars = |printed: &Option<Printed>| {
            printed
                .as_ref()
                .map(|printed| printed.text.chars().collect::<Vec<_>>())
        };
        let (left_chars, right_chars) = (chars(&left), chars(&right));
        let start = match (&left_chars, &right_chars) {
            (Some(l), Some(r)) if l.len() > VALUE_CAP || r.len() > VALUE_CAP => {
                let first = l.iter().zip(r).take_while(|(a, b)| a == b).count();
                first.saturating_sub(VALUE_CAP / 2)
            }
            _ => 0,
        };
        let value = |printed: Option<Printed>, chars: Option<Vec<char>>| {
            Some(printed?.window(&chars?, start, VALUE_CAP))
        };
        (value(left, left_chars), value(right, right_chars))
    }

    /// `term` printed in full (module documentation, "Printing"), not yet cut.
    fn render(&self, term: &Pattern) -> Printed {
        let note;
        if at_most_nodes(term, PRINT_NODES) {
            match &self.printer {
                Ok(printer) => {
                    let printed = printer.print_kore(
                        term,
                        &Options {
                            mode: Mode::Pretty,
                            color: false,
                            reverse_aliases: false,
                            sort_collections: true,
                            list_spelling: ListSpelling::Program,
                        },
                    );
                    if printed.warnings.is_empty() {
                        return Printed {
                            text: one_line(&printed.text),
                            rendering: "k",
                            note: None,
                        };
                    }
                    note = printed
                        .warnings
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join("; ");
                }
                Err(error) => note = format!("no K printer: {error}"),
            }
        } else {
            note = format!("more than {PRINT_NODES} nodes");
        }
        Printed {
            text: term.to_string(),
            rendering: "kore",
            note: Some(note),
        }
    }

    /// An end's summary: `{head, class}` (module documentation, "An end's summary").
    pub fn summary(&self, end: &Pattern) -> Value {
        json!({
            "head": self.computation_head(end).map(|head| self.print(head, HEAD_CAP)),
            "class": class(end),
        })
    }

    /// The summaries of a run's ends, in the set's order.
    pub fn summaries<'t>(&self, ends: impl IntoIterator<Item = &'t Pattern>) -> Value {
        Value::Array(ends.into_iter().map(|end| self.summary(end)).collect())
    }

    /// The summaries of the ends of a run with a stop, in the set's order, each with `halt`
    /// (module documentation, "An end's summary"): `stop` where some path of the run reached the
    /// end at its last stop (its projection is one of `stopped`'s, the run's stop ends,
    /// kink-campaign `TestEvidence::stop_ends`, projected as the slot projects them), `own` where
    /// every path that reached it ended on its own. Evidence only: both are ends of the truncated
    /// system, compared alike.
    pub fn halted_summaries<'t>(
        &self,
        ends: impl IntoIterator<Item = &'t Pattern>,
        stopped: &BTreeSet<Pattern>,
    ) -> Value {
        let stopped = stopped
            .iter()
            .map(|end| self.compared(end))
            .collect::<BTreeSet<_>>();
        Value::Array(
            ends.into_iter()
                .map(|end| {
                    let mut summary = self.summary(end);
                    summary["halt"] = json!(if stopped.contains(end) { "stop" } else { "own" });
                    summary
                })
                .collect(),
        )
    }

    /// An end as the second slot compares it: with the cells it leaves out replaced
    /// ([`Self::projecting`]), else with `<generatedCounter>`'s content erased.
    fn compared(&self, end: &Pattern) -> Pattern {
        match &self.projection {
            Some(projection) => projection.project(end).into_owned(),
            None => counter_erased(end).into_owned(),
        }
    }

    /// The cells of `target`, a pattern's compiled target, that it names: each cell an application
    /// in `target` gives a content of its own, an argument that is neither a cell nor a variable
    /// `generated` holds (module documentation, "A query witness").
    pub fn named_cells(
        &self,
        target: &Pattern,
        generated: &dyn Fn(&str) -> bool,
    ) -> BTreeSet<String> {
        let mut named = BTreeSet::new();
        let mut pending = vec![target];
        while let Some(term) = pending.pop() {
            if let Some((symbol, arguments)) = self.is_cell(term)
                && arguments.iter().any(|argument| {
                    self.is_cell(argument).is_none()
                        && !matches!(argument, Pattern::Variable(variable)
                            if generated(&variable.name))
                })
            {
                named.insert(symbol.to_owned());
            }
            pending.extend(walk::children(term));
        }
        named
    }

    /// A query witness's state for a reader (module documentation, "A query witness"):
    /// `{cells: [{path, named, value}]}`, a cell of `named` printed in full and every other cell
    /// shortened.
    pub fn witness_state(&self, state: &Pattern, named: &BTreeSet<String>) -> Value {
        let mut cells = Vec::new();
        let mut pending = vec![(state, Vec::new())];
        while let Some((term, mut path)) = pending.pop() {
            let Some((symbol, arguments)) = self.is_cell(term) else {
                cells.push(json!({"path": path, "named": false, "value": self.shortened(term)}));
                continue;
            };
            path.push(label_or_name(symbol));
            let content = match arguments {
                [content] => content,
                _ => term,
            };
            if named.contains(symbol) {
                cells.push(json!({
                    "path": path,
                    "named": true,
                    "value": self.print(content, usize::MAX),
                }));
            } else if !arguments.is_empty()
                && arguments
                    .iter()
                    .all(|argument| self.is_cell(argument).is_some())
            {
                pending.extend(arguments.iter().rev().map(|child| (child, path.clone())));
            } else {
                cells.push(json!({
                    "path": path,
                    "named": false,
                    "value": self.shortened(content),
                }));
            }
        }
        json!({ "cells": cells })
    }

    /// A query witness's binding value for a reader (module documentation, "A query witness"): a
    /// long collection by its length and some elements, any other value printed in full.
    pub fn witness_value(&self, value: &Pattern) -> Value {
        self.long_collection(value)
            .unwrap_or_else(|| self.print(value, usize::MAX))
    }

    /// A cell the pattern does not name, shortened: a long collection by its length and some
    /// elements, any other content cut at [`HEAD_CAP`].
    fn shortened(&self, content: &Pattern) -> Value {
        self.long_collection(content)
            .unwrap_or_else(|| self.print(content, HEAD_CAP))
    }

    /// A concrete collection of more than [`WITNESS_ITEMS`] elements, as `{collection, length,
    /// last}` for a list (its last elements, in order) or `{collection, length, first}` for a map
    /// or a set (its first entries in printed order, the order of their printed keys, as K prints
    /// a map), each element printed and cut at [`HEAD_CAP`]; `None` for any other term.
    fn long_collection(&self, term: &Pattern) -> Option<Value> {
        let printed = |term: &Pattern| self.print(term, HEAD_CAP);
        if let Some(items) = self.list_items(term) {
            return (items.len() > WITNESS_ITEMS).then(|| {
                json!({
                    "collection": "list",
                    "length": items.len(),
                    "last": items[items.len() - WITNESS_ITEMS..]
                        .iter()
                        .map(|item| printed(item))
                        .collect::<Vec<_>>(),
                })
            });
        }
        for (name, collection) in [("map", &self.map), ("set", &self.set)] {
            let Some(elements) = collection.elements(term) else {
                continue;
            };
            if elements.len() <= WITNESS_ITEMS {
                return None;
            }
            let mut entries = elements
                .iter()
                .map(|arguments| {
                    let key = arguments.first().map(printed);
                    let text = key
                        .as_ref()
                        .and_then(|key| key["text"].as_str())
                        .unwrap_or_default()
                        .to_owned();
                    (text, *arguments)
                })
                .collect::<Vec<_>>();
            entries.sort_by(|(left, a), (right, b)| left.cmp(right).then_with(|| a.cmp(b)));
            let first = entries
                .iter()
                .take(WITNESS_ITEMS)
                .map(|(_, arguments)| match *arguments {
                    [key, value] => json!({"key": printed(key), "value": printed(value)}),
                    [element] => printed(element),
                    _ => Value::Null,
                })
                .collect::<Vec<_>>();
            return Some(json!({
                "collection": name,
                "length": elements.len(),
                "first": first,
            }));
        }
        None
    }

    /// The kill evidence of two end sets (module documentation): the front end's document when
    /// a renderer is set and both sets have an end, else kink's own ([`K_EVIDENCE_VERSION`]:
    /// `{format, outside, path, baseline, mutant}`, each side `{final_configurations, complete,
    /// classes, end, value}`, with `note` when a renderer showed no difference); `None` when no
    /// end of one is outside the other (no complete pair of sets that a slot distinguished).
    pub fn difference(
        &self,
        baseline: &BTreeSet<Pattern>,
        mutant: &BTreeSet<Pattern>,
        mutant_complete: bool,
    ) -> Option<Value> {
        let mut own = self.own_difference(baseline, mutant, mutant_complete)?;
        let Some(renderer) = self.renderer.get() else {
            return Some(own);
        };
        if baseline.is_empty() || mutant.is_empty() {
            return Some(own);
        }
        let format = renderer.format();
        let note = match renderer.difference(baseline, mutant, mutant_complete, &self.not_compared)
        {
            Ok(document) if document["format"] == format => return Some(document),
            Ok(document) => format!(
                "the front end's evidence names the format {}, not {format}",
                document["format"]
            ),
            Err(reason) => reason,
        };
        own["note"] = json!(format!("no {format} evidence: {note}"));
        Some(own)
    }

    /// kink's own evidence of two end sets (module documentation): `{format, outside, path,
    /// baseline, mutant}`; `None` when no end of one is outside the other.
    fn own_difference(
        &self,
        baseline: &BTreeSet<Pattern>,
        mutant: &BTreeSet<Pattern>,
        mutant_complete: bool,
    ) -> Option<Value> {
        let (outside, from, to) = match mutant.iter().find(|end| !baseline.contains(*end)) {
            Some(end) => ("mutant", end, baseline),
            None if mutant_complete => (
                "baseline",
                baseline.iter().find(|end| !mutant.contains(*end))?,
                mutant,
            ),
            None => return None,
        };
        let nearest = to.iter().min_by_key(|end| self.distance(from, end));
        let (path, from_value, to_value) = match nearest {
            Some(near) => {
                let found = self.first_difference(from, near);
                let (from_value, to_value) = self.print_values(found.left, found.right);
                (
                    Value::Array(found.path.into_iter().map(Value::String).collect()),
                    from_value,
                    to_value,
                )
            }
            None => (Value::Null, None, None),
        };
        let side = |set: &BTreeSet<Pattern>, complete: bool, end: Option<&Pattern>, value| {
            json!({
                "final_configurations": set.len(),
                "complete": complete,
                "classes": set.iter().map(class).collect::<BTreeSet<_>>(),
                "end": end.map(|end| self.summary(end)),
                "value": value,
            })
        };
        let (baseline_side, mutant_side) = if outside == "mutant" {
            (
                side(baseline, true, nearest, to_value),
                side(mutant, mutant_complete, Some(from), from_value),
            )
        } else {
            (
                side(baseline, true, Some(from), from_value),
                side(mutant, mutant_complete, nearest, to_value),
            )
        };
        Some(json!({
            "format": K_EVIDENCE_VERSION,
            "outside": outside,
            "path": path,
            "baseline": baseline_side,
            "mutant": mutant_side,
        }))
    }

    /// The kill evidence of one test from its two sides' evidence (module documentation, "The
    /// ends compared"); `None` when the baseline side holds no whole-term value. Where the second
    /// slot leaves cells out ([`Self::projecting`]), its values are the projected ends, and the
    /// one-sided ends are projected as the slot projects them, so the evidence never shows a
    /// difference in a cell left out.
    pub fn test_difference(&self, baseline: &TestEvidence, mutant: &TestEvidence) -> Option<Value> {
        let baseline_set = whole_term(&baseline.run)?;
        match whole_term(&mutant.run) {
            Some(mutant_set) => self.difference(baseline_set, mutant_set, true),
            None => {
                let one_sided = mutant
                    .one_sided_ends
                    .iter()
                    .map(|end| self.compared(end))
                    .collect();
                self.difference(baseline_set, &one_sided, false)
            }
        }
    }

    /// The evidence of a difference of observation channels (module documentation, "Observation
    /// evidence"): the front end's document when its renderer writes observation evidence
    /// ([`EndRenderer::observation_difference`]), else kink's own ([`Self::own_observation`]),
    /// with `note` when a renderer showed no difference.
    #[must_use]
    pub fn observation_difference(
        &self,
        difference: &ObservedDifference,
        observe: Option<&crate::manifest::ObserveSection>,
    ) -> Value {
        let mut own = self.own_observation(difference, observe);
        let Some(renderer) = self.renderer.get() else {
            return own;
        };
        let Some(format) = renderer.observation_format() else {
            return own;
        };
        let note = match renderer.observation_difference(difference, observe) {
            Ok(document) if document["format"] == format => return document,
            Ok(document) => format!(
                "the front end's evidence names the format {}, not {format}",
                document["format"]
            ),
            Err(reason) => reason,
        };
        own["note"] = json!(format!("no {format} evidence: {note}"));
        own
    }

    /// kink's evidence of a difference of the two sides' prefix sets (module documentation,
    /// "Observation evidence"; kink-campaign `Outside`), which no capture run re-derives, since
    /// no one baseline path holds the difference: `{format, position: {channel, index, at_end,
    /// outside}, mutant: {element}}`, `format` [`K_SET_EVIDENCE_VERSION`]. Where the mutant's
    /// prefix is outside, `mutant.element` is its element at the index, read where its probe
    /// found the difference ([`Self::element`]), and no path of the baseline has the prefix it
    /// ends; where the baseline's is outside, a real path of the baseline has a prefix of that
    /// length that no path of the mutant has, and `mutant.element` is `"absent"`.
    #[must_use]
    pub fn observation_set_difference(
        &self,
        verdict: &kink_campaign::ObservationVerdict,
        observe: Option<&crate::manifest::ObserveSection>,
    ) -> Value {
        let Some(position) = &verdict.position else {
            return Value::Null;
        };
        let cells = observe.and_then(|observe| {
            observe
                .points
                .iter()
                .find(|point| point.name == position.channel)
                .map(|point| point.cells.as_slice())
        });
        let mutant = match (&verdict.element, position.outside) {
            (Some(element), Some(kink_campaign::Outside::Mutant)) => self.element(element, cells),
            _ => json!("absent"),
        };
        json!({
            "format": K_SET_EVIDENCE_VERSION,
            "position": {
                "channel": position.channel,
                "index": position.index,
                "at_end": position.at_end,
                "outside": position.outside.map(kink_campaign::Outside::name),
            },
            "mutant": {"element": mutant},
        })
    }

    /// kink's own evidence of a difference of observation channels: `{format, position:
    /// {channel, index, at_end}, baseline: {element}, mutant: {element}}`, each element as
    /// [`Self::element`] prints it under the declaration `observe` (the manifest's, which names
    /// each class's cells).
    fn own_observation(
        &self,
        difference: &ObservedDifference,
        observe: Option<&crate::manifest::ObserveSection>,
    ) -> Value {
        let position = &difference.position;
        let cells = observe.and_then(|observe| {
            observe
                .points
                .iter()
                .find(|point| point.name == position.channel)
                .map(|point| point.cells.as_slice())
        });
        json!({
            "format": K_EVIDENCE_VERSION,
            "position": {
                "channel": position.channel,
                "index": position.index,
                "at_end": position.at_end,
            },
            "baseline": {"element": self.element(&difference.baseline, cells)},
            "mutant": {"element": self.element(&difference.mutant, cells)},
        })
    }

    /// One element of an observation difference printed for a reader: `{cells: {<cell>: value}}`
    /// for a point class's content, by the class's cells `cells` in order, `{item: value}` for a
    /// log's, each value as [`Self::print`] prints it (cut at [`VALUE_CAP`]); `{value}` for an
    /// element a front end's functions gave, its document as the front end wrote it; `"end"`,
    /// `"undefined"`, `"cycle"` (the side's path returned to an earlier state, so its channel has
    /// no element there, ever) or `"undecided"` otherwise.
    fn element(&self, element: &Element, cells: Option<&[String]>) -> Value {
        match element {
            Element::Content(values) => match cells {
                Some(cells) if cells.len() == values.len() => {
                    let cells = cells
                        .iter()
                        .zip(values)
                        .map(|(cell, value)| (cell.clone(), self.print(value, VALUE_CAP)))
                        .collect::<serde_json::Map<_, _>>();
                    json!({"cells": cells})
                }
                _ => match values.as_slice() {
                    [item] => json!({"item": self.print(item, VALUE_CAP)}),
                    values => json!({"values": values
                        .iter()
                        .map(|value| self.print(value, VALUE_CAP))
                        .collect::<Vec<_>>()}),
                },
            },
            Element::Evaluated(value) => json!({"value": value}),
            Element::End => json!("end"),
            Element::Undefined => json!("undefined"),
            Element::Cycle => json!("cycle"),
            Element::Undecided => json!("undecided"),
        }
    }

    /// The computation head of an end (module documentation, "An end's summary"): the first item
    /// of its first main cell in pre-order over its cells, or the cell's content when that is no
    /// sequence.
    pub fn computation_head<'t>(&self, end: &'t Pattern) -> Option<&'t Pattern> {
        let mut pending = vec![end];
        while let Some(term) = pending.pop() {
            let Some((symbol, arguments)) = self.is_cell(term) else {
                continue;
            };
            if !self.main_cells.contains(symbol) {
                pending.extend(arguments.iter().rev());
                continue;
            }
            let [content] = arguments else {
                return None;
            };
            return Some(match content {
                Pattern::Application { symbol, arguments }
                    if symbol.name == KSEQ && arguments.len() == 2 =>
                {
                    &arguments[0]
                }
                _ => content,
            });
        }
        None
    }

    fn is_cell<'t>(&self, term: &'t Pattern) -> Option<(&'t str, &'t [Pattern])> {
        match term {
            Pattern::Application { symbol, arguments } if self.cells.contains(&symbol.name) => {
                Some((symbol.name.as_str(), arguments.as_slice()))
            }
            _ => None,
        }
    }

    /// The entries of a concrete map, by key; `None` for any other term (a symbolic map, a map
    /// with a repeated key, a term that is not a map).
    fn map_entries<'t>(&self, term: &'t Pattern) -> Option<BTreeMap<&'t Pattern, &'t Pattern>> {
        let mut entries = BTreeMap::new();
        for element in self.map.elements(term)? {
            let [key, value] = element else {
                return None;
            };
            if entries.insert(key, value).is_some() {
                return None;
            }
        }
        Some(entries)
    }

    /// The elements of a concrete list, in order; `None` for any other term.
    fn list_items<'t>(&self, term: &'t Pattern) -> Option<Vec<&'t Pattern>> {
        self.list
            .elements(term)?
            .into_iter()
            .map(|element| match element {
                [item] => Some(item),
                _ => None,
            })
            .collect()
    }

    /// The cell distance of two terms (module documentation, "The pair of ends").
    fn distance(&self, left: &Pattern, right: &Pattern) -> usize {
        let mut distance = 0;
        let mut pending = vec![(left, right)];
        while let Some((left, right)) = pending.pop() {
            if left == right {
                continue;
            }
            if let (Some((l, la)), Some((r, ra))) = (self.is_cell(left), self.is_cell(right))
                && l == r
                && la.len() == ra.len()
            {
                pending.extend(la.iter().zip(ra));
                continue;
            }
            if let (Some(l), Some(r)) = (self.map_entries(left), self.map_entries(right)) {
                let keys = l.keys().chain(r.keys()).collect::<BTreeSet<_>>();
                distance += keys
                    .into_iter()
                    .filter(|key| l.get(*key) != r.get(*key))
                    .count();
                continue;
            }
            distance += 1;
        }
        distance
    }

    /// The first differing cell path of two different terms and the two values there (module
    /// documentation, "The first differing cell path").
    fn first_difference<'t>(&self, left: &'t Pattern, right: &'t Pattern) -> Found<'t> {
        let mut path = Vec::new();
        let (mut left, mut right) = (left, right);
        while let (Some((l, la)), Some((r, ra))) = (self.is_cell(left), self.is_cell(right)) {
            if l != r || la.len() != ra.len() {
                break;
            }
            path.push(label_or_name(l));
            let Some((cl, cr)) = la.iter().zip(ra).find(|(cl, cr)| cl != cr) else {
                // Equal cells: the caller passes different terms, so this is not reached.
                break;
            };
            (left, right) = (cl, cr);
            let same_cell = matches!(
                (self.is_cell(cl), self.is_cell(cr)),
                (Some((a, aa)), Some((b, ba))) if a == b && aa.len() == ba.len()
            );
            if !same_cell {
                break;
            }
        }
        let (mut left, mut right) = (Some(left), Some(right));
        while let (Some(l), Some(r)) = (left, right) {
            if let (Some(lm), Some(rm)) = (self.map_entries(l), self.map_entries(r)) {
                let keys = lm.keys().chain(rm.keys()).collect::<BTreeSet<_>>();
                let Some(key) = keys.into_iter().find(|key| lm.get(*key) != rm.get(*key)) else {
                    break;
                };
                let key_text = self.print(key, HEAD_CAP);
                path.push(format!(
                    "[{}]",
                    key_text["text"].as_str().unwrap_or_default()
                ));
                (left, right) = (lm.get(key).copied(), rm.get(key).copied());
            } else if let (Some(ll), Some(rl)) = (self.list_items(l), self.list_items(r)) {
                let Some(index) =
                    (0..ll.len().max(rl.len())).find(|index| ll.get(*index) != rl.get(*index))
                else {
                    break;
                };
                path.push(format!("[{index}]"));
                (left, right) = (ll.get(index).copied(), rl.get(index).copied());
            } else {
                break;
            }
        }
        Found { path, left, right }
    }
}

/// A first difference: the cell path and the two values there (`None` for a map key one side
/// lacks, or a list index past one side's end).
struct Found<'t> {
    path: Vec<String>,
    left: Option<&'t Pattern>,
    right: Option<&'t Pattern>,
}

/// A term printed in full: its text, `"k"` or `"kore"`, and why it is KORE when it is.
struct Printed {
    text: String,
    rendering: &'static str,
    note: Option<String>,
}

impl Printed {
    /// `{text, rendering, truncated, offset}` (and `note` for KORE): the at most `cap` characters
    /// of the text (`chars`) from character `start`; `truncated` when any is left out.
    fn window(&self, chars: &[char], start: usize, cap: usize) -> Value {
        let start = start.min(chars.len());
        let end = chars.len().min(start.saturating_add(cap));
        let mut value = json!({
            "text": chars[start..end].iter().collect::<String>(),
            "rendering": self.rendering,
            "truncated": start > 0 || end < chars.len(),
            "offset": start,
        });
        if let Some(note) = &self.note {
            value["note"] = json!(note);
        }
        value
    }
}

/// The whole-term value of a side's run, when it is one.
fn whole_term(run: &SideRun) -> Option<&BTreeSet<Pattern>> {
    let SideRun::Sides { sides } = run else {
        return None;
    };
    sides.iter().find_map(|side| match side {
        OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(terms))) => Some(terms),
        _ => None,
    })
}

/// An end's class: the flow's classifier's answer for it, as the exit-stop slot projects it.
pub fn class(end: &Pattern) -> String {
    crate::results::kebab(&format!("{:?}", crate::results::classify(end)))
}

/// Whether `term` has at most `limit` nodes (an iterative count that stops at the limit).
fn at_most_nodes(term: &Pattern, limit: usize) -> bool {
    let mut count = 0;
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        count += 1;
        if count > limit {
            return false;
        }
        pending.extend(walk::children(term));
    }
    true
}

/// A print's layout on one line: every run of whitespace that holds a newline becomes one space.
/// K text writes a newline inside a literal as an escape, so no token holds one.
fn one_line(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut pending = String::new();
    for c in text.chars() {
        if c.is_whitespace() {
            pending.push(c);
            continue;
        }
        if pending.contains('\n') {
            out.push(' ');
        } else {
            out.push_str(&pending);
        }
        pending.clear();
        out.push(c);
    }
    out.trim().to_owned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::outcomes::{CachedOutcome, OutcomeRecord, OutcomeStore};
    use k_rust::kore::parser::parse_pattern;
    use kink_campaign::{ExitStop, OracleOutcome, RunNotes, TerminalClass};

    const TOP: &str = "Lbl'-LT-'generatedTop'-GT-'";
    const K: &str = "Lbl'-LT-'k'-GT-'";
    const REGS: &str = "Lbl'-LT-'regs'-GT-'";
    const COUNTER: &str = "Lbl'-LT-'generatedCounter'-GT-'";
    const CONCAT: &str = "Lbl'Unds'Map'Unds'";
    const ELEMENT: &str = "Lbl'UndsPipe'-'-GT-Unds'";
    const UNIT: &str = "Lbl'Stop'Map";
    const CODE: &str = "Lbl'-LT-'code'-GT-'";
    const BUS: &str = "Lbl'-LT-'bus'-GT-'";
    const LIST: [&str; 3] = ["Lbl'Unds'List'Unds'", "LblListItem", "Lbl'Stop'List"];

    /// A reader whose main cell is `<k>`, as k-rust makes a cell named `k`.
    fn reader() -> EndReader {
        EndReader::with_symbols(
            &[TOP, K, REGS, COUNTER, CODE, BUS],
            &[K],
            [CONCAT, ELEMENT, UNIT],
            LIST,
        )
    }

    fn int(value: i64) -> String {
        format!("\\dv{{SortInt{{}}}}(\"{value}\")")
    }

    /// `<generatedTop> <k> head ~> .K </k> <regs> map </regs> <generatedCounter> counter
    /// </generatedCounter> </generatedTop>`, the map's entries `key |-> value`.
    fn config(head: &str, regs: &[(i64, i64)], counter: i64) -> Pattern {
        let map = regs
            .iter()
            .fold(format!("{UNIT}{{}}()"), |map, (key, value)| {
                format!(
                    "{CONCAT}{{}}({ELEMENT}{{}}({}, {}), {map})",
                    int(*key),
                    int(*value)
                )
            });
        parse_pattern(&format!(
            "{TOP}{{}}({K}{{}}(kseq{{}}({head}, dotk{{}}())), {REGS}{{}}({map}), {COUNTER}{{}}({}))",
            int(counter)
        ))
        .unwrap()
    }

    const LOCKED: &str = "LblstepLocked{}()";

    /// FB-51: a witness prints the cells the pattern names in full and shortens every other by
    /// its structure: a long map by its length and its first entries in printed order, a long
    /// list by its length and its last elements, any other content cut at [`HEAD_CAP`]. A binding
    /// of a long list is shortened so too, and a short value is printed whole.
    #[test]
    fn a_witness_prints_the_named_cells_and_shortens_the_rest() {
        let reader = reader();
        let generated = |name: &str| name.starts_with("Var'Unds'");
        let target = parse_pattern(&format!(
            "{TOP}{{}}({K}{{}}(kseq{{}}(VarX:SortKItem{{}}, Var'Unds'DotVar0:SortK{{}})), \
             Var'Unds'DotVar1:SortGeneratedCounterCell{{}})"
        ))
        .unwrap();
        let named = reader.named_cells(&target, &generated);
        assert_eq!(named, BTreeSet::from([K.to_owned()]));
        let [concat, element, unit] = LIST;
        let list = (1..=12).fold(format!("{unit}{{}}()"), |list, item| {
            format!("{concat}{{}}({list}, {element}{{}}({}))", int(item))
        });
        let regs = (1..=10).map(|key| (key, key * 100)).collect::<Vec<_>>();
        let state = config(LOCKED, &regs, 7);
        let Pattern::Application { symbol, arguments } = &state else {
            panic!("a configuration");
        };
        let (symbol, mut arguments) = (symbol.clone(), arguments.clone());
        arguments.insert(2, parse_pattern(&format!("{BUS}{{}}({list})")).unwrap());
        let state = Pattern::Application { symbol, arguments };
        let witness = reader.witness_state(&state, &named);
        let cells = witness["cells"].as_array().unwrap();
        let paths = cells
            .iter()
            .map(|cell| cell["path"].as_array().unwrap().last().unwrap().clone())
            .collect::<Vec<_>>();
        assert_eq!(
            paths,
            [
                json!("<k>"),
                json!("<regs>"),
                json!("<bus>"),
                json!("<generatedCounter>")
            ],
            "{witness:#}"
        );
        assert_eq!(cells[0]["path"], json!(["<generatedTop>", "<k>"]));
        assert_eq!(cells[0]["named"], true);
        assert_eq!(cells[0]["value"]["truncated"], false);
        assert!(
            cells[0]["value"]["text"].as_str().unwrap().contains(LOCKED),
            "{witness:#}"
        );
        let map = &cells[1]["value"];
        assert_eq!(
            (&map["collection"], &map["length"]),
            (&json!("map"), &json!(10))
        );
        let first = map["first"].as_array().unwrap();
        assert_eq!(first.len(), WITNESS_ITEMS);
        // Printed order: the key printed `...("10")` comes before `...("2")`.
        assert_eq!(first[0]["key"]["text"], int(1));
        assert_eq!(first[1]["key"]["text"], int(10));
        assert_eq!(first[1]["value"]["text"], int(1000));
        let rom = &cells[2]["value"];
        assert_eq!(
            (&rom["collection"], &rom["length"]),
            (&json!("list"), &json!(12))
        );
        let last = rom["last"]
            .as_array()
            .unwrap()
            .iter()
            .map(|item| item["text"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        assert_eq!(last, (5..=12).map(int).collect::<Vec<_>>());
        assert_eq!(cells[3]["named"], false);
        assert_eq!(cells[3]["value"]["text"], int(7));
        let binding = reader.witness_value(&parse_pattern(&list).unwrap());
        assert_eq!(binding["length"], 12, "{binding:#}");
        assert_eq!(binding["last"].as_array().unwrap().len(), WITNESS_ITEMS);
        assert_eq!(
            reader.witness_value(&parse_pattern(&int(3)).unwrap())["text"],
            int(3)
        );
    }

    fn set(ends: &[Pattern]) -> BTreeSet<Pattern> {
        ends.iter().cloned().collect()
    }

    #[test]
    fn a_kill_names_the_first_differing_cell_path_and_both_values() {
        let baseline = config(LOCKED, &[(1, 1), (2, 2)], 0);
        let mutant = config(LOCKED, &[(1, 1), (2, 3)], 0);
        let difference = reader()
            .difference(&set(&[baseline]), &set(&[mutant]), true)
            .unwrap();
        assert_eq!(difference["outside"], "mutant");
        assert_eq!(
            difference["path"],
            json!(["<generatedTop>", "<regs>", format!("[{}]", int(2))])
        );
        // Without a printer (this reader has none) both values are KORE text, saying why.
        assert_eq!(difference["baseline"]["value"]["text"], int(2));
        assert_eq!(difference["mutant"]["value"]["text"], int(3));
        assert_eq!(difference["mutant"]["value"]["rendering"], "kore");
        assert_eq!(difference["mutant"]["value"]["truncated"], false);
        assert!(difference["mutant"]["value"]["note"].is_string());
        for side in ["baseline", "mutant"] {
            let side = &difference[side];
            assert_eq!(side["final_configurations"], 1);
            assert_eq!(side["complete"], true);
            assert_eq!(side["classes"], json!(["normal"]));
            assert_eq!(side["end"]["head"]["text"], LOCKED);
            assert_eq!(side["end"]["class"], "normal");
        }
    }

    #[test]
    fn a_key_one_map_lacks_is_a_null_value_and_a_head_cell_stops_the_path() {
        let difference = reader()
            .difference(
                &set(&[config(LOCKED, &[(1, 1)], 0)]),
                &set(&[config(LOCKED, &[(1, 1), (4, 4)], 0)]),
                true,
            )
            .unwrap();
        assert_eq!(
            difference["path"],
            json!(["<generatedTop>", "<regs>", format!("[{}]", int(4))])
        );
        assert_eq!(difference["baseline"]["value"], Value::Null);
        assert_eq!(difference["mutant"]["value"]["text"], int(4));
        // A difference in the computation stops at `<k>`: its content is no cell and no map.
        let difference = reader()
            .difference(
                &set(&[config(LOCKED, &[(1, 1)], 0)]),
                &set(&[config("LblstepBoundary{}()", &[(1, 1)], 0)]),
                true,
            )
            .unwrap();
        assert_eq!(difference["path"], json!(["<generatedTop>", "<k>"]));
        assert_eq!(
            difference["mutant"]["end"]["head"]["text"],
            "LblstepBoundary{}()"
        );
    }

    #[test]
    fn the_nearest_baseline_end_is_the_one_differing_in_fewest_cells() {
        let mutant = config(LOCKED, &[(1, 1), (2, 3)], 0);
        let far = config(LOCKED, &[(1, 5), (2, 5)], 0);
        let near = config(LOCKED, &[(1, 1), (2, 2)], 0);
        let reader = reader();
        assert_eq!(reader.distance(&mutant, &far), 2);
        assert_eq!(reader.distance(&mutant, &near), 1);
        let difference = reader
            .difference(
                &set(&[far.clone(), near]),
                &set(std::slice::from_ref(&mutant)),
                true,
            )
            .unwrap();
        assert_eq!(difference["baseline"]["value"]["text"], int(2));
        assert_eq!(difference["baseline"]["final_configurations"], 2);
        // Among equally near ends, the first in the set's order.
        let other = config(LOCKED, &[(1, 6), (2, 6)], 0);
        assert_eq!(reader.distance(&mutant, &other), 2);
        let tied = set(&[far.clone(), other]);
        let expected = if *tied.iter().next().unwrap() == far {
            int(5)
        } else {
            int(6)
        };
        let difference = reader.difference(&tied, &set(&[mutant]), true).unwrap();
        assert_eq!(difference["path"][2], format!("[{}]", int(1)));
        assert_eq!(difference["baseline"]["value"]["text"], expected);
    }

    #[test]
    fn a_baseline_end_the_mutant_lacks_is_the_evidence_when_every_mutant_end_is_the_baselines() {
        let kept = config(LOCKED, &[(1, 1)], 0);
        let lost = config(LOCKED, &[(1, 2)], 0);
        let difference = reader()
            .difference(
                &set(&[kept.clone(), lost]),
                &set(std::slice::from_ref(&kept)),
                true,
            )
            .unwrap();
        assert_eq!(difference["outside"], "baseline");
        assert_eq!(difference["baseline"]["value"]["text"], int(2));
        assert_eq!(difference["mutant"]["value"]["text"], int(1));
        assert_eq!(difference["mutant"]["final_configurations"], 1);
        // A mutant with no end (every path an undefined step): no pair, so no path or value.
        let difference = reader()
            .difference(&set(std::slice::from_ref(&kept)), &BTreeSet::new(), true)
            .unwrap();
        assert_eq!(difference["outside"], "baseline");
        assert_eq!(difference["path"], Value::Null);
        assert_eq!(difference["mutant"]["end"], Value::Null);
        assert_eq!(difference["mutant"]["value"], Value::Null);
        assert_eq!(difference["mutant"]["classes"], json!([]));
        assert_eq!(difference["baseline"]["end"]["class"], "normal");
        // Equal sets have no difference.
        assert_eq!(
            reader().difference(&set(std::slice::from_ref(&kept)), &set(&[kept]), true),
            None
        );
    }

    fn whole_term(ends: &[Pattern]) -> SideRun {
        SideRun::Sides {
            sides: vec![
                OracleSide::Normal(OracleValue::ExitStop(BTreeSet::from([ExitStop {
                    class: TerminalClass::Normal,
                    code: None,
                }]))),
                OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(set(ends)))),
            ],
        }
    }

    fn evidence(run: SideRun, ends: &[Pattern]) -> TestEvidence {
        TestEvidence {
            test_id: "t".into(),
            run,
            notes: RunNotes::default(),
            ends: set(ends),
            undefined_steps: false,
            one_sided_ends: BTreeSet::new(),
            stop_ends: BTreeSet::new(),
            payloads: BTreeMap::new(),
        }
    }

    #[test]
    fn a_one_sided_kill_compares_the_one_sided_ends_that_killed() {
        let baseline_end = config(LOCKED, &[(1, 1)], 0);
        let baseline = evidence(
            whole_term(std::slice::from_ref(&baseline_end)),
            std::slice::from_ref(&baseline_end),
        );
        // The mutant's run reached its work budget: both its sides are unknown, its ends are the
        // explored complete paths' ends, and its one-sided ends those of them the one-sided rule
        // kept (here the stuck end with 2), with the counter not yet erased. An explored end
        // outside the baseline's set that is no one-sided end (here with 0, before it in term
        // order) killed nothing, so it is not the evidence.
        let unknown = SideRun::Sides {
            sides: vec![OracleSide::Unknown, OracleSide::Unknown],
        };
        let one_sided = |ends: &[Pattern], kept: &[Pattern]| {
            let mut mutant = evidence(unknown.clone(), ends);
            mutant.one_sided_ends = set(kept);
            mutant
        };
        let (other, killing) = (config(LOCKED, &[(1, 0)], 7), config(LOCKED, &[(1, 2)], 7));
        let mutant = one_sided(
            &[other.clone(), killing.clone()],
            std::slice::from_ref(&killing),
        );
        let reader = reader();
        let difference = reader.test_difference(&baseline, &mutant).unwrap();
        assert_eq!(difference["outside"], "mutant");
        assert_eq!(difference["path"][1], "<regs>");
        assert_eq!(difference["mutant"]["complete"], false);
        assert_eq!(difference["mutant"]["final_configurations"], 1);
        assert_eq!(difference["mutant"]["value"]["text"], int(2));
        assert_eq!(difference["baseline"]["value"]["text"], int(1));
        // Without a one-sided end there is no evidence, whatever the explored ends are.
        assert_eq!(
            reader.test_difference(&baseline, &one_sided(&[other, killing], &[])),
            None
        );
        // A one-sided end that differs only in its counter is the baseline's end: no evidence,
        // and an incomplete mutant side never makes a baseline end the evidence.
        let counter_only = config(LOCKED, &[(1, 1)], 9);
        let same = one_sided(
            std::slice::from_ref(&counter_only),
            std::slice::from_ref(&counter_only),
        );
        assert_eq!(reader.test_difference(&baseline, &same), None);
        // The report reads the slots' sides from the difference: the mutant's value is unknown.
        let slots = crate::report::slots_value(
            &crate::results::ORACLE_SLOTS,
            &[OracleOutcome::Unknown, OracleOutcome::Distinguish],
            Some(&baseline.run),
            Some(&mutant.run),
            false,
            &difference,
        );
        assert_eq!(
            slots["whole-term"]["sides"],
            json!({
                "baseline": {"final_configurations": 1},
                "mutant": {"final_configurations": 1, "complete": false},
            })
        );
        // A two-sided kill's sides are the runs' own.
        let complete = evidence(
            whole_term(&[config(LOCKED, &[(1, 2)], 0)]),
            &[config(LOCKED, &[(1, 2)], 0)],
        );
        let difference = reader.test_difference(&baseline, &complete).unwrap();
        assert_eq!(difference["mutant"]["complete"], true);
    }

    #[test]
    fn a_cached_kill_keeps_its_difference_and_shows_its_sides() {
        let difference = reader()
            .difference(
                &set(&[config(LOCKED, &[(1, 1)], 0)]),
                &set(&[config(LOCKED, &[(1, 2)], 0)]),
                true,
            )
            .unwrap();
        let directory = std::env::temp_dir().join(format!("kink-flow-cf16-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        let store = kink_corpus::Store::new(&directory);
        let outcomes = OutcomeStore::new(&directory, json!({"test": "cf16"}));
        let identity = kink_patch::sha256(b"mutation");
        let program = kink_patch::sha256(b"program").to_string();
        let record = OutcomeRecord {
            program_id: "p".into(),
            baseline_run_sha256: "0".repeat(64),
            outcome: CachedOutcome::Killed,
            slots: vec![OracleOutcome::Agree, OracleOutcome::Distinguish],
            mutant_run_sha256: "1".repeat(64),
            difference: difference.clone(),
            cause: None,
            open_application: false,
            smt_unknowns: 0,
            decider_smt_unknowns: 0,
            allowance_bytes: None,
            observation: serde_json::Value::Null,
            polls: crate::outcomes::RunPolls {
                count: 0,
                bound: 0,
                cut: false,
            },
        };
        outcomes
            .write(
                &store,
                identity,
                "m",
                &Value::Null,
                &Value::Null,
                &[(program.clone(), record.clone())],
            )
            .unwrap();
        let read = outcomes.read(identity);
        assert_eq!(read.get(&program), Some(&record));
        let slots = crate::report::slots_value(
            &crate::results::ORACLE_SLOTS,
            &record.slots,
            None,
            None,
            false,
            &record.difference,
        );
        assert_eq!(
            slots["whole-term"]["sides"],
            json!({
                "baseline": {"final_configurations": 1},
                "mutant": {"final_configurations": 1},
            })
        );
        // The difference is in the record digest: an altered one is ignored like any other
        // altered record, and a file of the previous version is not current.
        let path = outcomes.path(identity);
        let mut file: Value =
            serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
        file["records"][&program]["difference"]["path"] = json!(["<elsewhere>"]);
        std::fs::write(&path, file.to_string()).unwrap();
        assert!(outcomes.read(identity).is_empty());
        file["records"][&program]["difference"] = difference;
        file["version"] = json!(crate::outcomes::OUTCOMES_VERSION - 1);
        std::fs::write(&path, file.to_string()).unwrap();
        assert!(outcomes.read(identity).is_empty());
        let _ = std::fs::remove_dir_all(&directory);
    }

    /// A front end's renderer that answers `answer`, with what it was given added to a document.
    struct Fixed(Result<Value, String>);

    impl EndRenderer for Fixed {
        fn format(&self) -> &'static str {
            "test-difference/1"
        }

        fn identity(&self) -> Result<Value, String> {
            Ok(json!({"names": "test"}))
        }

        fn difference(
            &self,
            baseline: &BTreeSet<Pattern>,
            mutant: &BTreeSet<Pattern>,
            mutant_complete: bool,
            not_compared: &[String],
        ) -> Result<Value, String> {
            self.0.clone().map(|mut document| {
                document["given"] = json!({
                    "baseline": baseline.len(),
                    "mutant": mutant.len(),
                    "mutant_complete": mutant_complete,
                    "not_compared": not_compared,
                });
                document
            })
        }
    }

    fn rendering(answer: Result<Value, String>) -> EndReader {
        reader().rendering(
            Renderer(Some(Arc::new(Fixed(answer)))),
            vec!["scratch".into()],
        )
    }

    #[test]
    fn a_front_ends_renderer_writes_the_evidence_in_its_format() {
        let baseline = set(&[config(LOCKED, &[(1, 1)], 0)]);
        let mutant = set(&[config(LOCKED, &[(1, 2)], 0)]);
        // kink's own evidence names its format.
        let own = reader().difference(&baseline, &mutant, true).unwrap();
        assert_eq!(own["format"], K_EVIDENCE_VERSION);
        // With a renderer the evidence is its document, given the slot's ends, whether the
        // mutant's are complete and the cells left out.
        let document = json!({"format": "test-difference/1"});
        assert_eq!(
            rendering(Ok(document.clone()))
                .difference(&baseline, &mutant, false)
                .unwrap(),
            json!({
                "format": "test-difference/1",
                "given": {
                    "baseline": 1,
                    "mutant": 1,
                    "mutant_complete": false,
                    "not_compared": ["scratch"],
                },
            })
        );
        // A renderer that shows no difference: kink's own evidence, saying why.
        let fallback = rendering(Err("the ends are equal".into()))
            .difference(&baseline, &mutant, true)
            .unwrap();
        assert_eq!(
            fallback["note"],
            "no test-difference/1 evidence: the ends are equal"
        );
        let mut without_note = fallback.clone();
        without_note.as_object_mut().unwrap().remove("note");
        assert_eq!(without_note, own);
        // A document that names another format is not taken.
        let other = rendering(Ok(json!({"format": "other/1"})))
            .difference(&baseline, &mutant, true)
            .unwrap();
        assert_eq!(other["format"], K_EVIDENCE_VERSION);
        assert!(
            other["note"].as_str().unwrap().contains("\"other/1\""),
            "{other:#}"
        );
        // A side with no end has no end a front end could show: kink's own evidence, no note.
        let empty = rendering(Ok(document.clone()))
            .difference(&baseline, &BTreeSet::new(), true)
            .unwrap();
        assert_eq!(empty["format"], K_EVIDENCE_VERSION);
        assert_eq!(empty.get("note"), None);
        // Equal sets are no kill: no evidence, whatever the renderer would say.
        assert_eq!(
            rendering(Ok(document)).difference(&baseline, &baseline, true),
            None
        );
    }

    #[test]
    fn a_front_ends_evidence_gives_a_cached_kills_sides_and_names_its_format_in_the_context() {
        // A cached or one-sided kill's sides are read from its evidence: a front end's names
        // each side's count of ends and whether it is complete.
        let document = json!({
            "format": "krs-difference/2",
            "left": {"name": "baseline", "ends": 2, "complete": true},
            "right": {"name": "mutant", "ends": 1, "complete": false},
        });
        let slots = crate::report::slots_value(
            &crate::results::ORACLE_SLOTS,
            &[OracleOutcome::Agree, OracleOutcome::Distinguish],
            None,
            None,
            false,
            &document,
        );
        assert_eq!(
            slots["whole-term"]["sides"],
            json!({
                "baseline": {"final_configurations": 2},
                "mutant": {"final_configurations": 1, "complete": false},
            })
        );
        // The tier-1 context names a front end's format and further inputs, and kink's own by
        // their absence, so a store never serves another renderer's evidence, nor one the same
        // renderer would write over other names.
        let context = |evidence: Option<&Value>| {
            crate::digest::outcome_context(
                kink_patch::sha256(b"build"),
                crate::digest::ExecutionDigest {
                    kind: crate::digest::EXECUTION_DIGEST_KIND,
                    digest: kink_patch::sha256(b"specification"),
                },
                crate::manifest::Budget::default(),
                &crate::observed::ResultProjection {
                    state: kink_campaign::StateProjection::WholeTerm,
                    compared: Some(vec!["k".into()]),
                    not_compared: Vec::new(),
                    unobservable: Vec::new(),
                },
                None,
                evidence,
                None,
            )
        };
        let own = context(None);
        assert_eq!(reader().renderer.evidence(), Ok(None));
        let evidence = rendering(Ok(json!({})))
            .renderer
            .evidence()
            .unwrap()
            .unwrap();
        assert_eq!(
            evidence,
            json!({"format": "test-difference/1", "identity": {"names": "test"}})
        );
        let front = context(Some(&evidence));
        assert_eq!(own.get("evidence"), None);
        assert_eq!(front["evidence"], evidence);
        let mut renamed = evidence.clone();
        renamed["identity"]["names"] = json!("renamed");
        assert_ne!(
            crate::digest::context_sha256(&front),
            crate::digest::context_sha256(&context(Some(&renamed)))
        );
        let mut without = front.clone();
        without.as_object_mut().unwrap().remove("evidence");
        assert_eq!(without, own);
    }

    #[test]
    fn prints_are_bounded_and_on_one_line() {
        assert_eq!(one_line("<k>\n  done ( 1 )\n</k>"), "<k> done ( 1 ) </k>");
        assert_eq!(one_line("\"a  b\""), "\"a  b\"");
        let long = "x".repeat(VALUE_CAP + 5);
        let printed = Printed {
            text: long.clone(),
            rendering: "k",
            note: None,
        };
        let chars = long.chars().collect::<Vec<_>>();
        let value = printed.window(&chars, 0, VALUE_CAP);
        assert_eq!(value["truncated"], true);
        assert_eq!(value["offset"], 0);
        assert_eq!(value["text"].as_str().unwrap().len(), VALUE_CAP);
        assert_eq!(printed.window(&chars, 0, VALUE_CAP + 5)["truncated"], false);
        assert!(at_most_nodes(&config(LOCKED, &[(1, 1)], 0), 100));
        assert!(!at_most_nodes(&config(LOCKED, &[(1, 1)], 0), 3));
    }

    #[test]
    fn the_computation_head_is_read_from_the_main_cell_whatever_its_name() {
        // `<code maincell="">`: the main cell is `<code>`, and a cell named `k` beside it is no
        // computation cell.
        let code = EndReader::with_symbols(
            &[TOP, K, CODE, COUNTER],
            &[CODE],
            [CONCAT, ELEMENT, UNIT],
            LIST,
        );
        let end = parse_pattern(&format!(
            "{TOP}{{}}({K}{{}}(kseq{{}}(LblstepBoundary{{}}(), dotk{{}}())), \
             {CODE}{{}}(kseq{{}}({LOCKED}, dotk{{}}())), {COUNTER}{{}}({}))",
            int(0)
        ))
        .unwrap();
        assert_eq!(code.summary(&end)["head"]["text"], LOCKED);
        // An empty main cell's head is its content, `.K`; an end without one has no head.
        let empty = parse_pattern(&format!("{TOP}{{}}({CODE}{{}}(dotk{{}}()))")).unwrap();
        assert_eq!(code.summary(&empty)["head"]["text"], "dotk{}()");
        let none = parse_pattern(&format!(
            "{TOP}{{}}({K}{{}}(kseq{{}}({LOCKED}, dotk{{}}())))"
        ))
        .unwrap();
        assert_eq!(code.summary(&none)["head"], Value::Null);
        // A reader whose main cell is `<k>` reads the other.
        assert_eq!(
            reader().summary(&end)["head"]["text"],
            "LblstepBoundary{}()"
        );
    }

    /// `<generatedTop> <bus> ListItem(b_0) ... </bus> </generatedTop>`.
    fn bus(items: &[i64]) -> Pattern {
        let [concat, element, unit] = LIST;
        let list = items
            .iter()
            .rev()
            .fold(format!("{unit}{{}}()"), |list, item| {
                format!("{concat}{{}}({element}{{}}({}), {list})", int(*item))
            });
        parse_pattern(&format!("{TOP}{{}}({BUS}{{}}({list}))")).unwrap()
    }

    #[test]
    fn a_list_cell_is_followed_to_its_first_differing_index() {
        let difference = reader()
            .difference(&set(&[bus(&[1, 2, 3])]), &set(&[bus(&[1, 2, 4])]), true)
            .unwrap();
        assert_eq!(
            difference["path"],
            json!(["<generatedTop>", "<bus>", "[2]"])
        );
        assert_eq!(difference["baseline"]["value"]["text"], int(3));
        assert_eq!(difference["mutant"]["value"]["text"], int(4));
        // An index past one list's end is a null value there.
        let difference = reader()
            .difference(&set(&[bus(&[1])]), &set(&[bus(&[1, 5])]), true)
            .unwrap();
        assert_eq!(difference["path"][2], "[1]");
        assert_eq!(difference["baseline"]["value"], Value::Null);
        assert_eq!(difference["mutant"]["value"]["text"], int(5));
    }

    #[test]
    fn long_values_are_cut_around_their_first_difference() {
        // Two `<k>` contents whose printed texts agree on far more than the cap.
        let string = |last: char| {
            format!(
                "\\dv{{SortString{{}}}}(\"{}{last}{}\")",
                "a".repeat(3 * VALUE_CAP),
                "z".repeat(VALUE_CAP)
            )
        };
        let difference = reader()
            .difference(
                &set(&[config(&string('b'), &[], 0)]),
                &set(&[config(&string('c'), &[], 0)]),
                true,
            )
            .unwrap();
        assert_eq!(difference["path"], json!(["<generatedTop>", "<k>"]));
        let (baseline, mutant) = (
            &difference["baseline"]["value"],
            &difference["mutant"]["value"],
        );
        let text = |value: &Value| value["text"].as_str().unwrap().to_owned();
        assert_ne!(text(baseline), text(mutant));
        for value in [baseline, mutant] {
            assert_eq!(value["truncated"], true);
            assert_eq!(text(value).chars().count(), VALUE_CAP);
            assert_eq!(value["offset"], baseline["offset"]);
            // The difference sits half a cap into the window.
            assert_eq!(text(value).chars().nth(VALUE_CAP / 2 - 1), Some('a'));
        }
        assert!(baseline["offset"].as_u64().unwrap() > 0);
        assert_eq!(text(baseline).chars().nth(VALUE_CAP / 2), Some('b'));
        // Short values start at the start.
        let difference = reader()
            .difference(
                &set(&[config(LOCKED, &[(1, 1)], 0)]),
                &set(&[config(LOCKED, &[(1, 2)], 0)]),
                true,
            )
            .unwrap();
        assert_eq!(difference["mutant"]["value"]["offset"], 0);
    }
}
