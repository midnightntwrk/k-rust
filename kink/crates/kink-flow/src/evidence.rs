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

use k_rust::{
    backend::counter_erased,
    definition::{AttributeKey, Sentence},
    kast::identifier::{encode, label_or_name},
    kore::{ast::Pattern, walk},
};
use kink_campaign::{CellProjection, FinalResult, OracleSide, OracleValue, SideRun, TestEvidence};
use kink_native::ValidatedDefinition;
use krs_unparse::{ListSpelling, Mode, Options, Unparser};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// The most characters of one printed value the evidence keeps.
pub const VALUE_CAP: usize = 2000;
/// The most characters of one printed computation head or map key.
pub const HEAD_CAP: usize = 200;
/// The most nodes of a term printed as K text; a larger one is printed as KORE (the printer is
/// recursive, and the text would be cut anyway).
pub const PRINT_NODES: usize = 100_000;
/// The KORE names of K's computation sequence.
const KSEQ: &str = "kseq";

/// What kill evidence and end summaries read from the compiled definition: its printer, its cell
/// symbols (and which are main cells), and its map and list symbols. Built once per command
/// ([`crate::results::BaselineRunner`]).
pub struct EndReader {
    /// The second slot's cell projection, when it leaves some cell out: the one-sided ends that
    /// killed are projected with it, as the slot projected them ([`Self::test_difference`]).
    projection: Option<CellProjection>,
    printer: Result<Unparser, String>,
    cells: BTreeSet<String>,
    main_cells: BTreeSet<String>,
    map: Collection,
    list: Collection,
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
            printer,
            cells: BTreeSet::new(),
            main_cells: BTreeSet::new(),
            map: Collection::default(),
            list: Collection::default(),
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

    /// A reader with no printer and the given cell, main cell, map and list symbols (KORE names;
    /// each collection's concatenation, element and unit), for tests.
    #[cfg(test)]
    fn with_symbols(cells: &[&str], main_cells: &[&str], map: [&str; 3], list: [&str; 3]) -> Self {
        let collection = |[concat, element, unit]: [&str; 3]| Collection {
            concat: BTreeSet::from([concat.to_owned()]),
            element: BTreeSet::from([element.to_owned()]),
            unit: BTreeSet::from([unit.to_owned()]),
        };
        Self {
            projection: None,
            printer: Err("no printer".into()),
            cells: cells.iter().map(|cell| (*cell).to_owned()).collect(),
            main_cells: main_cells.iter().map(|cell| (*cell).to_owned()).collect(),
            map: collection(map),
            list: collection(list),
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

    /// The kill evidence of two end sets (module documentation): `{outside, path, baseline,
    /// mutant}`, each side `{final_configurations, complete, classes, end, value}`; `None` when
    /// no end of one is outside the other (no complete pair of sets that a slot distinguished).
    pub fn difference(
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
                    .map(|end| match &self.projection {
                        Some(projection) => projection.project(end).into_owned(),
                        None => counter_erased(end).into_owned(),
                    })
                    .collect();
                self.difference(baseline_set, &one_sided, false)
            }
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
        let end = chars.len().min(start + cap);
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
            allowance_bytes: None,
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
        file["version"] = json!(1);
        std::fs::write(&path, file.to_string()).unwrap();
        assert!(outcomes.read(identity).is_empty());
        let _ = std::fs::remove_dir_all(&directory);
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
