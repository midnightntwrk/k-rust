//! The KRS names of a `coverage` document's guard nodes.
//!
//! kink-flow reports a guarded sentence's `guard` at the K level: each node of its written
//! `requires`, with the outcomes the comparable programs' runs saw where the node was reached
//! (`kink_flow::guards`). A KRS sentence's `requires` is not all the author's: KRS states the
//! test of each partial construct a condition evaluates before it (a definedness test), guards a
//! looked-up key or element (a lookup guard), and puts a `k::bits!` template's match test, the
//! template's range and each fixed run, before the authored condition. This module names every
//! node by what produced it and groups the guard as the author reads it.
//!
//! # Correspondence
//!
//! The emission's source map records the generated range and the origin of every node of the
//! Definition IR the K renders, nested by depth. The front end walks the map's nodes of the
//! sentence's condition along kink-flow's display tree: at every connective node the map's node
//! must render the same Boolean connective (its own text, outside its operands, is the
//! connective's K syntax) with the same operands, a left-nested chain of one conjunction or
//! disjunction read as one node as kink-flow reads it; at an atom the map's node must render no
//! connective. A sentence whose compiled condition has another shape (or more than one conjunct of
//! the written condition) is named by no guess: its guard and its nodes have `krs: null`, and the
//! document lists it under `krs.unmatched_guards` with the reason.
//!
//! # Origins and text
//!
//! A node is `authored` where its map node renders authored syntax, `template` inside a template's
//! match test (below), and otherwise the kind of the insertion that produced it
//! (`definedness_test`, `lookup_guard`, ...; `krs_ir::InsertedNode`), with `anchor`, the authored
//! construct the insertion serves. An authored range is the token that produced the node (an
//! operator's own token, `>` for `a > b`), so an atom's `text` is the source the atom renders: the
//! span from the first to the last authored token of its nodes, in the file of the atom's own,
//! with the parentheses that span opens or closes; a connective's `text` is its own token (`&&`,
//! `!`, an `else`). `line` and `column` position the text's start in the package's current source
//! as the rows' `krs` objects position a sentence, and the text is read only where that source is
//! still the revision the collector read; elsewhere `text`, `line` and `column` are null.
//!
//! # Templates
//!
//! A `k::bits!` template is pattern syntax: the KRS language moves its match test into the
//! condition, ahead of every authored conjunct, as the range test `v >= 0 && v < 2^w` and one
//! equality per fixed run of the template, most significant first, all of whose tokens take one
//! span. The occurrence of the template's binder in the sentence's left-hand side carries the
//! template's own range, its string literal, so the templates of a sentence and their order are
//! read from its left-hand side, and each template's string gives its number of conjuncts: two,
//! and one per maximal run of fixed bits (`0` and `1`, a space, a field letter or `_` ending a
//! run). The leading conjuncts of the condition's chain are then the templates', each checked to
//! be such a test of its binder at one span; a sentence where they are not is listed under
//! `krs.unmatched_guards`.
//!
//! # The grouping
//!
//! Each node of `guard.operands` gains `krs = {origin, item, text, file, line, column, anchor?}`,
//! and the guard gains `krs = {authored, generated, templates, held_by, refuted_by, never}`:
//!
//! - `authored`: the authored atoms (and exclusive connectives, whose outcomes are their own) in
//!   preorder, each `{path, text, file, line, column, true_by, false_by, undefined_by,
//!   undecided_by, never}`, the outcomes of its K node; the inserted joins between a test and the
//!   conjunct it guards are not operands, so the conjunct stands in the test's join's place.
//! - `generated`: each inserted atom (a definedness test or a lookup guard) with its `origin`, its
//!   K `text`, its `anchor` and its outcomes. A test that was `false` for some program means the
//!   construct it serves had no value there, so the sentence's condition did not hold. Generated
//!   guards are never counted as gaps of the authored guard; they do decide what is reached, since
//!   an authored conjunct after a false test was not.
//! - `templates`: `null`, or `{conjuncts, binders, matched_by, not_matched_by}`: the paths of the
//!   templates' conjuncts, each template by its source range, the programs with an entry whose
//!   templates all matched (the last template conjunct reached `true`) and those with an entry
//!   where one did not.
//! - `held_by`, `refuted_by` and `never` read the guard as the author's condition alone. Its
//!   conjuncts are the nodes below the condition's conjunctions, in written order; the authored
//!   ones are the author's condition, and the templates' and the inserted tests' are not. KRS
//!   joins conjuncts with `andThenBool`, so a conjunct is reached only where every conjunct
//!   before it was `true`. `held_by` lists the programs for which the last authored conjunct was
//!   reached `true`, where the author's condition was seen to hold, and `refuted_by` those for
//!   which some authored conjunct was reached `false`. A template that did not match, or an
//!   inserted test that was `false`, refutes nothing the author wrote: the first is a pattern miss
//!   (`templates`), the second leaves the authored conjunct it guards unreached or, inside it,
//!   undefined, which that operand's own outcomes report. `never` lists `held` and `refuted`
//!   where those lists are empty. A sentence whose condition has no authored conjunct (only
//!   templates, inserted tests, or both) has no condition of the author's to report: `held_by`
//!   and `refuted_by` are `null` and `never` is empty, and whether a program reaches the sentence
//!   is its pattern's status.
//!
//! # A guard with no node
//!
//! Whether a sentence's condition has an authored conjunct is a fact of the definition, not of
//! the programs that reached it, so every guarded sentence is grouped, also one whose
//! `guard.operands` is empty: one no comparable program entered, or one whose compiled condition
//! kink-flow shows as no tree of the written `requires`. Its condition is read from the emission
//! alone, as the display tree is read where it has nodes: the leading conjuncts of the
//! condition's chain are its templates' tests, checked as above, and the nodes below the
//! conjunctions of the rest are its conjuncts, each authored or inserted by its map node. Its
//! `authored`, `generated` and the `templates`' `conjuncts` are empty, since no node carries their
//! outcomes, and:
//!
//! - with no authored conjunct, `held_by` and `refuted_by` are `null` and `never` is empty, as
//!   above;
//! - with one, where no program's condition was seen to hold or be refuted, or where every
//!   conjunct is the author's, the guard's own `held_by` and `refuted_by` are the author's
//!   condition's: for an unentered sentence both are empty and `never` lists `held` and
//!   `refuted`;
//! - with templates, where no program reached the condition, the `templates`' `matched_by` and
//!   `not_matched_by` are empty, and the row's `krs.status` is `unmatched`.
//!
//! Where a program reached the condition and the outcomes of the author's conjuncts cannot be
//! told from those of a template or an inserted test without nodes, the sentence is named by no
//! guess and listed under `krs.unmatched_guards`.
//!
//! A sentence with templates also gains, in its row's `krs`, `matched_by` (the templates'
//! `matched_by`) and `status`: `fired` where kink-flow's is, else `matched` where some program
//! matched its templates, else `unmatched`. The K left-hand side of such a sentence is a bare
//! variable, because the templates moved into the condition, so kink-flow's `matched_by` lists
//! every program that evaluated the function at all; the KRS pattern is matched only where the
//! templates are.
//!
//! kink-flow's requirements family reads this grouping (`kink_flow::coverage::derive`): a
//! requirement is an authored operand's truth, or the author's condition held or refuted, so the
//! inserted tests and the templates are never obligations.

use std::collections::BTreeMap;
use std::ops::Range;
use std::sync::Mutex;

use krs_compiler::{DEFINITION_ARTIFACT, SourceMap, SourceMapNodeKind};
use krs_ir::{InsertedNode, LineIndex, SourceFileId, SourceRange};
use krs_ir_levels::{DefinitionIr, DefinitionSentence};
use serde_json::{Map, Value, json};

/// Reads an authored file's text, `None` when it is not the revision the collector read.
type ReadSource = Box<dyn Fn(&SourceFileId) -> Option<String> + Send + Sync>;

/// The K syntax of each Boolean connective kink-flow names by its hook.
const CONNECTIVES: [&str; 7] = [
    "andBool",
    "andThenBool",
    "orBool",
    "orElseBool",
    "impliesBool",
    "xorBool",
    "notBool",
];

/// One node of the emission's source map in `definition.k`.
#[derive(Clone, Debug)]
struct MapNode {
    range: Range<usize>,
    depth: u32,
    kind: SourceMapNodeKind,
    authored: Option<SourceRange>,
    inserted: Option<(InsertedNode, Option<SourceRange>)>,
}

/// The guard names of one emission.
pub(crate) struct GuardNames {
    definition: String,
    /// Every node rendered in `definition.k`, by start, outer nodes first.
    nodes: Vec<MapNode>,
    /// Each rule sentence's range in `definition.k`, by its emitted label.
    sentences: BTreeMap<String, Range<usize>>,
    read: ReadSource,
    /// Each authored file's text and lines, read on first need; `None` where it is unavailable.
    texts: Mutex<BTreeMap<SourceFileId, Option<(String, LineIndex)>>>,
}

/// Why a guard is named by no guess.
type Unmatched = String;

impl GuardNames {
    /// The names of the guards of `definition` (the emitted `definition.k`) by `map` and `ir`, its
    /// source map and Definition IR, reading authored files with `read`.
    pub(crate) fn new(
        definition: &str,
        map: &SourceMap,
        ir: &DefinitionIr,
        read: impl Fn(&SourceFileId) -> Option<String> + Send + Sync + 'static,
    ) -> Self {
        let mut by_key = BTreeMap::new();
        let mut nodes = Vec::new();
        for entry in map.entries() {
            let Some(generated) = entry.generated() else {
                continue;
            };
            if generated.artifact() != DEFINITION_ARTIFACT {
                continue;
            }
            let (Ok(start), Ok(end)) = (
                usize::try_from(generated.start_byte()),
                usize::try_from(generated.end_byte()),
            ) else {
                continue;
            };
            if start > end || end > definition.len() {
                continue;
            }
            by_key.insert(entry.key().clone(), start..end);
            nodes.push(MapNode {
                range: start..end,
                depth: entry.depth(),
                kind: entry.node_kind(),
                authored: entry.origin().exact_authored_range(),
                inserted: entry
                    .inserted()
                    .map(|(kind, anchor)| (kind, anchor.cloned())),
            });
        }
        nodes.sort_by_key(|node| {
            (
                node.range.start,
                std::cmp::Reverse(node.range.end),
                node.depth,
            )
        });
        let mut sentences = BTreeMap::new();
        for module in ir.modules() {
            for sentence in module.sentences() {
                let DefinitionSentence::Rule(rule) = sentence else {
                    continue;
                };
                if let Some(range) = by_key.get(sentence.origin().key()) {
                    sentences.insert(rule.label().emitted_name().to_owned(), range.clone());
                }
            }
        }
        Self {
            definition: definition.to_owned(),
            nodes,
            sentences,
            read: Box::new(read),
            texts: Mutex::new(BTreeMap::new()),
        }
    }

    /// Name the guard of `row`, a `coverage` rule item of the sentence of K module `module` labelled
    /// `label` (bare or module-qualified), as the module documentation says; `programs` are the
    /// document's program ids in corpus order. `Err` says why the guard is named by no guess; its
    /// nodes and the guard then have `krs: null`.
    pub(crate) fn name(
        &self,
        row: &mut Map<String, Value>,
        module: &str,
        label: &str,
        programs: &[String],
    ) -> Result<(), Unmatched> {
        let named = self.try_name(row, module, label, programs);
        if named.is_err()
            && let Some(guard) = row.get_mut("guard").and_then(Value::as_object_mut)
        {
            for operand in guard
                .get_mut("operands")
                .and_then(Value::as_array_mut)
                .into_iter()
                .flatten()
            {
                if let Some(operand) = operand.as_object_mut() {
                    operand.insert("krs".into(), Value::Null);
                }
            }
            guard.insert("krs".into(), Value::Null);
        }
        named
    }

    fn try_name(
        &self,
        row: &mut Map<String, Value>,
        module: &str,
        label: &str,
        programs: &[String],
    ) -> Result<(), Unmatched> {
        let Some(guard) = row.get("guard") else {
            return Ok(());
        };
        let display = Display::of(guard);
        let range = self
            .sentences
            .get(label)
            .or_else(|| {
                label
                    .strip_prefix(&format!("{module}."))
                    .and_then(|bare| self.sentences.get(bare))
            })
            .ok_or_else(|| format!("the emission's source map has no sentence labelled {label}"))?;
        let sentence = Sentence::of(&self.nodes, range);
        let condition = sentence
            .condition_root()
            .ok_or("the emission's source map has no condition of the sentence")?;
        if display.nodes.is_empty() {
            return self.name_without_nodes(row, &sentence, condition, programs);
        }
        let roots = display.children("");
        let [root] = roots.as_slice() else {
            return Err(
                "its compiled condition has more than one conjunct of the written requires".into(),
            );
        };
        let mut paired = BTreeMap::new();
        self.pair(&display, *root, &sentence, condition, &mut paired)?;
        let templates = self.templates(&display, *root, &sentence, &paired)?;
        let item = row
            .get("krs")
            .and_then(|krs| krs.get("item"))
            .cloned()
            .unwrap_or(Value::Null);
        // Each display node's `krs`.
        let mut named = Vec::with_capacity(display.nodes.len());
        for (index, node) in display.nodes.iter().enumerate() {
            let Some(&map_index) = paired.get(&index) else {
                named.push(None);
                continue;
            };
            let in_template = templates
                .as_ref()
                .is_some_and(|found| found.covers(&node.path));
            named.push(Some(self.node_krs(
                &sentence,
                map_index,
                node,
                in_template,
                &item,
            )));
        }
        let guard = row
            .get_mut("guard")
            .and_then(Value::as_object_mut)
            .ok_or("the row's guard is no object")?;
        let operands = guard
            .get_mut("operands")
            .and_then(Value::as_array_mut)
            .ok_or("the row's guard has no operands")?;
        for (operand, krs) in operands.iter_mut().zip(&named) {
            if let (Some(operand), Some(krs)) = (operand.as_object_mut(), krs) {
                operand.insert("krs".into(), krs.clone());
            }
        }
        let grouped = group(guard, templates.as_ref(), programs);
        insert_grouping(row, grouped);
        Ok(())
    }

    /// Name the guard of `row` whose display tree has no node (no comparable program entered the
    /// condition, or kink-flow shows it as no tree of the written `requires`) by the sentence's
    /// condition, the map node `condition`, as the emission writes it (module documentation, "A
    /// guard with no node").
    fn name_without_nodes(
        &self,
        row: &mut Map<String, Value>,
        sentence: &Sentence,
        condition: usize,
        programs: &[String],
    ) -> Result<(), Unmatched> {
        let reading = self.read_condition(sentence, condition)?;
        let guard = row
            .get_mut("guard")
            .and_then(Value::as_object_mut)
            .ok_or("the row's guard is no object")?;
        let seen = ["held_by", "refuted_by"].into_iter().any(|key| {
            guard
                .get(key)
                .and_then(Value::as_array)
                .is_some_and(|programs| !programs.is_empty())
        });
        if seen && !reading.binders.is_empty() {
            return Err("its templates' outcomes have no node in the coverage document".into());
        }
        if seen && reading.authored && reading.inserted {
            return Err(
                "its condition has tests KRS inserted, and the coverage document shows no node to tell their outcomes from the author's"
                    .into(),
            );
        }
        let templates = if reading.binders.is_empty() {
            Value::Null
        } else {
            json!({
                "conjuncts": [],
                "binders": reading
                    .binders
                    .iter()
                    .map(|binder| self.position(&binder.range).value())
                    .collect::<Vec<_>>(),
                "matched_by": [],
                "not_matched_by": [],
            })
        };
        // With an authored conjunct, either no program reached the condition or every conjunct
        // is the author's: the guard's own outcomes are the author's condition's.
        let (held, refuted) = if reading.authored {
            (
                union(programs, &[&guard["held_by"]]),
                union(programs, &[&guard["refuted_by"]]),
            )
        } else {
            (Value::Null, Value::Null)
        };
        let mut grouped = Map::new();
        grouped.insert("templates".into(), templates);
        grouped.insert("authored".into(), json!([]));
        grouped.insert("generated".into(), json!([]));
        let never = never(&held, &refuted);
        grouped.insert("held_by".into(), held);
        grouped.insert("refuted_by".into(), refuted);
        grouped.insert("never".into(), never);
        insert_grouping(row, grouped);
        Ok(())
    }

    /// The sentence's condition, whose `requires` is the map node `condition`, as the emission
    /// writes it: its templates, whose tests are the leading conjuncts of its chain, and whether
    /// a later conjunct is the author's or a test KRS inserted (module documentation, "A guard
    /// with no node").
    fn read_condition(
        &self,
        sentence: &Sentence,
        condition: usize,
    ) -> Result<Condition, Unmatched> {
        let root = self.through_casts(sentence, condition);
        let own = self.own_text(sentence, root);
        let chain = if matches!(own.as_str(), "andBool" | "andThenBool")
            && sentence.children(root).len() == 2
        {
            self.chain(sentence, root, &own)
        } else {
            vec![condition]
        };
        let binders = sentence.template_binders(self);
        let mut span = None;
        let mut at = 0;
        for binder in &binders {
            for _ in 0..binder.conjuncts {
                let Some(&conjunct) = chain.get(at) else {
                    return Err(
                        "its condition has fewer conjuncts than its templates' tests".into(),
                    );
                };
                if !self.tests_template(sentence, conjunct, binder, &mut span) {
                    return Err(format!(
                        "its condition's conjunct {at} is not the test of the template {}",
                        binder.variable
                    ));
                }
                at += 1;
            }
        }
        let mut conjuncts = Vec::new();
        for &operand in &chain[at..] {
            self.map_conjuncts(sentence, operand, &mut conjuncts);
        }
        let inserted = |conjunct: &usize| sentence.nodes[*conjunct].inserted.is_some();
        Ok(Condition {
            authored: conjuncts.iter().any(|conjunct| !inserted(conjunct)),
            inserted: conjuncts.iter().any(inserted),
            binders,
        })
    }

    /// The conjuncts at the map node `map_index`: the nodes below its conjunctions (the written
    /// ones and the joins of the inserted tests alike), in written order, as [`conjuncts`] reads
    /// a display tree.
    fn map_conjuncts(&self, sentence: &Sentence, map_index: usize, conjuncts: &mut Vec<usize>) {
        let at = self.through_casts(sentence, map_index);
        let children = sentence.children(at);
        if children.len() == 2
            && matches!(
                self.own_text(sentence, at).as_str(),
                "andBool" | "andThenBool"
            )
        {
            for child in children {
                self.map_conjuncts(sentence, child, conjuncts);
            }
        } else {
            conjuncts.push(map_index);
        }
    }

    /// Whether the map node `map_index` is a conjunct of the test of the template `binder`: it
    /// reads the binder, and its nodes all take one span, the span of the template's conjuncts
    /// before it (`span`, which it sets) (module documentation, "Templates").
    fn tests_template(
        &self,
        sentence: &Sentence,
        map_index: usize,
        binder: &Binder,
        span: &mut Option<SourceRange>,
    ) -> bool {
        let subtree = sentence.subtree(map_index);
        let reads = subtree
            .iter()
            .any(|&node| self.definition[sentence.nodes[node].range.clone()] == binder.variable);
        let spans = subtree
            .iter()
            .map(|&node| sentence.nodes[node].authored.clone())
            .collect::<Vec<_>>();
        let one = spans.first().cloned().flatten();
        let same = one.is_some() && spans.iter().all(|range| *range == one);
        if subtree.len() < 2 || !reads || !same || (span.is_some() && *span != one) {
            return false;
        }
        *span = one;
        true
    }

    /// Pair the display node `index` with the map node `map_index` and their operands (module
    /// documentation, "Correspondence").
    fn pair(
        &self,
        display: &Display<'_>,
        index: usize,
        sentence: &Sentence,
        map_index: usize,
        paired: &mut BTreeMap<usize, usize>,
    ) -> Result<(), Unmatched> {
        let node = &display.nodes[index];
        let mismatch = |what: &str| {
            format!(
                "its compiled condition's node {} ({}) is {what} in the emitted K",
                node.path, node.text
            )
        };
        match node.kind {
            "conjunction" | "disjunction" | "implication" | "exclusive" | "negation" => {
                let connective = node.connective;
                if !CONNECTIVES.contains(&connective) {
                    return Err(mismatch("a connective KRS does not write"));
                }
                let map_index = self.through_casts(sentence, map_index);
                if self.own_text(sentence, map_index) != connective {
                    return Err(mismatch("another construct"));
                }
                let operands = if matches!(node.kind, "conjunction" | "disjunction") {
                    self.chain(sentence, map_index, connective)
                } else {
                    sentence.children(map_index)
                };
                let shown = display.children(&node.path);
                let arity = if connective == "notBool" { 1 } else { 2 };
                if sentence.children(map_index).len() != arity || operands.len() != shown.len() {
                    return Err(mismatch("a node of other operands"));
                }
                paired.insert(index, map_index);
                for (child, map_child) in shown.into_iter().zip(operands) {
                    self.pair(display, child, sentence, map_child, paired)?;
                }
                Ok(())
            }
            "atom" => {
                let own = self.own_text(sentence, map_index);
                if CONNECTIVES.contains(&own.as_str()) {
                    return Err(mismatch("a connective"));
                }
                paired.insert(index, map_index);
                Ok(())
            }
            _ => Err(mismatch("no Boolean term")),
        }
    }

    /// `map_index`, or the node a cast or a sort projection of it holds: brackets and casts are no
    /// nodes of a compiled condition.
    fn through_casts(&self, sentence: &Sentence, map_index: usize) -> usize {
        let mut at = map_index;
        loop {
            let children = sentence.children(at);
            let own = self.own_text(sentence, at);
            let cast = own.starts_with(":>") || own.starts_with("{}:>") || own.starts_with(':');
            match children.as_slice() {
                [child] if cast => at = *child,
                _ => return at,
            }
        }
    }

    /// The operands of the chain of `connective` at `map_index`, its left-nested applications read
    /// as one node.
    fn chain(&self, sentence: &Sentence, map_index: usize, connective: &str) -> Vec<usize> {
        let children = sentence.children(map_index);
        let [first, second] = children.as_slice() else {
            return children;
        };
        let mut operands = if self.own_text(sentence, *first) == connective {
            self.chain(sentence, *first, connective)
        } else {
            vec![*first]
        };
        operands.push(*second);
        operands
    }

    /// The text a map node renders outside its operands, without layout and brackets.
    fn own_text(&self, sentence: &Sentence, map_index: usize) -> String {
        let range = &sentence.nodes[map_index].range;
        let mut text = String::new();
        let mut at = range.start;
        for child in sentence.children(map_index) {
            let child = &sentence.nodes[child].range;
            text.push_str(&self.definition[at..child.start]);
            at = child.end;
        }
        text.push_str(&self.definition[at..range.end]);
        text.chars()
            .filter(|character| !character.is_whitespace() && !matches!(character, '(' | ')' | ','))
            .collect()
    }

    /// The templates of the sentence whose display tree's root is `root`, by the leading
    /// conjuncts of its chain (module documentation, "Templates").
    fn templates(
        &self,
        display: &Display<'_>,
        root: usize,
        sentence: &Sentence,
        paired: &BTreeMap<usize, usize>,
    ) -> Result<Option<Templates>, Unmatched> {
        let binders = sentence.template_binders(self);
        if binders.is_empty() {
            return Ok(None);
        }
        let root_node = &display.nodes[root];
        let conjuncts = if root_node.kind == "conjunction" {
            display.children(&root_node.path)
        } else {
            vec![root]
        };
        let mut paths = Vec::new();
        let mut span: Option<SourceRange> = None;
        let mut at = 0;
        for binder in &binders {
            for _ in 0..binder.conjuncts {
                let Some(&conjunct) = conjuncts.get(at) else {
                    return Err(
                        "its condition has fewer conjuncts than its templates' tests".into(),
                    );
                };
                at += 1;
                let map_index = paired
                    .get(&conjunct)
                    .copied()
                    .ok_or("a template conjunct has no node in the emitted K")?;
                if !self.tests_template(sentence, map_index, binder, &mut span) {
                    return Err(format!(
                        "its condition's conjunct {} is not the test of the template {}",
                        display.nodes[conjunct].path, binder.variable
                    ));
                }
                paths.push(display.nodes[conjunct].path.clone());
            }
        }
        let binders = binders
            .iter()
            .map(|binder| self.position(&binder.range))
            .collect();
        Ok(Some(Templates { paths, binders }))
    }

    /// The `krs` object of the display node `node`, paired with the map node `map_index`.
    fn node_krs(
        &self,
        sentence: &Sentence,
        map_index: usize,
        node: &DisplayNode<'_>,
        in_template: bool,
        item: &Value,
    ) -> Value {
        let map_node = &sentence.nodes[map_index];
        let origin = match (&map_node.inserted, in_template) {
            (Some((kind, _)), _) => kind.as_str(),
            (None, true) => "template",
            (None, false) => "authored",
        };
        let position = if node.kind == "atom" || node.kind == "exclusive" {
            sentence.covering(map_index)
        } else {
            map_node.authored.clone()
        }
        .map_or_else(Position::unknown, |range| self.position(&range));
        let mut krs = json!({
            "origin": origin,
            "item": item,
            "text": position.text,
            "file": position.file,
            "line": position.line,
            "column": position.column,
        });
        if let Some((_, anchor)) = &map_node.inserted {
            let anchor = anchor
                .clone()
                .or_else(|| map_node.authored.clone())
                .map_or_else(Position::unknown, |range| self.position(&range));
            krs["anchor"] = anchor.value();
        }
        krs
    }

    /// `range` read in its file, with the brackets its text opens or closes, and positioned.
    fn position(&self, range: &SourceRange) -> Position {
        let file = range.file.package_relative_path().to_owned();
        let mut texts = self
            .texts
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let entry = texts.entry(range.file.clone()).or_insert_with(|| {
            (self.read)(&range.file).map(|text| {
                let lines = LineIndex::new(&text);
                (text, lines)
            })
        });
        let Some((text, lines)) = entry.as_ref() else {
            return Position {
                file: Some(file),
                ..Position::unknown()
            };
        };
        let (Ok(start), Ok(end)) = (
            usize::try_from(range.start_byte),
            usize::try_from(range.end_byte),
        ) else {
            return Position::unknown();
        };
        let Some((start, end)) = balanced(text, start, end) else {
            return Position {
                file: Some(file),
                ..Position::unknown()
            };
        };
        let position = lines.byte_to_position(start).ok();
        Position {
            text: Some(text[start..end].to_owned()),
            file: Some(file),
            line: position.map(krs_ir::Position::line),
            column: position.map(krs_ir::Position::scalar_column),
        }
    }
}

/// `start..end` in `text`, widened over the brackets its text leaves open or closes, where they
/// follow or precede it across layout; `None` for a range outside the text.
fn balanced(text: &str, mut start: usize, mut end: usize) -> Option<(usize, usize)> {
    if start > end
        || end > text.len()
        || !text.is_char_boundary(start)
        || !text.is_char_boundary(end)
    {
        return None;
    }
    let depth = |slice: &str| {
        slice
            .chars()
            .fold(0i64, |depth, character| match character {
                '(' => depth + 1,
                ')' => depth - 1,
                _ => depth,
            })
    };
    let mut open = depth(&text[start..end]);
    while open > 0 {
        let rest = &text[end..];
        let skipped = rest.len() - rest.trim_start().len();
        if rest.trim_start().starts_with(')') {
            end += skipped + 1;
            open -= 1;
        } else {
            break;
        }
    }
    while open < 0 {
        let before = &text[..start];
        let trimmed = before.trim_end();
        if trimmed.ends_with('(') {
            start = trimmed.len() - 1;
            open += 1;
        } else {
            break;
        }
    }
    Some((start, end))
}

/// A position a `krs` object gives.
struct Position {
    text: Option<String>,
    file: Option<String>,
    line: Option<u32>,
    column: Option<u32>,
}

impl Position {
    const fn unknown() -> Self {
        Self {
            text: None,
            file: None,
            line: None,
            column: None,
        }
    }

    fn value(&self) -> Value {
        json!({"text": self.text, "file": self.file, "line": self.line, "column": self.column})
    }
}

/// A sentence's map nodes.
struct Sentence {
    nodes: Vec<MapNode>,
}

/// A template of a sentence, from its binder's occurrence in the left-hand side.
struct Binder {
    /// The binder's K text (`Bits:Int`).
    variable: String,
    /// The template's string literal.
    range: SourceRange,
    /// The conjuncts of the template's test.
    conjuncts: usize,
}

impl Sentence {
    /// The map nodes inside `range`, a sentence's, outer first.
    fn of(nodes: &[MapNode], range: &Range<usize>) -> Self {
        Self {
            nodes: nodes
                .iter()
                .filter(|node| range.start <= node.range.start && node.range.end <= range.end)
                .cloned()
                .collect(),
        }
    }

    /// The nodes one level below `index` in its range, by start.
    fn children(&self, index: usize) -> Vec<usize> {
        let parent = &self.nodes[index];
        let mut children = self
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| {
                node.depth == parent.depth + 1
                    && parent.range.start <= node.range.start
                    && node.range.end <= parent.range.end
            })
            .map(|(child, _)| child)
            .collect::<Vec<_>>();
        children.sort_by_key(|&child| self.nodes[child].range.start);
        children
    }

    /// `index` and every node below it.
    fn subtree(&self, index: usize) -> Vec<usize> {
        let mut nodes = vec![index];
        let mut at = 0;
        while at < nodes.len() {
            let children = self.children(nodes[at]);
            nodes.extend(children);
            at += 1;
        }
        nodes
    }

    /// The source an atom renders: the span from the first to the last authored token of its
    /// nodes in its own file (module documentation, "Origins and text").
    fn covering(&self, map_index: usize) -> Option<SourceRange> {
        let own = self.nodes[map_index].authored.clone()?;
        let mut range = own.clone();
        for node in self.subtree(map_index) {
            if let Some(authored) = &self.nodes[node].authored
                && authored.file == own.file
            {
                range.start_byte = range.start_byte.min(authored.start_byte);
                range.end_byte = range.end_byte.max(authored.end_byte);
            }
        }
        Some(range)
    }

    /// The `requires`'s root: the node one level below the sentence's condition node.
    fn condition_root(&self) -> Option<usize> {
        let condition = self
            .nodes
            .iter()
            .position(|node| node.kind == SourceMapNodeKind::RuleCondition)?;
        self.children(condition)
            .into_iter()
            .max_by_key(|&child| self.nodes[child].range.len())
    }

    /// The templates of the sentence's left-hand side, in written order: each variable node
    /// outside the condition whose authored range is a string literal, which only a template's
    /// binder takes.
    fn template_binders(&self, names: &GuardNames) -> Vec<Binder> {
        let condition = self
            .nodes
            .iter()
            .find(|node| node.kind == SourceMapNodeKind::RuleCondition)
            .map(|node| node.range.clone());
        let mut binders = Vec::<Binder>::new();
        for (index, node) in self.nodes.iter().enumerate() {
            if condition.as_ref().is_some_and(|condition| {
                condition.start <= node.range.start && node.range.end <= condition.end
            }) || !self.children(index).is_empty()
            {
                continue;
            }
            let Some(range) = &node.authored else {
                continue;
            };
            let Some(literal) = names.source_slice(range) else {
                continue;
            };
            let Some(template) = literal
                .strip_prefix('"')
                .and_then(|rest| rest.strip_suffix('"'))
            else {
                continue;
            };
            let variable = names.definition[node.range.clone()].to_owned();
            if !is_variable(&variable) {
                continue;
            }
            if binders
                .iter()
                .any(|binder| binder.variable == variable && binder.range == *range)
            {
                continue;
            }
            let Some(conjuncts) = test_conjuncts(template) else {
                continue;
            };
            binders.push(Binder {
                variable,
                range: range.clone(),
                conjuncts,
            });
        }
        binders.sort_by_key(|binder| binder.range.start_byte);
        binders
    }
}

/// A node of a sentence's condition as a flip's occurrence reads it: kink-flow's display path of
/// the node, and the Rust source the node renders, where it is readable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ConditionNode {
    /// The display path (`0.1`), in the space of `guard.operands[].path`.
    pub(crate) path: String,
    /// The authored text the node renders, as an operand's `krs.text` gives it.
    pub(crate) text: Option<String>,
}

impl GuardNames {
    /// Every node of the condition of the sentence labelled `label` that kink-flow's display tree
    /// shows, by its range in `definition.k` (start and end), with its display path: what a condition flip's
    /// occurrence, a range of `definition.k`, reaches in a `coverage` rule item's guard.
    ///
    /// The walk is the correspondence the naming checks (module documentation,
    /// "Correspondence"), read from the emission alone: the condition's root is the display
    /// root, a Boolean connective's operands are its children (a left-nested chain of one
    /// conjunction or disjunction read as one node), each at `<path>.<k>`, and casts are no nodes.
    /// The root's path is `0`: KRS writes a sentence's condition as its one `requires`, which is
    /// the compiled axiom's first conjunct `\equals(C, true)`, and kink-flow names a display root
    /// by its conjunct's index. A node of a shape the walk does not read (a connective of another
    /// arity) has no entry, and neither has anything below it, so an occurrence there is placed
    /// by no guess.
    pub(crate) fn condition_nodes(&self, label: &str) -> BTreeMap<(usize, usize), ConditionNode> {
        let mut nodes = BTreeMap::new();
        let Some(range) = self.sentences.get(label) else {
            return nodes;
        };
        let sentence = Sentence::of(&self.nodes, range);
        if let Some(root) = sentence.condition_root() {
            self.walk(&sentence, root, "0", &mut nodes);
        }
        nodes
    }

    fn walk(
        &self,
        sentence: &Sentence,
        map_index: usize,
        path: &str,
        nodes: &mut BTreeMap<(usize, usize), ConditionNode>,
    ) {
        let text = sentence
            .covering(map_index)
            .and_then(|range| self.position(&range).text);
        // The node and every cast around the node it holds render the one display node.
        let mut at = map_index;
        loop {
            nodes
                .entry((sentence.nodes[at].range.start, sentence.nodes[at].range.end))
                .or_insert_with(|| ConditionNode {
                    path: path.to_owned(),
                    text: text.clone(),
                });
            let next = self.through_casts(sentence, at);
            if next == at {
                let children = sentence.children(at);
                let own = self.own_text(sentence, at);
                if !CONNECTIVES.contains(&own.as_str()) {
                    return;
                }
                let arity = if own == "notBool" { 1 } else { 2 };
                if children.len() != arity {
                    return;
                }
                let operands = if matches!(
                    own.as_str(),
                    "andBool" | "andThenBool" | "orBool" | "orElseBool"
                ) {
                    self.chain(sentence, at, &own)
                } else {
                    children
                };
                for (k, operand) in operands.into_iter().enumerate() {
                    self.walk(sentence, operand, &format!("{path}.{k}"), nodes);
                }
                return;
            }
            // One cast step at a time, so that each cast's range is recorded.
            at = sentence.children(at)[0];
        }
    }

    /// The text of `range` in its file, where the file is available.
    fn source_slice(&self, range: &SourceRange) -> Option<String> {
        let mut texts = self
            .texts
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let entry = texts.entry(range.file.clone()).or_insert_with(|| {
            (self.read)(&range.file).map(|text| {
                let lines = LineIndex::new(&text);
                (text, lines)
            })
        });
        let (text, _) = entry.as_ref()?;
        text.get(usize::try_from(range.start_byte).ok()?..usize::try_from(range.end_byte).ok()?)
            .map(str::to_owned)
    }
}

/// Whether `text`, a node's K text, is a variable of a sort (`Bits:Int`).
fn is_variable(text: &str) -> bool {
    let Some((name, sort)) = text.split_once(':') else {
        return false;
    };
    let word = |part: &str| {
        !part.is_empty()
            && part.chars().all(|character| {
                character.is_ascii_alphanumeric() || matches!(character, '_' | '\'')
            })
    };
    name.starts_with(|first: char| first.is_ascii_uppercase() || first == '_')
        && word(name)
        && word(sort)
}

/// The conjuncts of the match test of the template `template` (its string's contents): the range
/// test's two, and one per maximal run of fixed bits; `None` for a template every bit of which is
/// fixed, which is its literal and has no test, or a string that is no template.
fn test_conjuncts(template: &str) -> Option<usize> {
    let mut runs = 0;
    let mut in_run = false;
    let mut variable = false;
    for character in template.chars() {
        match character {
            '0' | '1' => {
                if !in_run {
                    runs += 1;
                }
                in_run = true;
            }
            ' ' => in_run = false,
            '_' => {
                in_run = false;
                variable = true;
            }
            letter if letter.is_ascii_alphabetic() => {
                in_run = false;
                variable = true;
            }
            _ => return None,
        }
    }
    variable.then_some(2 + runs)
}

/// A sentence's condition as the emission writes it ([`GuardNames::read_condition`]).
struct Condition {
    /// The templates of its left-hand side, whose tests lead the condition.
    binders: Vec<Binder>,
    /// Whether a conjunct after the templates' tests is the author's.
    authored: bool,
    /// Whether a conjunct after the templates' tests is a test KRS inserted.
    inserted: bool,
}

/// Put `grouped`, a guard's `krs`, in `row`, and, where the sentence has templates, its row's
/// `krs.matched_by` and `krs.status` (module documentation, "The grouping").
fn insert_grouping(row: &mut Map<String, Value>, grouped: Map<String, Value>) {
    let matched = grouped
        .get("templates")
        .and_then(|templates| templates.get("matched_by"))
        .cloned();
    if let Some(guard) = row.get_mut("guard").and_then(Value::as_object_mut) {
        guard.insert("krs".into(), Value::Object(grouped));
    }
    if let Some(matched_by) = matched {
        let fired = row.get("status").and_then(Value::as_str) == Some(kink_flow::coverage::FIRED);
        let status = if fired {
            kink_flow::coverage::FIRED
        } else if matched_by
            .as_array()
            .is_some_and(|programs| !programs.is_empty())
        {
            kink_flow::coverage::MATCHED
        } else {
            kink_flow::coverage::UNMATCHED
        };
        if let Some(krs) = row.get_mut("krs").and_then(Value::as_object_mut) {
            krs.insert("matched_by".into(), matched_by);
            krs.insert("status".into(), json!(status));
        }
    }
}

/// A grouped guard's `never`: `held` and `refuted` where `held` and `refuted`, its program lists,
/// are empty; nothing where they are `null` (no condition of the author's).
fn never(held: &Value, refuted: &Value) -> Value {
    Value::Array(
        [("held", held), ("refuted", refuted)]
            .into_iter()
            .filter(|(_, programs)| programs.as_array().is_some_and(Vec::is_empty))
            .map(|(name, _)| json!(name))
            .collect(),
    )
}

/// The templates of a guard: their conjuncts' display paths and their binders' positions.
struct Templates {
    paths: Vec<String>,
    binders: Vec<Position>,
}

impl Templates {
    /// Whether the display node at `path` lies in a template's conjunct.
    fn covers(&self, path: &str) -> bool {
        self.paths
            .iter()
            .any(|conjunct| path == conjunct || path.starts_with(&format!("{conjunct}.")))
    }
}

/// One node of a row's `guard.operands`.
struct DisplayNode<'g> {
    path: String,
    kind: &'g str,
    connective: &'g str,
    text: &'g str,
}

/// A row's display tree.
struct Display<'g> {
    nodes: Vec<DisplayNode<'g>>,
}

impl<'g> Display<'g> {
    fn of(guard: &'g Value) -> Self {
        let nodes = guard["operands"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|operand| DisplayNode {
                path: operand["path"].as_str().unwrap_or_default().to_owned(),
                kind: operand["kind"].as_str().unwrap_or_default(),
                connective: operand["connective"].as_str().unwrap_or_default(),
                text: operand["text"].as_str().unwrap_or_default(),
            })
            .collect();
        Self { nodes }
    }

    /// The display nodes directly below `path` (`""`: the roots), in written order.
    fn children(&self, path: &str) -> Vec<usize> {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| match node.path.rsplit_once('.') {
                Some((parent, _)) => parent == path,
                None => path.is_empty(),
            })
            .map(|(index, _)| index)
            .collect()
    }
}

/// The program lists of `values`, merged in the order of `programs`.
fn union(programs: &[String], values: &[&Value]) -> Value {
    Value::Array(
        programs
            .iter()
            .filter(|program| {
                values.iter().any(|value| {
                    value
                        .as_array()
                        .is_some_and(|listed| listed.iter().any(|item| item == program.as_str()))
                })
            })
            .map(|program| json!(program))
            .collect(),
    )
}

/// The outcome fields a grouped operand copies from its K node.
const OUTCOMES: [&str; 4] = ["true_by", "false_by", "undefined_by", "undecided_by"];

/// The guard's `krs` (module documentation, "The grouping").
fn group(
    guard: &Map<String, Value>,
    templates: Option<&Templates>,
    programs: &[String],
) -> Map<String, Value> {
    let operands = guard
        .get("operands")
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .unwrap_or_default();
    let mut authored = Vec::new();
    let mut generated = Vec::new();
    for operand in operands {
        let krs = &operand["krs"];
        let kind = operand["kind"].as_str().unwrap_or_default();
        if !kink_flow::guards::own_outcomes(kind) {
            continue;
        }
        let mut grouped = Map::new();
        grouped.insert("path".into(), operand["path"].clone());
        match krs["origin"].as_str() {
            Some("authored") => {
                for key in ["text", "file", "line", "column"] {
                    grouped.insert(key.into(), krs[key].clone());
                }
                for key in OUTCOMES.into_iter().chain(["never"]) {
                    grouped.insert(key.into(), operand[key].clone());
                }
                authored.push(Value::Object(grouped));
            }
            Some("template") | None => {}
            Some(origin) => {
                grouped.insert("origin".into(), json!(origin));
                grouped.insert("text".into(), operand["text"].clone());
                grouped.insert("anchor".into(), krs["anchor"].clone());
                for key in OUTCOMES {
                    grouped.insert(key.into(), operand[key].clone());
                }
                generated.push(Value::Object(grouped));
            }
        }
    }
    let mut group = Map::new();
    group.insert(
        "templates".into(),
        templates.map_or(Value::Null, |templates| {
            templated(operands, templates, programs)
        }),
    );
    let condition = conjuncts(operands)
        .into_iter()
        .filter(|conjunct| conjunct["krs"]["origin"] == "authored")
        .collect::<Vec<_>>();
    let (held, refuted) = match condition.last() {
        None => (Value::Null, Value::Null),
        Some(last) => (
            union(programs, &[&last["true_by"]]),
            union(
                programs,
                &condition
                    .iter()
                    .map(|conjunct| &conjunct["false_by"])
                    .collect::<Vec<_>>(),
            ),
        ),
    };
    group.insert("authored".into(), Value::Array(authored));
    group.insert("generated".into(), Value::Array(generated));
    let never = never(&held, &refuted);
    group.insert("held_by".into(), held);
    group.insert("refuted_by".into(), refuted);
    group.insert("never".into(), never);
    group
}

/// The conjuncts of a guard's condition: the nodes below its conjunctions (the written ones and
/// the joins of the inserted tests alike), in written order.
fn conjuncts(operands: &[Value]) -> Vec<&Value> {
    fn below<'o>(operands: &'o [Value], parent: &str, conjuncts: &mut Vec<&'o Value>) {
        for operand in operands {
            let path = operand["path"].as_str().unwrap_or_default();
            let child = match path.rsplit_once('.') {
                Some((above, _)) => above == parent,
                None => parent.is_empty(),
            };
            if !child {
                continue;
            }
            if operand["kind"] == "conjunction" {
                below(operands, path, conjuncts);
            } else {
                conjuncts.push(operand);
            }
        }
    }
    let mut conjuncts = Vec::new();
    below(operands, "", &mut conjuncts);
    conjuncts
}

/// The guard's `templates` (module documentation, "The grouping").
fn templated(operands: &[Value], templates: &Templates, programs: &[String]) -> Value {
    let by_path = |path: &str| operands.iter().find(|operand| operand["path"] == path);
    let last = templates.paths.last().and_then(|path| by_path(path));
    let matched = last.map_or(Value::Array(Vec::new()), |last| last["true_by"].clone());
    let missed = templates
        .paths
        .iter()
        .filter_map(|path| by_path(path))
        .flat_map(|conjunct| [&conjunct["false_by"], &conjunct["undefined_by"]])
        .collect::<Vec<_>>();
    json!({
        "conjuncts": templates.paths,
        "binders": templates.binders.iter().map(Position::value).collect::<Vec<_>>(),
        "matched_by": matched,
        "not_matched_by": union(programs, &missed),
    })
}

#[cfg(test)]
mod tests {
    use serde_json::{Value, json};

    use super::{balanced, group, test_conjuncts};

    /// A node of a row's `guard.operands`, named by `origin`.
    fn node(path: &str, kind: &str, origin: &str, true_by: &[&str], false_by: &[&str]) -> Value {
        json!({
            "path": path, "kind": kind, "text": path,
            "true_by": true_by, "false_by": false_by, "undefined_by": [], "undecided_by": [],
            "krs": {"origin": origin, "text": path, "anchor": null},
        })
    }

    /// The guard's `krs` of a guard of `operands`, over the programs `a`, `b` and `c`.
    fn grouped(operands: &[Value]) -> Value {
        let guard = json!({
            "operands": operands,
            "held_by": ["a"], "refuted_by": ["a", "b", "c"], "never": [],
        });
        let programs = ["a", "b", "c"].map(str::to_owned);
        Value::Object(group(guard.as_object().unwrap(), None, &programs))
    }

    /// The author's condition is its authored conjuncts alone: an inserted test or a template
    /// that was `false` refutes nothing, and a condition with no authored conjunct has no gap.
    #[test]
    fn held_and_refuted_read_the_authored_conjuncts() {
        // A looked-up key's guard, then `v > 3`: `c` misses the key, `b` refutes `v > 3`.
        let looked_up = grouped(&[
            node("0", "conjunction", "authored", &["a"], &["b", "c"]),
            node("0.0", "atom", "lookup_guard", &["a", "b"], &["c"]),
            node("0.1", "atom", "authored", &["a"], &["b"]),
        ]);
        assert_eq!(looked_up["held_by"], json!(["a"]));
        assert_eq!(looked_up["refuted_by"], json!(["b"]));
        assert_eq!(looked_up["never"], json!([]));
        // `x > 0 && m[k] > 0`, the read's test joined to the conjunct it guards: `b` has no
        // `m[k]`, so the author's condition never was `false`.
        let tested = grouped(&[
            node("0", "conjunction", "authored", &["a"], &["b"]),
            node("0.0", "atom", "authored", &["a", "b"], &[]),
            node("0.1", "conjunction", "definedness_test", &["a"], &["b"]),
            node("0.1.0", "atom", "definedness_test", &["a"], &["b"]),
            node("0.1.1", "atom", "authored", &["a"], &[]),
        ]);
        assert_eq!(tested["held_by"], json!(["a"]));
        assert_eq!(tested["refuted_by"], json!([]));
        assert_eq!(tested["never"], json!(["refuted"]));
        // A template's test and a looked-up key's guard alone.
        for operands in [
            vec![
                node("0", "conjunction", "authored", &["a"], &["b", "c"]),
                node("0.0", "atom", "template", &["a", "b", "c"], &[]),
                node("0.1", "atom", "template", &["a"], &["b", "c"]),
            ],
            vec![node("0", "atom", "lookup_guard", &["a"], &["b", "c"])],
        ] {
            let none = grouped(&operands);
            assert_eq!(none["held_by"], Value::Null, "{none:#}");
            assert_eq!(none["refuted_by"], Value::Null, "{none:#}");
            assert_eq!(none["never"], json!([]), "{none:#}");
            assert_eq!(none["authored"], json!([]), "{none:#}");
        }
    }

    /// A template's test is its range and one equality per run of fixed bits; a fully fixed
    /// template is its literal and has none.
    #[test]
    fn a_templates_test_has_its_range_and_one_conjunct_per_fixed_run() {
        assert_eq!(test_conjuncts("01 rrr sss"), Some(3));
        assert_eq!(test_conjuncts("0aaa"), Some(3));
        assert_eq!(test_conjuncts("iiii 0011"), Some(3));
        assert_eq!(test_conjuncts("bbb 0 b_"), Some(3));
        assert_eq!(test_conjuncts("10 01 aa"), Some(4));
        assert_eq!(test_conjuncts("1_ __"), Some(3));
        assert_eq!(test_conjuncts("aaaa"), Some(2));
        assert_eq!(test_conjuncts("0110"), None);
        assert_eq!(test_conjuncts("not a template!"), None);
    }

    /// A span's text takes the brackets it opens or closes.
    #[test]
    fn a_span_takes_the_brackets_it_leaves_open() {
        let text = "x && !(irq && ime) || y";
        let start = text.find('!').unwrap();
        let end = text.find("ime").unwrap() + 3;
        let (start, end) = balanced(text, start, end).unwrap();
        assert_eq!(&text[start..end], "!(irq && ime)");
        let start = text.find("irq").unwrap();
        let end = text.find(')').unwrap() + 1;
        let (start, end) = balanced(text, start, end).unwrap();
        assert_eq!(&text[start..end], "(irq && ime)");
    }
}
