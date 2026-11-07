//! The re-derivation check of a K mutation of a definition KRS emitted: whether each sentence the
//! mutation edits is what KRS derives from the edited authored content.
//!
//! The judge ([`krs_compiler::judge_edits`]) refuses edits of what KRS inserted and hands on every
//! sentence whose authored content an edit changes ([`SentenceVerdict::NeedsRederivation`]).
//! For such a sentence `S` this check:
//!
//! 1. reads the mutant's sentence with the rule grammar of its module in the baseline definition,
//!    after removing each definedness test KRS states in it and the `andThenBool` that joins the
//!    test, keeping the conjunct it guards: what remains is authored content;
//! 2. lifts the content of each part of `S` an edit changes (the rewrite, a cell clause, the
//!    `requires`, the `ensures`) into the semantic IR, by the baseline's own names: variables by
//!    the sentence's naming in reverse, productions, sorts and cells by the names the baseline's
//!    K gives them ([`KLabelIndex`]), builtin and collection operations by the catalog's K labels;
//!    the lift admits only what authored syntax produces at a position, and every name a
//!    condition or a result reads must be bound by the sentence, as in Rust;
//! 3. puts the lifted parts in place of the baseline's in `S`'s pre-derivation sentence, the
//!    parts no edit changes, the sentence's identity, label, nondet group and attributes kept;
//! 4. derives and renders that sentence with KRS's own passes ([`Rederivation::rederive`]);
//! 5. compares the rendering with the mutant's sentence, both parsed, up to a bijective renaming
//!    of variables, with attributes other than the label compared as text.
//!
//! Equal: the mutant's sentence is what KRS emits for the lifted sentence, which a source that
//! spells each lifted part in Rust lowers to, so the sentence is accepted. Different: the mutant
//! keeps a derived node that does not follow the edit, or misses one, and the check refuses it,
//! showing the text KRS derives. A mutation whose every changed sentence is the baseline's up to
//! renaming changes nothing and is refused.
//!
//! Refusals are sound by construction (a refused mutant is never run); every place where the
//! lift reads less than KRS writes is a refusal, never an acceptance. One is coarser than the
//! judge: a part of the sentence that holds a lookup guard or a local function is not lifted, so
//! an edit anywhere in that part is not judged, even where its container lies outside the
//! family. An edit of another part is judged, and the derivation lifts the sentence's local
//! functions again; it is accepted only when their declarations and equations are the
//! baseline's.
//!
//! The derivation passes re-run KRS's semantic checks, and the theory's validation checks the
//! sentence's terms; the checks KRS makes only on Rust syntax are stood for by the lift's
//! position and scope rules, each a refusal: a function or builtin operation, a sort test or
//! projection, a collection operation other than an item, the empty collection or a
//! concatenation, `:=K` or `#let` in a pattern; `_`, `#Or`, `#as` or a rewrite outside one; a
//! name a condition or result reads that the sentence does not bind; a name written at another
//! sort than the sentence binds it at; a name KRS made where KRS does not write it; an alias
//! inside its own subpattern; a write of a Map instance's key other than as the sentence matched
//! it (KRS's `map-collection-key`). A new application of a parametric production, a new `:=K` or
//! `#let`, a new cell term and a new Bytes token are not read (refused): their instance, local
//! binders or spelling are not in the K text alone.
//!
//! A configuration rule's cells are read where the emitter places them
//! ([`DefinitionIndex::clause_layout`]): a rule about one instance of a `?` or `*` cell names that
//! instance's cells inside the instance's cell, beside the key cells KRS adds so that the rule
//! passes its instance's keys to a function evaluated in it. That placement is the rule's
//! footprint, the cells and instances it reads or writes; an edit that changes it (a cell added,
//! dropped or moved to another instance or out of one) is refused. A function evaluated in one
//! instance receives the keys KRS passes after its own arguments, which are not lifted: KRS
//! derives them, and the key cells, for the lifted sentence again, and the comparison with the
//! mutant's sentence checks them.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::ops::Range;

use k_rust::builtin;
use k_rust::definition::{Attributes, Sentence};
use k_rust::kast::Term;
use k_rust::outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation};
use krs_compiler::{
    DEFINITION_ARTIFACT, DescriptorLoweringError, EditJudgement, JudgeError, KEdit, KLabelIndex,
    MutationVerdict, Rederivation, RederiveFailure, SentenceJudgement, SentenceVerdict, Site,
    SourceMap, SourceMapNodeKind, judge_edits,
};
use krs_ir::{
    ApplicationRef, AtLeastTwo, BuiltinOperation, CellAttribute, CellClauseKind,
    CellCollectionType, CellContentFrame, CellMultiplicity, CellPost, CollectionResultSort,
    ConfigurationClause, FixedCell, FixedCellClause, FixedCellContent, FixedConfigurationRewrite,
    GeneratedOperation, InsertedNode, ListOperation, MapOperation, NodeOrigin, OperationSort,
    SemanticId, SemanticIdKind, SetOperation, SourceMapKey, StableItemId,
};
use krs_ir_levels::{
    IrCondition, IrRewrite, IrTermKind, ListOperands, MapEntry, MapOperands, RuleBodyRef,
    SemanticCondition, SemanticModule, SemanticRule, SemanticRuleCondition, SemanticSortRef,
    SemanticTerm, SemanticVariable, SetOperands, SymbolId,
    k_surface::{DefinitionIndex, written_items},
};

/// The re-derivation check over one baseline: its in-process lowering, its `definition.k` and
/// source map, and its K as k-rust reads it.
pub struct MutantChecker<'a> {
    rederivation: Rederivation<'a>,
    source: &'a str,
    map: &'a SourceMap,
    loaded: LoadedDefinition,
    nodes: Vec<Node>,
    by_key: BTreeMap<SourceMapKey, usize>,
    /// The baseline's Definition IR, indexed.
    definition: DefinitionIndex<'a>,
    /// The cells at or inside the keys of Map collections' instances.
    keys: BTreeMap<&'a SemanticId, KeyCell<'a>>,
}

/// One node of the baseline's `definition.k`.
#[derive(Clone, Debug)]
struct Node {
    key: SourceMapKey,
    kind: SourceMapNodeKind,
    depth: u32,
    range: Range<usize>,
    inserted: Option<InsertedNode>,
}

/// Why a baseline cannot be checked against at all.
#[derive(Debug)]
#[non_exhaustive]
pub enum CheckerError {
    /// k-rust does not load the baseline's `definition.k`.
    Load(String),
    /// The source map holds a range outside `definition.k`.
    Map,
}

impl fmt::Display for CheckerError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Load(message) => {
                write!(formatter, "k-rust does not load the definition: {message}")
            }
            Self::Map => formatter.write_str("the source map does not index the definition's text"),
        }
    }
}

impl std::error::Error for CheckerError {}

/// The check of one mutation: the judge's answer and, for each sentence it hands on, this
/// check's.
#[derive(Debug)]
pub struct MutationCheck {
    /// The judge's answer.
    pub judgement: EditJudgement,
    /// One entry per sentence the judge hands on, in text order; empty when the judge refuses.
    pub sentences: Vec<SentenceCheck>,
}

impl MutationCheck {
    /// Whether the mutation is accepted: the judge refuses nothing, every changed sentence is
    /// accepted, and some changed sentence is not the baseline's up to renaming.
    #[must_use]
    pub fn accepted(&self) -> bool {
        self.judgement.verdict() == MutationVerdict::NeedsRederivation
            && self
                .sentences
                .iter()
                .all(|sentence| sentence.outcome.is_ok())
            && !self.unchanged()
    }

    /// Whether every sentence the judge hands on is accepted and is the baseline's up to
    /// renaming: the mutation changes nothing, and it is refused.
    #[must_use]
    pub fn unchanged(&self) -> bool {
        !self.sentences.is_empty()
            && self
                .sentences
                .iter()
                .all(|sentence| matches!(&sentence.outcome, Ok(accepted) if accepted.unchanged))
    }
}

/// The check of one sentence.
#[derive(Debug)]
pub struct SentenceCheck {
    /// The sentence's source-map key.
    pub sentence: SourceMapKey,
    /// The Rust item of the sentence, as the judge names it.
    pub item: Option<StableItemId>,
    /// The check's answer.
    pub outcome: Result<Accepted, Refusal>,
}

/// An accepted sentence.
#[derive(Clone, Debug)]
pub struct Accepted {
    /// The pre-derivation sentence `A'` whose emission the mutant's sentence is: the baseline's
    /// with the lifted parts in place, its identity, label, nondet group and the fields K does not
    /// show kept. `None` for a `raw_k!` sentence, whose text is the author's.
    pub pre_derivation: Option<SemanticRule>,
    /// Whether the mutant's sentence is the baseline's up to a renaming of variables (and its
    /// label): alone, it changes nothing.
    pub unchanged: bool,
    /// Whether the mutation deletes the whole sentence, which the source without it emits;
    /// there is then no pre-derivation sentence.
    pub deleted: bool,
}

/// Why a sentence is refused.
#[derive(Debug)]
#[non_exhaustive]
pub enum Refusal {
    /// The mutant's sentence is not what KRS derives from its authored content.
    DerivedMismatch {
        /// The sentence KRS emits for the mutant's authored content.
        derived: String,
        /// The mutant's sentence.
        mutant: String,
        /// The definedness tests KRS states in it, in text order.
        derived_tests: Vec<String>,
        /// The tests the mutant keeps where the baseline states them, in text order.
        mutant_tests: Vec<String>,
    },
    /// The lift reads a construct no authored syntax produces at its position.
    Lift(LiftRefusal),
    /// KRS refuses the lifted sentence: a refusal of its derivation passes or of the semantic
    /// theory's validation, with KRS's code.
    Krs(Box<DescriptorLoweringError>),
    /// The check cannot judge the sentence.
    NotJudged(NotJudged),
    /// The mutant's sentence is not a rule of its module's grammar.
    Unparsable(String),
}

impl From<LiftRefusal> for Refusal {
    fn from(refusal: LiftRefusal) -> Self {
        Self::Lift(refusal)
    }
}

impl Refusal {
    /// KRS's diagnostic code of a [`Refusal::Krs`].
    #[must_use]
    pub fn krs_code(&self) -> Option<String> {
        match self {
            Self::Krs(error) => Some(
                krs_diagnostic::ToDiagnostic::to_diagnostic(error.as_ref())
                    .code
                    .to_string(),
            ),
            _ => None,
        }
    }
}

impl fmt::Display for Refusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DerivedMismatch {
                derived,
                derived_tests,
                mutant_tests,
                ..
            } => {
                write!(formatter, "KRS derives `{}`", derived.trim())?;
                if derived_tests != mutant_tests {
                    if derived_tests.is_empty() {
                        formatter.write_str(", which states no test here")?;
                    } else {
                        write!(formatter, ", stating `{}`", derived_tests.join("`, `"))?;
                    }
                    if mutant_tests.is_empty() {
                        formatter.write_str("; the mutant states none")?;
                    } else {
                        write!(
                            formatter,
                            "; the mutant has `{}`",
                            mutant_tests.join("`, `")
                        )?;
                    }
                }
                Ok(())
            }
            Self::Lift(refusal) => refusal.fmt(formatter),
            Self::Krs(error) => error.fmt(formatter),
            Self::NotJudged(reason) => reason.fmt(formatter),
            Self::Unparsable(message) => {
                write!(formatter, "the edited sentence does not parse: {message}")
            }
        }
    }
}

/// A construct the lift does not read as authored syntax.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum LiftRefusal {
    /// A K label no KRS construct renders.
    UnknownLabel(String),
    /// A sort name the definition does not declare.
    UnknownSort(String),
    /// A cell the configuration does not declare.
    UnknownCell(String),
    /// A name that a condition or result reads and the sentence does not bind.
    Unbound(String),
    /// A construct a position does not admit: `what` at a pattern position, say.
    NotAdmitted(String),
    /// A variable written at another sort than the sentence declares it at.
    SortMismatch(String),
    /// A shape the lift does not read.
    Shape(String),
}

impl fmt::Display for LiftRefusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownLabel(label) => {
                write!(formatter, "no KRS construct renders the K label `{label}`")
            }
            Self::UnknownSort(sort) => {
                write!(formatter, "the definition declares no sort `{sort}`")
            }
            Self::UnknownCell(cell) => {
                write!(formatter, "the configuration declares no cell `<{cell}>`")
            }
            Self::Unbound(name) => write!(formatter, "`{name}` is bound nowhere in the sentence"),
            Self::NotAdmitted(what) => write!(formatter, "no authored syntax writes {what}"),
            Self::SortMismatch(name) => write!(
                formatter,
                "`{name}` is written at another sort than the sentence binds it at"
            ),
            Self::Shape(shape) => write!(formatter, "the check does not read {shape}"),
        }
    }
}

/// What the check does not judge.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum NotJudged {
    /// The edit changes an attribute other than the label (a priority, `owise`, ...).
    Attributes,
    /// The sentence derives a local function whose declaration or equations, sentences of their
    /// own, differ from the baseline's.
    LocalFunction,
    /// The edit reaches a part of the sentence that holds a lookup guard or a local function.
    Family,
    /// The sentence's form is not one the check reads: a context, a predicate simplification, a
    /// function context, an optional or collection cell, a cell grouped in its repeated
    /// ancestor, a stream cell.
    Form(String),
    /// The edit changes the sentence's shape: its cells, its form, a frame KRS adds.
    Skeleton(String),
    /// An edit's changed bytes cross a boundary the check needs (a test's), so the mutant's
    /// extent of the node is undefined.
    Boundary,
    /// The sentence has no re-derivation here.
    Sentence(String),
}

impl fmt::Display for NotJudged {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Attributes => formatter.write_str("an edit of a sentence's attributes other than its label is not judged"),
            Self::LocalFunction => formatter.write_str("the sentence holds a block or test KRS lifts into a function of its own, and the edit changes that function's declaration or equations; it is not judged"),
            Self::Family => formatter.write_str("the edited part of the sentence holds a lookup guard or a local function; it is not judged"),
            Self::Form(form) => write!(formatter, "{form} is not judged"),
            Self::Skeleton(what) => write!(formatter, "the edit changes {what}; it is not judged"),
            Self::Boundary => formatter.write_str("an edit's changed bytes cross the boundary of a test KRS states and the conjunct it guards; write the two as separate edits"),
            Self::Sentence(why) => write!(formatter, "the sentence is not judged: {why}"),
        }
    }
}

/// One trimmed edit: the baseline bytes `start..end` become `replacement`.
#[derive(Clone, Debug)]
struct Trimmed {
    start: usize,
    end: usize,
    replacement: String,
}

/// Which side of an insertion at a position a mapped position takes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Side {
    /// Before text inserted at the position.
    Left,
    /// After text inserted at the position.
    Right,
}

fn char_boundary_prefix(left: &str, right: &str) -> usize {
    let mut length = 0;
    for ((index, a), b) in left.char_indices().zip(right.chars()) {
        if a != b {
            return index;
        }
        length = index + a.len_utf8();
    }
    length
}

fn char_boundary_suffix(left: &str, right: &str) -> usize {
    let mut length = 0;
    for (a, b) in left.chars().rev().zip(right.chars().rev()) {
        if a != b {
            break;
        }
        length += a.len_utf8();
    }
    length
}

/// The edits with the longest common prefix, then suffix, of each edit's old and new text
/// removed, in range order and, at one point, in their order.
fn trimmed(source: &str, edits: &[KEdit<'_>]) -> Vec<Trimmed> {
    let mut order = (0..edits.len()).collect::<Vec<_>>();
    order.sort_by_key(|&index| (edits[index].range.start, edits[index].range.end, index));
    order
        .into_iter()
        .map(|index| {
            let edit = &edits[index];
            let old = &source[edit.range.clone()];
            let new = edit.replacement;
            let prefix = char_boundary_prefix(old, new);
            let suffix = char_boundary_suffix(&old[prefix..], &new[prefix..]);
            Trimmed {
                start: edit.range.start + prefix,
                end: edit.range.end - suffix,
                replacement: new[prefix..new.len() - suffix].to_owned(),
            }
        })
        .filter(|edit| edit.start != edit.end || !edit.replacement.is_empty())
        .collect()
}

/// The mutant position of the baseline position `position`, or `None` when an edit's changed
/// bytes hold it strictly inside.
fn image(edits: &[Trimmed], position: usize, side: Side) -> Option<usize> {
    let mut shifted = position;
    for edit in edits {
        let before = edit.end < position
            || (edit.end == position && (edit.start < edit.end || side == Side::Right));
        if before {
            shifted = shifted + edit.replacement.len() - (edit.end - edit.start);
        } else if edit.start < position && position < edit.end {
            return None;
        }
    }
    Some(shifted)
}

fn image_range(edits: &[Trimmed], range: &Range<usize>) -> Option<Range<usize>> {
    Some(image(edits, range.start, Side::Left)?..image(edits, range.end, Side::Right)?)
}

/// A sentence's text split as KRS renders a rule: `rule`, an optional `[label]:`, the contents,
/// and an optional attribute list at the end.
#[derive(Clone, Debug)]
struct SplitSentence {
    contents: Range<usize>,
    attributes: Vec<(String, Option<String>)>,
}

/// The byte after the bracket group that opens at `open`, or `None` when it does not close.
fn group_end(text: &str, open: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut chars = text[open..].char_indices();
    while let Some((offset, character)) = chars.next() {
        match character {
            '"' => {
                let mut escaped = false;
                for (_, inner) in chars.by_ref() {
                    if escaped {
                        escaped = false;
                    } else if inner == '\\' {
                        escaped = true;
                    } else if inner == '"' {
                        break;
                    }
                }
            }
            '[' | '(' | '{' => depth += 1,
            ']' | ')' | '}' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(open + offset + 1);
                }
            }
            _ => {}
        }
    }
    None
}

/// The items of an attribute list's text, when every item has an attribute's shape: a key of
/// lowercase letters, digits and `-`, and an optional parenthesized value.
fn attribute_items(text: &str) -> Option<Vec<(String, Option<String>)>> {
    let mut items = Vec::new();
    let mut rest = text.trim();
    while !rest.is_empty() {
        let key_length = rest
            .find(|character: char| {
                !(character.is_ascii_lowercase() || character.is_ascii_digit() || character == '-')
            })
            .unwrap_or(rest.len());
        if key_length == 0 || !rest.starts_with(|character: char| character.is_ascii_lowercase()) {
            return None;
        }
        let key = rest[..key_length].to_owned();
        rest = rest[key_length..].trim_start();
        let value = if rest.starts_with('(') {
            let end = group_end(rest, 0)?;
            let value = rest[1..end - 1].to_owned();
            rest = rest[end..].trim_start();
            Some(value)
        } else {
            None
        };
        items.push((key, value));
        if let Some(after) = rest.strip_prefix(',') {
            rest = after.trim_start();
        } else if !rest.is_empty() {
            return None;
        }
    }
    Some(items)
}

fn split_sentence(text: &str) -> Option<SplitSentence> {
    let start = text.len() - text.trim_start().len();
    let after_keyword = text.len() - text[start..].strip_prefix("rule")?.len();
    let mut contents_start = after_keyword;
    let rest = &text[after_keyword..];
    let trimmed_rest = rest.trim_start();
    if trimmed_rest.starts_with('[') {
        let open = after_keyword + (rest.len() - trimmed_rest.len());
        if let Some(close) = group_end(text, open) {
            let after = text[close..].trim_start();
            if let Some(colon) = after.strip_prefix(':') {
                contents_start = text.len() - colon.len();
            }
        }
    }
    let mut contents_end = text.trim_end().len();
    let mut attributes = Vec::new();
    if text[..contents_end].ends_with(']') {
        // The last bracket group that closes at the end, if it reads as attributes.
        let mut candidate = None;
        for (index, character) in text[contents_start..contents_end].char_indices() {
            if character == '[' && group_end(text, contents_start + index) == Some(contents_end) {
                candidate = Some(contents_start + index);
                break;
            }
        }
        if let Some(open) = candidate
            && let Some(items) = attribute_items(&text[open + 1..contents_end - 1])
        {
            attributes = items;
            contents_end = open;
        }
    }
    attributes.retain(|(key, _)| key != "label");
    Some(SplitSentence {
        contents: contents_start..contents_end,
        attributes,
    })
}

/// A rule's parsed contents.
struct ParsedRule {
    body: Term,
    requires: Option<Term>,
    ensures: Option<Term>,
}

fn present(term: Term) -> Option<Term> {
    term.metadata()
        .and_then(|metadata| metadata.span.as_ref())
        .is_some()
        .then_some(term)
}

impl<'a> MutantChecker<'a> {
    /// The check over the baseline `rederivation`, whose `definition.k` is `source`, indexed by
    /// `map`.
    ///
    /// # Errors
    ///
    /// [`CheckerError::Load`] when k-rust does not load `source`.
    pub fn new(
        rederivation: Rederivation<'a>,
        source: &'a str,
        map: &'a SourceMap,
    ) -> Result<Self, CheckerError> {
        let main = rederivation
            .lowered()
            .definition()
            .main_module()
            .as_str()
            .to_owned();
        let options = LoadOptions {
            implicit_sources: vec![
                builtin::embedded("kast.md").ok_or_else(|| CheckerError::Load("kast.md".into()))?,
                builtin::embedded("prelude.md")
                    .ok_or_else(|| CheckerError::Load("prelude.md".into()))?,
            ],
            ..LoadOptions::default()
        };
        let mut resolver = |_: &str, required: &str| {
            builtin::embedded(required).ok_or_else(|| format!("no builtin source {required}"))
        };
        let (loaded, _) = load_for_compilation(
            ResolvedSource::new(DEFINITION_ARTIFACT, source),
            main,
            None,
            &mut resolver,
            &options,
        )
        .map_err(|error| CheckerError::Load(error.to_string()))?;
        let mut nodes = Vec::new();
        for entry in map.entries() {
            let Some(generated) = entry.generated() else {
                continue;
            };
            if generated.artifact() != DEFINITION_ARTIFACT {
                continue;
            }
            let start = usize::try_from(generated.start_byte()).map_err(|_| CheckerError::Map)?;
            let end = usize::try_from(generated.end_byte()).map_err(|_| CheckerError::Map)?;
            if start > end || end > source.len() {
                return Err(CheckerError::Map);
            }
            nodes.push(Node {
                key: entry.key().clone(),
                kind: entry.node_kind(),
                depth: entry.depth(),
                range: start..end,
                inserted: entry.inserted().map(|(kind, _)| kind),
            });
        }
        let by_key = nodes
            .iter()
            .enumerate()
            .map(|(index, node)| (node.key.clone(), index))
            .collect();
        let definition = DefinitionIndex::new(rederivation.lowered().definition());
        let keys = map_keys(rederivation.retained().theory().modules());
        Ok(Self {
            rederivation,
            source,
            map,
            loaded,
            nodes,
            by_key,
            definition,
            keys,
        })
    }

    /// The baseline's re-derivation.
    #[must_use]
    pub const fn rederivation(&self) -> &Rederivation<'a> {
        &self.rederivation
    }

    /// Judges `edits` of the baseline's `definition.k` and checks every sentence the judge hands
    /// on.
    ///
    /// # Errors
    ///
    /// The judge's error for edits it cannot apply.
    pub fn check(&self, edits: &[KEdit<'_>]) -> Result<MutationCheck, JudgeError> {
        let judgement = judge_edits(self.source, self.map, DEFINITION_ARTIFACT, edits)?;
        let sentences = if judgement.verdict() == MutationVerdict::NeedsRederivation {
            judgement
                .sentences
                .iter()
                .map(|sentence| self.check_sentence(edits, &judgement, sentence))
                .collect()
        } else {
            Vec::new()
        };
        Ok(MutationCheck {
            judgement,
            sentences,
        })
    }

    /// Checks one sentence the judge hands on.
    #[must_use]
    pub fn check_sentence(
        &self,
        edits: &[KEdit<'_>],
        judgement: &EditJudgement,
        sentence: &SentenceJudgement,
    ) -> SentenceCheck {
        let outcome = match &sentence.verdict {
            SentenceVerdict::NeedsRederivation { containers } => {
                let containers = containers
                    .iter()
                    .map(|container| (container.emitted.clone(), container.kind))
                    .collect::<Vec<_>>();
                self.check_edited(
                    &trimmed(self.source, edits),
                    &judgement.mutant,
                    &sentence.sentence,
                    &containers,
                )
            }
            _ => Err(Refusal::NotJudged(NotJudged::Sentence(
                "the judge refuses it".into(),
            ))),
        };
        SentenceCheck {
            sentence: sentence.sentence.clone(),
            item: sentence.item.clone(),
            outcome,
        }
    }

    /// The fixed point at the baseline sentence `key`: the check of the baseline itself as the
    /// mutant, with the whole sentence as the container, which every node lifted and derived
    /// again must reproduce.
    ///
    /// # Errors
    ///
    /// The check's refusal of the sentence, which is a place where the lift reads less than KRS
    /// writes.
    pub fn fixed_point(&self, key: &SourceMapKey) -> Result<Accepted, Refusal> {
        let Some(node) = self.by_key.get(key).map(|&index| &self.nodes[index]) else {
            return Err(Refusal::NotJudged(NotJudged::Sentence(format!(
                "{key} is no sentence of the definition"
            ))));
        };
        self.check_edited(&[], self.source, key, &[(node.range.clone(), node.kind)])
    }

    /// The rule sentences of the baseline's `definition.k`, by key, in text order.
    #[must_use]
    pub fn rule_sentences(&self) -> Vec<SourceMapKey> {
        let mut sentences = self
            .nodes
            .iter()
            .filter(|node| node.kind == SourceMapNodeKind::Rule)
            .collect::<Vec<_>>();
        sentences.sort_by_key(|node| node.range.start);
        sentences.into_iter().map(|node| node.key.clone()).collect()
    }

    /// The nodes of the sentence `sentence` (its range), deepest last.
    fn nodes_in(&self, range: &Range<usize>) -> Vec<&Node> {
        self.nodes
            .iter()
            .filter(|node| range.start <= node.range.start && node.range.end <= range.end)
            .collect()
    }

    fn check_edited(
        &self,
        edits: &[Trimmed],
        mutant: &str,
        key: &SourceMapKey,
        containers: &[(Range<usize>, SourceMapNodeKind)],
    ) -> Result<Accepted, Refusal> {
        let sentence = self
            .by_key
            .get(key)
            .map(|&index| &self.nodes[index])
            .ok_or_else(|| {
                Refusal::NotJudged(NotJudged::Sentence(format!("{key} is no sentence")))
            })?;
        if sentence.kind == SourceMapNodeKind::RawSentence {
            return Ok(Accepted {
                pre_derivation: None,
                unchanged: false,
                deleted: false,
            });
        }
        // A deletion of the whole sentence: one edit removes every token of it and writes none.
        let text = &self.source[sentence.range.clone()];
        let tokens = sentence.range.start + (text.len() - text.trim_start().len())
            ..sentence.range.start + text.trim_end().len();
        if edits.iter().any(|edit| {
            edit.start <= tokens.start
                && tokens.end <= edit.end
                && edit.replacement.trim().is_empty()
        }) {
            return Ok(Accepted {
                pre_derivation: None,
                unchanged: false,
                deleted: true,
            });
        }
        let site = self
            .rederivation
            .site(key)
            .map_err(|error| Refusal::NotJudged(NotJudged::Sentence(error.to_string())))?;
        let baseline_text = &self.source[sentence.range.clone()];
        let mutant_range =
            image_range(edits, &sentence.range).ok_or(Refusal::NotJudged(NotJudged::Boundary))?;
        let mutant_text = &mutant[mutant_range.clone()];
        let nodes = self.nodes_in(&sentence.range);
        // The mutant's authored content: its text with each test KRS states removed.
        let tests = definedness_joins(&nodes, self.source);
        let authored_text = strip_tests(edits, mutant, &mutant_range, &tests)?;
        let baseline_split = split_sentence(baseline_text)
            .ok_or_else(|| Refusal::NotJudged(NotJudged::Form("this sentence".into())))?;
        let mutant_split = split_sentence(mutant_text)
            .ok_or_else(|| Refusal::NotJudged(NotJudged::Skeleton("the rule keyword".into())))?;
        let authored_split = split_sentence(&authored_text)
            .ok_or_else(|| Refusal::NotJudged(NotJudged::Skeleton("the rule keyword".into())))?;
        if mutant_split.attributes != baseline_split.attributes {
            return Err(Refusal::NotJudged(NotJudged::Attributes));
        }
        let module = site.emitted_module.clone();
        let mutant_parse = self.parse(&module, &mutant_text[mutant_split.contents.clone()])?;
        let authored_parse =
            self.parse(&module, &authored_text[authored_split.contents.clone()])?;
        let lifted = self.lift_sentence(&site, sentence, &nodes, &authored_parse, containers)?;
        let rederived =
            self.rederivation
                .rederive(&site, lifted)
                .map_err(|failure| match failure {
                    RederiveFailure::LocalFunction => Refusal::NotJudged(NotJudged::LocalFunction),
                    RederiveFailure::Refused(error) => Refusal::Krs(Box::new(error)),
                    other => Refusal::NotJudged(NotJudged::Sentence(other.to_string())),
                })?;
        let derived_split = split_sentence(&rederived.text)
            .ok_or_else(|| Refusal::NotJudged(NotJudged::Sentence("its rendering".into())))?;
        let derived_parse = self.parse(&module, &rederived.text[derived_split.contents.clone()])?;
        if derived_split.attributes != mutant_split.attributes
            || !same_rule(&derived_parse, &mutant_parse)
        {
            return Err(Refusal::DerivedMismatch {
                derived: rederived.text.clone(),
                mutant: mutant_text.to_owned(),
                derived_tests: derived_tests(&rederived),
                mutant_tests: tests
                    .iter()
                    .filter_map(|join| {
                        image_range(edits, &join.test).map(|range| mutant[range].to_owned())
                    })
                    .collect(),
            });
        }
        let baseline_parse =
            self.parse(&module, &baseline_text[baseline_split.contents.clone()])?;
        Ok(Accepted {
            pre_derivation: Some(rederived.pre_derivation),
            unchanged: same_rule(&baseline_parse, &mutant_parse),
            deleted: false,
        })
    }

    fn parse(&self, module: &str, contents: &str) -> Result<ParsedRule, Refusal> {
        let attributes = Attributes::new(BTreeMap::from([
            (
                k_rust::definition::SOURCE_ATTRIBUTE.into(),
                serde_json::json!(DEFINITION_ARTIFACT),
            ),
            (
                k_rust::definition::SOURCE_ID_ATTRIBUTE.into(),
                serde_json::json!(0),
            ),
            ("contentStartOffset".into(), serde_json::json!(0)),
        ]));
        match k_rust::inner::parse_rule_content(
            self.loaded.resolved(),
            module,
            contents,
            attributes,
        ) {
            Ok(Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            }) => Ok(ParsedRule {
                body,
                requires: present(requires),
                ensures: present(ensures),
            }),
            Ok(_) => Err(Refusal::Unparsable("not a rule".into())),
            Err(error) => Err(Refusal::Unparsable(error.to_string())),
        }
    }

    /// The clause of `clauses` (a configuration rule's pre-derivation clauses) each of `emitted`
    /// (its Definition IR clauses) is lowered from, by provenance, in emitted order; `None` for a
    /// key cell KRS adds, so that the rule passes its instance's key to a function evaluated in
    /// it. Each clause is lowered to exactly one emitted clause of its own cell.
    fn clause_owners<T, U>(
        &self,
        clauses: &[ConfigurationClause<SemanticId, T>],
        emitted: &[ConfigurationClause<SymbolId, U>],
    ) -> Result<Vec<Option<usize>>, Refusal> {
        let unpaired = || {
            Refusal::NotJudged(NotJudged::Sentence(
                "its Definition IR clauses are neither its own clauses nor key cells KRS adds"
                    .into(),
            ))
        };
        let mut paired = vec![false; clauses.len()];
        let mut owners = Vec::with_capacity(emitted.len());
        for emitted in emitted {
            let cell = self
                .definition
                .cell_name(emitted.cell())
                .and_then(|name| self.rederivation.index().cell(name))
                .ok_or_else(unpaired)?;
            let owner = clauses.iter().position(|clause| {
                self.rederivation
                    .definition_keys(clause.origin_key())
                    .contains(emitted.origin_key())
            });
            match owner {
                Some(index) if !paired[index] && clauses[index].cell() == cell => {
                    paired[index] = true;
                }
                None if matches!(emitted, ConfigurationClause::Fixed(_))
                    && emitted.origin().origin().inserted().is_some()
                    && self.keys.get(cell).is_some_and(KeyCell::is_key) => {}
                _ => return Err(unpaired()),
            }
            owners.push(owner);
        }
        if paired.contains(&false) {
            return Err(unpaired());
        }
        Ok(owners)
    }

    /// The range of the Definition IR node lowered from the semantic node `key`, the outermost
    /// when several are.
    fn range_of(&self, key: &SourceMapKey) -> Option<Range<usize>> {
        self.rederivation
            .definition_keys(key)
            .iter()
            .filter_map(|definition| self.by_key.get(definition))
            .map(|&index| self.nodes[index].range.clone())
            .max_by_key(ExactSizeIterator::len)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "One pass over the parts of a sentence, in the order K writes them."
    )]
    fn lift_sentence(
        &self,
        site: &Site<'_>,
        sentence: &Node,
        nodes: &[&Node],
        parsed: &ParsedRule,
        containers: &[(Range<usize>, SourceMapNodeKind)],
    ) -> Result<SemanticRule, Refusal> {
        let whole = containers
            .iter()
            .any(|(range, kind)| *kind == SourceMapNodeKind::Rule || *range == sentence.range);
        let touches = |range: Option<Range<usize>>| {
            whole
                || range.is_none_or(|range| {
                    containers.iter().any(|(container, _)| {
                        container.start < range.end && range.start < container.end
                            || (container.start == container.end
                                && range.start <= container.start
                                && container.start <= range.end)
                    })
                })
        };
        // A part that holds a lookup guard or a local function is not lifted.
        let holds_family = |range: &Range<usize>| {
            nodes.iter().any(|node| {
                range.start <= node.range.start
                    && node.range.end <= range.end
                    && matches!(
                        node.inserted,
                        Some(InsertedNode::LookupGuard | InsertedNode::LocalFunction)
                    )
            })
        };
        let rule = site.pre_derivation;
        let mut lift = Lift::new(self.rederivation.index(), site, rule);
        let mut lifted = rule.clone();
        match rule.relational_body() {
            RuleBodyRef::Term(body) => {
                if site.definition.function_context().is_some() {
                    return Err(Refusal::NotJudged(NotJudged::Form(
                        "a function context".into(),
                    )));
                }
                let range = self.range_of(body.origin().key()).or_else(|| {
                    body.local_term()
                        .and_then(|local| self.range_of(local.origin().key()))
                });
                if touches(range.clone()) {
                    if range.as_ref().is_some_and(holds_family) {
                        return Err(Refusal::NotJudged(NotJudged::Family));
                    }
                    let body = lift.term_body(body, &parsed.body, rule.kind(), site.head_fixed)?;
                    lifted = lifted.with_term_body(body).map_err(|error| {
                        Refusal::NotJudged(NotJudged::Sentence(error.to_string()))
                    })?;
                }
            }
            RuleBodyRef::Configuration { body, .. } => {
                let RuleBodyRef::Configuration {
                    body: emitted_body, ..
                } = site.definition.relational_body()
                else {
                    return Err(Refusal::NotJudged(NotJudged::Sentence(
                        "its Definition IR body".into(),
                    )));
                };
                let emitted = emitted_body.clauses();
                let owners = self.clause_owners(body.clauses(), emitted)?;
                let items = clause_items(&parsed.body, emitted, &self.definition)?;
                let mut lifted_clauses = vec![None; body.clauses().len()];
                let mut changed = false;
                for ((emitted, items), owner) in emitted.iter().zip(items).zip(owners) {
                    // A key cell KRS adds is derived again for the lifted sentence.
                    let Some(index) = owner else {
                        continue;
                    };
                    let clause = &body.clauses()[index];
                    let range = self.range_of(clause.origin_key());
                    let emitted_range = self
                        .by_key
                        .get(emitted.origin_key())
                        .map(|&index| self.nodes[index].range.clone());
                    let range = range.or(emitted_range);
                    if !touches(range.clone()) {
                        lifted_clauses[index] = Some(clause.clone());
                        continue;
                    }
                    if range.as_ref().is_some_and(holds_family) {
                        return Err(Refusal::NotJudged(NotJudged::Family));
                    }
                    let ConfigurationClause::Fixed(fixed) = clause else {
                        return Err(Refusal::NotJudged(NotJudged::Form(
                            "an optional or collection cell".into(),
                        )));
                    };
                    if let ConfigurationClause::Fixed(emitted) = emitted
                        && matches!(emitted.frame(), CellContentFrame::ListRemainder { .. })
                    {
                        return Err(Refusal::NotJudged(NotJudged::Form("a stream cell".into())));
                    }
                    let [item] = items.as_slice() else {
                        return Err(Refusal::NotJudged(NotJudged::Skeleton(
                            "the cells the rule mentions".into(),
                        )));
                    };
                    let lifted = lift.clause(fixed, item)?;
                    if let Some(key) = self.keys.get(fixed.cell()) {
                        match key_kept(&lifted) {
                            Some(true) => {}
                            Some(false) => return Err(key.refusal()),
                            None => {
                                return Err(Refusal::NotJudged(NotJudged::Form(
                                    "an in-place rewrite at or inside a Map instance's key".into(),
                                )));
                            }
                        }
                    }
                    lifted_clauses[index] = Some(ConfigurationClause::Fixed(lifted));
                    changed = true;
                }
                let clauses = lifted_clauses
                    .into_iter()
                    .collect::<Option<Vec<_>>>()
                    .expect("every clause has its emitted clause");
                if changed {
                    let rewritten = FixedConfigurationRewrite::new(
                        body.origin().clone(),
                        body.configuration().clone(),
                        clauses,
                        body.omitted_siblings().to_vec(),
                    )
                    .map_err(|error| Refusal::NotJudged(NotJudged::Sentence(error.to_string())))?;
                    lifted = lifted.with_configuration_body(rewritten).map_err(|error| {
                        Refusal::NotJudged(NotJudged::Sentence(error.to_string()))
                    })?;
                }
            }
            RuleBodyRef::Predicate(_) => {
                return Err(Refusal::NotJudged(NotJudged::Form(
                    "a predicate simplification".into(),
                )));
            }
        }
        for ensures in [false, true] {
            let (baseline, parsed) = if ensures {
                (rule.ensures(), parsed.ensures.as_ref())
            } else {
                (rule.requires(), parsed.requires.as_ref())
            };
            let range = match baseline {
                Some(IrCondition::Bool(condition)) => self.range_of(condition.origin().key()),
                Some(condition @ IrCondition::Predicate(_)) => {
                    if touches(self.range_of(condition.origin().key())) {
                        return Err(Refusal::NotJudged(NotJudged::Form(
                            "a matching-logic condition".into(),
                        )));
                    }
                    continue;
                }
                None => None,
            };
            // A condition the baseline lacks is touched only by an edit of the sentence itself.
            let edited = match &range {
                Some(_) => touches(range.clone()),
                None => whole || parsed.is_some(),
            };
            if !edited {
                continue;
            }
            if range.as_ref().is_some_and(holds_family) {
                return Err(Refusal::NotJudged(NotJudged::Family));
            }
            let condition = match parsed {
                None => None,
                Some(term) => {
                    let guide = match baseline {
                        Some(IrCondition::Bool(condition)) => Some(condition),
                        _ => None,
                    };
                    let origin = guide.map_or_else(
                        || lift.fresh_origin(rule.origin()),
                        |condition| condition.origin().clone(),
                    );
                    let lifted_term = lift.term(
                        term,
                        guide.map(SemanticRuleCondition::term),
                        Position::Value,
                        Some(&SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bool)),
                    )?;
                    Some(SemanticCondition::Bool(SemanticRuleCondition::new(
                        origin,
                        lifted_term,
                    )))
                }
            };
            lifted = if ensures {
                lifted.with_ensures(condition)
            } else {
                lifted
                    .with_requires(condition)
                    .map_err(|error| Refusal::Lift(LiftRefusal::Shape(error.to_string())))?
            };
        }
        // The sentence declares exactly the variables it holds: a name an edit removes from
        // every place is no binder of the edited sentence.
        let mut variables = rule.variables().to_vec();
        variables.extend(lift.new_variables);
        let held = held_variables(&lifted);
        let declared_elsewhere = held_variables_outside_terms(rule);
        variables.retain(|variable| {
            held.contains(variable.id()) || declared_elsewhere.contains(variable.id())
        });
        let lifted = lifted.with_variables(variables);
        // Every name a result or a condition reads must be bound, as in Rust; one the baseline
        // reads unbound (an existential, a fresh name) stays as it is.
        let before = unbound(rule);
        if let Some(name) = unbound(&lifted).difference(&before).next() {
            let shown = site.names.name(name).unwrap_or(name.as_str()).to_owned();
            return Err(Refusal::Lift(LiftRefusal::Unbound(shown)));
        }
        Ok(lifted)
    }
}

/// A test KRS states and the `andThenBool` that joins it: the join's range, the test's, and the
/// conjunct it guards.
#[derive(Clone, Debug)]
struct Join {
    whole: Range<usize>,
    test: Range<usize>,
    guarded: Range<usize>,
}

/// The definedness joins among `nodes`, outermost first.
fn definedness_joins(nodes: &[&Node], source: &str) -> Vec<Join> {
    let mut joins = Vec::new();
    for node in nodes {
        if node.inserted != Some(InsertedNode::DefinednessTest) {
            continue;
        }
        let mut children = nodes
            .iter()
            .filter(|child| {
                child.depth == node.depth + 1
                    && node.range.start <= child.range.start
                    && child.range.end <= node.range.end
            })
            .collect::<Vec<_>>();
        children.sort_by_key(|child| child.range.start);
        let [test, guarded] = children.as_slice() else {
            continue;
        };
        if test.inserted != Some(InsertedNode::DefinednessTest) {
            continue;
        }
        let between =
            source[test.range.end..guarded.range.start].trim_matches(|character: char| {
                character.is_whitespace() || character == '(' || character == ')'
            });
        if between != "andThenBool" {
            continue;
        }
        joins.push(Join {
            whole: node.range.clone(),
            test: test.range.clone(),
            guarded: guarded.range.clone(),
        });
    }
    joins.sort_by_key(|join| (join.whole.start, std::cmp::Reverse(join.whole.end)));
    joins
}

/// The mutant's text of `range` with each join in it replaced by the conjunct it guards.
fn strip_tests(
    edits: &[Trimmed],
    mutant: &str,
    range: &Range<usize>,
    joins: &[Join],
) -> Result<String, Refusal> {
    let mapped = joins
        .iter()
        .map(|join| {
            Some((
                image_range(edits, &join.whole)?,
                image_range(edits, &join.guarded)?,
            ))
        })
        .collect::<Option<Vec<_>>>()
        .ok_or(Refusal::NotJudged(NotJudged::Boundary))?;
    Ok(strip_in(mutant, range.clone(), &mapped))
}

fn strip_in(mutant: &str, range: Range<usize>, joins: &[(Range<usize>, Range<usize>)]) -> String {
    let mut output = String::new();
    let mut at = range.start;
    let mut index = 0;
    while index < joins.len() {
        let (join, guarded) = &joins[index];
        if join.start < at || join.end > range.end {
            index += 1;
            continue;
        }
        output.push_str(&mutant[at..join.start]);
        let inner = joins
            .iter()
            .filter(|(other, _)| guarded.start <= other.start && other.end <= guarded.end)
            .cloned()
            .collect::<Vec<_>>();
        output.push_str(&strip_in(mutant, guarded.clone(), &inner));
        at = join.end;
        index += 1;
    }
    output.push_str(&mutant[at..range.end]);
    output
}

/// The definedness tests the re-derived sentence states, in text order.
fn derived_tests(rederived: &krs_compiler::Rederived) -> Vec<String> {
    let mut tests = BTreeSet::new();
    let mut visit = |term: &krs_ir_levels::DefinitionTerm| {
        collect_tests(term, &mut tests);
    };
    if let Some(IrCondition::Bool(condition)) = rederived.definition.requires() {
        visit(condition.term());
    }
    let ranges = rederived
        .ranges
        .iter()
        .cloned()
        .collect::<BTreeMap<SourceMapKey, Range<usize>>>();
    let mut found = tests
        .iter()
        .filter_map(|key| ranges.get(key))
        .map(|range| (range.start, rederived.text[range.clone()].to_owned()))
        .collect::<Vec<_>>();
    found.sort();
    found.into_iter().map(|(_, text)| text).collect()
}

/// The outermost tests of `term`: the left operand of each join KRS inserted.
fn collect_tests(term: &krs_ir_levels::DefinitionTerm, tests: &mut BTreeSet<SourceMapKey>) {
    let inserted = term.origin().origin().inserted().map(|(kind, _)| kind);
    if inserted == Some(InsertedNode::DefinednessTest)
        && let IrTermKind::Application { arguments, .. } = term.kind()
        && let [test, guarded] = arguments.as_slice()
        && test.origin().origin().inserted().map(|(kind, _)| kind)
            == Some(InsertedNode::DefinednessTest)
    {
        tests.insert(test.origin().key().clone());
        collect_tests(guarded, tests);
        return;
    }
    for child in term.children() {
        collect_tests(child, tests);
    }
}

/// The cell items of a configuration rule's body: the leaves of its `#cells` tree.
fn cell_items(body: &Term) -> Vec<&Term> {
    let mut items = Vec::new();
    let mut pending = vec![body];
    while let Some(term) = pending.pop() {
        match term.unannotated() {
            Term::Apply { label, arguments } if label.name == "#cells" => {
                pending.extend(arguments.iter().rev());
            }
            _ => items.push(term),
        }
    }
    items
}

/// The items of a configuration rule's body that each of `clauses` (the sentence's Definition IR
/// clauses) is written as, one list per clause, in clause order.
///
/// The cells a rule mentions are its footprint, and the emitter writes them where
/// [`DefinitionIndex::clause_layout`] places them: a rule whose cells lie in an instance, below a
/// `?` or `*` cell, is about one instance, so its clauses are written inside that instance's
/// cell, open on the right, nested in the cells of the enclosing instances it names, each
/// instance's cell holding the clauses that lie in it directly and then the cell of the next
/// instance; the clauses of a rule whose cells lie in no instance are written at the top; each
/// clause as the items [`written_items`] counts. Mentioning an instance's cells this way is the
/// footprint, not a change of it. The body must hold exactly that placement: an instance cell
/// missing, added, or holding another instance's cell, or a cell added or dropped at some level,
/// changes the cells (or instances) the rule reads or writes, and is refused. What this reads of
/// the instance cells' frames, and the frames themselves, the comparison of the derived sentence
/// with the mutant's checks again.
fn clause_items<'t, T>(
    body: &'t Term,
    clauses: &[ConfigurationClause<SymbolId, T>],
    definition: &DefinitionIndex<'_>,
) -> Result<Vec<Vec<&'t Term>>, Refusal> {
    fn footprint() -> Refusal {
        Refusal::NotJudged(NotJudged::Skeleton("the cells the rule mentions".into()))
    }
    // The items of one level, given to its clauses in order; none may be left.
    fn assign<'t, T>(
        level: &[usize],
        items: Vec<&'t Term>,
        clauses: &[ConfigurationClause<SymbolId, T>],
        groups: &mut [Vec<&'t Term>],
    ) -> Result<(), Refusal> {
        let mut items = items.into_iter();
        for &index in level {
            for _ in 0..written_items(&clauses[index]) {
                groups[index].push(items.next().ok_or_else(footprint)?);
            }
        }
        if items.next().is_some() {
            return Err(footprint());
        }
        Ok(())
    }
    let layout = definition
        .clause_layout(clauses.iter().map(ConfigurationClause::cell))
        .map_err(|error| Refusal::NotJudged(NotJudged::Sentence(error.to_string())))?;
    let mut groups = vec![Vec::new(); clauses.len()];
    let items = cell_items(body);
    if layout.chain.is_empty() {
        let top = layout.levels.first().map_or(&[][..], Vec::as_slice);
        assign(top, items, clauses, &mut groups)?;
        return Ok(groups);
    }
    // The top holds the outermost instance's cell alone.
    let &[mut cell] = items.as_slice() else {
        return Err(footprint());
    };
    for (position, (instance, level)) in layout.chain.iter().zip(&layout.levels).enumerate() {
        let name = definition.cell_name(instance).ok_or_else(|| {
            Refusal::NotJudged(NotJudged::Sentence(format!("instance cell {instance}")))
        })?;
        let Term::Apply { label, arguments } = cell.unannotated() else {
            return Err(footprint());
        };
        let [_, content, _] = arguments.as_slice() else {
            return Err(footprint());
        };
        if label
            .name
            .strip_prefix('<')
            .and_then(|rest| rest.strip_suffix('>'))
            != Some(name)
        {
            return Err(footprint());
        }
        let mut items = cell_items(content);
        let inner = if position + 1 < layout.chain.len() {
            Some(items.pop().ok_or_else(footprint)?)
        } else {
            None
        };
        assign(level, items, clauses, &mut groups)?;
        match inner {
            Some(next) => cell = next,
            None => break,
        }
    }
    Ok(groups)
}

/// A cell of the Semantic IR's configuration.
type SemanticCell = FixedCell<SemanticSortRef, SemanticId>;

/// A cell at or inside the key of a Map collection's instances, the instance cell's first child.
struct KeyCell<'d> {
    /// The collection cell.
    holder: &'d SemanticCell,
    /// The key cell.
    key: &'d SemanticCell,
    /// The cell itself: the key, or a cell inside it.
    cell: &'d SemanticCell,
}

impl KeyCell<'_> {
    /// Whether the cell is the key cell itself.
    fn is_key(&self) -> bool {
        self.cell.id() == self.key.id()
    }

    /// The refusal of a sentence that writes this cell other than as its subject matched it,
    /// with the reason KRS gives the Rust source the sentence stands for, which writes the key
    /// ([`krs_ir::subject::key_write_reason`]). The sentence is about one instance of the
    /// collection, whose instance type is the group it is a rule for.
    fn refusal(&self) -> Refusal {
        let field = |cell: &SemanticCell| {
            let field = cell.field().unwrap_or(cell.name());
            field.strip_prefix("r#").unwrap_or(field).to_owned()
        };
        let group = self.holder.declaration().map_or_else(
            || self.holder.name().to_owned(),
            |declaration| declaration.item_name().to_owned(),
        );
        Refusal::Krs(Box::new(DescriptorLoweringError::GroupInstance {
            code: krs_diagnostic::codes::analysis::MAP_COLLECTION_KEY,
            reason: krs_ir::subject::key_write_reason(
                &group,
                &field(self.holder),
                &field(self.key),
                &field(self.cell),
            ),
            range: None,
            item: None,
        }))
    }
}

/// The cells at or inside the keys of Map collections' instances in `modules`' configurations,
/// by cell.
fn map_keys(modules: &[SemanticModule]) -> BTreeMap<&SemanticId, KeyCell<'_>> {
    fn inside<'d>(
        holder: &'d SemanticCell,
        key: &'d SemanticCell,
        cell: &'d SemanticCell,
        keys: &mut BTreeMap<&'d SemanticId, KeyCell<'d>>,
    ) {
        keys.insert(cell.id(), KeyCell { holder, key, cell });
        if let FixedCellContent::Children { children } = cell.content() {
            for child in children {
                inside(holder, key, child, keys);
            }
        }
    }
    fn walk<'d>(cells: &'d [SemanticCell], keys: &mut BTreeMap<&'d SemanticId, KeyCell<'d>>) {
        for cell in cells {
            let FixedCellContent::Children { children } = cell.content() else {
                continue;
            };
            let star = cell.attributes().iter().any(|attribute| {
                matches!(
                    attribute,
                    CellAttribute::Multiplicity {
                        value: CellMultiplicity::Star,
                        ..
                    }
                )
            });
            let map = cell.attributes().iter().any(|attribute| {
                matches!(
                    attribute,
                    CellAttribute::CollectionType {
                        value: CellCollectionType::Map,
                        ..
                    }
                )
            });
            if star
                && map
                && let Some(key) = children.first()
            {
                inside(cell, key, key, keys);
            }
            walk(children, keys);
        }
    }
    let mut keys = BTreeMap::new();
    for module in modules {
        if let Some(configuration) = module.configuration() {
            walk(configuration.cells(), &mut keys);
        }
    }
    keys
}

/// Whether a lifted clause of a cell at or inside a Map instance's key keeps what its subject
/// matched there: it leaves the content as matched, or writes back the variable the subject bound
/// it to (as a variable or an alias) or the same token, as KRS's own predicate over a written key
/// ([`krs_ir::subject::keeps_key_term`]) admits. `None` for an in-place rewrite inside the
/// content, which KRS judges by each rewrite's sides ([`krs_ir::subject::rewrites_keep`]) and
/// the lift does not read.
///
/// A key restated as another literal than the baseline's (`<id> 0 </id>` as `<id> 1 </id>`) is
/// no write: the subject matches another instance, which a Rust source writes as `id: 1`, so
/// it is a change of pattern, judged as any other.
fn key_kept(clause: &FixedCellClause<SemanticId, SemanticTerm>) -> Option<bool> {
    let written = match clause.after() {
        CellPost::Preserve => return Some(true),
        CellPost::Local => return None,
        CellPost::Replace { term } => term,
    };
    let matched = clause.before();
    let unaliased = match matched.kind() {
        IrTermKind::As { pattern, .. } => pattern.as_ref(),
        _ => matched,
    };
    Some(match (written.kind(), matched.kind(), unaliased.kind()) {
        (
            IrTermKind::Variable { variable },
            IrTermKind::Variable { variable: bound } | IrTermKind::As { alias: bound, .. },
            _,
        ) => variable == bound,
        (IrTermKind::Token { value }, _, IrTermKind::Token { value: other }) => {
            value == other && written.sort() == unaliased.sort()
        }
        _ => false,
    })
}

/// Whether two parsed rules are equal up to a bijective renaming of their variables.
fn same_rule(left: &ParsedRule, right: &ParsedRule) -> bool {
    let mut renaming = Renaming::default();
    renaming.same(&left.body, &right.body)
        && match (&left.requires, &right.requires) {
            (Some(left), Some(right)) => renaming.same(left, right),
            (None, None) => true,
            _ => false,
        }
        && match (&left.ensures, &right.ensures) {
            (Some(left), Some(right)) => renaming.same(left, right),
            (None, None) => true,
            _ => false,
        }
}

#[derive(Default)]
struct Renaming {
    forward: BTreeMap<String, String>,
    backward: BTreeMap<String, String>,
}

impl Renaming {
    fn same(&mut self, left: &Term, right: &Term) -> bool {
        match (left.unannotated(), right.unannotated()) {
            (
                Term::Variable {
                    name: left_name,
                    sort: left_sort,
                },
                Term::Variable {
                    name: right_name,
                    sort: right_sort,
                },
            ) => {
                if left_sort != right_sort {
                    return false;
                }
                if left_name == "_" || right_name == "_" {
                    return left_name == right_name;
                }
                let forward = self
                    .forward
                    .entry(left_name.clone())
                    .or_insert_with(|| right_name.clone())
                    .clone();
                let backward = self
                    .backward
                    .entry(right_name.clone())
                    .or_insert_with(|| left_name.clone())
                    .clone();
                forward == *right_name && backward == *left_name
            }
            (
                Term::Apply {
                    label: left_label,
                    arguments: left_arguments,
                },
                Term::Apply {
                    label: right_label,
                    arguments: right_arguments,
                },
            ) => {
                left_label == right_label
                    && left_arguments.len() == right_arguments.len()
                    && left_arguments
                        .iter()
                        .zip(right_arguments)
                        .all(|(left, right)| self.same(left, right))
            }
            (
                Term::Token {
                    token: left_token,
                    sort: left_sort,
                },
                Term::Token {
                    token: right_token,
                    sort: right_sort,
                },
            ) => left_token == right_token && left_sort == right_sort,
            (
                Term::Rewrite {
                    left: left_from,
                    right: left_to,
                },
                Term::Rewrite {
                    left: right_from,
                    right: right_to,
                },
            ) => self.same(left_from, right_from) && self.same(left_to, right_to),
            (
                Term::As {
                    pattern: left_pattern,
                    alias: left_alias,
                },
                Term::As {
                    pattern: right_pattern,
                    alias: right_alias,
                },
            ) => self.same(left_pattern, right_pattern) && self.same(left_alias, right_alias),
            (Term::Sequence(left), Term::Sequence(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right)
                        .all(|(left, right)| self.same(left, right))
            }
            (Term::InjectedLabel(left), Term::InjectedLabel(right)) => left == right,
            _ => false,
        }
    }
}

/// The variables a result or condition of `rule` reads that no pattern, alias, local binder or
/// declared binder of `rule` binds.
fn unbound(rule: &SemanticRule) -> BTreeSet<SemanticId> {
    let mut bound = BTreeSet::new();
    let mut read = BTreeSet::new();
    for binder in rule.fresh().iter().chain(rule.existentials()) {
        bound.insert(binder.id().clone());
    }
    if let Some(unbound) = rule.unbound_variables() {
        for variable in unbound.variables() {
            if let Some(id) = variable.id() {
                bound.insert(id.clone());
            }
        }
    }
    match rule.relational_body() {
        RuleBodyRef::Term(body) => {
            if let Some(local) = body.local_term() {
                pattern_names(&local.pre_pattern(), &mut bound);
                value_names(&local.post_term(), &mut read, &mut bound);
            } else {
                pattern_names(body.from(), &mut bound);
                value_names(body.to(), &mut read, &mut bound);
            }
        }
        RuleBodyRef::Configuration { body, .. } => {
            for clause in body.fixed_clauses() {
                pattern_names(&clause.before().pre_pattern(), &mut bound);
                if let Some(binding) = clause.frame().binding() {
                    bound.insert(binding.clone());
                }
                match clause.after() {
                    CellPost::Replace { term } => value_names(term, &mut read, &mut bound),
                    CellPost::Local => {
                        value_names(&clause.before().post_term(), &mut read, &mut bound);
                    }
                    CellPost::Preserve => {}
                }
            }
        }
        RuleBodyRef::Predicate(_) => {}
    }
    for condition in [rule.requires(), rule.ensures()].into_iter().flatten() {
        if let IrCondition::Bool(condition) = condition {
            value_names(condition.term(), &mut read, &mut bound);
        }
    }
    read.difference(&bound).cloned().collect()
}

/// Every variable a term of `rule` holds, its aliases, local binders and frame bindings among
/// them.
fn held_variables(rule: &SemanticRule) -> BTreeSet<SemanticId> {
    let mut held = BTreeSet::new();
    let _ = rule.try_map_terms(&mut |term| {
        collect_held(term, &mut held);
        Ok::<_, std::convert::Infallible>(term.clone())
    });
    if let RuleBodyRef::Configuration { body, .. } = rule.relational_body() {
        for clause in body.fixed_clauses() {
            if let Some(binding) = clause.frame().binding() {
                held.insert(binding.clone());
            }
        }
    }
    held
}

/// The variables `rule` declares outside its terms: fresh names, existentials, declared unbound
/// names, and every binder of a clause the check does not read.
fn held_variables_outside_terms(rule: &SemanticRule) -> BTreeSet<SemanticId> {
    let mut held = BTreeSet::new();
    for binder in rule.fresh().iter().chain(rule.existentials()) {
        held.insert(binder.id().clone());
    }
    if let Some(unbound) = rule.unbound_variables() {
        held.extend(
            unbound
                .variables()
                .iter()
                .filter_map(|variable| variable.id().cloned()),
        );
    }
    if let RuleBodyRef::Configuration { body, .. } = rule.relational_body() {
        for clause in body.clauses() {
            if !matches!(clause, ConfigurationClause::Fixed(_)) {
                held.extend(
                    rule.variables()
                        .iter()
                        .map(|variable| variable.id().clone()),
                );
            }
        }
    }
    held
}

fn collect_held(term: &SemanticTerm, held: &mut BTreeSet<SemanticId>) {
    match term.kind() {
        IrTermKind::Variable { variable } => {
            held.insert(variable.clone());
        }
        IrTermKind::As { alias, .. } => {
            held.insert(alias.clone());
        }
        IrTermKind::Matches { binds, .. } | IrTermKind::Let { binds, .. } => {
            held.extend(binds.iter().cloned());
        }
        _ => {}
    }
    for child in term.children() {
        collect_held(child, held);
    }
}

fn pattern_names(term: &SemanticTerm, bound: &mut BTreeSet<SemanticId>) {
    match term.kind() {
        IrTermKind::Variable { variable } => {
            bound.insert(variable.clone());
        }
        IrTermKind::As { alias, .. } => {
            bound.insert(alias.clone());
        }
        IrTermKind::Matches { binds, .. } | IrTermKind::Let { binds, .. } => {
            bound.extend(binds.iter().cloned());
        }
        _ => {}
    }
    for child in term.children() {
        pattern_names(child, bound);
    }
}

fn value_names(
    term: &SemanticTerm,
    read: &mut BTreeSet<SemanticId>,
    bound: &mut BTreeSet<SemanticId>,
) {
    match term.kind() {
        IrTermKind::Variable { variable } if variable.kind() != SemanticIdKind::Wildcard => {
            read.insert(variable.clone());
        }
        IrTermKind::Matches { pattern, binds, .. } | IrTermKind::Let { pattern, binds, .. } => {
            bound.extend(binds.iter().cloned());
            pattern_names(pattern, bound);
        }
        _ => {}
    }
    for child in term.children() {
        value_names(child, read, bound);
    }
}

/// Where a lifted term stands, which decides what authored syntax writes there.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Position {
    /// A pattern: constructors, names, literals, collection patterns, `@` and `|`.
    Pattern,
    /// The root of an equation's or simplification's left side: the function it defines.
    Head,
    /// A result or a condition: any expression.
    Value,
}

impl Position {
    const fn of_arguments(self) -> Self {
        match self {
            Self::Pattern | Self::Head => Self::Pattern,
            Self::Value => Self::Value,
        }
    }
}

/// The lift of one sentence's parts into the semantic IR.
struct Lift<'i> {
    index: &'i KLabelIndex,
    /// The origin a new node copies the stack of when no baseline node guides it.
    base: NodeOrigin,
    /// Each emitted variable name of the baseline sentence, with its identity.
    names: BTreeMap<String, SemanticId>,
    /// The declared sort of each variable of the sentence, new ones included.
    sorts: BTreeMap<SemanticId, SemanticSortRef>,
    new_variables: Vec<SemanticVariable>,
    fresh: usize,
    next_wildcard: usize,
}

fn cast_sort(label: &str) -> Option<&str> {
    label
        .strip_prefix("#SemanticCastTo")
        .or_else(|| label.strip_prefix("#SyntacticCastTo"))
}

fn wildcard_ordinal(id: &SemanticId) -> Option<usize> {
    if id.kind() != SemanticIdKind::Wildcard {
        return None;
    }
    id.as_str()
        .rsplit(|character: char| !character.is_ascii_digit())
        .next()
        .and_then(|digits| digits.parse().ok())
}

fn snake(name: &str) -> String {
    let mut output = String::new();
    for (index, character) in name.chars().enumerate() {
        if character.is_ascii_uppercase() {
            if index != 0 {
                output.push('_');
            }
            output.push(character.to_ascii_lowercase());
        } else {
            output.push(character);
        }
    }
    output
}

impl<'i> Lift<'i> {
    fn new(index: &'i KLabelIndex, site: &Site<'_>, rule: &SemanticRule) -> Self {
        let names = site
            .names
            .iter()
            .map(|(id, name)| (name.to_owned(), id.clone()))
            .collect();
        let sorts = rule
            .variables()
            .iter()
            .map(|variable| (variable.id().clone(), variable.sort().clone()))
            .collect::<BTreeMap<_, _>>();
        let next_wildcard = sorts
            .keys()
            .filter_map(wildcard_ordinal)
            .max()
            .map_or(0, |ordinal| ordinal + 1);
        Self {
            index,
            base: rule.origin().clone(),
            names,
            sorts,
            new_variables: Vec::new(),
            fresh: 0,
            next_wildcard,
        }
    }

    /// A new node's origin: `base`'s stack under a key of its own.
    fn fresh_origin(&mut self, base: &NodeOrigin) -> NodeOrigin {
        self.fresh += 1;
        let key = SourceMapKey::new(format!("{}~lift-{}", base.key().as_str(), self.fresh))
            .unwrap_or_else(|_| base.key().clone());
        NodeOrigin::new(key, base.origin().clone())
    }

    fn origin(&mut self, guide: Option<&SemanticTerm>, base: &NodeOrigin) -> NodeOrigin {
        guide.map_or_else(|| self.fresh_origin(base), |guide| guide.origin().clone())
    }

    fn sort(&self, name: &str) -> Result<SemanticSortRef, LiftRefusal> {
        self.index
            .sort(name)
            .cloned()
            .ok_or_else(|| LiftRefusal::UnknownSort(name.to_owned()))
    }

    /// The lift of a single-body sentence's term, guided by the baseline's `body`; with
    /// `head_fixed` (a function shorthand's equation, an equation table's row), the head must
    /// apply the baseline's function, since the sentence's source does not write it alone.
    fn term_body(
        &mut self,
        body: &IrRewrite<krs_ir_levels::SemanticLevel>,
        parsed: &Term,
        kind: krs_ir::SentenceKind,
        head_fixed: bool,
    ) -> Result<IrRewrite<krs_ir_levels::SemanticLevel>, Refusal> {
        let same_head = |lifted: &SemanticTerm, guide: &SemanticTerm| {
            !head_fixed
                || matches!(
                    (lifted.kind(), guide.kind()),
                    (
                        IrTermKind::Application { application: own, .. },
                        IrTermKind::Application { application: baseline, .. },
                    ) if own == baseline
                )
        };
        let moved = || {
            Refusal::Lift(LiftRefusal::NotAdmitted(
                "another function at the head of an equation whose head is written at its function's declaration or its table's header".into(),
            ))
        };
        let head = if matches!(
            kind,
            krs_ir::SentenceKind::Equation | krs_ir::SentenceKind::Simplification
        ) {
            Position::Head
        } else {
            Position::Pattern
        };
        match (parsed.unannotated(), body.local_term()) {
            (Term::Rewrite { left, right }, None) => {
                let from = self.term(left, Some(body.from()), head, Some(body.from().sort()))?;
                if !same_head(&from, body.from()) {
                    return Err(moved());
                }
                let to = self.term(
                    right,
                    Some(body.to()),
                    Position::Value,
                    Some(body.to().sort()),
                )?;
                Ok(IrRewrite::new(
                    body.origin().clone(),
                    body.sort().clone(),
                    from,
                    to,
                ))
            }
            (Term::Rewrite { .. }, Some(_)) | (_, None) => Err(Refusal::NotJudged(
                NotJudged::Skeleton("where the rule's rewrite stands".into()),
            )),
            (_, Some(local)) => {
                let term = self.term(parsed, Some(local), head, Some(local.sort()))?;
                if !same_head(&term, local) {
                    return Err(moved());
                }
                Ok(IrRewrite::local(term))
            }
        }
    }

    fn clause(
        &mut self,
        clause: &FixedCellClause<SemanticId, SemanticTerm>,
        item: &Term,
    ) -> Result<FixedCellClause<SemanticId, SemanticTerm>, Refusal> {
        let skeleton = |what: &str| Refusal::NotJudged(NotJudged::Skeleton(what.to_owned()));
        let guide_after = match clause.after() {
            CellPost::Replace { term } => Some(term),
            CellPost::Preserve | CellPost::Local => None,
        };
        if clause.kind() == CellClauseKind::Whole {
            let (before, after) = self.cell_content(item, clause.before(), guide_after, clause)?;
            return Ok(FixedCellClause::whole(
                clause.origin().clone(),
                clause.cell().clone(),
                before,
                after,
            ));
        }
        let Term::Apply { label, arguments } = item.unannotated() else {
            return Err(skeleton("the cells the rule mentions"));
        };
        let name = label
            .name
            .strip_prefix('<')
            .and_then(|name| name.strip_suffix('>'))
            .ok_or_else(|| skeleton("the cells the rule mentions"))?;
        if self.index.cell(name) != Some(clause.cell()) {
            return Err(skeleton("the cells the rule mentions"));
        }
        let [left, content, right] = arguments.as_slice() else {
            return Err(skeleton("a cell's frame"));
        };
        let dots = |term: &Term| match term.unannotated() {
            Term::Apply { label, .. } if label.name == "#dots" => Some(true),
            Term::Apply { label, .. } if label.name == "#noDots" => Some(false),
            _ => None,
        };
        if dots(left) != Some(false) {
            return Err(skeleton("a cell's frame"));
        }
        let open = dots(right).ok_or_else(|| skeleton("a cell's frame"))?;
        let frame_inserted = clause
            .frame()
            .origin()
            .is_some_and(|origin| origin.origin().inserted().is_some());
        // A frame renders ` ...` exactly when it binds nothing and is not exact.
        let dotted = matches!(
            clause.frame(),
            CellContentFrame::KSequenceTail { binding: None, .. }
                | CellContentFrame::MapRemainder { binding: None, .. }
                | CellContentFrame::ListRemainder { .. }
        );
        let frame = if dotted == open {
            clause.frame().clone()
        } else if dotted
            && !frame_inserted
            && !matches!(clause.frame(), CellContentFrame::ListRemainder { .. })
        {
            // A deleted frame the author wrote reads as a closed match; one KRS adds stays.
            CellContentFrame::Exact
        } else {
            return Err(skeleton("a cell's frame"));
        };
        let content = strip_named_frame(content, &frame, self)?;
        let (before, after) = self.cell_content(&content, clause.before(), guide_after, clause)?;
        Ok(FixedCellClause::new(
            clause.origin().clone(),
            clause.cell().clone(),
            before,
            after,
            frame,
        ))
    }

    fn cell_content(
        &mut self,
        content: &Term,
        guide_before: &SemanticTerm,
        guide_after: Option<&SemanticTerm>,
        clause: &FixedCellClause<SemanticId, SemanticTerm>,
    ) -> Result<(SemanticTerm, CellPost<SemanticTerm>), Refusal> {
        let local_guide = matches!(clause.after(), CellPost::Local);
        if let Term::Rewrite { left, right } = content.unannotated() {
            let before = self.term(
                left,
                (!local_guide).then_some(guide_before),
                Position::Pattern,
                Some(guide_before.sort()),
            )?;
            let after = self.term(
                right,
                guide_after,
                Position::Value,
                Some(guide_after.map_or(guide_before.sort(), SemanticTerm::sort)),
            )?;
            return Ok((before, CellPost::Replace { term: after }));
        }
        let guide = (local_guide || guide_after.is_none()).then_some(guide_before);
        let before = self.term(content, guide, Position::Pattern, Some(guide_before.sort()))?;
        let after = if before.contains_rewrite() {
            CellPost::Local
        } else {
            CellPost::Preserve
        };
        Ok((before, after))
    }

    fn variable(
        &mut self,
        name: &str,
        sort: &SemanticSortRef,
        guide: Option<&SemanticTerm>,
        position: Position,
        base: &NodeOrigin,
        generated_admitted: bool,
    ) -> Result<SemanticTerm, LiftRefusal> {
        if name == "_" {
            if position == Position::Value {
                return Err(LiftRefusal::NotAdmitted("`_` outside a pattern".into()));
            }
            if let Some(guide) = guide
                && let IrTermKind::Variable { variable } = guide.kind()
                && variable.kind() == SemanticIdKind::Wildcard
                && guide.sort() == sort
            {
                return Ok(guide.clone());
            }
            let id = SemanticId::wildcard(self.next_wildcard);
            self.next_wildcard += 1;
            self.sorts.insert(id.clone(), sort.clone());
            self.new_variables
                .push(SemanticVariable::new(id.clone(), sort.clone()));
            let origin = self.fresh_origin(base);
            return Ok(SemanticTerm::variable(origin, sort.clone(), id));
        }
        let id = if let Some(id) = self.names.get(name) {
            id.clone()
        } else {
            if position == Position::Value {
                return Err(LiftRefusal::Unbound(name.to_owned()));
            }
            let mut spelling = snake(name);
            while self.sorts.keys().any(|id| id.as_str() == spelling) {
                spelling.push('_');
            }
            let id = SemanticId::authored(spelling)
                .map_err(|_| LiftRefusal::Shape(format!("the name `{name}`")))?;
            self.names.insert(name.to_owned(), id.clone());
            self.sorts.insert(id.clone(), sort.clone());
            self.new_variables
                .push(SemanticVariable::new(id.clone(), sort.clone()));
            id
        };
        if self.sorts.get(&id) != Some(sort) {
            return Err(LiftRefusal::SortMismatch(name.to_owned()));
        }
        let guided = guide.is_some_and(
            |guide| matches!(guide.kind(), IrTermKind::Variable { variable } if *variable == id),
        );
        // A name KRS made for no token (a template's binder, a record update's field, a
        // lookup's name) stands only where KRS writes it: no Rust spelling reads it elsewhere.
        if id.is_generated_name() && !id.is_rest_name() && !guided && !generated_admitted {
            return Err(LiftRefusal::NotAdmitted(format!(
                "`{name}`, a name KRS made, where KRS does not write it"
            )));
        }
        let origin = match guide {
            Some(guide) if guided => guide.origin().clone(),
            _ => self.fresh_origin(base),
        };
        Ok(SemanticTerm::variable(origin, sort.clone(), id))
    }

    /// Lifts `term` at `position`, guided by the baseline's term `guide` at the same place:
    /// where the mutant has the guide's head, the lifted node keeps the guide's origin, and the
    /// guide resolves what the K text leaves open (which of two renderings a node is, an
    /// instance), otherwise the node is read on its own.
    #[expect(
        clippy::too_many_lines,
        reason = "One arm per K term form KRS renders."
    )]
    fn term(
        &mut self,
        term: &Term,
        guide: Option<&SemanticTerm>,
        position: Position,
        expected: Option<&SemanticSortRef>,
    ) -> Result<SemanticTerm, LiftRefusal> {
        let base = guide.map_or_else(|| self.base.clone(), |guide| guide.origin().clone());
        let base = &base;
        // A KSequence of one item renders as the item.
        if let Some(guide) = guide
            && let IrTermKind::KSequence { item_sort, items } = guide.kind()
            && !matches!(term.unannotated(), Term::Sequence(_))
            && items.len() == 1
        {
            let item = self.term(term, items.first(), position, Some(item_sort))?;
            return Ok(guide.with_kind(IrTermKind::KSequence {
                item_sort: item_sort.clone(),
                items: vec![item],
            }));
        }
        match term.unannotated() {
            Term::Apply { label, arguments } => {
                let name = label.name.as_str();
                if let Some(sort) = cast_sort(name) {
                    let sort = self.sort(sort)?;
                    let [operand] = arguments.as_slice() else {
                        return Err(LiftRefusal::Shape(format!("`{name}` of several operands")));
                    };
                    return match operand.unannotated() {
                        Term::Variable { name, .. } => {
                            self.variable(name, &sort, guide, position, base, false)
                        }
                        _ => Err(LiftRefusal::Shape("a sort cast of a term".into())),
                    };
                }
                if name == "#Or" {
                    if position == Position::Value {
                        return Err(LiftRefusal::NotAdmitted("`#Or` outside a pattern".into()));
                    }
                    let mut alternatives = Vec::new();
                    let mut pending = vec![term];
                    while let Some(next) = pending.pop() {
                        match next.unannotated() {
                            Term::Apply { label, arguments } if label.name == "#Or" => {
                                pending.extend(arguments.iter().rev());
                            }
                            _ => alternatives.push(next),
                        }
                    }
                    let guides = match guide.map(SemanticTerm::kind) {
                        Some(IrTermKind::Or {
                            alternatives: guides,
                        }) if guides.iter().count() == alternatives.len() => {
                            guides.iter().map(Some).collect::<Vec<_>>()
                        }
                        _ => vec![None; alternatives.len()],
                    };
                    let lifted = alternatives
                        .into_iter()
                        .zip(guides)
                        .map(|(alternative, guide)| {
                            self.term(alternative, guide, Position::Pattern, expected)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let sort = guide
                        .map(SemanticTerm::sort)
                        .or(expected)
                        .cloned()
                        .unwrap_or_else(|| lifted[0].sort().clone());
                    let alternatives = AtLeastTwo::try_from(lifted)
                        .map_err(|_| LiftRefusal::Shape("`#Or` of one alternative".into()))?;
                    let origin = self.origin(
                        guide.filter(|guide| matches!(guide.kind(), IrTermKind::Or { .. })),
                        base,
                    );
                    return Ok(SemanticTerm::pattern_or(origin, sort, alternatives));
                }
                if name == "_:=K_" {
                    let [pattern, subject] = arguments.as_slice() else {
                        return Err(LiftRefusal::Shape("`:=K`".into()));
                    };
                    if position != Position::Value {
                        return Err(LiftRefusal::NotAdmitted("`:=K` in a pattern".into()));
                    }
                    let (guide_subject, guide_pattern, binds) = match guide.map(SemanticTerm::kind)
                    {
                        Some(IrTermKind::Matches {
                            subject,
                            pattern,
                            binds,
                        }) => (
                            Some(subject.as_ref()),
                            Some(pattern.as_ref()),
                            Some(binds.clone()),
                        ),
                        _ => (None, None, None),
                    };
                    let subject = self.term(subject, guide_subject, Position::Value, None)?;
                    let pattern = self.term(
                        pattern,
                        guide_pattern,
                        Position::Pattern,
                        Some(subject.sort()),
                    )?;
                    let binds = binds.ok_or_else(|| LiftRefusal::Shape("a new `:=K`".into()))?;
                    let origin = self.origin(guide, base);
                    return Ok(SemanticTerm::matches(
                        origin,
                        SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bool),
                        subject,
                        pattern,
                        binds,
                    ));
                }
                if name == "#let" {
                    let [pattern, value, body] = arguments.as_slice() else {
                        return Err(LiftRefusal::Shape("`#let`".into()));
                    };
                    if position != Position::Value {
                        return Err(LiftRefusal::NotAdmitted("`#let` in a pattern".into()));
                    }
                    let Some(IrTermKind::Let {
                        pattern: guide_pattern,
                        value: guide_value,
                        body: guide_body,
                        binds,
                    }) = guide.map(SemanticTerm::kind)
                    else {
                        return Err(LiftRefusal::Shape("a new `#let`".into()));
                    };
                    let value = self.term(value, Some(guide_value), Position::Value, None)?;
                    let pattern = self.term(
                        pattern,
                        Some(guide_pattern),
                        Position::Pattern,
                        Some(value.sort()),
                    )?;
                    let body = self.term(body, Some(guide_body), Position::Value, expected)?;
                    let sort = body.sort().clone();
                    let origin = self.origin(guide, base);
                    return Ok(SemanticTerm::let_binding(
                        origin,
                        sort,
                        pattern,
                        value,
                        body,
                        binds.clone(),
                    ));
                }
                if name.starts_with('<') && name.ends_with('>') && name.len() > 2 {
                    return self.cell_term(term, guide, position);
                }
                if let Some(production) = self.index.production(name).cloned() {
                    if position == Position::Pattern && production.function {
                        return Err(LiftRefusal::NotAdmitted(format!(
                            "the function `{name}` in a pattern"
                        )));
                    }
                    if arguments.len() != production.arguments.len() + production.keys {
                        return Err(LiftRefusal::Shape(format!(
                            "`{name}` of {} operands",
                            arguments.len()
                        )));
                    }
                    // A function evaluated in one instance receives the instance's keys after
                    // its own arguments, which KRS passes: they are not lifted.
                    let arguments = &arguments[..production.arguments.len()];
                    let same = guide.and_then(|guide| match guide.kind() {
                        IrTermKind::Application {
                            application: ApplicationRef::Declared(id),
                            arguments,
                            instance,
                            head_instance_fixed,
                        } if *id == production.id
                            && arguments.len() == production.arguments.len() =>
                        {
                            Some((guide, arguments, instance, *head_instance_fixed))
                        }
                        _ => None,
                    });
                    if production.parametric && same.is_none() {
                        return Err(LiftRefusal::Shape(format!(
                            "a new application of the parametric `{name}`"
                        )));
                    }
                    let lifted = arguments
                        .iter()
                        .enumerate()
                        .map(|(index, argument)| {
                            self.term(
                                argument,
                                same.map(|(_, arguments, _, _)| &arguments[index]),
                                position.of_arguments(),
                                Some(&production.arguments[index]),
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    if let Some((guide, _, instance, fixed)) = same {
                        return Ok(SemanticTerm::parametric_application(
                            guide.origin().clone(),
                            guide.sort().clone(),
                            ApplicationRef::Declared(production.id.clone()),
                            lifted,
                            instance.clone(),
                            fixed,
                        ));
                    }
                    let origin = self.fresh_origin(base);
                    return Ok(SemanticTerm::application(
                        origin,
                        production.result.clone(),
                        ApplicationRef::Declared(production.id.clone()),
                        lifted,
                    ));
                }
                if let Some(lifted) =
                    self.collection(term, name, arguments, guide, position, expected, base)?
                {
                    return Ok(lifted);
                }
                if let Some(sort) = name
                    .strip_prefix("is")
                    .and_then(|sort| self.index.sort(sort))
                    .cloned()
                    && arguments.len() == 1
                {
                    return self.generated(
                        GeneratedOperation::SortPredicate(sort),
                        &arguments[0],
                        guide,
                        position,
                        base,
                    );
                }
                if let Some(sort) = name
                    .strip_prefix("project:")
                    .and_then(|sort| self.index.sort(sort))
                    .cloned()
                    && arguments.len() == 1
                {
                    // A projected collection lookup renders its own projection.
                    let generated_guide = guide.is_some_and(|guide| {
                        matches!(
                            guide.kind(),
                            IrTermKind::Application {
                                application: ApplicationRef::Generated(_),
                                ..
                            }
                        )
                    });
                    if !generated_guide
                        && let Term::Apply {
                            label,
                            arguments: inner,
                        } = arguments[0].unannotated()
                        && let Some(lifted) = self.collection(
                            &arguments[0],
                            &label.name,
                            inner,
                            guide,
                            position,
                            Some(&sort),
                            base,
                        )?
                        && collection_projected(&lifted)
                    {
                        return Ok(lifted);
                    }
                    return self.generated(
                        GeneratedOperation::SortProjection(sort),
                        &arguments[0],
                        guide,
                        position,
                        base,
                    );
                }
                if let Some(operation) = BuiltinOperation::ALL.into_iter().find(|operation| {
                    operation.spec().k_label == name
                        && operation.spec().argument_sorts.len() == arguments.len()
                }) {
                    if position != Position::Value {
                        return Err(LiftRefusal::NotAdmitted(format!(
                            "the operation `{name}` in a pattern"
                        )));
                    }
                    let spec = operation.spec();
                    let same = guide.and_then(|guide| match guide.kind() {
                        IrTermKind::Application {
                            application: ApplicationRef::Builtin(own),
                            arguments,
                            ..
                        } if *own == operation && arguments.len() == spec.argument_sorts.len() => {
                            Some((guide, arguments))
                        }
                        _ => None,
                    });
                    let mut lifted = Vec::with_capacity(arguments.len());
                    for (index, argument) in arguments.iter().enumerate() {
                        let expected = match spec.argument_sorts[index] {
                            OperationSort::Builtin(sort) => Some(SemanticSortRef::Builtin(sort)),
                            OperationSort::K | OperationSort::Parameter => None,
                        };
                        lifted.push(self.term(
                            argument,
                            same.map(|(_, arguments)| &arguments[index]),
                            Position::Value,
                            expected.as_ref(),
                        )?);
                    }
                    let sort = match spec.result_sort {
                        OperationSort::Builtin(sort) => SemanticSortRef::Builtin(sort),
                        OperationSort::K => same.map_or(
                            SemanticSortRef::Builtin(krs_ir::BuiltinSort::KSequence),
                            |(guide, _)| guide.sort().clone(),
                        ),
                        OperationSort::Parameter => match same {
                            Some((guide, _)) => guide.sort().clone(),
                            None => spec
                                .argument_sorts
                                .iter()
                                .position(|sort| *sort == OperationSort::Parameter)
                                .map(|index| lifted[index].sort().clone())
                                .ok_or_else(|| LiftRefusal::Shape(format!("`{name}`")))?,
                        },
                    };
                    let origin = match same {
                        Some((guide, _)) => guide.origin().clone(),
                        None => self.fresh_origin(base),
                    };
                    return Ok(SemanticTerm::application(
                        origin,
                        sort,
                        ApplicationRef::Builtin(operation),
                        lifted,
                    ));
                }
                Err(LiftRefusal::UnknownLabel(name.to_owned()))
            }
            Term::Variable { name, .. } => {
                let sort = guide
                    .map(SemanticTerm::sort)
                    .or(expected)
                    .cloned()
                    .ok_or_else(|| LiftRefusal::Shape(format!("`{name}` with no sort")))?;
                self.variable(name, &sort, guide, position, base, false)
            }
            Term::Token { token, sort } => {
                let sort = self.sort(&sort.name)?;
                if let Some(guide) = guide
                    && let IrTermKind::Token { value } = guide.kind()
                    && guide.sort() == &sort
                    && (value == token
                        || krs_ir::bytes_token::decode(value).is_ok_and(|bytes| {
                            krs_ir::bytes_token::program_spelling(&bytes) == *token
                        }))
                {
                    return Ok(guide.clone());
                }
                if sort == SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bytes) {
                    return Err(LiftRefusal::Shape("a new Bytes token".into()));
                }
                let origin = self.fresh_origin(base);
                SemanticTerm::token(origin, sort, token.clone())
                    .map_err(|error| LiftRefusal::Shape(error.to_string()))
            }
            Term::Rewrite { left, right } => {
                if position == Position::Value {
                    return Err(LiftRefusal::NotAdmitted("a rewrite in a result".into()));
                }
                let (guide_from, guide_to) = match guide.map(SemanticTerm::kind) {
                    Some(IrTermKind::Rewrite { from, to }) => {
                        (Some(from.as_ref()), Some(to.as_ref()))
                    }
                    _ => (None, None),
                };
                let from = self.term(left, guide_from, Position::Pattern, expected)?;
                let to = self.term(right, guide_to, Position::Value, Some(from.sort()))?;
                let sort = guide.map_or_else(|| from.sort().clone(), |guide| guide.sort().clone());
                let origin = self.origin(guide_from.and(guide), base);
                SemanticTerm::rewrite(origin, sort, from, to)
                    .map_err(|error| LiftRefusal::Shape(error.to_string()))
            }
            Term::As { pattern, alias } => {
                if position == Position::Value {
                    return Err(LiftRefusal::NotAdmitted("`#as` outside a pattern".into()));
                }
                let (guide_pattern, guide_alias) = match guide.map(SemanticTerm::kind) {
                    Some(IrTermKind::As { alias, pattern }) => {
                        (Some(pattern.as_ref()), Some(alias))
                    }
                    _ => (None, None),
                };
                let Term::Apply { label, arguments } = alias.unannotated() else {
                    return Err(LiftRefusal::Shape("`#as` of a term".into()));
                };
                let (Some(sort), [variable]) = (cast_sort(&label.name), arguments.as_slice())
                else {
                    return Err(LiftRefusal::Shape("`#as` of a term".into()));
                };
                let sort = self.sort(sort)?;
                let Term::Variable { name, .. } = variable.unannotated() else {
                    return Err(LiftRefusal::Shape("`#as` of a term".into()));
                };
                let generated_admitted =
                    guide_alias.is_some_and(|own| self.names.get(name.as_str()) == Some(own));
                let alias = self.variable(
                    name,
                    &sort,
                    None,
                    Position::Pattern,
                    base,
                    generated_admitted,
                )?;
                let IrTermKind::Variable { variable: alias } = alias.kind() else {
                    return Err(LiftRefusal::Shape("`#as`".into()));
                };
                let lifted = self.term(pattern, guide_pattern, Position::Pattern, Some(&sort))?;
                // An alias names the whole match, so it does not occur inside its own subpattern.
                let mut inner = BTreeSet::new();
                collect_held(&lifted, &mut inner);
                if inner.contains(alias) {
                    return Err(LiftRefusal::NotAdmitted(format!(
                        "`{name}` bound inside its own alias"
                    )));
                }
                let origin = match guide_alias {
                    Some(own) if own == alias => self.origin(guide, base),
                    _ => self.fresh_origin(base),
                };
                Ok(SemanticTerm::pattern_as(
                    origin,
                    sort,
                    alias.clone(),
                    lifted,
                ))
            }
            Term::Sequence(items) => {
                let (guide_items, item_sort) = match guide.map(SemanticTerm::kind) {
                    Some(IrTermKind::KSequence { item_sort, items }) => {
                        (Some(items), Some(item_sort.clone()))
                    }
                    _ => (None, None),
                };
                let lifted = items
                    .iter()
                    .enumerate()
                    .map(|(index, item)| {
                        let guide = guide_items
                            .filter(|guides| guides.len() == items.len())
                            .map(|guides| &guides[index]);
                        self.term(item, guide, position, None)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let k = SemanticSortRef::Builtin(krs_ir::BuiltinSort::KSequence);
                let item_sort = item_sort.unwrap_or_else(|| {
                    if lifted.iter().any(|item| *item.sort() == k) {
                        k.clone()
                    } else {
                        self.index
                            .sort("KItem")
                            .cloned()
                            .unwrap_or_else(|| k.clone())
                    }
                });
                Ok(match guide {
                    Some(guide) if guide_items.is_some() => {
                        guide.with_kind(IrTermKind::KSequence {
                            item_sort,
                            items: lifted,
                        })
                    }
                    _ => {
                        let origin = self.fresh_origin(base);
                        SemanticTerm::variable(origin, k, SemanticId::wildcard(0)).with_kind(
                            IrTermKind::KSequence {
                                item_sort,
                                items: lifted,
                            },
                        )
                    }
                })
            }
            Term::InjectedLabel(_) | Term::Annotated { .. } => {
                Err(LiftRefusal::Shape("an injected label".into()))
            }
        }
    }

    fn generated(
        &mut self,
        operation: GeneratedOperation<SemanticSortRef>,
        operand: &Term,
        guide: Option<&SemanticTerm>,
        position: Position,
        base: &NodeOrigin,
    ) -> Result<SemanticTerm, LiftRefusal> {
        if position != Position::Value {
            return Err(LiftRefusal::NotAdmitted(
                "a sort test or projection in a pattern".into(),
            ));
        }
        let same = guide.and_then(|guide| match guide.kind() {
            IrTermKind::Application {
                application: ApplicationRef::Generated(own),
                arguments,
                ..
            } if *own == operation && arguments.len() == 1 => Some((guide, &arguments[0])),
            _ => None,
        });
        // The operand of a sort operation renders a projected lookup without its projection.
        let lifted = match operand.unannotated() {
            Term::Apply { label, arguments } => {
                let guide_operand = same.map(|(_, operand)| operand);
                let expected = guide_operand
                    .map(SemanticTerm::sort)
                    .cloned()
                    .or_else(|| self.index.sort("KItem").cloned());
                match self.collection(
                    operand,
                    &label.name,
                    arguments,
                    guide_operand,
                    Position::Value,
                    expected.as_ref(),
                    base,
                )? {
                    Some(lifted) => lifted,
                    None => self.term(operand, guide_operand, Position::Value, None)?,
                }
            }
            _ => self.term(
                operand,
                same.map(|(_, operand)| operand),
                Position::Value,
                None,
            )?,
        };
        let sort = match &operation {
            GeneratedOperation::SortPredicate(_) => {
                SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bool)
            }
            GeneratedOperation::SortProjection(sort) => sort.clone(),
        };
        let origin = match same {
            Some((guide, _)) => guide.origin().clone(),
            None => self.fresh_origin(base),
        };
        Ok(SemanticTerm::application(
            origin,
            sort,
            ApplicationRef::Generated(operation),
            vec![lifted],
        ))
    }

    /// The lift of `term` as a collection operation, when its label is one; `expected` is the
    /// sort a projected lookup reads at.
    #[expect(
        clippy::too_many_arguments,
        reason = "The lift's context and the term's."
    )]
    #[expect(
        clippy::too_many_lines,
        reason = "One arm per collection operation family."
    )]
    fn collection(
        &mut self,
        term: &Term,
        name: &str,
        arguments: &[Term],
        guide: Option<&SemanticTerm>,
        position: Position,
        expected: Option<&SemanticSortRef>,
        base: &NodeOrigin,
    ) -> Result<Option<SemanticTerm>, LiftRefusal> {
        let structural = |label: &str| {
            [
                MapOperation::Item.spec().k_label,
                MapOperation::Empty.spec().k_label,
                MapOperation::CONCATENATION.k_label,
            ]
            .contains(&label)
                || [
                    ListOperation::Item.spec().k_label,
                    ListOperation::Empty.spec().k_label,
                    ListOperation::Concat.spec().k_label,
                ]
                .contains(&label)
                || [
                    SetOperation::Item.spec().k_label,
                    SetOperation::Empty.spec().k_label,
                    SetOperation::Concat.spec().k_label,
                ]
                .contains(&label)
        };
        let is_collection = MapOperation::ALL
            .iter()
            .any(|operation| operation.spec().k_label == name)
            || name == MapOperation::CONCATENATION.k_label
            || ListOperation::ALL
                .iter()
                .any(|operation| operation.spec().k_label == name)
            || SetOperation::ALL
                .iter()
                .any(|operation| operation.spec().k_label == name);
        if !is_collection {
            return Ok(None);
        }
        if position != Position::Value && !structural(name) {
            return Err(LiftRefusal::NotAdmitted(format!(
                "the operation `{name}` in a pattern"
            )));
        }
        let guide_operands = |guide: Option<&SemanticTerm>| -> Option<Vec<SemanticTerm>> {
            match guide?.kind() {
                IrTermKind::Map(operands) => Some(operands.operands().cloned().collect()),
                IrTermKind::List(operands) => Some(operands.operands().cloned().collect()),
                IrTermKind::Set(operands) => Some(operands.operands().cloned().collect()),
                _ => None,
            }
        };
        // Maps: items and their concatenation flatten into one item list.
        if name == MapOperation::Item.spec().k_label || name == MapOperation::CONCATENATION.k_label
        {
            let mut leaves = Vec::new();
            let mut pending = vec![term];
            while let Some(next) = pending.pop() {
                match next.unannotated() {
                    Term::Apply { label, arguments }
                        if label.name == MapOperation::CONCATENATION.k_label =>
                    {
                        pending.extend(arguments.iter().rev());
                    }
                    Term::Apply { label, arguments }
                        if label.name == MapOperation::Item.spec().k_label
                            && arguments.len() == 2 =>
                    {
                        leaves.push((&arguments[0], &arguments[1]));
                    }
                    _ => {
                        return Err(LiftRefusal::Shape(
                            "a map joined with a term other than an item".into(),
                        ));
                    }
                }
            }
            let guides = match guide.map(SemanticTerm::kind) {
                Some(IrTermKind::Map(operands)) if matches!(operands.as_ref(), MapOperands::Items(entries) if entries.iter().count() == leaves.len()) => {
                    guide_operands(guide)
                }
                _ => None,
            };
            let mut entries = Vec::new();
            for (index, (key, value)) in leaves.into_iter().enumerate() {
                let key = self.term(
                    key,
                    guides.as_ref().map(|guides| &guides[2 * index]),
                    position,
                    None,
                )?;
                let value = self.term(
                    value,
                    guides.as_ref().map(|guides| &guides[2 * index + 1]),
                    position,
                    None,
                )?;
                entries.push(MapEntry { key, value });
            }
            let operands = MapOperands::items(entries)
                .map_err(|error| LiftRefusal::Shape(error.to_string()))?;
            let origin = if guides.is_some() {
                self.origin(guide, base)
            } else {
                self.fresh_origin(base)
            };
            let sort = guide.filter(|_| guides.is_some()).map_or(
                SemanticSortRef::Builtin(krs_ir::BuiltinSort::Map),
                |guide| guide.sort().clone(),
            );
            return Ok(Some(SemanticTerm::typed_map(origin, sort, operands)));
        }
        // Associative concatenations of lists and sets follow the guide's nesting, else nest to
        // the right.
        for (concat, sort) in [
            (
                ListOperation::Concat.spec().k_label,
                krs_ir::BuiltinSort::List,
            ),
            (
                SetOperation::Concat.spec().k_label,
                krs_ir::BuiltinSort::Set,
            ),
        ] {
            if name != concat {
                continue;
            }
            let mut leaves = Vec::new();
            let mut pending = vec![term];
            while let Some(next) = pending.pop() {
                match next.unannotated() {
                    Term::Apply { label, arguments } if label.name == concat => {
                        pending.extend(arguments.iter().rev());
                    }
                    _ => leaves.push(next),
                }
            }
            let mut guide_leaves = Vec::new();
            if let Some(guide) = guide {
                flatten_concat(guide, &mut guide_leaves);
            }
            let shaped = guide.filter(|_| guide_leaves.len() == leaves.len());
            let lifted = leaves
                .into_iter()
                .enumerate()
                .map(|(index, leaf)| {
                    self.term(
                        leaf,
                        shaped.map(|_| guide_leaves[index]),
                        position,
                        Some(&SemanticSortRef::Builtin(sort)),
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let mut lifted = lifted.into_iter();
            if let Some(guide) = shaped {
                return Ok(Some(rebuild_concat(guide, &mut lifted)?));
            }
            let items = lifted.collect::<Vec<_>>();
            let mut items = items.into_iter().rev();
            let mut joined = items
                .next()
                .ok_or_else(|| LiftRefusal::Shape("an empty concatenation".into()))?;
            for left in items {
                let origin = self.fresh_origin(base);
                joined = if sort == krs_ir::BuiltinSort::List {
                    SemanticTerm::list(
                        origin,
                        SemanticSortRef::Builtin(sort),
                        ListOperands::Concat {
                            left,
                            right: joined,
                        },
                    )
                } else {
                    SemanticTerm::set(
                        origin,
                        SemanticSortRef::Builtin(sort),
                        SetOperands::from_operands(SetOperation::Concat, vec![left, joined])
                            .map_err(|error| LiftRefusal::Shape(error.to_string()))?,
                    )
                };
            }
            return Ok(Some(joined));
        }
        let guide_args = guide_operands(guide);
        let lift_operands =
            |this: &mut Self, count: usize| -> Result<Vec<SemanticTerm>, LiftRefusal> {
                arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let guide = guide_args
                            .as_ref()
                            .filter(|guides| guides.len() == count)
                            .map(|guides| &guides[index]);
                        this.term(argument, guide, position, None)
                    })
                    .collect()
            };
        let result = |spec: &krs_ir::CollectionOperationSpec, fallback: krs_ir::BuiltinSort| {
            match spec.result_sort {
                CollectionResultSort::Builtin(sort) => Some(SemanticSortRef::Builtin(sort)),
                CollectionResultSort::Projected => None,
            }
            .unwrap_or(SemanticSortRef::Builtin(fallback))
        };
        if let Some(operation) = MapOperation::ALL
            .into_iter()
            .find(|operation| operation.spec().k_label == name)
        {
            let operands = lift_operands(self, arguments.len())?;
            let operands = MapOperands::from_operands(operation, operands)
                .map_err(|error| LiftRefusal::Shape(error.to_string()))?;
            let same = guide.filter(|guide| matches!(guide.kind(), IrTermKind::Map(own) if own.operation() == operation));
            let sort = projected_sort(operation.spec(), same, expected, self.index)
                .unwrap_or_else(|| result(operation.spec(), krs_ir::BuiltinSort::Map));
            let origin = self.origin(same, base);
            return Ok(Some(SemanticTerm::typed_map(origin, sort, operands)));
        }
        if let Some(operation) = ListOperation::ALL
            .into_iter()
            .find(|operation| operation.spec().k_label == name)
        {
            let operands = lift_operands(self, arguments.len())?;
            let operands = ListOperands::from_operands(operation, operands)
                .map_err(|error| LiftRefusal::Shape(error.to_string()))?;
            let same = guide.filter(|guide| matches!(guide.kind(), IrTermKind::List(own) if own.operation() == operation));
            let sort = projected_sort(operation.spec(), same, expected, self.index)
                .unwrap_or_else(|| result(operation.spec(), krs_ir::BuiltinSort::List));
            let origin = self.origin(same, base);
            return Ok(Some(SemanticTerm::list(origin, sort, operands)));
        }
        if let Some(operation) = SetOperation::ALL
            .into_iter()
            .find(|operation| operation.spec().k_label == name)
        {
            let operands = lift_operands(self, arguments.len())?;
            let operands = SetOperands::from_operands(operation, operands)
                .map_err(|error| LiftRefusal::Shape(error.to_string()))?;
            let same = guide.filter(|guide| matches!(guide.kind(), IrTermKind::Set(own) if own.operation() == operation));
            let sort = projected_sort(operation.spec(), same, expected, self.index)
                .unwrap_or_else(|| result(operation.spec(), krs_ir::BuiltinSort::Set));
            let origin = self.origin(same, base);
            return Ok(Some(SemanticTerm::set(origin, sort, operands)));
        }
        Ok(None)
    }

    /// A cell written inside a term (a group cell's term): `<c> children </c>`.
    fn cell_term(
        &mut self,
        term: &Term,
        guide: Option<&SemanticTerm>,
        position: Position,
    ) -> Result<SemanticTerm, LiftRefusal> {
        let Term::Apply { label, arguments } = term.unannotated() else {
            return Err(LiftRefusal::Shape("a cell".into()));
        };
        let name = &label.name[1..label.name.len() - 1];
        let cell = self
            .index
            .cell(name)
            .cloned()
            .ok_or_else(|| LiftRefusal::UnknownCell(name.to_owned()))?;
        let Some((guide, guides)) = guide.and_then(|guide| match guide.kind() {
            IrTermKind::Cell {
                cell: own,
                children,
            } if *own == cell => Some((guide, children)),
            _ => None,
        }) else {
            return Err(LiftRefusal::Shape(format!("a new cell term `<{name}>`")));
        };
        let [left, content, right] = arguments.as_slice() else {
            return Err(LiftRefusal::Shape(format!("the cell `<{name}>`")));
        };
        let closed = |term: &Term| matches!(term.unannotated(), Term::Apply { label, .. } if label.name == "#noDots");
        if !closed(left) || !closed(right) {
            return Err(LiftRefusal::Shape(format!(
                "a frame of the cell `<{name}>` in a term"
            )));
        }
        let children = cell_items(content);
        let children = if guides.len() == 1 && children.len() == 1 {
            vec![self.term(
                children[0],
                Some(&guides[0]),
                position,
                Some(guides[0].sort()),
            )?]
        } else if guides.len() == children.len() {
            children
                .into_iter()
                .zip(guides)
                .map(|(child, guide)| self.term(child, Some(guide), position, Some(guide.sort())))
                .collect::<Result<Vec<_>, _>>()?
        } else {
            return Err(LiftRefusal::Shape(format!("the children of `<{name}>`")));
        };
        Ok(guide.with_kind(IrTermKind::Cell { cell, children }))
    }
}

/// `leaves` joined in the shape of the concatenation `guide`.
fn rebuild_concat(
    guide: &SemanticTerm,
    leaves: &mut impl Iterator<Item = SemanticTerm>,
) -> Result<SemanticTerm, LiftRefusal> {
    match guide.kind() {
        IrTermKind::List(operands)
            if let ListOperands::Concat { left, right } = operands.as_ref() =>
        {
            let left = rebuild_concat(left, leaves)?;
            let right = rebuild_concat(right, leaves)?;
            Ok(
                guide.with_kind(IrTermKind::List(Box::new(ListOperands::Concat {
                    left,
                    right,
                }))),
            )
        }
        IrTermKind::Set(operands) if operands.operation() == SetOperation::Concat => {
            let guides = operands.operands().collect::<Vec<_>>();
            let [left, right] = guides.as_slice() else {
                return Err(LiftRefusal::Shape("a set concatenation".into()));
            };
            let left = rebuild_concat(left, leaves)?;
            let right = rebuild_concat(right, leaves)?;
            Ok(guide.with_kind(IrTermKind::Set(Box::new(
                SetOperands::from_operands(SetOperation::Concat, vec![left, right])
                    .map_err(|error| LiftRefusal::Shape(error.to_string()))?,
            ))))
        }
        _ => leaves
            .next()
            .ok_or_else(|| LiftRefusal::Shape("a concatenation".into())),
    }
}

/// The leaves of a list or set concatenation tree.
fn flatten_concat<'t>(term: &'t SemanticTerm, leaves: &mut Vec<&'t SemanticTerm>) {
    match term.kind() {
        IrTermKind::List(operands) if matches!(operands.as_ref(), ListOperands::Concat { .. }) => {
            for operand in operands.operands() {
                flatten_concat(operand, leaves);
            }
        }
        IrTermKind::Set(operands) if operands.operation() == SetOperation::Concat => {
            for operand in operands.operands() {
                flatten_concat(operand, leaves);
            }
        }
        _ => leaves.push(term),
    }
}

/// The sort of a projected collection lookup: the guide's, else the one it is read at, else
/// `KItem`, at which its projection is the identity.
fn projected_sort(
    spec: &krs_ir::CollectionOperationSpec,
    same: Option<&SemanticTerm>,
    expected: Option<&SemanticSortRef>,
    index: &KLabelIndex,
) -> Option<SemanticSortRef> {
    if !spec.is_projected() {
        return None;
    }
    same.map(SemanticTerm::sort)
        .or(expected)
        .cloned()
        .or_else(|| index.sort("KItem").cloned())
}

/// Whether `term` is a collection operation whose result is projected.
fn collection_projected(term: &SemanticTerm) -> bool {
    match term.kind() {
        IrTermKind::Map(operands) => operands.operation().spec().is_projected(),
        IrTermKind::List(operands) => operands.operation().spec().is_projected(),
        IrTermKind::Set(operands) => operands.operation().spec().is_projected(),
        _ => false,
    }
}

/// A cell's content with the named frame KRS writes beside it removed: ` ~> Rest:K` after a
/// K sequence, ` Rest:Map` after map items, on both sides of a rewrite (on the left only for a
/// moved remainder).
fn strip_named_frame(
    content: &Term,
    frame: &CellContentFrame,
    lift: &Lift<'_>,
) -> Result<Term, Refusal> {
    let skeleton = || Refusal::NotJudged(NotJudged::Skeleton("a cell's named frame".into()));
    let (binding, separator) = match frame {
        CellContentFrame::KSequenceTail {
            binding: Some(binding),
            ..
        } => (binding, None),
        CellContentFrame::MapRemainder {
            binding: Some(binding),
            ..
        }
        | CellContentFrame::MovedMapRemainder { binding, .. } => {
            (binding, Some(MapOperation::CONCATENATION.k_label))
        }
        _ => return Ok(content.clone()),
    };
    let named = |term: &Term| match term.unannotated() {
        Term::Apply { label, arguments } if cast_sort(&label.name).is_some() => matches!(
            arguments.as_slice(),
            [variable] if matches!(variable.unannotated(), Term::Variable { name, .. } if lift.names.get(name) == Some(binding))
        ),
        _ => false,
    };
    let strip = |term: &Term| -> Result<Term, Refusal> {
        match (term.unannotated(), separator) {
            (Term::Sequence(items), None) if items.last().is_some_and(named) => {
                let mut items = items.clone();
                items.pop();
                Ok(if items.len() == 1 {
                    items.remove(0)
                } else {
                    Term::Sequence(items)
                })
            }
            (Term::Apply { label, arguments }, Some(concat))
                if label.name == concat && arguments.len() == 2 && named(&arguments[1]) =>
            {
                Ok(arguments[0].clone())
            }
            _ => Err(skeleton()),
        }
    };
    match content.unannotated() {
        Term::Rewrite { left, right } => {
            let stripped_left = strip(left)?;
            let stripped_right = if matches!(frame, CellContentFrame::MovedMapRemainder { .. }) {
                right.as_ref().clone()
            } else {
                strip(right)?
            };
            Ok(Term::Rewrite {
                left: Box::new(stripped_left),
                right: Box::new(stripped_right),
            })
        }
        _ => strip(content),
    }
}

trait OriginKey {
    fn origin_key(&self) -> &SourceMapKey;
}

impl<C, T> OriginKey for ConfigurationClause<C, T> {
    fn origin_key(&self) -> &SourceMapKey {
        match self {
            Self::Fixed(clause) => clause.origin().key(),
            Self::Optional(clause) => clause.origin().key(),
            Self::Instances(clause) => clause.origin().key(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn edit(start: usize, end: usize, replacement: &str) -> Trimmed {
        Trimmed {
            start,
            end,
            replacement: replacement.to_owned(),
        }
    }

    #[test]
    fn an_edit_is_trimmed_to_the_bytes_it_changes() {
        let source = "a ( B:Int ) >Int 1";
        let edits = [KEdit::new(2..11, "( B:Int +Int 1 )")];
        let trimmed = trimmed(source, &edits);
        assert_eq!(trimmed.len(), 1);
        assert_eq!((trimmed[0].start, trimmed[0].end), (10, 10));
        assert_eq!(trimmed[0].replacement, "+Int 1 ");
        // An edit that changes nothing contributes nothing.
        assert!(super::trimmed(source, &[KEdit::new(0..1, "a")]).is_empty());
    }

    #[test]
    fn a_position_maps_through_the_edits_before_it() {
        // `0123456789`: bytes 2..4 become `xyz`, and `!` is inserted at 6.
        let edits = [edit(2, 4, "xyz"), edit(6, 6, "!")];
        assert_eq!(image(&edits, 1, Side::Left), Some(1));
        assert_eq!(image(&edits, 2, Side::Left), Some(2));
        assert_eq!(image(&edits, 3, Side::Left), None);
        assert_eq!(image(&edits, 4, Side::Left), Some(5));
        assert_eq!(image(&edits, 6, Side::Left), Some(7));
        assert_eq!(image(&edits, 6, Side::Right), Some(8));
        assert_eq!(image_range(&edits, &(4..6)), Some(5..8));
    }

    #[test]
    fn a_sentence_splits_into_its_contents_and_attributes() {
        let configuration = "  rule [div]:\n    <k> div A:Int => .K ... </k>\n    requires A:Int >Int 0\n    [priority(40)]\n";
        let split = split_sentence(configuration).unwrap();
        assert_eq!(
            configuration[split.contents.clone()].trim(),
            "<k> div A:Int => .K ... </k>\n    requires A:Int >Int 0"
        );
        assert_eq!(
            split.attributes,
            [("priority".to_owned(), Some("40".to_owned()))]
        );
        let term = "  rule plus ( zero , N:Nat ) => N:Nat [label(nat--plus_zero), owise]\n";
        let split = split_sentence(term).unwrap();
        assert_eq!(
            term[split.contents.clone()].trim(),
            "plus ( zero , N:Nat ) => N:Nat"
        );
        assert_eq!(split.attributes, [("owise".to_owned(), None)]);
        // A map lookup at the end is contents, not attributes.
        let lookup = "  rule f ( M:Map ) => M:Map [ 1 ] [label(f)]\n";
        let split = split_sentence(lookup).unwrap();
        assert_eq!(
            lookup[split.contents.clone()].trim(),
            "f ( M:Map ) => M:Map [ 1 ]"
        );
        assert!(split.attributes.is_empty());
    }

    #[test]
    fn a_test_and_its_join_are_replaced_by_the_conjunct_it_guards() {
        let text = "T1 andThenBool (T2 andThenBool (R))";
        // The outer join holds the inner one in its guarded conjunct.
        let joins = [(0..35, 16..34), (16..34, 32..33)];
        assert_eq!(strip_in(text, 0..text.len(), &joins), "R");
    }
}
