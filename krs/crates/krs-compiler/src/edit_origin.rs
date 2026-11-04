//! The generated-only edit judge: which emitted nodes a K edit of a definition KRS emitted
//! changes, and whether the author wrote them.
//!
//! A K mutation of a KRS definition must be a definition some KRS source emits, since a
//! survivor of any other mutant names a misunderstanding no author can write.
//! The judge is the first of two stages that decide this, and it reads only the emitted text,
//! its source map and the edits.
//! It refuses a sentence in which every node the mutation can change is one KRS inserted (a
//! definedness test, a lookup guard, a name KRS made, a frame the language adds, a local
//! function's scaffolding): the authored content of that sentence is then the baseline's, KRS
//! derives the baseline's nodes from it, and the mutant differs from them.
//! It also refuses what it cannot hand to the second stage: a mutation whose tokens are the
//! baseline's, a change of tokens outside every sentence, an edit of a declaration, an edit
//! that cuts through an inserted node, and an edit that reaches a lookup-guard or
//! local-function family, whose derivation reads more than the edited construct.
//! Every other changed sentence needs the second stage, which parses the mutant, derives what
//! KRS derives from the edited authored content and compares the mutant's sentence with that
//! derivation's rendering; until a caller has run it, the judge's answer for such a sentence
//! is [`SentenceVerdict::NeedsRederivation`], never an acceptance.
//!
//! The judge is pure: it takes the text of one artifact and the map whose generated ranges
//! index that text, so that a caller may pass the in-process [`crate::EmittedK`] or load
//! `definition.k` and `sources.json` from disk.

use std::cmp::Reverse;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::ops::Range;

use krs_ir::{InsertedNode, OriginFrame, SourceMapKey, SourceRange, StableItemId};

use crate::sidecar::{SourceMap, SourceMapEntry, SourceMapNodeKind};

/// One replacement in a generated artifact's text: the bytes `range` of the baseline text
/// become `replacement`.
///
/// The edits of one call must not overlap: sorted by range, each starts at or after the end of
/// the one before, so that two insertions may share a point and are applied in their order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KEdit<'a> {
    /// The baseline bytes the edit rewrites.
    pub range: Range<usize>,
    /// The text written in their place; empty for a deletion.
    pub replacement: &'a str,
}

impl<'a> KEdit<'a> {
    /// The edit that writes `replacement` in place of the baseline bytes `range`.
    #[must_use]
    pub const fn new(range: Range<usize>, replacement: &'a str) -> Self {
        Self { range, replacement }
    }
}

/// What one mutation's edits do to the emitted nodes of one artifact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EditJudgement {
    /// One entry per sentence the edits change, in text order.
    pub sentences: Vec<SentenceJudgement>,
    /// The changes of tokens outside every sentence, in text order.
    pub outside: Vec<OutsideChange>,
    /// The mutant: the baseline text with the edits applied, in range order and, at one
    /// point, in their order. Every [`EditContainer::mutant`] range indexes it.
    pub mutant: String,
}

/// The judge's answer for a whole mutation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum MutationVerdict {
    /// The mutant's tokens are the baseline's: the edits change only layout and comments, or
    /// nothing. K reads the same sentences from both texts, so the mutant is equivalent to the
    /// baseline by construction, and it is refused.
    ChangesNoNode,
    /// The judge refuses the mutation; [`EditJudgement::outside`] and the refusing sentences'
    /// verdicts say why.
    Refused,
    /// The judge refuses nothing, and every changed sentence is
    /// [`SentenceVerdict::NeedsRederivation`]: the mutation may be accepted only once the
    /// re-derivation accepts each of them. This is not an acceptance.
    NeedsRederivation,
}

impl EditJudgement {
    /// The judge's answer for the mutation.
    #[must_use]
    pub fn verdict(&self) -> MutationVerdict {
        if self.outside.is_empty() && self.sentences.is_empty() {
            MutationVerdict::ChangesNoNode
        } else if !self.outside.is_empty()
            || self
                .sentences
                .iter()
                .any(|sentence| sentence.verdict.refuses())
        {
            MutationVerdict::Refused
        } else {
            MutationVerdict::NeedsRederivation
        }
    }

    /// Whether the judge alone refuses the mutation.
    #[must_use]
    pub fn refused(&self) -> bool {
        self.verdict() != MutationVerdict::NeedsRederivation
    }
}

/// A change of tokens that no sentence holds: the module's own syntax (its name, an import,
/// `endmodule`), tokens written before a sentence's first token where no sentence ends, or a
/// change that writes tokens in place of tokens of more than one sentence.
///
/// Such tokens are module syntax, begin a new sentence, or move where a sentence ends, and no
/// per-sentence stage reads them, so the judge refuses them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OutsideChange {
    /// The indices of the edits that make the change, ascending.
    pub edits: Vec<usize>,
    /// The baseline bytes of the tokens the change removes; for a change that only writes
    /// tokens, the layout between the baseline tokens it writes between.
    pub changed: Range<usize>,
}

/// What the edits do to one sentence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SentenceJudgement {
    /// The sentence's source-map key.
    pub sentence: SourceMapKey,
    /// The sentence's node kind.
    pub kind: SourceMapNodeKind,
    /// The sentence's emitted bytes.
    pub emitted: Range<usize>,
    /// The Rust item the sentence comes from: the item of the latest frame of its origin that
    /// names one other than a generated production, so that a lifted local function's equation
    /// names the item it was lifted from.
    pub item: Option<StableItemId>,
    /// The indices of the edits that change the sentence, ascending.
    pub edits: Vec<usize>,
    /// The judge's answer for the sentence.
    pub verdict: SentenceVerdict,
}

/// The judge's answer for one sentence.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum SentenceVerdict {
    /// Some node a change can alter renders authored syntax, and the judge refuses nothing:
    /// the re-derivation decides whether the sentence is accepted.
    ///
    /// A container is the deepest authored node that holds every node one change can alter,
    /// as far as tokens and brackets tell; nested containers merge into the outer one.
    /// The judge does not know K's priorities and associativities, so written tokens can
    /// associate with their neighbours beyond what the brackets show: inserting ` +Int D`
    /// after `B` in `A +Int B *Int C` reads as `(A +Int B) +Int (D *Int C)`, and no subterm of
    /// the mutant has the extent of the `*Int` application the judge names.
    /// The re-derivation must therefore parse the mutant sentence and check that each
    /// container's [`EditContainer::mutant`] extent is one subterm of that parse (for a
    /// sentence container, one sentence of the sentence's kind); where it is not, it takes the
    /// deepest authored ancestor whose extent is, or refuses.
    NeedsRederivation {
        /// Where the re-derivation reads the mutant's authored content, in text order.
        containers: Vec<EditContainer>,
    },
    /// Every node a change can alter is one KRS inserted, wherever the tokens and brackets
    /// leave the written tokens' attachment open; `nodes` are the outermost of them.
    InsertedOnly {
        /// The inserted nodes the changes can alter, in text order.
        nodes: Vec<InsertedNodeRef>,
    },
    /// An edit changes authored syntax and cuts through an inserted node, neither containing it
    /// nor inside it, so the node's extent in the mutant is undefined.
    CrossesInserted {
        /// The inserted nodes an edit cuts through, in text order.
        nodes: Vec<InsertedNodeRef>,
    },
    /// An edit changes authored syntax that a lookup-guard or local-function family reads: a
    /// container holds part of such a family or lies inside it, or the sentence is a local
    /// function's equation. Their re-derivation reads more than the edited construct (a guard
    /// the lowered pattern, a local function its other equation and its call), and it does not
    /// exist yet, so the edit is not judged.
    FamilyNotJudged {
        /// The outermost family nodes the edits reach, in text order.
        nodes: Vec<InsertedNodeRef>,
    },
    /// The sentence is not a rule, a claim or a raw sentence: an edit of a declaration (a
    /// production, the configuration, a context alias) changes what every rule means, which
    /// no per-sentence judgement decides.
    NotARule,
}

impl SentenceVerdict {
    /// Whether this verdict refuses the mutation.
    #[must_use]
    pub const fn refuses(&self) -> bool {
        !matches!(self, Self::NeedsRederivation { .. })
    }
}

/// An authored node that holds a change.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EditContainer {
    /// The node's source-map key.
    pub key: SourceMapKey,
    /// The node's kind.
    pub kind: SourceMapNodeKind,
    /// The node's emitted bytes in the baseline.
    pub emitted: Range<usize>,
    /// The node's extent in [`EditJudgement::mutant`]: from the first to the last of its tokens
    /// there, the tokens the changes it holds write included; empty, where its tokens stood,
    /// when the mutant keeps none of them.
    pub mutant: Range<usize>,
    /// The edits whose changes it holds, ascending.
    pub edits: Vec<usize>,
}

/// An inserted node the judge names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InsertedNodeRef {
    /// The node's source-map key.
    pub key: SourceMapKey,
    /// What KRS inserted.
    pub kind: InsertedNode,
    /// The node's emitted bytes.
    pub emitted: Range<usize>,
    /// The authored node to edit instead, when the map names one.
    pub nearest_authored: Option<AuthoredNodeRef>,
}

/// The authored node nearest to an inserted one: the construct it serves, or its nearest
/// authored ancestor.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AuthoredNodeRef {
    /// The emitted node; `None` when no emitted node of the sentence renders the construct (it
    /// was inlined elsewhere), in which case `source` still locates the Rust.
    pub key: Option<SourceMapKey>,
    /// The emitted node's bytes.
    pub emitted: Option<Range<usize>>,
    /// The Rust the author edits instead.
    pub source: Option<SourceRange>,
}

/// Why the judge cannot judge a set of edits against a map.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum JudgeError {
    /// Edit `edit`'s range is reversed or ends past the text.
    OutOfBounds {
        /// The edit's index.
        edit: usize,
    },
    /// Edit `edit`'s range does not start and end on character boundaries.
    NotCharBoundary {
        /// The edit's index.
        edit: usize,
    },
    /// Edits `first` and `second` overlap.
    Overlapping {
        /// The earlier edit's index.
        first: usize,
        /// The later edit's index.
        second: usize,
    },
    /// The map has no generated range in the artifact.
    UnknownArtifact {
        /// The artifact asked for.
        artifact: String,
    },
    /// A generated range of the map does not lie in the text on character boundaries, so the
    /// map does not index this text.
    StaleMap {
        /// The entry whose range does not fit.
        key: SourceMapKey,
    },
}

impl fmt::Display for JudgeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutOfBounds { edit } => {
                write!(formatter, "edit[{edit}]'s range lies outside the text")
            }
            Self::NotCharBoundary { edit } => write!(
                formatter,
                "edit[{edit}]'s range does not start and end on character boundaries"
            ),
            Self::Overlapping { first, second } => {
                write!(formatter, "edit[{first}] and edit[{second}] overlap")
            }
            Self::UnknownArtifact { artifact } => {
                write!(formatter, "the source map renders no node in {artifact}")
            }
            Self::StaleMap { key } => write!(
                formatter,
                "the source map's range of {} does not fit the text: the map was not emitted \
                 with this text",
                key.as_str()
            ),
        }
    }
}

impl Error for JudgeError {}

/// Judges `edits` of `source`, the text of `artifact` (normally
/// [`crate::DEFINITION_ARTIFACT`]), against `map`, whose generated ranges for `artifact` index
/// `source`.
///
/// The rule, for the nodes that have a generated range in `artifact`:
///
/// 1. Both texts are read as K reads them: whitespace, `//` and `/* */` comments are layout;
///    a string literal, a bracket and a comma are tokens, and so is every other run of
///    characters.
///    A baseline token that no edit touches and that the mutant holds at its shifted place is
///    kept.
///    Between kept tokens the baseline's and the mutant's tokens are matched by a longest
///    common subsequence in which a bracket matches only a bracket whose group holds the same
///    tokens, then bracket pairs that stand in corresponding places, then the other tokens.
///    A change is a maximal run of unmatched tokens: baseline tokens it removes and mutant
///    tokens it writes; two changes whose written brackets pair with each other are one
///    change, which wraps the tokens between them.
///    So a mutation is judged by the tokens it changes, however its edits are written: the
///    context an edit names, layout and comments do not count, and a written character that
///    joins a neighbouring token, or a comment or string that an edit opens or closes, changes
///    every token it takes in.
/// 2. The nodes a change can alter are the deepest nodes holding each token it removes (the
///    depth of the source map tells apart nodes of one range); and, when it writes tokens
///    where it removes none, or more than one token or bracketed group in place of removed
///    ones, also the deepest node holding the matched tokens on both sides of it and every
///    node that ends or starts at its edges, a bracket pair around exactly a node counting as
///    that node's (inside such a pair, when the written brackets pair among themselves and
///    no comma stands outside them).
///    The tokens and brackets do not tell at which of those the written tokens attach
///    (`notBool` written before `((10 /Int A:Int) >Int 1)` may negate the bracketed authored
///    condition or the conjunction KRS wrote around it), so each counts.
///    A change after which a bracket pairs with another partner, or with none, can alter the
///    whole sentence.
/// 3. A change belongs to the sentence holding its tokens.
///    Tokens written after a sentence's last token and before the next token belong to that
///    sentence, whose container is then the whole sentence: they continue it, or they begin
///    module syntax or a sentence, which the re-derivation refuses when it reads the
///    sentence's extent as one sentence.
///    The rest, and a change that writes tokens in place of tokens of two sentences, is
///    [`EditJudgement::outside`].
///    A sentence's own tokens (keywords, its label, its attributes) are the sentence node's,
///    and like any node's they count as authored unless the sentence is inserted.
/// 4. Per sentence: an edit of a sentence other than a rule, claim or raw sentence is
///    [`SentenceVerdict::NotARule`]; otherwise, when some node a change can alter is
///    authored, the sentence is [`SentenceVerdict::CrossesInserted`] if a change removes part
///    of an inserted node's tokens and some outside it, [`SentenceVerdict::FamilyNotJudged`]
///    if a container reaches a lookup-guard or local-function family or the sentence is a
///    local function's equation, and [`SentenceVerdict::NeedsRederivation`] otherwise; when
///    every such node is inserted, [`SentenceVerdict::InsertedOnly`].
/// 5. A change's container is the deepest node of its sentence that has no inserted frame and
///    holds every node the change can alter; nested containers merge into the outer one.
///
/// The judge reads groups from brackets only, and where a change removes a test or guard KRS
/// added to a condition, that is all KRS's own output needs: the authored tokens it leaves
/// beside each other keep their grouping.
/// KRS states a definedness test only before a conjunct of the condition's top-level
/// conjunction, or of the body of a `#let` that stands there, and a lookup guard only before
/// the whole condition, each joined by an `andThenBool` that stands in the place of what it
/// guards; so KRS never emits a test or guard as an operand of an authored operator other than
/// the conjunction or `#let` that holds that place.
/// And KRS brackets every operand of a builtin operator that is itself a builtin application,
/// so removing a test or guard with the `andThenBool` that joins it leaves what it guarded
/// whole, in the place the joined test held.
///
/// # Errors
///
/// Returns [`JudgeError`] when an edit does not fit `source`, two edits overlap, or `map`
/// renders nothing in `artifact` or does not index `source`.
pub fn judge_edits(
    source: &str,
    map: &SourceMap,
    artifact: &str,
    edits: &[KEdit<'_>],
) -> Result<EditJudgement, JudgeError> {
    let nodes = Nodes::of(source, map, artifact)?;
    let order = check_edits(source, edits)?;
    let mutant = apply_edits(source, edits, &order);
    let base = Lexed::new(source);
    let after = Lexed::new(&mutant);
    let alignment = Alignment::of(&base, &after, edits, &order);
    let hunks = alignment.hunks(&base, &after, edits);
    let mut touched: Vec<Touched> = Vec::new();
    let mut outside = Vec::new();
    for (index, hunk) in hunks.iter().enumerate() {
        let sentence_of = |token: usize| nodes.sentence_at(base.tokens[token].start);
        let mut part = |sentence: usize, old: Range<usize>, new: Range<usize>| {
            let entry = sentence_entry(&mut touched, sentence);
            entry.parts.push(Part {
                hunk: index,
                old,
                new,
                before: hunk.before,
                after: hunk.after,
            });
            entry.damaged |= hunk.damaged;
        };
        if hunk.old.is_empty() {
            let holder = match (hunk.before, hunk.after) {
                (Some(before), Some(after)) if sentence_of(before) == sentence_of(after) => {
                    sentence_of(before)
                }
                _ => None,
            };
            let ended = hunk.before.and_then(|before| {
                sentence_of(before).filter(|&sentence| {
                    nodes.all[sentence]
                        .span(&base)
                        .is_some_and(|span| span.1 == before)
                })
            });
            match holder.or(ended) {
                Some(sentence) => part(sentence, hunk.old.clone(), hunk.new.clone()),
                None => outside.push(OutsideChange {
                    edits: hunk.edits.clone(),
                    changed: hunk.region(&base),
                }),
            }
            continue;
        }
        let mut groups: Vec<(Option<usize>, Range<usize>)> = Vec::new();
        for token in hunk.old.clone() {
            let sentence = sentence_of(token);
            match groups.last_mut() {
                Some((last, range)) if *last == sentence => range.end = token + 1,
                _ => groups.push((sentence, token..token + 1)),
            }
        }
        if let [(Some(sentence), _)] = groups.as_slice() {
            part(*sentence, hunk.old.clone(), hunk.new.clone());
            continue;
        }
        for (sentence, range) in &groups {
            if let Some(sentence) = sentence {
                part(*sentence, range.clone(), hunk.new.start..hunk.new.start);
            }
        }
        if !hunk.new.is_empty() || groups.iter().any(|(sentence, _)| sentence.is_none()) {
            outside.push(OutsideChange {
                edits: hunk.edits.clone(),
                changed: base.tokens[hunk.old.start].start..base.tokens[hunk.old.end - 1].end,
            });
        }
    }
    for &sentence in &alignment.regrouped(&base, &after, &nodes) {
        sentence_entry(&mut touched, sentence).damaged = true;
    }
    touched.retain(|entry| !entry.parts.is_empty());
    touched.sort_by_key(|entry| entry.sentence);
    let context = Context {
        nodes: &nodes,
        base: &base,
        after: &after,
        alignment: &alignment,
        hunks: &hunks,
    };
    let sentences = touched
        .into_iter()
        .map(|entry| entry.judge(&context))
        .collect();
    Ok(EditJudgement {
        sentences,
        outside,
        mutant,
    })
}

/// Checks that the edits fit `source` and do not overlap; returns their indices in range
/// order, insertions at one point in their order.
fn check_edits(source: &str, edits: &[KEdit<'_>]) -> Result<Vec<usize>, JudgeError> {
    for (index, edit) in edits.iter().enumerate() {
        if edit.range.start > edit.range.end || edit.range.end > source.len() {
            return Err(JudgeError::OutOfBounds { edit: index });
        }
        if !source.is_char_boundary(edit.range.start) || !source.is_char_boundary(edit.range.end) {
            return Err(JudgeError::NotCharBoundary { edit: index });
        }
    }
    let mut order = (0..edits.len()).collect::<Vec<_>>();
    order.sort_by_key(|&index| (edits[index].range.start, edits[index].range.end, index));
    for pair in order.windows(2) {
        let (first, second) = (pair[0], pair[1]);
        if edits[second].range.start < edits[first].range.end {
            return Err(JudgeError::Overlapping {
                first: first.min(second),
                second: first.max(second),
            });
        }
    }
    Ok(order)
}

/// `source` with `edits` applied in `order`.
fn apply_edits(source: &str, edits: &[KEdit<'_>], order: &[usize]) -> String {
    let mut mutant = String::with_capacity(source.len());
    let mut at = 0;
    for &index in order {
        let edit = &edits[index];
        mutant.push_str(&source[at..edit.range.start]);
        mutant.push_str(edit.replacement);
        at = edit.range.end;
    }
    mutant.push_str(&source[at..]);
    mutant
}

/// Whether `character` is a bracket or a comma, each a token of its own.
const fn is_punctuation(character: char) -> bool {
    matches!(character, '(' | ')' | '[' | ']' | '{' | '}' | ',')
}

/// The tokens of K text, as K's layout separates them.
///
/// Whitespace, `//` line comments and `/* */` block comments are layout; a string literal is
/// one token, a bracket or a comma is one token, and every other run of characters up to
/// layout, a bracket, a comma or a string is one token. An unterminated comment or string runs
/// to the end of the text.
/// A run is coarser than K's tokens where K's grammar splits it, which can only make a change
/// look larger.
fn lex(text: &str) -> Vec<Range<usize>> {
    let mut tokens = Vec::new();
    let mut at = 0;
    while let Some(character) = text[at..].chars().next() {
        let rest = &text[at..];
        if character.is_whitespace() {
            at += character.len_utf8();
        } else if rest.starts_with("//") {
            at += rest.find(['\n', '\r']).unwrap_or(rest.len());
        } else if rest.starts_with("/*") {
            at += rest
                .strip_prefix("/*")
                .and_then(|body| body.find("*/"))
                .map_or(rest.len(), |end| end + 4);
        } else if character == '"' {
            let mut end = 1;
            let mut characters = rest[1..].chars();
            while let Some(next) = characters.next() {
                end += next.len_utf8();
                if next == '\\' {
                    end += characters.next().map_or(0, char::len_utf8);
                } else if next == '"' {
                    break;
                }
            }
            tokens.push(at..at + end);
            at += end;
        } else if is_punctuation(character) {
            tokens.push(at..at + 1);
            at += 1;
        } else {
            let mut end = 0;
            for next in rest.chars() {
                let tail = &rest[end..];
                if next.is_whitespace()
                    || is_punctuation(next)
                    || next == '"'
                    || tail.starts_with("//")
                    || tail.starts_with("/*")
                {
                    break;
                }
                end += next.len_utf8();
            }
            tokens.push(at..at + end);
            at += end;
        }
    }
    tokens
}

/// A text read as tokens, with its bracket pairs.
struct Lexed<'t> {
    text: &'t str,
    tokens: Vec<Range<usize>>,
    /// Each bracket's partner; `None` for other tokens and for a bracket that pairs with none.
    partner: Vec<Option<usize>>,
}

impl<'t> Lexed<'t> {
    fn new(text: &'t str) -> Self {
        let tokens = lex(text);
        let mut partner = vec![None; tokens.len()];
        let mut open: Vec<(usize, &str)> = Vec::new();
        for (index, token) in tokens.iter().enumerate() {
            match &text[token.clone()] {
                "(" => open.push((index, ")")),
                "[" => open.push((index, "]")),
                "{" => open.push((index, "}")),
                close @ (")" | "]" | "}") => {
                    if let Some(&(start, expected)) = open.last()
                        && expected == close
                    {
                        open.pop();
                        partner[start] = Some(index);
                        partner[index] = Some(start);
                    }
                }
                _ => {}
            }
        }
        Self {
            text,
            tokens,
            partner,
        }
    }

    fn text(&self, index: usize) -> &'t str {
        &self.text[self.tokens[index].clone()]
    }

    fn is_bracket(&self, index: usize) -> bool {
        matches!(self.text(index), "(" | ")" | "[" | "]" | "{" | "}")
    }

    fn is_open(&self, index: usize) -> bool {
        matches!(self.text(index), "(" | "[" | "{")
    }

    /// The first and last tokens meeting `range`; `None` when it meets none.
    fn span(&self, range: &Range<usize>) -> Option<(usize, usize)> {
        if range.is_empty() {
            return None;
        }
        let first = self
            .tokens
            .partition_point(|token| token.end <= range.start);
        let last = self.tokens.partition_point(|token| token.start < range.end);
        (first < last).then(|| (first, last - 1))
    }

    /// `span` widened over each bracket pair that encloses exactly it.
    fn enclosed(&self, span: (usize, usize)) -> (usize, usize) {
        let (mut first, mut last) = span;
        while first > 0 && self.partner[first - 1].is_some_and(|partner| partner == last + 1) {
            first -= 1;
            last += 1;
        }
        (first, last)
    }

    /// Whether the tokens `range` are one token or one bracketed group.
    fn is_atomic(&self, range: &Range<usize>) -> bool {
        range.len() == 1
            || (range.len() > 1
                && self.is_open(range.start)
                && self.partner[range.start] == Some(range.end - 1))
    }

    /// Whether every bracket of the tokens `range` pairs inside it and no comma stands outside
    /// its groups, so that the tokens stay inside the innermost group around them.
    fn is_contained(&self, range: &Range<usize>) -> bool {
        let mut depth = 0_usize;
        for index in range.clone() {
            if self.is_bracket(index)
                && !self.partner[index].is_some_and(|partner| range.contains(&partner))
            {
                return false;
            }
            match self.text(index) {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => depth -= 1,
                "," if depth == 0 => return false,
                _ => {}
            }
        }
        true
    }
}

/// How many token pairs a longest common subsequence compares at most; a larger change is
/// taken whole, which can only make it look larger.
const MATCH_LIMIT: usize = 1 << 22;

/// The pairs of a longest common subsequence of `a` and `b`, ascending in both; among the
/// longest, the one that matches each element of `a` as early in `b` as it can.
fn common_subsequence(left: &[usize], right: &[usize]) -> Vec<(usize, usize)> {
    let prefix = left
        .iter()
        .zip(right)
        .take_while(|(one, other)| one == other)
        .count();
    let suffix = left[prefix..]
        .iter()
        .rev()
        .zip(right[prefix..].iter().rev())
        .take_while(|(one, other)| one == other)
        .count();
    let middle_left = &left[prefix..left.len() - suffix];
    let middle_right = &right[prefix..right.len() - suffix];
    let mut pairs = (0..prefix).map(|index| (index, index)).collect::<Vec<_>>();
    let (rows, columns) = (middle_left.len(), middle_right.len());
    if rows > 0 && columns > 0 && rows.saturating_mul(columns) <= MATCH_LIMIT {
        // `table[row * width + column]`: the length of a longest common subsequence of the
        // middles from `row` and from `column` on.
        let width = columns + 1;
        let mut table = vec![0_u32; (rows + 1) * width];
        for row in (0..rows).rev() {
            for column in (0..columns).rev() {
                table[row * width + column] = if middle_left[row] == middle_right[column] {
                    table[(row + 1) * width + column + 1] + 1
                } else {
                    table[(row + 1) * width + column].max(table[row * width + column + 1])
                };
            }
        }
        let (mut row, mut column) = (0, 0);
        while row < rows && column < columns {
            if middle_left[row] == middle_right[column]
                && table[row * width + column] == table[(row + 1) * width + column + 1] + 1
            {
                pairs.push((prefix + row, prefix + column));
                row += 1;
                column += 1;
            } else if table[(row + 1) * width + column] >= table[row * width + column + 1] {
                row += 1;
            } else {
                column += 1;
            }
        }
    }
    pairs.extend(
        (0..suffix).map(|offset| (left.len() - suffix + offset, right.len() - suffix + offset)),
    );
    pairs
}

/// Comparison keys of tokens: equal keys for equal tokens, and for brackets, equal keys for
/// brackets of one shape whose groups hold the same tokens.
#[derive(Default)]
struct Keys {
    ids: HashMap<String, usize>,
}

impl Keys {
    fn id(&mut self, key: String) -> usize {
        let next = self.ids.len();
        *self.ids.entry(key).or_insert(next)
    }

    fn text(&mut self, text: &str) -> usize {
        self.id(format!("t{text}"))
    }

    fn of(&mut self, lexed: &Lexed<'_>, index: usize, side: char) -> usize {
        if !lexed.is_bracket(index) {
            return self.text(lexed.text(index));
        }
        let Some(partner) = lexed.partner[index] else {
            return self.id(format!("u{side}{index}"));
        };
        let mut key = format!("g{}", lexed.text(index));
        for inner in index.min(partner) + 1..index.max(partner) {
            key.push('\u{0}');
            key.push_str(lexed.text(inner));
        }
        self.id(key)
    }
}

/// Which baseline tokens the mutant keeps, and as which of its tokens.
struct Alignment {
    /// For each baseline token, the mutant token matched to it.
    image: Vec<Option<usize>>,
    /// For each mutant token, the baseline token matched to it.
    preimage: Vec<Option<usize>>,
    /// For each baseline token, whether no edit touches it and the mutant holds it at its
    /// shifted place.
    kept: Vec<bool>,
}

impl Alignment {
    fn of(base: &Lexed<'_>, after: &Lexed<'_>, edits: &[KEdit<'_>], order: &[usize]) -> Self {
        let mut alignment = Self {
            image: vec![None; base.tokens.len()],
            preimage: vec![None; after.tokens.len()],
            kept: vec![false; base.tokens.len()],
        };
        // Kept tokens: untouched by every edit, and at their shifted place in the mutant.
        let (mut next, mut shift, mut cursor) = (0, 0_isize, 0);
        for (index, token) in base.tokens.iter().enumerate() {
            while let Some(&edit) = order.get(next)
                && edits[edit].range.end <= token.start
            {
                let edit = &edits[edit];
                shift += edit.replacement.len().cast_signed() - edit.range.len().cast_signed();
                next += 1;
            }
            if order
                .get(next)
                .is_some_and(|&edit| edits[edit].range.start < token.end)
            {
                continue;
            }
            let Some(place) = token.start.checked_add_signed(shift) else {
                continue;
            };
            while after
                .tokens
                .get(cursor)
                .is_some_and(|candidate| candidate.start < place)
            {
                cursor += 1;
            }
            if after
                .tokens
                .get(cursor)
                .is_some_and(|candidate| candidate.start == place && candidate.len() == token.len())
            {
                alignment.set(index, cursor);
                alignment.kept[index] = true;
                cursor += 1;
            }
        }
        for (old, new) in alignment.runs(0..base.tokens.len(), 0..after.tokens.len()) {
            alignment.match_gap(base, after, old, new);
        }
        alignment
    }

    fn set(&mut self, old: usize, new: usize) {
        self.image[old] = Some(new);
        self.preimage[new] = Some(old);
    }

    /// The runs of unmatched tokens between matched ones inside `old` and `new`, each with its
    /// counterpart, empty runs included.
    fn runs(&self, old: Range<usize>, new: Range<usize>) -> Vec<(Range<usize>, Range<usize>)> {
        let mut runs = Vec::new();
        let (mut old_start, mut new_start) = (old.start, new.start);
        for index in old.clone() {
            if let Some(image) = self.image[index] {
                runs.push((old_start..index, new_start..image));
                old_start = index + 1;
                new_start = image + 1;
            }
        }
        runs.push((old_start..old.end, new_start..new.end));
        runs
    }

    /// Matches the tokens between two kept ones.
    fn match_gap(
        &mut self,
        base: &Lexed<'_>,
        after: &Lexed<'_>,
        old: Range<usize>,
        new: Range<usize>,
    ) {
        if old.is_empty() || new.is_empty() || old.len().saturating_mul(new.len()) > MATCH_LIMIT {
            return;
        }
        let mut keys = Keys::default();
        let a = old
            .clone()
            .map(|index| keys.of(base, index, 'b'))
            .collect::<Vec<_>>();
        let b = new
            .clone()
            .map(|index| keys.of(after, index, 'm'))
            .collect::<Vec<_>>();
        for (i, j) in common_subsequence(&a, &b) {
            self.set(old.start + i, new.start + j);
        }
        // A bracket whose partner is matched matches the partner of that match.
        while let Some((old_bracket, new_bracket)) = self.anchored_bracket(base, after, &old, &new)
        {
            self.set(old_bracket, new_bracket);
        }
        // Bracket pairs whose ends stand in corresponding runs.
        while let Some((open_old, open_new, close_old, close_new)) =
            self.corresponding_pair(base, after, &old, &new)
        {
            self.set(open_old, open_new);
            self.set(close_old, close_new);
        }
        for (run_old, run_new) in self.runs(old, new) {
            let a_tokens = run_old
                .filter(|&index| !base.is_bracket(index))
                .collect::<Vec<_>>();
            let b_tokens = run_new
                .filter(|&index| !after.is_bracket(index))
                .collect::<Vec<_>>();
            let a = a_tokens
                .iter()
                .map(|&index| keys.text(base.text(index)))
                .collect::<Vec<_>>();
            let b = b_tokens
                .iter()
                .map(|&index| keys.text(after.text(index)))
                .collect::<Vec<_>>();
            for (i, j) in common_subsequence(&a, &b) {
                self.set(a_tokens[i], b_tokens[j]);
            }
        }
    }

    /// The first unmatched baseline bracket whose partner is matched, with the partner of
    /// that match, when it is unmatched and stands in the corresponding run.
    fn anchored_bracket(
        &self,
        base: &Lexed<'_>,
        after: &Lexed<'_>,
        old: &Range<usize>,
        new: &Range<usize>,
    ) -> Option<(usize, usize)> {
        for (run_old, run_new) in self.runs(old.clone(), new.clone()) {
            for index in run_old {
                if !base.is_bracket(index) {
                    continue;
                }
                if let Some(target) = base.partner[index]
                    .and_then(|partner| self.image[partner])
                    .and_then(|image| after.partner[image])
                    && run_new.contains(&target)
                    && after.text(target) == base.text(index)
                {
                    return Some((index, target));
                }
            }
        }
        None
    }

    /// The first unmatched baseline bracket pair, by its opening bracket, that has an unmatched
    /// mutant pair of the same shape whose opening and closing brackets stand in the runs
    /// corresponding to the baseline pair's.
    fn corresponding_pair(
        &self,
        base: &Lexed<'_>,
        after: &Lexed<'_>,
        old: &Range<usize>,
        new: &Range<usize>,
    ) -> Option<(usize, usize, usize, usize)> {
        let runs = self.runs(old.clone(), new.clone());
        let run_of = |index: usize| runs.iter().position(|(run, _)| run.contains(&index));
        for (run_old, run_new) in &runs {
            for open_old in run_old.clone() {
                if !base.is_open(open_old) {
                    continue;
                }
                let Some(close_old) = base.partner[open_old] else {
                    continue;
                };
                let Some(close_run) = run_of(close_old) else {
                    continue;
                };
                for open_new in run_new.clone() {
                    if after.text(open_new) != base.text(open_old) {
                        continue;
                    }
                    if let Some(close_new) = after.partner[open_new]
                        && runs[close_run].1.contains(&close_new)
                    {
                        return Some((open_old, open_new, close_old, close_new));
                    }
                }
            }
        }
        None
    }

    /// The changes: maximal runs of unmatched tokens between matched ones, two of them merged
    /// when brackets they write pair with each other.
    fn hunks(&self, base: &Lexed<'_>, after: &Lexed<'_>, edits: &[KEdit<'_>]) -> Vec<Hunk> {
        let mut hunks = Vec::new();
        let mut before = None;
        let (mut old_start, mut new_start) = (0, 0);
        let mut close = |old: Range<usize>, new: Range<usize>, before, after| {
            if !old.is_empty() || !new.is_empty() {
                hunks.push(Hunk {
                    old,
                    new,
                    before,
                    after,
                    damaged: false,
                    edits: Vec::new(),
                });
            }
        };
        for (index, image) in self.image.iter().enumerate() {
            if let Some(image) = *image {
                close(old_start..index, new_start..image, before, Some(index));
                before = Some(index);
                old_start = index + 1;
                new_start = image + 1;
            }
        }
        close(
            old_start..base.tokens.len(),
            new_start..after.tokens.len(),
            before,
            None,
        );
        // A bracket written in one change and its partner in another wrap the tokens between.
        let mut owner = vec![usize::MAX; after.tokens.len()];
        for (index, hunk) in hunks.iter().enumerate() {
            for token in hunk.new.clone() {
                owner[token] = index;
            }
        }
        let mut reach = (0..hunks.len()).collect::<Vec<_>>();
        for (index, hunk) in hunks.iter().enumerate() {
            for token in hunk.new.clone() {
                if let Some(partner) = after.partner[token]
                    && self.preimage[partner].is_none()
                {
                    let other = owner[partner];
                    let (low, high) = (index.min(other), index.max(other));
                    reach[low] = reach[low].max(high);
                }
            }
        }
        let mut merged: Vec<Hunk> = Vec::new();
        let mut index = 0;
        while index < hunks.len() {
            let mut end = reach[index];
            let mut scan = index;
            while scan <= end {
                end = end.max(reach[scan]);
                scan += 1;
            }
            let (first, last) = (&hunks[index], &hunks[end]);
            merged.push(Hunk {
                old: first.old.start..last.old.end,
                new: first.new.start..last.new.end,
                before: first.before,
                after: last.after,
                damaged: false,
                edits: Vec::new(),
            });
            index = end + 1;
        }
        let meeting = |region: &Range<usize>| {
            (0..edits.len())
                .filter(|&edit| {
                    let range = &edits[edit].range;
                    if range.is_empty() {
                        region.start <= range.start && range.start <= region.end
                    } else {
                        range.start < region.end && region.start < range.end
                    }
                })
                .collect::<Vec<_>>()
        };
        for hunk in &mut merged {
            hunk.damaged = self.unpairs(base, after, hunk);
            hunk.edits = meeting(&hunk.region(base));
            if hunk.edits.is_empty() {
                // A change the lexing of an edit's text makes away from it: the edits between
                // the kept tokens around it.
                let before = hunk
                    .before
                    .and_then(|before| (0..=before).rev().find(|&token| self.kept[token]));
                let after = hunk
                    .after
                    .and_then(|after| (after..base.tokens.len()).find(|&token| self.kept[token]));
                let start = before.map_or(0, |before| base.tokens[before].end);
                let end = after.map_or(base.text.len(), |after| base.tokens[after].start);
                hunk.edits = meeting(&(start..end));
            }
        }
        merged
    }

    /// Whether `hunk` removes or writes a bracket whose partner the mutant keeps or which has
    /// none, so that a bracket pairs with another partner after it.
    fn unpairs(&self, base: &Lexed<'_>, after: &Lexed<'_>, hunk: &Hunk) -> bool {
        hunk.old.clone().any(|index| {
            base.is_bracket(index)
                && self.image[index].is_none()
                && base.partner[index].is_none_or(|partner| self.image[partner].is_some())
        }) || hunk.new.clone().any(|index| {
            after.is_bracket(index)
                && self.preimage[index].is_none()
                && after.partner[index].is_none_or(|partner| self.preimage[partner].is_some())
        })
    }

    /// The sentences holding a matched bracket whose partner's match is not its match's
    /// partner.
    fn regrouped(&self, base: &Lexed<'_>, after: &Lexed<'_>, nodes: &Nodes<'_>) -> Vec<usize> {
        let mut sentences = Vec::new();
        for (index, image) in self.image.iter().enumerate() {
            if let Some(image) = *image
                && base.is_bracket(index)
                && base.partner[index].and_then(|partner| self.image[partner])
                    != after.partner[image]
                && let Some(sentence) = nodes.sentence_at(base.tokens[index].start)
                && !sentences.contains(&sentence)
            {
                sentences.push(sentence);
            }
        }
        sentences
    }
}

/// One change: the baseline tokens `old` it removes become the mutant tokens `new`.
///
/// `before` and `after` are the matched baseline tokens around it. A change merged from
/// several also counts the matched tokens it wraps in `old` and `new`.
struct Hunk {
    old: Range<usize>,
    new: Range<usize>,
    before: Option<usize>,
    after: Option<usize>,
    /// Whether a bracket pairs with another partner, or with none, after the change.
    damaged: bool,
    /// The edits that make it, ascending.
    edits: Vec<usize>,
}

impl Hunk {
    /// The baseline bytes between the matched tokens around the change.
    fn region(&self, base: &Lexed<'_>) -> Range<usize> {
        let start = self.before.map_or(0, |before| base.tokens[before].end);
        let end = self
            .after
            .map_or(base.text.len(), |after| base.tokens[after].start);
        start..end
    }
}

/// A node with a generated range in the judged artifact.
struct Node<'m> {
    entry: &'m SourceMapEntry,
    start: usize,
    end: usize,
    depth: u32,
    inserted: Option<InsertedNode>,
}

impl Node<'_> {
    const fn holds(&self, range: &Range<usize>) -> bool {
        self.start <= range.start && range.end <= self.end
    }

    const fn meets(&self, range: &Range<usize>) -> bool {
        self.start < range.end && range.start < self.end
    }

    const fn is_empty(&self) -> bool {
        self.start == self.end
    }

    const fn range(&self) -> Range<usize> {
        self.start..self.end
    }

    const fn is_sentence(&self) -> bool {
        self.depth == 1
    }

    fn span(&self, base: &Lexed<'_>) -> Option<(usize, usize)> {
        base.span(&self.range())
    }
}

/// Whether the token span `outer` holds `inner`.
const fn spans_hold(outer: (usize, usize), inner: (usize, usize)) -> bool {
    outer.0 <= inner.0 && inner.1 <= outer.1
}

/// The rendered nodes of one artifact, in text order with outer nodes first.
struct Nodes<'m> {
    all: Vec<Node<'m>>,
    /// Indices into `all` of the sentences, in text order.
    sentences: Vec<usize>,
}

impl<'m> Nodes<'m> {
    fn of(source: &str, map: &'m SourceMap, artifact: &str) -> Result<Self, JudgeError> {
        let mut all = Vec::new();
        for entry in map.entries() {
            let Some(generated) = entry.generated() else {
                continue;
            };
            if generated.artifact() != artifact {
                continue;
            }
            let stale = || JudgeError::StaleMap {
                key: entry.key().clone(),
            };
            let start = usize::try_from(generated.start_byte()).map_err(|_| stale())?;
            let end = usize::try_from(generated.end_byte()).map_err(|_| stale())?;
            if start > end
                || end > source.len()
                || !source.is_char_boundary(start)
                || !source.is_char_boundary(end)
            {
                return Err(stale());
            }
            all.push(Node {
                entry,
                start,
                end,
                depth: entry.depth(),
                inserted: entry.inserted().map(|(kind, _)| kind),
            });
        }
        if all.is_empty() {
            return Err(JudgeError::UnknownArtifact {
                artifact: artifact.to_owned(),
            });
        }
        all.sort_by_key(|node| (node.start, Reverse(node.end), node.depth));
        let sentences = all
            .iter()
            .enumerate()
            .filter(|(_, node)| {
                node.is_sentence() && node.entry.node_kind() != SourceMapNodeKind::ProductionGroup
            })
            .map(|(index, _)| index)
            .collect();
        Ok(Self { all, sentences })
    }

    /// The sentence holding the byte `at`.
    fn sentence_at(&self, at: usize) -> Option<usize> {
        let position = self
            .sentences
            .partition_point(|&sentence| self.all[sentence].start <= at);
        position
            .checked_sub(1)
            .map(|position| self.sentences[position])
            .filter(|&sentence| at < self.all[sentence].end)
    }

    /// The nodes of `sentence`, the sentence among them.
    fn within(&self, sentence: usize) -> impl Iterator<Item = usize> + '_ {
        let outer = self.all[sentence].range();
        self.all
            .iter()
            .enumerate()
            .filter(move |(index, node)| {
                *index == sentence
                    || (node.depth > 1 && outer.start <= node.start && node.end <= outer.end)
            })
            .map(|(index, _)| index)
    }

    /// The deepest of `candidates`; `None` when there is none.
    fn deepest(&self, candidates: impl Iterator<Item = usize>) -> Option<usize> {
        candidates.max_by_key(|&index| (self.all[index].depth, Reverse(index)))
    }

    fn inserted_ref(&self, sentence: usize, index: usize) -> InsertedNodeRef {
        let node = &self.all[index];
        InsertedNodeRef {
            key: node.entry.key().clone(),
            kind: node
                .inserted
                .expect("an inserted node reference names an inserted node"),
            emitted: node.range(),
            nearest_authored: self.nearest_authored(sentence, index),
        }
    }

    /// The authored node to edit instead of the inserted node `index` of `sentence`: the node
    /// rendering the construct the inserted node serves (its anchor, else its own authored
    /// range), the deepest such node holding it or else the nearest in the text, and with no
    /// such node its deepest authored ancestor.
    fn nearest_authored(&self, sentence: usize, index: usize) -> Option<AuthoredNodeRef> {
        let node = &self.all[index];
        let range = node
            .entry
            .inserted()
            .and_then(|(_, anchor)| anchor.cloned())
            .or_else(|| node.entry.origin().exact_authored_range());
        let authored = |candidate: &usize| {
            let other = &self.all[*candidate];
            *candidate != index && *candidate != sentence && other.inserted.is_none()
        };
        let chosen = range
            .as_ref()
            .and_then(|range| {
                let candidates = self
                    .within(sentence)
                    .filter(authored)
                    .filter(|&candidate| {
                        self.all[candidate]
                            .entry
                            .origin()
                            .exact_authored_range()
                            .as_ref()
                            == Some(range)
                    })
                    .collect::<Vec<_>>();
                self.deepest(
                    candidates
                        .iter()
                        .copied()
                        .filter(|&candidate| self.all[candidate].holds(&node.range())),
                )
                .or_else(|| {
                    candidates.iter().copied().min_by_key(|&candidate| {
                        let other = &self.all[candidate];
                        let distance = node
                            .start
                            .saturating_sub(other.end)
                            .max(other.start.saturating_sub(node.end));
                        (distance, other.start)
                    })
                })
            })
            .or_else(|| {
                self.deepest(self.within(sentence).filter(authored).filter(|&candidate| {
                    let other = &self.all[candidate];
                    other.holds(&node.range()) && other.depth < node.depth
                }))
            });
        match chosen {
            Some(chosen) => {
                let other = &self.all[chosen];
                Some(AuthoredNodeRef {
                    key: Some(other.entry.key().clone()),
                    emitted: Some(other.range()),
                    source: range.or_else(|| other.entry.origin().exact_authored_range()),
                })
            }
            None => range.map(|range| AuthoredNodeRef {
                key: None,
                emitted: None,
                source: Some(range),
            }),
        }
    }

    /// `indices` without those inside another of them, in text order.
    fn outermost(&self, mut indices: Vec<usize>) -> Vec<usize> {
        indices.sort_unstable();
        indices.dedup();
        let mut kept: Vec<usize> = Vec::new();
        for index in indices {
            let node = &self.all[index];
            if !kept
                .iter()
                .any(|&outer| self.all[outer].holds(&node.range()))
            {
                kept.push(index);
            }
        }
        kept
    }
}

/// What the judge reads while it judges one sentence.
struct Context<'c, 'm, 't> {
    nodes: &'c Nodes<'m>,
    base: &'c Lexed<'t>,
    after: &'c Lexed<'t>,
    alignment: &'c Alignment,
    hunks: &'c [Hunk],
}

/// One change's part in one sentence: the sentence's tokens `old` it removes and the mutant
/// tokens `new` it writes.
struct Part {
    hunk: usize,
    old: Range<usize>,
    new: Range<usize>,
    before: Option<usize>,
    after: Option<usize>,
}

/// What the changes do to one sentence.
struct Touched {
    sentence: usize,
    parts: Vec<Part>,
    /// Whether a bracket of the sentence pairs with another partner after the changes.
    damaged: bool,
}

fn sentence_entry(touched: &mut Vec<Touched>, sentence: usize) -> &mut Touched {
    let position = touched
        .iter()
        .position(|entry| entry.sentence == sentence)
        .unwrap_or_else(|| {
            touched.push(Touched {
                sentence,
                parts: Vec::new(),
                damaged: false,
            });
            touched.len() - 1
        });
    &mut touched[position]
}

/// A node of the judged sentence, with its token spans.
struct Spanned {
    index: usize,
    /// Its first and last tokens.
    span: (usize, usize),
    /// `span` widened over the bracket pairs enclosing exactly it.
    enclosed: (usize, usize),
}

impl Touched {
    fn judge(self, context: &Context<'_, '_, '_>) -> SentenceJudgement {
        let sentence = &context.nodes.all[self.sentence];
        let mut edits = self
            .parts
            .iter()
            .flat_map(|part| context.hunks[part.hunk].edits.iter().copied())
            .collect::<Vec<_>>();
        edits.sort_unstable();
        edits.dedup();
        let verdict = self.verdict(context);
        SentenceJudgement {
            sentence: sentence.entry.key().clone(),
            kind: sentence.entry.node_kind(),
            emitted: sentence.range(),
            item: sentence_item(sentence.entry),
            edits,
            verdict,
        }
    }

    /// The nodes of the sentence that hold a token, with their spans.
    fn spanned(&self, context: &Context<'_, '_, '_>) -> Vec<Spanned> {
        context
            .nodes
            .within(self.sentence)
            .filter_map(|index| {
                let span = context.nodes.all[index].span(context.base)?;
                Some(Spanned {
                    index,
                    span,
                    enclosed: context.base.enclosed(span),
                })
            })
            .collect()
    }

    /// The nodes `part` can alter.
    fn candidates(
        &self,
        context: &Context<'_, '_, '_>,
        spanned: &[Spanned],
        part: &Part,
    ) -> Vec<usize> {
        let (nodes, base) = (context.nodes, context.base);
        let mut candidates = Vec::new();
        // The deepest nodes holding each byte of each removed token.
        for token in part.old.clone() {
            let range = base.tokens[token].clone();
            let meeting = spanned
                .iter()
                .map(|node| node.index)
                .filter(|&index| !nodes.all[index].is_empty() && nodes.all[index].meets(&range))
                .collect::<Vec<_>>();
            let mut cuts = vec![range.start, range.end];
            for &index in &meeting {
                let node = &nodes.all[index];
                cuts.extend(
                    [node.start, node.end]
                        .into_iter()
                        .filter(|&cut| range.start < cut && cut < range.end),
                );
            }
            cuts.sort_unstable();
            cuts.dedup();
            for segment in cuts.windows(2) {
                let segment = segment[0]..segment[1];
                let holding = meeting
                    .iter()
                    .copied()
                    .filter(|&index| nodes.all[index].holds(&segment));
                if let Some(depth) = holding.clone().map(|index| nodes.all[index].depth).max() {
                    candidates.extend(holding.filter(|&index| nodes.all[index].depth == depth));
                }
            }
        }
        // Where written tokens attach, the tokens and brackets do not tell.
        if !part.new.is_empty() && (part.old.is_empty() || !context.after.is_atomic(&part.new)) {
            let contained = context.after.is_contained(&part.new);
            let inside = |token: Option<usize>| {
                token.filter(|&token| {
                    nodes.sentence_at(base.tokens[token].start) == Some(self.sentence)
                })
            };
            let (before, after) = (inside(part.before), inside(part.after));
            let holder = before.zip(after).and_then(|around| {
                nodes.deepest(
                    spanned
                        .iter()
                        .filter(|node| {
                            let span = if contained { node.enclosed } else { node.span };
                            spans_hold(span, around)
                        })
                        .map(|node| node.index),
                )
            });
            candidates.push(holder.unwrap_or(self.sentence));
            let removed = !part.old.is_empty();
            let ends = [before, removed.then(|| part.old.end - 1)];
            let starts = [after, removed.then_some(part.old.start)];
            for node in spanned {
                let ends_here = [node.span.1, node.enclosed.1]
                    .iter()
                    .any(|&last| ends.contains(&Some(last)));
                let starts_here = [node.span.0, node.enclosed.0]
                    .iter()
                    .any(|&first| starts.contains(&Some(first)));
                if ends_here || starts_here {
                    candidates.push(node.index);
                }
            }
        }
        if self.damaged {
            candidates.push(self.sentence);
        }
        candidates.sort_unstable();
        candidates.dedup();
        candidates
    }

    fn verdict(&self, context: &Context<'_, '_, '_>) -> SentenceVerdict {
        let nodes = context.nodes;
        let sentence = &nodes.all[self.sentence];
        if !matches!(
            sentence.entry.node_kind(),
            SourceMapNodeKind::Rule | SourceMapNodeKind::Claim | SourceMapNodeKind::RawSentence
        ) {
            return SentenceVerdict::NotARule;
        }
        let refs = |indices: Vec<usize>| {
            nodes
                .outermost(indices)
                .into_iter()
                .map(|index| nodes.inserted_ref(self.sentence, index))
                .collect::<Vec<_>>()
        };
        let spanned = self.spanned(context);
        let span_of = |index: usize| {
            spanned
                .iter()
                .find(|node| node.index == index)
                .map(|node| node.span)
        };
        let candidates = self
            .parts
            .iter()
            .map(|part| self.candidates(context, &spanned, part))
            .collect::<Vec<_>>();
        if candidates.iter().flatten().next().is_some()
            && !candidates
                .iter()
                .flatten()
                .any(|&index| nodes.all[index].inserted.is_none())
        {
            return SentenceVerdict::InsertedOnly {
                nodes: refs(candidates.into_iter().flatten().collect()),
            };
        }
        let crossed = self
            .parts
            .iter()
            .filter(|part| !part.old.is_empty())
            .flat_map(|part| {
                let removed = (part.old.start, part.old.end - 1);
                spanned
                    .iter()
                    .filter(move |node| {
                        nodes.all[node.index].inserted.is_some()
                            && node.span.0 <= removed.1
                            && removed.0 <= node.span.1
                            && !spans_hold(node.span, removed)
                            && !spans_hold(removed, node.span)
                    })
                    .map(|node| node.index)
            })
            .collect::<Vec<_>>();
        if !crossed.is_empty() {
            return SentenceVerdict::CrossesInserted {
                nodes: refs(crossed),
            };
        }
        let containers = self.containers(context, &spanned, &candidates);
        let families = if sentence.inserted.is_some() {
            vec![self.sentence]
        } else {
            containers
                .iter()
                .filter_map(|(container, _)| span_of(*container))
                .flat_map(|container| {
                    spanned
                        .iter()
                        .filter(move |node| {
                            matches!(
                                nodes.all[node.index].inserted,
                                Some(InsertedNode::LookupGuard | InsertedNode::LocalFunction)
                            ) && node.span.0 <= container.1
                                && container.0 <= node.span.1
                        })
                        .map(|node| node.index)
                })
                .collect::<Vec<_>>()
        };
        if !families.is_empty() {
            return SentenceVerdict::FamilyNotJudged {
                nodes: refs(families),
            };
        }
        SentenceVerdict::NeedsRederivation {
            containers: containers
                .into_iter()
                .map(|(index, parts)| self.container(context, &spanned, index, &parts))
                .collect(),
        }
    }

    /// The deepest authored node holding each part's candidates and removed tokens, nested
    /// ones merged into the outer, each with the indices of the parts it holds.
    fn containers(
        &self,
        context: &Context<'_, '_, '_>,
        spanned: &[Spanned],
        candidates: &[Vec<usize>],
    ) -> Vec<(usize, Vec<usize>)> {
        let nodes = context.nodes;
        let span_of = |index: usize| {
            spanned
                .iter()
                .find(|node| node.index == index)
                .map(|node| node.span)
        };
        let mut found: Vec<(usize, usize)> = Vec::new();
        for (part_index, (part, candidates)) in self.parts.iter().zip(candidates).enumerate() {
            let mut needed = candidates
                .iter()
                .filter_map(|&index| span_of(index))
                .collect::<Vec<_>>();
            if !part.old.is_empty() {
                needed.push((part.old.start, part.old.end - 1));
            }
            let holding = spanned
                .iter()
                .filter(|node| {
                    nodes.all[node.index].inserted.is_none()
                        && needed.iter().all(|&span| spans_hold(node.span, span))
                })
                .map(|node| node.index);
            if let Some(container) = nodes.deepest(holding) {
                found.push((container, part_index));
            }
        }
        found.sort_unstable();
        let mut containers: Vec<(usize, Vec<usize>)> = Vec::new();
        for (index, part) in found {
            let node = &nodes.all[index];
            match containers
                .iter_mut()
                .find(|(outer, _)| nodes.all[*outer].holds(&node.range()))
            {
                Some((_, parts)) => parts.push(part),
                None => containers.push((index, vec![part])),
            }
        }
        containers
    }

    /// The container `index` holding `parts`.
    fn container(
        &self,
        context: &Context<'_, '_, '_>,
        spanned: &[Spanned],
        index: usize,
        parts: &[usize],
    ) -> EditContainer {
        let node = &context.nodes.all[index];
        let (after, alignment) = (context.after, context.alignment);
        let mut edits = parts
            .iter()
            .flat_map(|&part| context.hunks[self.parts[part].hunk].edits.iter().copied())
            .collect::<Vec<_>>();
        edits.sort_unstable();
        edits.dedup();
        let mut tokens = spanned
            .iter()
            .find(|spanned| spanned.index == index)
            .map(|spanned| spanned.span)
            .map(|(first, last)| {
                (first..=last)
                    .filter_map(|token| alignment.image[token])
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        tokens.extend(parts.iter().flat_map(|&part| self.parts[part].new.clone()));
        let mutant = if let (Some(&first), Some(&last)) = (tokens.iter().min(), tokens.iter().max())
        {
            after.tokens[first].start..after.tokens[last].end
        } else {
            let part = &self.parts[parts[0]];
            let at = part
                .before
                .and_then(|before| alignment.image[before])
                .map_or(0, |before| after.tokens[before].end);
            at..at
        };
        EditContainer {
            key: node.entry.key().clone(),
            kind: node.entry.node_kind(),
            emitted: node.range(),
            mutant,
            edits,
        }
    }
}

/// The item of the latest frame of `entry`'s origin that names one other than a generated
/// production.
fn sentence_item(entry: &SourceMapEntry) -> Option<StableItemId> {
    entry
        .origin()
        .frames()
        .iter()
        .rev()
        .find_map(|frame| match frame {
            OriginFrame::Ranged { item, .. } | OriginFrame::Transformation { item, .. } => {
                item.as_ref().filter(|item| !item.is_generated_production())
            }
            OriginFrame::Inserted { .. } => None,
        })
        .cloned()
}

#[cfg(test)]
mod tests {
    use std::ops::Range;

    use serde_json::{Value, json};

    use super::{
        EditJudgement, JudgeError, KEdit, MutationVerdict, SentenceJudgement, SentenceVerdict,
        judge_edits,
    };
    use crate::sidecar::{SourceMap, SourceMapNodeKind};
    use krs_ir::InsertedNode;

    /// A small emitted definition: a rule with a definedness test and a block-form frame, an
    /// equation with a label, a rule with a lookup guard, and a production.
    const TEXT: &str = "module TEST
  imports INT
  syntax KItem ::= go ( Int )
  // KRS t/src/lib.rs: d\u{e9}f
  rule [div]:
    <k> div A:Int => .K ... </k>
    requires (A:Int =/=Int 0) andThenBool ((10 /Int A:Int) >Int 1)
  // KRS t/src/lib.rs: go
  rule go ( N:Int ) => N:Int +Int 1 [label(t--go)]
  rule [key]:
    <k> key ( Krs_Instance0:KItem ) => .K </k>
    requires Krs_Instance0:KItem ==K (M:Map [ 7 ])
endmodule
";

    const DIV: &str = "  rule [div]:\n    <k> div A:Int => .K ... </k>\n    requires (A:Int =/=Int 0) andThenBool ((10 /Int A:Int) >Int 1)\n";
    const CONDITION: &str = "(A:Int =/=Int 0) andThenBool ((10 /Int A:Int) >Int 1)";
    const GO: &str = "  rule go ( N:Int ) => N:Int +Int 1 [label(t--go)]\n";
    const KEY: &str = "  rule [key]:\n    <k> key ( Krs_Instance0:KItem ) => .K </k>\n    requires Krs_Instance0:KItem ==K (M:Map [ 7 ])\n";
    const GUARD: &str = "Krs_Instance0:KItem ==K (M:Map [ 7 ])";

    /// The bytes of `inner`'s first occurrence inside the one occurrence of `outer` in `TEXT`.
    fn at(outer: &str, inner: &str) -> Range<usize> {
        let start = TEXT.find(outer).expect("outer occurs");
        assert_eq!(TEXT.rfind(outer), Some(start), "{outer:?} occurs once");
        let offset = outer.find(inner).expect("inner occurs in outer");
        start + offset..start + offset + inner.len()
    }

    fn file() -> Value {
        json!({
            "package": {
                "k_namespace": "TEST",
                "cargo_name": "t",
                "cargo_version": "0.0.0",
                "cargo_source": "workspace"
            },
            "package_relative_path": "src/lib.rs",
            "content_sha256": "0".repeat(64)
        })
    }

    fn rust(range: (u32, u32)) -> Value {
        json!({ "file": file(), "start_byte": range.0, "end_byte": range.1 })
    }

    /// The map's entries, each named by its position.
    #[derive(Default)]
    struct Entries(Vec<Value>);

    impl Entries {
        /// Adds a node of `kind` at `depth` rendering `range`, authored at the Rust bytes
        /// `authored`, inserted as `inserted` (with an anchor) when given, and naming `item`.
        fn node(
            &mut self,
            kind: &str,
            depth: u32,
            range: Range<usize>,
            authored: (u32, u32),
            inserted: Option<(&str, Option<(u32, u32)>)>,
            item: Option<&str>,
        ) -> &mut Self {
            let mut origin = vec![json!({
                "frame_type": "ranged", "kind": "authored", "range": rust(authored)
            })];
            if let Some((kind, anchor)) = inserted {
                let mut frame = json!({ "frame_type": "inserted", "kind": kind });
                if let Some(anchor) = anchor {
                    frame["anchor"] = rust(anchor);
                }
                origin.push(frame);
            }
            let mut definition = json!({ "frame_type": "transformation", "kind": "definition_ir" });
            if let Some(item) = item {
                definition["item"] = json!({
                    "package": file()["package"].clone(),
                    "module_path": [],
                    "item_name": item,
                    "item_kind": "rule",
                    "disambiguator": ""
                });
            }
            origin.push(definition);
            self.0.push(json!({
                "key": format!("node-{}", self.0.len()),
                "node_kind": kind,
                "depth": depth,
                "origin": origin,
                "generated": {
                    "artifact": "definition.k",
                    "start_byte": range.start,
                    "end_byte": range.end,
                    "start_line": 1, "start_column": 1, "end_line": 1, "end_column": 1
                }
            }));
            self
        }
    }

    const TEST: Option<(&str, Option<(u32, u32)>)> = Some(("definedness_test", Some((144, 145))));
    const GUARDED: Option<(&str, Option<(u32, u32)>)> = Some(("lookup_guard", None));

    #[expect(
        clippy::too_many_lines,
        reason = "One entry per node of the definition."
    )]
    fn map() -> SourceMap {
        let mut entries = Entries::default();
        entries
            .node("module", 0, at(TEXT, TEXT), (1, 2), None, None)
            .node(
                "production",
                1,
                at(
                    "  syntax KItem ::= go ( Int )\n",
                    "  syntax KItem ::= go ( Int )\n",
                ),
                (400, 401),
                None,
                Some("Go"),
            )
            .node("rule", 1, at(DIV, DIV), (100, 110), None, Some("div"))
            .node(
                "cell_clause",
                3,
                at(DIV, "    <k> div A:Int => .K ... </k>"),
                (111, 114),
                None,
                None,
            )
            .node("term", 4, at(DIV, "div A:Int"), (112, 113), None, None)
            .node("term", 5, at("div A:Int", "A:Int"), (115, 116), None, None)
            .node("term", 4, at(DIV, ".K"), (117, 118), None, None)
            .node(
                "cell_frame",
                4,
                at(DIV, " ..."),
                (112, 113),
                Some(("cell_frame", None)),
                None,
            )
            .node(
                "rule_condition",
                2,
                at(DIV, CONDITION),
                (120, 130),
                None,
                None,
            )
            .node("term", 3, at(DIV, CONDITION), (146, 147), TEST, None)
            .node("term", 4, at(DIV, "A:Int =/=Int 0"), (146, 147), TEST, None)
            .node(
                "term",
                5,
                at("(A:Int =/=Int 0)", "A:Int"),
                (146, 147),
                TEST,
                None,
            )
            .node("term", 5, at("=/=Int 0", "0"), (146, 147), TEST, None)
            .node(
                "term",
                4,
                at(DIV, "(10 /Int A:Int) >Int 1"),
                (140, 150),
                None,
                None,
            )
            .node("term", 5, at(DIV, "10 /Int A:Int"), (144, 145), None, None)
            .node("term", 6, at("(10 /Int", "10"), (142, 143), None, None)
            .node("term", 6, at("/Int A:Int", "A:Int"), (146, 147), None, None)
            .node("term", 5, at(">Int 1", "1"), (149, 150), None, None)
            .node("rule", 1, at(GO, GO), (200, 210), None, Some("go"))
            .node(
                "term",
                2,
                at(GO, "go ( N:Int ) => N:Int +Int 1"),
                (211, 212),
                None,
                None,
            )
            .node("term", 3, at(GO, "go ( N:Int )"), (213, 214), None, None)
            .node(
                "term",
                4,
                at("go ( N:Int )", "N:Int"),
                (215, 216),
                None,
                None,
            )
            .node("term", 3, at(GO, "N:Int +Int 1"), (217, 218), None, None)
            .node("term", 4, at("=> N:Int", "N:Int"), (215, 216), None, None)
            .node("term", 4, at("+Int 1", "1"), (219, 220), None, None)
            .node("rule", 1, at(KEY, KEY), (300, 310), None, Some("key"))
            .node(
                "cell_clause",
                3,
                at(KEY, "    <k> key ( Krs_Instance0:KItem ) => .K </k>"),
                (311, 312),
                None,
                None,
            )
            .node(
                "term",
                4,
                at(KEY, "key ( Krs_Instance0:KItem )"),
                (313, 314),
                None,
                None,
            )
            .node(
                "term",
                5,
                at("key ( Krs_Instance0:KItem )", "Krs_Instance0:KItem"),
                (315, 316),
                GUARDED,
                None,
            )
            .node("term", 4, at(") => .K </k>", ".K"), (317, 318), None, None)
            .node(
                "rule_condition",
                2,
                at(KEY, GUARD),
                (315, 316),
                GUARDED,
                None,
            )
            .node("term", 3, at(KEY, GUARD), (315, 316), GUARDED, None)
            .node(
                "term",
                4,
                at(GUARD, "Krs_Instance0:KItem"),
                (315, 316),
                GUARDED,
                None,
            )
            .node(
                "term",
                4,
                at(GUARD, "(M:Map [ 7 ])"),
                (320, 321),
                None,
                None,
            )
            .node("term", 5, at(GUARD, "M:Map"), (322, 323), None, None)
            .node("term", 5, at(GUARD, "7"), (324, 325), None, None);
        serde_json::from_value(json!({ "schema_version": 3, "entries": entries.0 })).unwrap()
    }

    fn judge(edits: &[KEdit<'_>]) -> EditJudgement {
        judge_edits(TEXT, &map(), "definition.k", edits).unwrap()
    }

    fn edit<'a>(outer: &str, inner: &str, replacement: &'a str) -> KEdit<'a> {
        KEdit::new(at(outer, inner), replacement)
    }

    fn only(judgement: &EditJudgement) -> &SentenceJudgement {
        assert!(judgement.outside.is_empty(), "{judgement:#?}");
        assert_eq!(judgement.sentences.len(), 1, "{judgement:#?}");
        &judgement.sentences[0]
    }

    /// The emitted text of each container of a sentence the re-derivation decides.
    fn containers(sentence: &SentenceJudgement) -> Vec<(&'static str, Vec<usize>)> {
        let SentenceVerdict::NeedsRederivation { containers } = &sentence.verdict else {
            panic!("needs re-derivation: {sentence:#?}");
        };
        containers
            .iter()
            .map(|container| (&TEXT[container.emitted.clone()], container.edits.clone()))
            .collect()
    }

    /// A named node: its text, its kind, its nearest authored node's text and Rust bytes.
    type Named = (
        &'static str,
        InsertedNode,
        Option<&'static str>,
        Option<(u32, u32)>,
    );

    /// Each named node as [`Named`].
    fn named(nodes: &[super::InsertedNodeRef]) -> Vec<Named> {
        nodes
            .iter()
            .map(|node| {
                let authored = node.nearest_authored.as_ref();
                (
                    &TEXT[node.emitted.clone()],
                    node.kind,
                    authored
                        .and_then(|authored| authored.emitted.clone())
                        .map(|range| &TEXT[range]),
                    authored
                        .and_then(|authored| authored.source.as_ref())
                        .map(|range| (range.start_byte, range.end_byte)),
                )
            })
            .collect()
    }

    /// An edit naming its whole condition as context changes only the bytes it rewrites.
    #[test]
    fn context_does_not_count() {
        let replaced = CONDITION.replace(">Int 1", ">Int 2");
        let judgement = judge(&[edit(DIV, CONDITION, &replaced)]);
        let sentence = only(&judgement);
        assert_eq!(
            sentence.item.as_ref().map(krs_ir::StableItemId::item_name),
            Some("div")
        );
        assert_eq!(containers(sentence), [("1", vec![0])]);
        assert_eq!(judgement.verdict(), MutationVerdict::NeedsRederivation);
        // The judge does not refuse it, and has no acceptance to give: the re-derivation
        // decides.
        assert!(!judgement.refused());
    }

    /// A condition and its root term share a range; the deeper one owns the bytes, and the
    /// container is the deepest authored node.
    #[test]
    fn depth_decides_ties() {
        let judgement = judge(&[edit(DIV, CONDITION, "true")]);
        let sentence = only(&judgement);
        let SentenceVerdict::NeedsRederivation { containers } = &sentence.verdict else {
            panic!("{sentence:#?}");
        };
        assert_eq!(containers.len(), 1);
        assert_eq!(containers[0].kind, SourceMapNodeKind::RuleCondition);
        // Deleting the test alone changes only KRS's nodes, of which the conjunction is the
        // outermost; the division it tests is the authored node to edit.
        let judgement = judge(&[edit(DIV, "(A:Int =/=Int 0) andThenBool ", "")]);
        let sentence = only(&judgement);
        let SentenceVerdict::InsertedOnly { nodes } = &sentence.verdict else {
            panic!("{sentence:#?}");
        };
        assert_eq!(
            named(nodes),
            [(
                CONDITION,
                InsertedNode::DefinednessTest,
                Some("10 /Int A:Int"),
                Some((144, 145))
            )]
        );
        assert_eq!(judgement.verdict(), MutationVerdict::Refused);
        let judgement = judge(&[edit("=/=Int 0", "0", "1")]);
        let SentenceVerdict::InsertedOnly { nodes } = &only(&judgement).verdict else {
            panic!("{judgement:#?}");
        };
        assert_eq!(
            named(nodes),
            [(
                "0",
                InsertedNode::DefinednessTest,
                Some("10 /Int A:Int"),
                Some((144, 145))
            )]
        );
    }

    /// One mutant judges alike however its edits are written: by the whole condition or by
    /// the bytes it deletes, and by a bracketed group or the token inside it.
    #[test]
    fn edits_are_judged_by_the_tokens_they_change() {
        let narrow = judge(&[edit(DIV, "(A:Int =/=Int 0) andThenBool ", "")]);
        // The whole condition as the find, the right operand's brackets dropped: the two
        // removed runs are both KRS's conjunction.
        let whole = judge(&[edit(DIV, CONDITION, "(10 /Int A:Int) >Int 1")]);
        for judgement in [&narrow, &whole] {
            let SentenceVerdict::InsertedOnly { nodes } = &only(judgement).verdict else {
                panic!("{judgement:#?}");
            };
            assert_eq!(
                named(nodes),
                [(
                    CONDITION,
                    InsertedNode::DefinednessTest,
                    Some("10 /Int A:Int"),
                    Some((144, 145))
                )]
            );
        }
        let token = judge(&[edit("/Int A:Int", "A:Int", "B:Int")]);
        let group = judge(&[edit(DIV, "(10 /Int A:Int)", "(10 /Int B:Int)")]);
        assert_eq!(containers(only(&token)), [("A:Int", vec![0])]);
        assert_eq!(containers(only(&group)), [("A:Int", vec![0])]);
        // Brackets written around a kept token wrap it: the change is that token's.
        let token = judge(&[edit("/Int A:Int", "A:Int", "(A:Int +Int 1)")]);
        let group = judge(&[edit(DIV, "(10 /Int A:Int)", "(10 /Int (A:Int +Int 1))")]);
        assert_eq!(containers(only(&token)), [("A:Int", vec![0])]);
        assert_eq!(containers(only(&group)), [("A:Int", vec![0])]);
        assert_eq!(token.mutant, group.mutant);
    }

    /// Tokens written where a node starts or ends may attach to it or to the node around it;
    /// only when each of them is inserted is the change KRS's alone.
    #[test]
    fn written_tokens_at_a_boundary() {
        // `notBool` before the bracketed authored condition may negate it.
        let judgement = judge(&[edit(DIV, "andThenBool ((10", "andThenBool notBool ((10")]);
        assert_eq!(containers(only(&judgement)), [(CONDITION, vec![0])]);
        // After `requires`, it may negate the test or the whole condition.
        let judgement = judge(&[edit(DIV, "requires (A", "requires notBool (A")]);
        assert_eq!(containers(only(&judgement)), [(DIV, vec![0])]);
        // Inside the test's brackets, every node it may attach to is KRS's.
        let judgement = judge(&[edit("=/=Int 0)", "0)", "0 +Int 0)")]);
        let SentenceVerdict::InsertedOnly { nodes } = &only(&judgement).verdict else {
            panic!("{judgement:#?}");
        };
        assert_eq!(nodes.len(), 1);
        assert_eq!(&TEXT[nodes[0].emitted.clone()], "A:Int =/=Int 0");
    }

    /// Written tokens get the container that holds every node they may attach to, whether
    /// they replace a token or follow it; a written character that joins a token rewrites it.
    #[test]
    fn insertions() {
        let end = at(DIV, "10 /Int A:Int").end;
        let inserted = judge(&[KEdit::new(end..end, " +Int 1")]);
        assert_eq!(containers(only(&inserted)), [("10 /Int A:Int", vec![0])]);
        let replaced = judge(&[edit("/Int A:Int", "A:Int", "B:Int +Int 1")]);
        assert_eq!(containers(only(&replaced)), [("10 /Int A:Int", vec![0])]);
        let end = at(">Int 1", "1").end;
        let judgement = judge(&[KEdit::new(end..end, "0")]);
        assert_eq!(containers(only(&judgement)), [("1", vec![0])]);
        let operator = at(DIV, ">Int");
        let judgement = judge(&[KEdit::new(operator.start + 1..operator.start + 1, "=")]);
        assert_eq!(
            containers(only(&judgement)),
            [("(10 /Int A:Int) >Int 1", vec![0])]
        );
    }

    /// Tokens written after a sentence's last token continue it, wherever in the layout that
    /// follows they are written, and its container is the whole sentence; tokens written where
    /// no sentence ends are outside every sentence.
    #[test]
    fn insertions_between_sentences() {
        let rule = "\n  rule [new]: <k> 1 => 2 </k>";
        let end = at(DIV, DIV).end;
        let next = at(GO, GO).start;
        for point in [end - 1, end, next] {
            let judgement = judge(&[KEdit::new(point..point, rule)]);
            let sentence = only(&judgement);
            assert_eq!(containers(sentence), [(DIV, vec![0])], "{point}");
            let SentenceVerdict::NeedsRederivation { containers } = &sentence.verdict else {
                unreachable!();
            };
            let extent = &judgement.mutant[containers[0].mutant.clone()];
            assert!(extent.starts_with("rule [div]:"), "{extent:?}");
            assert!(
                extent.ends_with("rule [new]: <k> 1 => 2 </k>"),
                "{extent:?}"
            );
        }
        // After an import: no sentence ends there.
        let point = at(TEXT, "  imports INT\n").end;
        let judgement = judge(&[KEdit::new(point..point, rule)]);
        assert!(judgement.sentences.is_empty());
        assert_eq!(judgement.outside.len(), 1);
        assert_eq!(judgement.verdict(), MutationVerdict::Refused);
        // After the production: they continue a declaration.
        let point = at(DIV, DIV).start;
        let judgement = judge(&[KEdit::new(point..point, rule)]);
        assert_eq!(only(&judgement).verdict, SentenceVerdict::NotARule);
    }

    /// A sentence's own tokens are the sentence node's, and authored; layout and comments are
    /// no tokens, so a mutant that changes only them changes nothing, unless the change joins
    /// two tokens or lets a comment take some in.
    #[test]
    fn sentence_tokens_layout_and_comments() {
        for (edits, sentence) in [
            (vec![edit(GO, "t--go", "t--gone")], GO),
            (vec![edit(DIV, "requires", "ensures")], DIV),
        ] {
            let judgement = judge(&edits);
            assert_eq!(containers(only(&judgement)), [(sentence, vec![0])]);
        }
        for edits in [
            vec![edit(DIV, "\n    requires", "\n      requires")],
            vec![edit(DIV, "(A:Int =/=Int 0)", "( A:Int  =/=Int 0 )")],
            vec![edit(TEXT, "d\u{e9}f", "def")],
            vec![edit(GO, "go ( N:Int )", "go ( N:Int )")],
            vec![],
        ] {
            let judgement = judge(&edits);
            assert!(judgement.sentences.is_empty() && judgement.outside.is_empty());
            assert_eq!(judgement.verdict(), MutationVerdict::ChangesNoNode);
        }
        // Two edits each delete part of the layout between `</k>` and `requires`; together
        // they join the two tokens.
        let layout = at(DIV, "</k>\n    requires").start + "</k>".len();
        let judgement = judge(&[
            KEdit::new(layout..layout + 3, ""),
            KEdit::new(layout + 3..layout + 5, ""),
        ]);
        assert_eq!(only(&judgement).edits, [0, 1]);
        assert_eq!(judgement.verdict(), MutationVerdict::NeedsRederivation);
        // Deleting the newline that ends a line comment takes the next line into it.
        let newline = at(TEXT, "// KRS t/src/lib.rs: go\n").end - 1;
        let judgement = judge(&[KEdit::new(newline..newline + 1, "")]);
        let sentence = only(&judgement);
        assert_eq!(containers(sentence), [(GO, vec![0])]);
        let SentenceVerdict::NeedsRederivation { containers } = &sentence.verdict else {
            unreachable!();
        };
        assert!(containers[0].mutant.is_empty());
    }

    /// A comment one edit opens and another closes takes in every token between them, and
    /// each sentence it reaches is judged.
    #[test]
    fn comments_opened_and_closed() {
        let open = at(DIV, DIV).end - 1;
        let close = at(KEY, KEY).end - 1;
        let judgement = judge(&[
            KEdit::new(open..open, " /*"),
            KEdit::new(close..close, " */"),
        ]);
        let sentences = judgement
            .sentences
            .iter()
            .map(|sentence| sentence.item.as_ref().unwrap().item_name())
            .collect::<Vec<_>>();
        assert_eq!(sentences, ["go", "key"]);
        assert!(judgement.outside.is_empty());
        assert_eq!(containers(&judgement.sentences[0]), [(GO, vec![0, 1])]);
        assert!(matches!(
            judgement.sentences[1].verdict,
            SentenceVerdict::FamilyNotJudged { .. }
        ));
        // An unterminated comment takes in the rest of the text, the module's own tokens too.
        let judgement = judge(&[KEdit::new(open..open, " /*")]);
        assert_eq!(judgement.sentences.len(), 2);
        assert_eq!(judgement.outside.len(), 1);
        assert_eq!(judgement.verdict(), MutationVerdict::Refused);
    }

    /// A change between two sentences that removes the comment between them changes each of
    /// them; one that writes tokens in place of both moves where a sentence ends.
    #[test]
    fn edit_spanning_two_sentences() {
        let span = "1)\n  // KRS t/src/lib.rs: go\n  rule go ( N";
        let judgement = judge(&[edit(span, span, "2)\n  rule go ( M")]);
        let sentences = judgement
            .sentences
            .iter()
            .map(|sentence| {
                (
                    sentence.item.as_ref().unwrap().item_name(),
                    sentence.edits.clone(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(sentences, [("div", vec![0]), ("go", vec![0])]);
        assert!(judgement.outside.is_empty());
        assert_eq!(judgement.verdict(), MutationVerdict::NeedsRederivation);
        let span = ">Int 1)\n  // KRS t/src/lib.rs: go\n  rule go";
        let judgement = judge(&[edit(span, span, "X")]);
        assert_eq!(judgement.sentences.len(), 2);
        assert_eq!(judgement.outside.len(), 1);
        assert_eq!(judgement.verdict(), MutationVerdict::Refused);
    }

    /// Two edits of one sentence, one changing only an inserted node and one an authored node,
    /// leave the sentence to the re-derivation with both containers; nested containers merge.
    #[test]
    fn containers_of_several_edits() {
        let judgement = judge(&[
            edit("=/=Int 0", "0", "1"),
            edit(DIV, "div A:Int", "div B:Int"),
        ]);
        assert_eq!(
            containers(only(&judgement)),
            [("A:Int", vec![1]), (CONDITION, vec![0])]
        );
        let judgement = judge(&[edit("(10 /Int", "10", "12"), edit(DIV, ">Int", ">=Int")]);
        assert_eq!(
            containers(only(&judgement)),
            [("(10 /Int A:Int) >Int 1", vec![0, 1])]
        );
    }

    /// An edit that cuts through an inserted node is refused, naming the node.
    #[test]
    fn crossing_an_inserted_node() {
        let judgement = judge(&[edit(DIV, "=/=Int 0) andThenBool ((10", "X")]);
        let SentenceVerdict::CrossesInserted { nodes } = &only(&judgement).verdict else {
            panic!("{judgement:#?}");
        };
        assert_eq!(
            named(nodes),
            [(
                "A:Int =/=Int 0",
                InsertedNode::DefinednessTest,
                Some("10 /Int A:Int"),
                Some((144, 145))
            )]
        );
    }

    /// An edit inside the construct a lookup guard holds is not judged; an edit of the guard
    /// alone, or of the name it introduces, changes only KRS's nodes.
    #[test]
    fn lookup_guards() {
        let judgement = judge(&[edit(GUARD, "7", "8")]);
        let SentenceVerdict::FamilyNotJudged { nodes } = &only(&judgement).verdict else {
            panic!("{judgement:#?}");
        };
        assert_eq!(
            named(nodes)
                .into_iter()
                .map(|(text, kind, ..)| (text, kind))
                .collect::<Vec<_>>(),
            [(GUARD, InsertedNode::LookupGuard)]
        );
        for edits in [
            [edit(GUARD, "==K", "=/=K")],
            [edit("key ( Krs_Instance0:KItem )", "Krs_Instance0", "X")],
        ] {
            let judgement = judge(&edits);
            let SentenceVerdict::InsertedOnly { nodes } = &only(&judgement).verdict else {
                panic!("{judgement:#?}");
            };
            assert!(
                nodes
                    .iter()
                    .all(|node| node.kind == InsertedNode::LookupGuard)
            );
        }
    }

    /// A frame the language adds is inserted; its authored node is the pattern it closes.
    /// Deleting ` ...` or the equal `... ` judges alike, since layout carries no node, and
    /// deleting the layout between two tokens rewrites both.
    #[test]
    fn implicit_frame() {
        let judgement = judge(&[edit(DIV, " ...", "")]);
        assert_eq!(judgement, judge(&[edit(DIV, "... ", "")]));
        let joined = judge(&[edit(DIV, ".K ...", ".K...")]);
        let SentenceVerdict::NeedsRederivation { containers } = &only(&joined).verdict else {
            panic!("{joined:#?}");
        };
        assert_eq!(containers[0].kind, SourceMapNodeKind::CellClause);
        let SentenceVerdict::InsertedOnly { nodes } = &only(&judgement).verdict else {
            panic!("{judgement:#?}");
        };
        assert_eq!(
            named(nodes),
            [(
                " ...",
                InsertedNode::CellFrame,
                Some("div A:Int"),
                Some((112, 113))
            )]
        );
    }

    /// An edit of a declaration is not judged per sentence.
    #[test]
    fn declarations() {
        let judgement = judge(&[edit("go ( Int )", "Int", "Int , Int")]);
        assert_eq!(only(&judgement).verdict, SentenceVerdict::NotARule);
        assert_eq!(judgement.verdict(), MutationVerdict::Refused);
    }

    #[test]
    fn errors() {
        let map = map();
        let judge = |source: &str, artifact: &str, edits: &[KEdit<'_>]| {
            judge_edits(source, &map, artifact, edits).unwrap_err()
        };
        assert_eq!(
            judge(TEXT, "definition.k", &[KEdit::new(0..TEXT.len() + 1, "")]),
            JudgeError::OutOfBounds { edit: 0 }
        );
        let accent = TEXT.find('\u{e9}').unwrap();
        assert_eq!(
            judge(
                TEXT,
                "definition.k",
                &[KEdit::new(accent + 1..accent + 2, "")]
            ),
            JudgeError::NotCharBoundary { edit: 0 }
        );
        assert_eq!(
            judge(
                TEXT,
                "definition.k",
                &[KEdit::new(10..20, "x"), KEdit::new(5..11, "y")]
            ),
            JudgeError::Overlapping {
                first: 0,
                second: 1
            }
        );
        assert!(matches!(
            judge(TEXT, "spec.k", &[]),
            JudgeError::UnknownArtifact { .. }
        ));
        assert!(matches!(
            judge(&TEXT[..TEXT.len() - 2], "definition.k", &[]),
            JudgeError::StaleMap { .. }
        ));
        // Two insertions at one point, and an insertion at an edit's end, do not overlap.
        let point = at(">Int 1", "1").end;
        assert!(
            judge_edits(
                TEXT,
                &map,
                "definition.k",
                &[KEdit::new(point..point, "0"), KEdit::new(point..point, "0")]
            )
            .is_ok()
        );
    }
}
