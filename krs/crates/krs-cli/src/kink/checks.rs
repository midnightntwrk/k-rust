//! The mutation checks only the krs front end can make, because they read what KRS knows and
//! the K does not say: which nodes of an edited sentence KRS generated, what KRS derives from the
//! edited authored content, and whether KRS admits the Rust source the mutation stands for.
//!
//! A K mutation of a KRS definition must be the emission of some Rust source `P'`, the
//! specification with the edited constructs written differently, or a survivor of it is a target
//! no author can write. Per mutation that resolves, in this order:
//!
//! 1. the judge ([`krs_compiler::judge_edits`]) refuses an edit of nodes KRS inserted
//!    (`generated-only`), a mutation whose tokens are the baseline's (`changes-no-node`), and
//!    what it cannot hand on (`not-judged`);
//! 2. the re-derivation ([`krs_k_rust::lift`]) lifts each edited sentence's authored content
//!    into the semantic IR and accepts the sentence only when it is what KRS emits for it; it
//!    refuses a derived node that does not follow the edit (`derived-mismatch`), a mutation equal
//!    to the specification up to names and brackets (`no-change`), KRS's refusal of the lifted
//!    sentence (its code), and what it does not read (`not-judged`);
//! 3. the theory check ([`krs_compiler::MutantTheory`]) runs KRS's own rule-level admission
//!    checks, unchanged, on the specification's pre-derivation theory with each edited sentence
//!    replaced by its lifted form and each deleted one removed, which is the theory `P'` lowers
//!    to; a refusal carries KRS's code (`krs::analysis::overlapping-rule-heads`,
//!    `krs::analysis::nondet-group`, ...) and names the sibling sentences an author's Rust edit
//!    of the edited constructs would also change.
//!
//! The theory check runs only after the re-derivation accepts every edited sentence: its verdict
//! is about `P'`, which emits the mutant only then. Overlap is judged by KRS's analysis on the
//! semantic IR, never restated over K, so it cannot drift from what `krs check` says of `P'`.
//!
//! Every mutation also gets, refused or not, a `claim-helper` warning for each edited equation
//! of a function only claims apply, a `partial-rendering` warning for an edited construct KRS
//! renders in other sentences the mutation leaves unchanged, and the Rust location of each edit
//! (the row's `krs.edits`).
//!
//! `check --mutations` adds the findings to their rows and the locations as the row's `krs`;
//! `run` and a `fuzz` kill job give each refused mutation its first refusal, by edit order,
//! through [`kink_flow::FrontEnd::refused`], so it runs nothing and its row is `invalid-mutation`
//! with the refusal's reason.
//!
//! Each judgement is stored in the corpus's judge cache ([`JudgeCache`]), which `check`, `run`, a
//! kill job and the condition flips ([`super::flips`]) read alike, so a mutation is judged once per
//! build and emission.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::ops::Range;

use kink_flow::{
    FlowManifest, InvalidMutation, InvalidReason, MutationCheck as FlowCheck, MutationList,
    ResolvedMutation, check::Finding,
};
use krs_compiler::{
    DEFINITION_ARTIFACT, EditContainer, InsertedNodeRef, KEdit, LoweredDefinition, MutantTheory,
    MutationVerdict, Rederivation, RetainedLowering, SentenceJudgement, SentenceVerdict,
    SourceMapNodeKind, TheoryChanges, TheoryRefusal, rule_sentence_key,
};
use krs_ir::{InsertedNode, LineIndex, SourceFileId, SourceMapKey, SourceRange};
use krs_k_rust::lift::{MutantChecker, MutationCheck, Refusal};
use serde_json::{Value, json};

use crate::{DiagnosticSources, EmittedDefinition, EmittedRule};

use super::DEFINITION_FILE;

/// The front end's reason for an edit that changes only nodes KRS inserted.
pub(crate) const GENERATED_ONLY: &str = "generated-only";
/// The front end's reason for a mutation whose tokens are the specification's.
pub(crate) const CHANGES_NO_NODE: &str = "changes-no-node";
/// The front end's reason for a derived node that does not follow the edit.
pub(crate) const DERIVED_MISMATCH: &str = "derived-mismatch";
/// The front end's reason for a mutation equal to the specification up to names and brackets.
pub(crate) const NO_CHANGE: &str = "no-change";
/// The front end's reason for a mutation KRS cannot yet tell a Rust source writes.
pub(crate) const NOT_JUDGED: &str = "not-judged";
/// The warning for an edited equation of a function only claims apply.
pub(crate) const CLAIM_HELPER: &str = "claim-helper";
/// The warning for an edited construct rendered in other sentences the mutation leaves.
pub(crate) const PARTIAL_RENDERING: &str = "partial-rendering";

const NEXT_CHANGES_NO_NODE: &str =
    "change what a rule says: as written the edits change only layout or comments";
const NEXT_DERIVED_MISMATCH: &str = "write the derived text KRS gives (the detail) in place of \
     the mutant's, in the same mutation, or delete it when KRS derives nothing there";
const NEXT_NO_CHANGE: &str = "change what the rule says: the edited rule is the \
     specification's rule up to names and brackets";
pub(crate) const NEXT_NOT_JUDGED: &str = "mutate another part of the rule: KRS cannot yet tell \
     whether a Rust source writes this edit";
const NEXT_CLAIM_HELPER: &str = "mutate a sentence programs reach; a misunderstanding of a \
     claim helper is found by `krs prove`, not by the corpus";
const NEXT_PARTIAL_RENDERING: &str = "this mutant is the source in which the author wrote this \
     occurrence out by hand; to mutate the construct itself, also edit its other renderings (the \
     detail)";

/// What the author does next for an edit of a node KRS inserted, for each kind with a step of its
/// own; any other kind takes [`NEXT_INSERTED`].
///
/// The one table serves the refusal ([`generated_only_next`]) and the judge cache's decoding
/// ([`next_steps`]), so a step a refusal gives is a step a stored judgement may hold. The steps
/// cannot be a `match` without a wildcard: [`InsertedNode`] is `#[non_exhaustive]`, so a match
/// outside its crate needs one, and a kind added there takes [`NEXT_INSERTED`], which both read.
const GENERATED_ONLY_NEXT: [(InsertedNode, &str); 5] = [
    (
        InsertedNode::DefinednessTest,
        "KRS states this test because the construct it guards has no value where the test \
         fails: edit that construct (the detail names it), with the test KRS derives from the \
         edited construct in the same mutation (`krs kink check` prints it)",
    ),
    (
        InsertedNode::LookupGuard,
        "KRS writes this guard for the instance or key the rule's pattern computes; edits of a \
         guard family are not judged yet, so mutate another part of the rule",
    ),
    (
        InsertedNode::GeneratedBinder,
        "this is a name KRS gave (to a k::bits! template, a record update's base, a lookup); \
         edit the tests or reads that use it",
    ),
    (
        InsertedNode::CellFrame,
        "the frame is the block form's: a block-form rule keeps the rest of the cell; edit what \
         the rule matches or writes in the cell instead (a machine-form rule with a closed \
         cell is the source of a closed match)",
    ),
    (
        InsertedNode::LocalFunction,
        "this is KRS's encoding of a `let` block or `k::matches!`; edits of it are not judged \
         yet, so mutate another part of the rule",
    ),
];

/// What the author does next for an edit of a node of kind `kind` KRS inserted.
fn generated_only_next(kind: InsertedNode) -> &'static str {
    GENERATED_ONLY_NEXT
        .iter()
        .find(|(own, _)| *own == kind)
        .map_or(NEXT_INSERTED, |(_, next)| next)
}

/// What the author does next for an edit of a node KRS inserted of a kind without its own step.
const NEXT_INSERTED: &str = "edit the authored node the detail names instead of what KRS inserted";

/// What the author does next for KRS's refusal `code` of the source a mutation stands for.
/// `siblings` says whether the detail lists siblings, renderings of an edited construct that the
/// mutation leaves unchanged: only then is making their edits a step the detail supports; without
/// them, the other sentence the detail names is changed in the same mutation (a correlated edit).
/// `one_item` says whether the refusal names one item: an overlap of one equation with itself,
/// which applies to one argument in two ways with different results, has no other equation to
/// change, so its step is to make every way give one result.
fn krs_next(code: &str, siblings: bool, one_item: bool) -> &'static str {
    match code {
        "krs::analysis::overlapping-rule-heads" if siblings => {
            "KRS accepts these rules only if they cannot apply to one configuration: also make \
             the edits the detail lists as siblings (an author's Rust edit changes every sentence \
             that renders the edited construct), or change the edit so that the guards stay \
             complementary; a nondet group would change the specification, not the mutation"
        }
        "krs::analysis::overlapping-rule-heads" => {
            "KRS accepts these rules only if they cannot apply to one configuration: change the \
             edit so that the guards stay complementary, or change the other rule the detail \
             names in the same mutation (a correlated edit); a nondet group would change the \
             specification, not the mutation"
        }
        "krs::analysis::nondet-group" => {
            "the edit contradicts the specification's nondet group: a member must still overlap \
             another member at one priority, and a group keeps two rules; mutate the group's \
             rules so that they still overlap, or mutate another rule"
        }
        "krs::analysis::priority-after-owise" => {
            "keep the priority below 200, or make the rule unable to apply where the `owise` rule \
             does"
        }
        "krs::analysis::overlapping-equations" | "krs::analysis::overlapping-match-arms"
            if one_item && siblings =>
        {
            "the equation the detail names now applies to the argument it names in two ways with \
             different results: also make the edits the detail lists as siblings (an if/else \
             condition is rendered, negated, in every later branch), or change the edit so that \
             every way the equation applies gives one result"
        }
        "krs::analysis::overlapping-equations" | "krs::analysis::overlapping-match-arms"
            if one_item =>
        {
            "the equation the detail names now applies to the argument it names in two ways with \
             different results: change the edit so that every way the equation applies gives one \
             result, or so that its pattern matches that argument one way"
        }
        "krs::analysis::overlapping-equations" | "krs::analysis::overlapping-match-arms"
            if siblings =>
        {
            "two equations now give different results at the argument the detail names: also \
             make the edits the detail lists as siblings (an if/else condition is rendered, \
             negated, in every later branch), or make the equations disjoint"
        }
        "krs::analysis::overlapping-equations" | "krs::analysis::overlapping-match-arms" => {
            "two equations now give different results at the argument the detail names: make \
             the equations disjoint, or change the other equation the detail names in the same \
             mutation (a correlated edit)"
        }
        _ => {
            "the detail is KRS's message for the Rust source this mutation stands for; change the \
             edit so that KRS would accept it"
        }
    }
}

/// The longest text a detail or location quotes.
const QUOTE_BYTES: usize = 200;

/// `text` trimmed, cut at [`QUOTE_BYTES`] on a character boundary with `…`.
fn quote(text: &str) -> String {
    let text = text.trim();
    if text.len() <= QUOTE_BYTES {
        return text.to_owned();
    }
    let mut end = QUOTE_BYTES;
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}…", &text[..end])
}

/// The bytes one edit changes: its range with the longest common prefix, then suffix, of the
/// old and new text removed (empty, at a point, for an insertion).
fn changed_range(source: &str, edit: &KEdit<'_>) -> Range<usize> {
    let old = &source[edit.range.clone()];
    let new = edit.replacement;
    let prefix = old
        .char_indices()
        .zip(new.chars())
        .find(|((_, a), b)| a != b)
        .map_or_else(|| old.len().min(new.len()), |((index, _), _)| index);
    let suffix = old[prefix..]
        .chars()
        .rev()
        .zip(new[prefix..].chars().rev())
        .take_while(|(a, b)| a == b)
        .map(|(a, _)| a.len_utf8())
        .sum::<usize>();
    edit.range.start + prefix..edit.range.end - suffix
}

/// Whether the changed bytes `changed` touch the node `node`: they overlap it, or, for an
/// insertion, lie inside it.
const fn touches(changed: &Range<usize>, node: &Range<usize>) -> bool {
    if changed.start == changed.end {
        node.start < changed.start && changed.start < node.end
    } else {
        changed.start < node.end && node.start < changed.end
    }
}

/// A Rust range positioned in the package's current source.
#[derive(Clone, Debug)]
struct RustSpan {
    file: String,
    line: Option<u32>,
    column: Option<u32>,
    end_line: Option<u32>,
    end_column: Option<u32>,
    text: Option<String>,
}

impl RustSpan {
    fn value(&self) -> Value {
        json!({
            "file": self.file,
            "line": self.line,
            "column": self.column,
            "end_line": self.end_line,
            "end_column": self.end_column,
            "text": self.text,
        })
    }

    /// `file:line:column`, as far as known.
    fn at(&self) -> String {
        match (self.line, self.column) {
            (Some(line), Some(column)) => format!("{}:{line}:{column}", self.file),
            (Some(line), None) => format!("{}:{line}", self.file),
            _ => self.file.clone(),
        }
    }

    /// `file:line:column` and the quoted Rust text, as a detail names a construct.
    fn described(&self) -> String {
        match &self.text {
            Some(text) => format!("{} (`{text}`)", self.at()),
            None => self.at(),
        }
    }
}

/// One package source: its text, its line index, and its Rust tokens when it lexes.
struct SourceText {
    text: String,
    index: LineIndex,
    tokens: Option<proc_macro2::TokenStream>,
}

/// The package sources, read on demand and indexed by line, as `krs run --trace` reads them.
struct Positions<'a> {
    sources: &'a DiagnosticSources,
    files: RefCell<BTreeMap<SourceFileId, Option<SourceText>>>,
    /// How many spans had no source to read: a file whose package is not selected, which is
    /// unreadable, or whose bytes are not the revision the build read. Such a span has no
    /// position, which a judgement read when the file is the build's revision has.
    unread: Cell<usize>,
}

impl Positions<'_> {
    /// The Rust construct whose source-map range is `range`, positioned: the range itself, or,
    /// for an application whose `arguments` (the authored ranges of the nodes below it in
    /// `definition.k`) are written in the group after it, through that group
    /// ([`construct_end`]).
    fn span(&self, range: &SourceRange, arguments: &[Range<usize>]) -> RustSpan {
        let mut files = self.files.borrow_mut();
        let indexed = files.entry(range.file.clone()).or_insert_with(|| {
            self.sources
                .source_text(&range.file)
                .map(|text| SourceText {
                    index: LineIndex::new(&text),
                    tokens: text.parse().ok(),
                    text: text.clone(),
                })
        });
        let file = range.file.package_relative_path().to_owned();
        let Some(SourceText {
            text,
            index,
            tokens,
        }) = indexed.as_ref()
        else {
            self.unread.set(self.unread.get() + 1);
            return RustSpan {
                file,
                line: None,
                column: None,
                end_line: None,
                end_column: None,
                text: None,
            };
        };
        let position = |byte: u32| {
            usize::try_from(byte)
                .ok()
                .and_then(|byte| index.byte_to_position(byte).ok())
        };
        let bytes = usize::try_from(range.start_byte)
            .ok()
            .zip(usize::try_from(range.end_byte).ok())
            .map(|(start, end)| {
                let end = tokens
                    .as_ref()
                    .and_then(|tokens| construct_end(tokens, &(start..end), arguments))
                    .unwrap_or(end);
                (start, end)
            });
        let start = position(range.start_byte);
        let end = bytes
            .and_then(|(_, end)| u32::try_from(end).ok())
            .and_then(position);
        RustSpan {
            file,
            line: start.map(krs_ir::Position::line),
            column: start.map(krs_ir::Position::scalar_column),
            end_line: end.map(krs_ir::Position::line),
            end_column: end.map(krs_ir::Position::scalar_column),
            text: bytes
                .and_then(|(start, end)| text.get(start..end))
                .map(quote),
        }
    }
}

/// The end of the Rust construct whose source-map range is `range` of the source `tokens` lexes,
/// when it extends past `range`.
///
/// The source map names an application by its head path, since the head is the token an
/// application is keyed by, and the application is that path with the argument group written
/// after it (`Plus(m, n)`, `NatSyntax::Succ(n)`, `Ctor { f: e }`): K renders the whole call as
/// one node, and an edit of that node replaces the whole call. Whether a node is an application
/// with arguments is what K says, not the Rust tokens: `arguments` are the authored ranges of
/// the nodes below it in `definition.k`, empty for a variable or a token. So a range that is
/// exactly a path (identifiers and `::`) ends with the parenthesized or braced group written
/// after it only when one of `arguments` begins inside that group; any other range is the
/// construct itself (`None`). A variable followed by a block, such as the operand `limit` of
/// `if value < limit { value }` or the scrutinee of `match value { .. }`, is therefore its own
/// construct.
fn construct_end(
    tokens: &proc_macro2::TokenStream,
    range: &Range<usize>,
    arguments: &[Range<usize>],
) -> Option<usize> {
    use proc_macro2::{Delimiter, TokenTree};
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let first = trees
        .iter()
        .position(|tree| tree.span().byte_range().end > range.start)?;
    let held = trees[first].span().byte_range();
    if held.start > range.start {
        return None;
    }
    if held.start < range.start {
        // The range lies inside this tree, which must then be a group holding all of it.
        return match &trees[first] {
            TokenTree::Group(group) if range.end <= held.end => {
                construct_end(&group.stream(), range, arguments)
            }
            _ => None,
        };
    }
    // The range must begin the path, not continue one (`Succ` of `NatSyntax::Succ`).
    if first > 0 && matches!(&trees[first - 1], TokenTree::Punct(punct) if punct.as_char() == ':') {
        return None;
    }
    let mut last = first;
    loop {
        let is_path = match &trees[last] {
            TokenTree::Ident(_) => true,
            TokenTree::Punct(punct) => punct.as_char() == ':',
            _ => false,
        };
        let end = trees[last].span().byte_range().end;
        if !is_path || end > range.end {
            return None;
        }
        if end == range.end {
            break;
        }
        last += 1;
        if last == trees.len() {
            return None;
        }
    }
    match trees.get(last + 1) {
        Some(TokenTree::Group(group))
            if matches!(group.delimiter(), Delimiter::Parenthesis | Delimiter::Brace) =>
        {
            let held = group.span().byte_range();
            arguments
                .iter()
                .any(|argument| held.start < argument.start && argument.end <= held.end)
                .then_some(held.end)
        }
        _ => None,
    }
}

/// One node of `definition.k`.
#[derive(Clone, Debug)]
struct Node {
    kind: SourceMapNodeKind,
    depth: u32,
    range: Range<usize>,
    inserted: bool,
    authored: Option<SourceRange>,
}

/// One rule sentence of `definition.k`, with the table entry that names it.
#[derive(Clone, Debug)]
struct Sentence<'a> {
    range: Range<usize>,
    rule: &'a EmittedRule,
}

/// A rendering of an edited construct in another sentence.
#[derive(Clone, Debug)]
struct Sibling {
    label: String,
    item: Option<String>,
    sentence: SourceMapKey,
    rust: RustSpan,
    k: String,
    changed: bool,
    named_by_krs: bool,
}

impl Sibling {
    fn value(&self) -> Value {
        json!({
            "label": self.label,
            "item": self.item,
            "rust": self.rust.value(),
            "k": self.k,
            "changed": self.changed,
            "named_by_krs": self.named_by_krs,
        })
    }
}

/// An edited construct: a container of an edited sentence, its Rust range and its renderings in
/// other sentences.
#[derive(Clone, Debug)]
struct Construct {
    sentence: SourceMapKey,
    /// The first of the edits it holds, an index of the resolved edits.
    edit: usize,
    rust: RustSpan,
    renderings: Vec<Sibling>,
}

/// One refusal the front end gives a mutation.
#[derive(Clone, Debug)]
struct KrsRefusal {
    reason: &'static str,
    next: &'static str,
    /// The edit it is about, an index of the resolved edits.
    edit: Option<usize>,
    detail: String,
}

/// Everything the front end says of one resolved mutation.
#[derive(Debug, Default)]
struct Judged {
    refusals: Vec<KrsRefusal>,
    warnings: Vec<Finding>,
    edits: Vec<Value>,
    siblings: Option<Vec<Value>>,
}

impl Judged {
    fn refuse(
        &mut self,
        reason: &'static str,
        next: &'static str,
        edit: Option<usize>,
        detail: String,
    ) {
        self.refusals.push(KrsRefusal {
            reason,
            next,
            edit,
            detail,
        });
    }

    fn not_judged(&mut self, edit: Option<usize>, detail: String) {
        self.refuse(NOT_JUDGED, NEXT_NOT_JUDGED, edit, detail);
    }

    /// The row's `krs` value.
    fn value(&self) -> Value {
        let mut value = json!({"edits": self.edits});
        if let Some(siblings) = &self.siblings {
            value["siblings"] = json!(siblings);
        }
        value
    }

    /// The refusals in edit order (a refusal of no edit last), in their order otherwise.
    fn ordered(&self) -> Vec<&KrsRefusal> {
        let mut refusals = self.refusals.iter().collect::<Vec<_>>();
        refusals.sort_by_key(|refusal| refusal.edit.unwrap_or(usize::MAX));
        refusals
    }

    /// The judgement as the judge cache stores it: every refusal and warning with its edit, and
    /// the row's `krs` value. A warning's sentence is not stored: it is the sentence of its edit.
    fn stored(&self) -> Value {
        json!({
            "refusals": self.refusals.iter().map(|refusal| json!({
                "reason": refusal.reason,
                "next": refusal.next,
                "edit": refusal.edit,
                "detail": refusal.detail,
            })).collect::<Vec<_>>(),
            "warnings": self.warnings.iter().map(|warning| json!({
                "reason": warning.reason,
                "edit": warning.edit,
                "detail": warning.detail,
                "next": warning.next,
            })).collect::<Vec<_>>(),
            "edits": self.edits,
            "siblings": self.siblings,
        })
    }

    /// The judgement `stored` holds ([`Self::stored`]) of `resolved`, or `None` when it is not
    /// one this build writes: a reason or next step that is none of the front end's, or an edit
    /// the mutation does not have.
    fn from_stored(stored: &Value, resolved: &ResolvedMutation) -> Option<Self> {
        let edit_at = |edit: usize| {
            resolved
                .edits
                .iter()
                .find(|resolved| resolved.edit == edit)
                .map(|resolved| resolved.at.clone())
        };
        let mut judged = Self::default();
        for refusal in stored.get("refusals")?.as_array()? {
            let reason = refusal_reason(refusal.get("reason")?.as_str()?)?;
            let next = refusal.get("next")?.as_str()?;
            let next = next_steps(reason)
                .into_iter()
                .find(|known| *known == next)?;
            let edit = match refusal.get("edit")? {
                Value::Null => None,
                edit => Some(usize::try_from(edit.as_u64()?).ok()?),
            };
            if edit.is_some_and(|edit| edit >= resolved.edits.len()) {
                return None;
            }
            judged.refuse(
                reason,
                next,
                edit,
                refusal.get("detail")?.as_str()?.to_owned(),
            );
        }
        for warning in stored.get("warnings")?.as_array()? {
            let edit = match warning.get("edit")? {
                Value::Null => None,
                edit => Some(usize::try_from(edit.as_u64()?).ok()?),
            };
            let at = match edit {
                Some(edit) => Some(edit_at(edit)?),
                None => None,
            };
            judged.warnings.push(Finding::warning(
                warning.get("reason")?.as_str()?,
                edit,
                at,
                warning.get("detail")?.as_str()?.to_owned(),
                warning.get("next")?.as_str().map(str::to_owned),
            ));
        }
        judged.edits.clone_from(stored.get("edits")?.as_array()?);
        judged.siblings = match stored.get("siblings")? {
            Value::Null => None,
            siblings => Some(siblings.as_array()?.clone()),
        };
        Some(judged)
    }
}

/// The front end's reason spelled `reason`, borrowed for the life of the program: one of its own
/// reasons, or a code KRS registers.
fn refusal_reason(reason: &str) -> Option<&'static str> {
    [
        GENERATED_ONLY,
        CHANGES_NO_NODE,
        DERIVED_MISMATCH,
        NO_CHANGE,
        NOT_JUDGED,
    ]
    .into_iter()
    .find(|own| *own == reason)
    .or_else(|| krs_diagnostic::codes::static_spelling(reason))
}

/// Every next step the front end gives a refusal for `reason`.
fn next_steps(reason: &'static str) -> Vec<&'static str> {
    match reason {
        GENERATED_ONLY => GENERATED_ONLY_NEXT
            .iter()
            .map(|(_, next)| *next)
            .chain([NEXT_INSERTED])
            .collect(),
        CHANGES_NO_NODE => vec![NEXT_CHANGES_NO_NODE],
        DERIVED_MISMATCH => vec![NEXT_DERIVED_MISMATCH],
        NO_CHANGE => vec![NEXT_NO_CHANGE],
        NOT_JUDGED => vec![NEXT_NOT_JUDGED],
        code => {
            let mut steps = Vec::new();
            for one_item in [false, true] {
                for siblings in [false, true] {
                    let step = krs_next(code, siblings, one_item);
                    if !steps.contains(&step) {
                        steps.push(step);
                    }
                }
            }
            steps
        }
    }
}

/// The format of a judge cache entry; any other is not read.
const JUDGE_CACHE_VERSION: u32 = 1;

/// The directory of the judge cache inside a corpus's cache directory.
pub(crate) const JUDGE_CACHE_DIRECTORY: &str = "krs-judge";

/// The front end's judgements of mutations, stored under the corpus's cache directory so that a
/// mutation is judged once per definition: `check --mutations`, `run`, a `fuzz` kill job and the
/// condition flips read and write the same entries.
///
/// A judgement is a function of what the judge reads, so an entry's key holds each of them: the
/// build that judges (kink-campaign `identity::kink_build`, the running executable's digest,
/// which fixes the judge's code and every message it writes), the emission it judges against
/// (`definition.k` and the source map, whose source identities carry the digest of every
/// authored file the Rust locations are read from), and the mutation as the judge reads it (each
/// resolved edit's file, bytes and replacement, and the mutant's text). The patch digest alone is
/// not the key: two mutations with one patch can differ in how their edits are spelled, which the
/// judgement's Rust locations and refused edits name. An entry whose key differs, which does
/// not decode, or which holds a reason or next step this build does not give, is judged again
/// and rewritten; a build whose identity is unknown reads and writes nothing.
///
/// An entry holds what a judgement of its key gives, so a judgement that could not read an
/// authored source is not written: the key names each file by the digest the build read, and a
/// file on disk that is another revision (edited since the build, or unreadable) leaves the
/// judgement's Rust locations without positions, which the next judgement of the same key, once
/// the file is that revision again, has.
pub(crate) struct JudgeCache {
    directory: std::path::PathBuf,
    /// The build and emission parts of every key; `None` when the build's identity is unknown.
    identity: Option<(String, String)>,
}

impl JudgeCache {
    /// The judge cache of a corpus whose cache directory is `cache`, for judgements against
    /// `emitted`.
    pub(crate) fn new(cache: &std::path::Path, emitted: &EmittedDefinition) -> Self {
        let directory = cache.join(JUDGE_CACHE_DIRECTORY);
        let identity = kink_campaign::identity::kink_build()
            .ok()
            .and_then(|build| {
                let sources = emitted.source_map.to_canonical_json().ok()?;
                let emission = digest_parts(&[emitted.definition.as_bytes(), sources.as_bytes()]);
                Some((build.to_string(), emission))
            });
        Self {
            directory,
            identity,
        }
    }

    /// The key of `resolved`'s judgement, as the file name and the stored key.
    fn key(&self, resolved: &ResolvedMutation) -> Option<(String, Value)> {
        let (build, emission) = self.identity.as_ref()?;
        let edits = resolved
            .edits
            .iter()
            .map(|edit| {
                json!([
                    edit.edit,
                    edit.file,
                    edit.range.start,
                    edit.range.end,
                    edit.replacement
                ])
            })
            .collect::<Vec<_>>();
        let mutant = resolved
            .edited_views
            .iter()
            .map(|(file, text)| json!([file, digest_parts(&[text.as_bytes()])]))
            .collect::<Vec<_>>();
        let key = json!({
            "version": JUDGE_CACHE_VERSION,
            "build": build,
            "emission": emission,
            "edits": edits,
            "mutant": mutant,
        });
        let name = digest_parts(&[key.to_string().as_bytes()]);
        Some((name, key))
    }

    fn read(&self, name: &str, key: &Value, resolved: &ResolvedMutation) -> Option<Judged> {
        let text = std::fs::read_to_string(self.directory.join(format!("{name}.json"))).ok()?;
        let entry = serde_json::from_str::<Value>(&text).ok()?;
        if entry.get("key")? != key {
            return None;
        }
        Judged::from_stored(entry.get("judged")?, resolved)
    }

    /// Store `judged` under `name`, written whole or not at all; a cache that cannot be written
    /// only means the next command judges again.
    fn write(&self, name: &str, key: &Value, judged: &Judged) {
        let entry = json!({"key": key, "judged": judged.stored()});
        let Ok(()) = std::fs::create_dir_all(&self.directory) else {
            return;
        };
        let Ok(mut file) = tempfile::NamedTempFile::new_in(&self.directory) else {
            return;
        };
        if std::io::Write::write_all(&mut file, entry.to_string().as_bytes()).is_ok() {
            _ = file.persist(self.directory.join(format!("{name}.json")));
        }
    }
}

/// The SHA-256 of `parts`, each prefixed by its length so that no two sequences share a digest,
/// in lowercase hexadecimal.
fn digest_parts(parts: &[&[u8]]) -> String {
    use sha2::Digest as _;
    let mut hasher = sha2::Sha256::new();
    for part in parts {
        hasher.update((part.len() as u64).to_le_bytes());
        hasher.update(part);
    }
    hasher
        .finalize()
        .iter()
        .fold(String::with_capacity(64), |mut hex, byte| {
            _ = write!(hex, "{byte:02x}");
            hex
        })
}

/// The emission a command judges mutations against, with the lowering it is emitted from.
pub(crate) struct Baseline<'a> {
    /// The emission, equal to `kink/definition.k`.
    pub(crate) emitted: &'a EmittedDefinition,
    /// The semantic lowering kept in process.
    pub(crate) retained: &'a RetainedLowering,
    /// The Definition IR lowering the K is emitted from.
    pub(crate) lowered: &'a LoweredDefinition,
    /// The selected packages' source roots, for Rust locations.
    pub(crate) sources: &'a DiagnosticSources,
}

/// The front end's checks over one baseline.
pub(crate) struct KrsChecks<'a> {
    emitted: &'a EmittedDefinition,
    checker: Result<MutantChecker<'a>, String>,
    theory: MutantTheory<'a>,
    positions: Positions<'a>,
    /// The nodes of `definition.k`, by key.
    nodes: BTreeMap<SourceMapKey, Node>,
    /// The nodes that render authored syntax, by their exact authored range.
    by_authored: BTreeMap<(SourceFileId, u32, u32), Vec<SourceMapKey>>,
    /// The rule sentences of `definition.k`, by Definition IR key.
    sentences: BTreeMap<SourceMapKey, Sentence<'a>>,
    /// The same sentences by the start of their emitted bytes.
    by_start: BTreeMap<usize, SourceMapKey>,
    /// The rule table by label.
    by_label: BTreeMap<&'a str, &'a EmittedRule>,
    /// The judge cache the judgements are read from and written to, when one is given.
    cache: Option<JudgeCache>,
}

impl<'a> KrsChecks<'a> {
    /// The checks over `baseline`.
    pub(crate) fn new(baseline: &Baseline<'a>) -> Self {
        let emitted = baseline.emitted;
        let checker = Rederivation::new(baseline.retained, baseline.lowered)
            .map_err(|error| error.to_string())
            .and_then(|rederivation| {
                MutantChecker::new(rederivation, &emitted.definition, &emitted.source_map)
                    .map_err(|error| error.to_string())
            });
        let mut nodes = BTreeMap::new();
        let mut by_authored = BTreeMap::<_, Vec<_>>::new();
        for entry in emitted.source_map.entries() {
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
            let authored = entry.origin().exact_authored_range();
            let inserted = entry.inserted().is_some();
            if let Some(range) = &authored
                && !inserted
            {
                by_authored
                    .entry((range.file.clone(), range.start_byte, range.end_byte))
                    .or_default()
                    .push(entry.key().clone());
            }
            nodes.insert(
                entry.key().clone(),
                Node {
                    kind: entry.node_kind(),
                    depth: entry.depth(),
                    range: start..end,
                    inserted,
                    authored,
                },
            );
        }
        // The rule table lists the Definition IR's rule sentences in their order.
        let keys = baseline
            .lowered
            .definition()
            .modules()
            .iter()
            .flat_map(krs_ir_levels::DefinitionModule::sentences)
            .filter(|sentence| matches!(sentence, krs_ir_levels::DefinitionSentence::Rule(_)))
            .map(|sentence| sentence.origin().key().clone());
        let sentences = keys
            .zip(&emitted.rules)
            .filter_map(|(key, rule)| {
                let range = nodes.get(&key)?.range.clone();
                Some((key, Sentence { range, rule }))
            })
            .collect::<BTreeMap<_, _>>();
        let by_start = sentences
            .iter()
            .map(|(key, sentence)| (sentence.range.start, key.clone()))
            .collect();
        Self {
            emitted,
            checker,
            theory: MutantTheory::new(baseline.retained),
            positions: Positions {
                sources: baseline.sources,
                files: RefCell::new(BTreeMap::new()),
                unread: Cell::new(0),
            },
            nodes,
            by_authored,
            sentences,
            by_start,
            by_label: emitted
                .rules
                .iter()
                .map(|rule| (rule.label.as_str(), rule))
                .collect(),
            cache: None,
        }
    }

    /// The emitted bytes and depth of the Definition IR node `key` in `definition.k`.
    pub(crate) fn node(&self, key: &SourceMapKey) -> Option<(Range<usize>, u32)> {
        self.nodes
            .get(key)
            .map(|node| (node.range.clone(), node.depth))
    }

    /// The emitted bytes and the rule table entry of the Definition IR rule sentence `key`.
    pub(crate) fn sentence(&self, key: &SourceMapKey) -> Option<(Range<usize>, &'a EmittedRule)> {
        self.sentences
            .get(key)
            .map(|sentence| (sentence.range.clone(), sentence.rule))
    }

    /// The distinct ranges of the nodes inside the sentence bytes `sentence` that hold the bytes
    /// `range`, innermost first.
    pub(crate) fn enclosing(
        &self,
        sentence: &Range<usize>,
        range: &Range<usize>,
    ) -> Vec<Range<usize>> {
        let mut holding = self
            .nodes
            .values()
            .filter(|node| {
                sentence.start <= node.range.start
                    && node.range.end <= sentence.end
                    && node.range.start <= range.start
                    && range.end <= node.range.end
            })
            .map(|node| node.range.clone())
            .collect::<Vec<_>>();
        holding.sort_by_key(|node| (node.len(), std::cmp::Reverse(node.start)));
        holding.dedup();
        holding
    }

    /// The bytes of the node of the sentence bytes `sentence` directly above the node at
    /// `range`: the innermost node that strictly holds it.
    pub(crate) fn parent(
        &self,
        sentence: &Range<usize>,
        range: &Range<usize>,
    ) -> Option<Range<usize>> {
        self.enclosing(sentence, range)
            .into_iter()
            .find(|node| node != range)
    }

    /// The checks, reading and writing their judgements in the judge cache of the corpus cache
    /// directory `cache` ([`JudgeCache`]).
    pub(crate) fn with_cache(mut self, cache: &std::path::Path) -> Self {
        self.cache = Some(JudgeCache::new(cache, self.emitted));
        self
    }

    /// `check --mutations`: add each resolved row's findings and its `krs` value.
    pub(crate) fn annotate_check(&self, check: &mut FlowCheck) {
        for row in &mut check.rows {
            let Ok(resolved) = &row.resolution else {
                continue;
            };
            let judged = self.judge(resolved);
            for refusal in judged.ordered() {
                row.findings.push(Finding::refused(
                    refusal.reason,
                    refusal.edit.map(|index| resolved.edits[index].edit),
                    refusal.edit.map(|index| resolved.edits[index].at.clone()),
                    refusal.detail.clone(),
                    Some(refusal.next.to_owned()),
                ));
            }
            row.findings.extend(judged.warnings.iter().cloned());
            row.extra.insert("krs".into(), judged.value());
        }
    }

    /// `run` and a `fuzz` kill job: the mutations of `list` that `run` runs and the front end
    /// refuses, by id, each with its first refusal by edit order. A mutation that does not
    /// resolve is left to kink-flow, which refuses it with its own reason.
    ///
    /// Only the mutations the command runs are judged: a refusal decides only what a mutation
    /// runs, and each judgement runs KRS's admission checks on a whole theory, which `run --only`
    /// and a kill job, the inner loop of fixing one mutation, would otherwise repeat for every
    /// mutation of the list. kink-flow counts what every mutation of the list targets in the run's
    /// `untargeted_rules` by its own resolution, whether the front end judged or refused it, so
    /// the list does not depend on which mutations are judged.
    pub(crate) fn refusals(
        &self,
        manifest: &FlowManifest,
        list: &MutationList,
        run: &RunList<'_>,
    ) -> BTreeMap<String, InvalidMutation> {
        let source = kink_flow::admit::corpus_source(manifest);
        let Ok(loaded) = kink_corpus::resolver::load_source(&source) else {
            // kink-flow refuses a specification it cannot load, for every mutation.
            return BTreeMap::new();
        };
        list.mutations
            .iter()
            .filter(|mutation| run.runs(&mutation.id))
            .filter_map(|mutation| {
                let resolved = kink_flow::resolve(manifest, &loaded, mutation).ok()?;
                Some((mutation.id.clone(), self.refusal(&resolved)?))
            })
            .collect()
    }

    /// The front end's first refusal of `resolved`, by edit order, as a run gives it: its
    /// reason, next step and detail, the detail counting the other refusals; `None` when the
    /// front end admits the mutation. Like the judgement, the refusal is a function of the
    /// definition and the mutation: it names `check` by its verb alone, never by a command line
    /// that would carry the checkout's paths.
    pub(crate) fn refusal(&self, resolved: &ResolvedMutation) -> Option<InvalidMutation> {
        let judged = self.judge(resolved);
        let ordered = judged.ordered();
        let first = ordered.first()?;
        let more = ordered.len() - 1;
        let detail = if more == 0 {
            first.detail.clone()
        } else {
            let edits = if more == 1 { "edit" } else { "edits" };
            format!(
                "{} (and {more} more refused {edits}, which `krs kink check` reports)",
                first.detail
            )
        };
        Some(InvalidMutation {
            edit: first.edit.map(|index| resolved.edits[index].edit),
            reason: InvalidReason::External {
                name: first.reason,
                next: first.next,
            },
            detail,
        })
    }

    /// The Rust construct the node `key` renders, whose authored range is `authored`
    /// ([`Positions::span`]); `None` names no emitted node, so `authored` is its own construct.
    fn rust(&self, key: Option<&SourceMapKey>, authored: &SourceRange) -> RustSpan {
        let arguments = key
            .map(|key| self.arguments(key, authored))
            .unwrap_or_default();
        self.positions.span(authored, &arguments)
    }

    /// The authored ranges, in `authored`'s file, of the nodes KRS did not insert below the node
    /// `key` in `definition.k`: an application's arguments and their subterms, and nothing for a
    /// variable or a token, which the emitted K renders with no node below it.
    fn arguments(&self, key: &SourceMapKey, authored: &SourceRange) -> Vec<Range<usize>> {
        let Some(node) = self.nodes.get(key) else {
            return Vec::new();
        };
        self.nodes
            .values()
            .filter(|below| {
                below.depth > node.depth
                    && !below.inserted
                    && node.range.start <= below.range.start
                    && below.range.end <= node.range.end
            })
            .filter_map(|below| below.authored.as_ref())
            .filter(|range| range.file == authored.file)
            .filter_map(|range| {
                Some(
                    usize::try_from(range.start_byte).ok()?
                        ..usize::try_from(range.end_byte).ok()?,
                )
            })
            .collect()
    }

    /// The sentence `key` as a detail names it: `label (item, file:line)`.
    fn describe(&self, key: &SourceMapKey) -> String {
        self.sentences
            .get(key)
            .map_or_else(|| key.to_string(), |sentence| describe_rule(sentence.rule))
    }

    /// The table entry of a K label, written bare or module-qualified.
    fn rule_labelled(&self, label: &str) -> Option<&'a EmittedRule> {
        let bare = label.rsplit_once('.').map_or(label, |(_, bare)| bare);
        self.by_label
            .get(label)
            .or_else(|| self.by_label.get(bare))
            .copied()
    }

    /// The table entry of the rule edit `index` is addressed to.
    fn rule_of(&self, resolved: &ResolvedMutation, index: usize) -> Option<&'a EmittedRule> {
        let at = &resolved.edits.get(index)?.at;
        let label = resolved
            .rules
            .iter()
            .find(|rule| &rule.at == at)?
            .label
            .as_deref()?;
        self.rule_labelled(label)
    }

    /// The K text of `range` in `definition.k`, quoted.
    fn k_text(&self, range: &Range<usize>) -> String {
        quote(
            self.emitted
                .definition
                .get(range.clone())
                .unwrap_or_default(),
        )
    }

    /// Everything the front end says of `resolved`, from the judge cache when it holds the
    /// judgement ([`JudgeCache`]).
    fn judge(&self, resolved: &ResolvedMutation) -> Judged {
        let Some((cache, (name, key))) = self
            .cache
            .as_ref()
            .and_then(|cache| Some((cache, cache.key(resolved)?)))
        else {
            return self.judge_fresh(resolved);
        };
        if let Some(judged) = cache.read(&name, &key, resolved) {
            return judged;
        }
        let unread = self.positions.unread.get();
        let judged = self.judge_fresh(resolved);
        // A judgement that could not read an authored source lacks positions the key does not
        // account for; it is this command's answer, not the one its key stands for.
        if self.positions.unread.get() == unread {
            cache.write(&name, &key, &judged);
        }
        judged
    }

    /// Everything the front end says of `resolved`, judged now.
    fn judge_fresh(&self, resolved: &ResolvedMutation) -> Judged {
        let mut judged = Judged::default();
        self.claim_helpers(resolved, &mut judged);
        // Every path that judges nothing still names each edit's rule, by its item.
        judged.edits = self.locations(resolved, None);
        if let Some((index, edit)) = resolved
            .edits
            .iter()
            .enumerate()
            .find(|(_, edit)| edit.file != DEFINITION_FILE)
        {
            judged.not_judged(
                Some(index),
                format!(
                    "edit[{}] is addressed to {}; the krs front end judges edits of \
                     {DEFINITION_FILE}, which KRS emits",
                    edit.edit, edit.file
                ),
            );
            return judged;
        }
        let edits = resolved
            .edits
            .iter()
            .map(|edit| {
                KEdit::new(
                    edit.range.clone(),
                    edit.replacement.as_deref().unwrap_or(""),
                )
            })
            .collect::<Vec<_>>();
        let checker = match &self.checker {
            Ok(checker) => checker,
            Err(message) => {
                judged.not_judged(
                    None,
                    format!(
                        "the krs front end cannot read the emission it judges against: {message}"
                    ),
                );
                return judged;
            }
        };
        let check = match checker.check(&edits) {
            Ok(check) => check,
            Err(error) => {
                judged.not_judged(
                    None,
                    format!("the edits do not apply to the emitted K: {error}"),
                );
                return judged;
            }
        };
        if resolved.edited_views.get(DEFINITION_FILE) != Some(&check.judgement.mutant) {
            judged.not_judged(
                None,
                format!(
                    "the mutant kink-flow resolved differs from the emitted K with the same edits \
                     applied, so {DEFINITION_FILE} is not this emission"
                ),
            );
            return judged;
        }
        let changed = edits
            .iter()
            .map(|edit| changed_range(&self.emitted.definition, edit))
            .collect::<Vec<_>>();
        let constructs = self.constructs(&check, &changed);
        judged.edits = self.locations(resolved, Some(&check));
        self.partial_renderings(resolved, &constructs, &mut judged);
        match check.judgement.verdict() {
            MutationVerdict::ChangesNoNode => judged.refuse(
                CHANGES_NO_NODE,
                NEXT_CHANGES_NO_NODE,
                (!resolved.edits.is_empty()).then_some(0),
                "the mutant's tokens are the specification's: K reads the same sentences from \
                 both texts"
                    .into(),
            ),
            MutationVerdict::NeedsRederivation => {
                self.rederivation(&check, &constructs, &mut judged);
            }
            _ => self.judge_refusals(&check, &mut judged),
        }
        judged
    }

    /// The judge's refusals: of changes outside every sentence and of each refused sentence.
    fn judge_refusals(&self, check: &MutationCheck, judged: &mut Judged) {
        for outside in &check.judgement.outside {
            judged.not_judged(
                outside.edits.first().copied(),
                format!(
                    "the edit changes `{}`, tokens no rule sentence holds (module syntax, or where \
                     a sentence starts or ends)",
                    self.k_text(&outside.changed)
                ),
            );
        }
        for sentence in &check.judgement.sentences {
            self.judge_refusal(sentence, judged);
        }
    }

    fn judge_refusal(&self, sentence: &SentenceJudgement, judged: &mut Judged) {
        let edit = sentence.edits.first().copied();
        let named = self.describe(&sentence.sentence);
        let nodes = |nodes: &[InsertedNodeRef]| {
            nodes
                .iter()
                .map(|node| self.inserted(node))
                .collect::<Vec<_>>()
                .join("; ")
        };
        match &sentence.verdict {
            SentenceVerdict::InsertedOnly { nodes: inserted } => {
                let kind = inserted
                    .first()
                    .map_or(InsertedNode::DefinednessTest, |node| node.kind);
                judged.refuse(
                    GENERATED_ONLY,
                    generated_only_next(kind),
                    edit,
                    format!("{named}: the edit changes only {}", nodes(inserted)),
                );
            }
            SentenceVerdict::CrossesInserted { nodes: inserted } => judged.not_judged(
                edit,
                format!(
                    "{named}: the edit changes authored syntax and cuts through {}, so that node's \
                     extent in the mutant is undefined; edit it whole, or leave it",
                    nodes(inserted)
                ),
            ),
            SentenceVerdict::FamilyNotJudged { nodes: family } => judged.not_judged(
                edit,
                format!(
                    "{named}: the edit reaches {}, whose derivation reads more than the edited \
                     construct",
                    nodes(family)
                ),
            ),
            SentenceVerdict::NotARule => judged.not_judged(
                edit,
                format!(
                    "{named}: the edit changes a declaration, which changes what every rule means"
                ),
            ),
            _ => {}
        }
    }

    /// An inserted node as a detail names it: its K text, its kind, and the authored node to edit
    /// instead.
    fn inserted(&self, node: &InsertedNodeRef) -> String {
        let mut text = format!(
            "`{}`, a {} KRS inserts",
            self.k_text(&node.emitted),
            node.kind.as_str().replace('_', " ")
        );
        if let Some(authored) = &node.nearest_authored {
            text.push_str("; the authored node it comes from is ");
            match &authored.emitted {
                Some(range) => _ = write!(text, "`{}`", self.k_text(range)),
                None => text.push_str("not rendered in this sentence"),
            }
            if let Some(source) = &authored.source {
                _ = write!(
                    text,
                    " at {}",
                    self.rust(authored.key.as_ref(), source).described()
                );
            }
        }
        text
    }

    /// The first edit of the judged sentence `key`.
    fn first_edit(check: &MutationCheck, key: &SourceMapKey) -> Option<usize> {
        check
            .judgement
            .sentences
            .iter()
            .find(|sentence| &sentence.sentence == key)
            .and_then(|sentence| sentence.edits.first().copied())
    }

    /// The re-derivation's refusals, then, when it accepts every sentence, the theory check.
    fn rederivation(&self, check: &MutationCheck, constructs: &[Construct], judged: &mut Judged) {
        for sentence in &check.sentences {
            let Err(refusal) = &sentence.outcome else {
                continue;
            };
            let edit = Self::first_edit(check, &sentence.sentence);
            let named = self.describe(&sentence.sentence);
            match refusal {
                Refusal::DerivedMismatch { .. } => judged.refuse(
                    DERIVED_MISMATCH,
                    NEXT_DERIVED_MISMATCH,
                    edit,
                    format!("{named}: {refusal}"),
                ),
                // A registered code is the refusal's reason, which the row states beside the
                // detail; only a code that is no reason is written in the detail.
                Refusal::Krs(_) => {
                    let code = refusal.krs_code().unwrap_or_default();
                    let at =
                        format!("KRS refuses the Rust source this mutation stands for, at {named}");
                    match krs_diagnostic::codes::static_spelling(&code) {
                        Some(code) => judged.refuse(
                            code,
                            // A sentence's own re-derivation refusal names no items.
                            krs_next(code, false, false),
                            edit,
                            format!("{at}: {refusal}"),
                        ),
                        None => judged.not_judged(edit, format!("{at}: {code}: {refusal}")),
                    }
                }
                _ => judged.not_judged(edit, format!("{named}: {refusal}")),
            }
        }
        if !judged.refusals.is_empty() {
            return;
        }
        let first = check
            .judgement
            .sentences
            .first()
            .and_then(|sentence| sentence.edits.first().copied());
        if check.unchanged() {
            judged.refuse(
                NO_CHANGE,
                NEXT_NO_CHANGE,
                first,
                "every edited sentence is the specification's up to a renaming of variables and \
                 brackets, so the mutant is the specification"
                    .into(),
            );
            return;
        }
        self.theory_check(check, first, constructs, judged);
    }

    /// KRS's rule-level admission checks on the theory the mutation's source lowers to.
    fn theory_check(
        &self,
        check: &MutationCheck,
        first: Option<usize>,
        constructs: &[Construct],
        judged: &mut Judged,
    ) {
        let Ok(checker) = &self.checker else {
            return;
        };
        let rederivation = checker.rederivation();
        let mut changes = TheoryChanges::default();
        let mut deleted = BTreeSet::new();
        for sentence in &check.sentences {
            let Ok(accepted) = &sentence.outcome else {
                continue;
            };
            if accepted.pre_derivation.is_none() && !accepted.deleted {
                // A raw_k! sentence: the author's K, which KRS's checks do not read.
                continue;
            }
            let site = match rederivation.site(&sentence.sentence) {
                Ok(site) => site,
                Err(error) => {
                    judged.not_judged(
                        first,
                        format!("{}: {error}", self.describe(&sentence.sentence)),
                    );
                    return;
                }
            };
            let key = rule_sentence_key(site.pre_derivation).clone();
            if accepted.deleted {
                changes.deleted.insert(key);
                deleted.insert(sentence.sentence.clone());
            } else if let Some(rule) = &accepted.pre_derivation {
                changes.replaced.insert(key, rule.clone());
            }
        }
        if changes.is_empty() {
            return;
        }
        let refusal = match self.theory.check(&changes) {
            Ok(Ok(())) => return,
            Ok(Err(refusal)) => refusal,
            Err(error) => {
                judged.not_judged(
                    first,
                    format!("KRS's admission checks are not run on this mutant: {error}"),
                );
                return;
            }
        };
        let named = self.named_sentences(&refusal, rederivation);
        let edited = check
            .judgement
            .sentences
            .iter()
            .map(|sentence| sentence.sentence.clone())
            .collect::<BTreeSet<_>>();
        let mut siblings = constructs
            .iter()
            .flat_map(|construct| construct.renderings.iter().cloned())
            .map(|mut sibling| {
                sibling.named_by_krs = named.contains(&sibling.sentence);
                sibling
            })
            .collect::<Vec<_>>();
        siblings.sort_by_key(|sibling| !sibling.named_by_krs);
        judged.siblings = Some(siblings.iter().map(Sibling::value).collect());
        let detail = self.theory_detail(&refusal, &named, &edited, &deleted, &siblings);
        // The detail lists the renderings the mutation leaves unchanged as its siblings.
        let listed = siblings.iter().any(|sibling| !sibling.changed);
        let one_item = refusal.items.len() == 1;
        judged.refuse(
            refusal.code,
            krs_next(refusal.code, listed, one_item),
            first,
            detail,
        );
    }

    /// The detail of KRS's refusal of the mutation's source: its message (its code is the row's
    /// reason), the sentences it names, and the renderings of the edited constructs the mutation
    /// leaves.
    fn theory_detail(
        &self,
        refusal: &TheoryRefusal,
        named: &[SourceMapKey],
        edited: &BTreeSet<SourceMapKey>,
        deleted: &BTreeSet<SourceMapKey>,
        siblings: &[Sibling],
    ) -> String {
        let mut detail = format!(
            "KRS refuses the Rust source this mutation stands for: {}. Sentences: {}",
            refusal.message.trim_end_matches('.'),
            named
                .iter()
                .map(|key| format!(
                    "{}, {}",
                    self.describe(key),
                    if deleted.contains(key) {
                        "deleted"
                    } else if edited.contains(key) {
                        "edited"
                    } else {
                        "not edited"
                    }
                ))
                .collect::<Vec<_>>()
                .join("; ")
        );
        // `siblings` holds those of the named sentences first.
        let unchanged = siblings
            .iter()
            .filter(|sibling| !sibling.changed)
            .collect::<Vec<_>>();
        if !unchanged.is_empty() {
            let shown = unchanged
                .iter()
                .take(8)
                .map(|sibling| {
                    format!(
                        "`{}` in `{}` ({}, rendered `{}`)",
                        sibling.rust.text.as_deref().unwrap_or("?"),
                        sibling.label,
                        sibling.rust.at(),
                        sibling.k
                    )
                })
                .collect::<Vec<_>>()
                .join("; ");
            _ = write!(
                detail,
                ". Siblings an author's Rust edit would also change: {shown}"
            );
            if unchanged.len() > 8 {
                _ = write!(
                    detail,
                    " and {} more (the row's krs.siblings)",
                    unchanged.len() - 8
                );
            }
        }
        // A rendering in a named sentence, changed or not, is one an author's Rust edit of the
        // construct reaches; with none, that edit leaves the named sentences as the mutant has
        // them.
        if !siblings.iter().any(|sibling| sibling.named_by_krs) {
            detail.push_str(
                ". No sentence KRS names holds another rendering of a construct this mutation \
                 edits, so no Rust edit of these constructs avoids the refusal by itself",
            );
        }
        let others = |keys: &mut dyn Iterator<Item = &SourceMapKey>| {
            keys.map(|key| self.describe(key))
                .collect::<Vec<_>>()
                .join("; ")
        };
        if !named.is_empty() && named.iter().all(|key| !edited.contains(key)) {
            if deleted.is_empty() {
                _ = write!(
                    detail,
                    ". None of the sentences KRS names is edited: KRS judges them by what the \
                     edited sentences ({}) change, such as an equation a rule's condition or \
                     result reads",
                    others(&mut edited.iter())
                );
            } else {
                _ = write!(
                    detail,
                    ". None of the sentences KRS names is edited: the mutation deletes {}",
                    others(&mut deleted.iter())
                );
            }
        }
        detail
    }

    /// The Definition IR sentences KRS's refusal names, in its order.
    fn named_sentences(
        &self,
        refusal: &TheoryRefusal,
        rederivation: &Rederivation<'_>,
    ) -> Vec<SourceMapKey> {
        let mut named = Vec::new();
        for semantic in &refusal.sentences {
            for key in rederivation.definition_keys(semantic) {
                if self.sentences.contains_key(key) && !named.contains(key) {
                    named.push(key.clone());
                }
            }
        }
        named
    }

    /// The edited constructs of the sentences the judge hands on: each container, with its Rust
    /// range and its renderings in other sentences.
    fn constructs(&self, check: &MutationCheck, changed: &[Range<usize>]) -> Vec<Construct> {
        check
            .judgement
            .sentences
            .iter()
            .filter_map(|sentence| match &sentence.verdict {
                SentenceVerdict::NeedsRederivation { containers } => Some(containers),
                _ => None,
            })
            .flatten()
            .filter_map(|container| self.construct(container, changed))
            .collect()
    }

    fn construct(&self, container: &EditContainer, changed: &[Range<usize>]) -> Option<Construct> {
        let node = self.nodes.get(&container.key)?;
        if node.kind == SourceMapNodeKind::Rule {
            // The whole sentence: no other sentence renders it.
            return None;
        }
        let authored = node.authored.as_ref()?;
        let own = self.sentence_of(&node.range)?;
        let mut outermost = BTreeMap::<SourceMapKey, &Node>::new();
        for key in self
            .by_authored
            .get(&(
                authored.file.clone(),
                authored.start_byte,
                authored.end_byte,
            ))
            .into_iter()
            .flatten()
        {
            let Some(rendering) = self.nodes.get(key) else {
                continue;
            };
            if rendering.inserted
                || matches!(
                    rendering.kind,
                    SourceMapNodeKind::Rule | SourceMapNodeKind::Module
                )
            {
                continue;
            }
            let Some(holder) = self.sentence_of(&rendering.range) else {
                continue;
            };
            if holder == own {
                continue;
            }
            outermost
                .entry(holder)
                .and_modify(|kept| {
                    if rendering.depth < kept.depth {
                        *kept = rendering;
                    }
                })
                .or_insert(rendering);
        }
        let rust = self.rust(Some(&container.key), authored);
        let renderings = outermost
            .into_iter()
            .map(|(holder, rendering)| {
                let rule = self.sentences.get(&holder).map(|sentence| sentence.rule);
                Sibling {
                    label: rule.map_or_else(|| holder.to_string(), |rule| rule.label.clone()),
                    item: rule.and_then(|rule| rule.item.clone()),
                    sentence: holder,
                    rust: rust.clone(),
                    k: self.k_text(&rendering.range),
                    changed: changed.iter().any(|range| touches(range, &rendering.range)),
                    named_by_krs: false,
                }
            })
            .collect();
        Some(Construct {
            sentence: own,
            edit: container.edits.first().copied().unwrap_or(0),
            rust,
            renderings,
        })
    }

    /// The rule sentence whose emitted bytes hold `range`.
    fn sentence_of(&self, range: &Range<usize>) -> Option<SourceMapKey> {
        let (_, key) = self.by_start.range(..=range.start).next_back()?;
        let sentence = self.sentences.get(key)?;
        (range.end <= sentence.range.end).then(|| key.clone())
    }

    /// One `partial-rendering` warning per edited construct with a rendering the mutation leaves.
    fn partial_renderings(
        &self,
        resolved: &ResolvedMutation,
        constructs: &[Construct],
        judged: &mut Judged,
    ) {
        for construct in constructs {
            let unchanged = construct
                .renderings
                .iter()
                .filter(|sibling| !sibling.changed)
                .map(|sibling| format!("`{}`", sibling.label))
                .collect::<Vec<_>>();
            if unchanged.is_empty() {
                continue;
            }
            let label = self.sentences.get(&construct.sentence).map_or_else(
                || construct.sentence.to_string(),
                |sentence| sentence.rule.label.clone(),
            );
            let edit = resolved.edits.get(construct.edit);
            judged.warnings.push(Finding::warning(
                PARTIAL_RENDERING,
                edit.map(|edit| edit.edit),
                edit.map(|edit| edit.at.clone()),
                format!(
                    "`{}` at {} is rendered in {} other sentences ({}); this mutation changes it \
                     in `{label}` and leaves it in {}",
                    construct.rust.text.as_deref().unwrap_or("?"),
                    construct.rust.at(),
                    construct.renderings.len(),
                    construct
                        .renderings
                        .iter()
                        .map(|sibling| format!("`{}`", sibling.label))
                        .collect::<Vec<_>>()
                        .join(", "),
                    unchanged.join(", ")
                ),
                Some(NEXT_PARTIAL_RENDERING.to_owned()),
            ));
        }
    }

    /// One `claim-helper` warning per edited equation of a function only claims apply.
    fn claim_helpers(&self, resolved: &ResolvedMutation, judged: &mut Judged) {
        for rule in &resolved.rules {
            let Some(emitted) = rule
                .label
                .as_deref()
                .and_then(|label| self.rule_labelled(label))
            else {
                continue;
            };
            if !emitted.claim_helper {
                continue;
            }
            // The function is named as a stop reads its item, and as the `// KRS` line writes
            // it beside that, since the item's name is the expansion's (`crate::expected` for
            // `Expected`).
            let function = match (&emitted.item, &emitted.source_item) {
                (Some(item), Some(source)) => format!("`{item}` (`{source}`)"),
                (Some(name), None) | (None, Some(name)) => format!("`{name}`"),
                (None, None) => "`?`".to_owned(),
            };
            judged.warnings.push(Finding::warning(
                CLAIM_HELPER,
                rule.edits.first().copied(),
                Some(rule.at.clone()),
                format!(
                    "`{}` is an equation of {function}, which only claims apply (claim helper): \
                     no program of the corpus reaches it",
                    emitted.label,
                ),
                Some(NEXT_CLAIM_HELPER.to_owned()),
            ));
        }
    }

    /// The Rust location of each edit (`krs.edits`): what the judge's `check` found it changes,
    /// or, with no judgement, its rule's item (`not-judged`).
    fn locations(&self, resolved: &ResolvedMutation, check: Option<&MutationCheck>) -> Vec<Value> {
        resolved
            .edits
            .iter()
            .enumerate()
            .map(|(index, edit)| {
                let holder = check.and_then(|check| {
                    check
                        .judgement
                        .sentences
                        .iter()
                        .find(|sentence| sentence.edits.contains(&index))
                });
                let rule = holder
                    .and_then(|sentence| self.sentences.get(&sentence.sentence))
                    .map(|sentence| sentence.rule)
                    .or_else(|| self.rule_of(resolved, index));
                let item_span = || {
                    rule.and_then(|rule| {
                        Some(json!({
                            "file": rule.file.clone()?,
                            "line": rule.line,
                            "column": rule.column,
                            "end_line": null,
                            "end_column": null,
                            "text": null,
                        }))
                    })
                    .into_iter()
                    .collect::<Vec<_>>()
                };
                let (judged, rust) = match holder.map(|sentence| &sentence.verdict) {
                    _ if edit.replacement.is_none() => ("deleted", item_span()),
                    _ if check.is_none() => ("not-judged", item_span()),
                    Some(SentenceVerdict::NeedsRederivation { containers }) => (
                        "authored",
                        containers
                            .iter()
                            .filter(|container| container.edits.contains(&index))
                            .filter_map(|container| {
                                let range = self.nodes.get(&container.key)?.authored.as_ref()?;
                                Some(self.rust(Some(&container.key), range).value())
                            })
                            .collect(),
                    ),
                    Some(
                        SentenceVerdict::InsertedOnly { nodes }
                        | SentenceVerdict::CrossesInserted { nodes }
                        | SentenceVerdict::FamilyNotJudged { nodes },
                    ) => (
                        "inserted",
                        nodes
                            .iter()
                            .filter_map(|node| {
                                let authored = node.nearest_authored.as_ref()?;
                                let range = authored.source.as_ref()?;
                                Some(self.rust(authored.key.as_ref(), range).value())
                            })
                            .collect(),
                    ),
                    _ => ("no-node", item_span()),
                };
                json!({
                    "edit": edit.edit,
                    "label": rule.map(|rule| rule.label.clone()),
                    "item": rule.and_then(|rule| rule.item.clone()),
                    "judged": judged,
                    "rust": rust,
                })
            })
            .collect()
    }
}

/// A table entry as a detail names it: `label (item, file:line)`.
fn describe_rule(rule: &EmittedRule) -> String {
    let mut place = Vec::new();
    if let Some(item) = &rule.item {
        place.push(item.clone());
    }
    match (&rule.file, rule.line) {
        (Some(file), Some(line)) => place.push(format!("{file}:{line}")),
        (Some(file), None) => place.push(file.clone()),
        _ => {}
    }
    if place.is_empty() {
        format!("`{}`", rule.label)
    } else {
        format!("`{}` ({})", rule.label, place.join(", "))
    }
}

/// The mutation list a `run` or a `fuzz` kill job reads, and which of its mutations it runs.
pub(crate) struct RunList<'c> {
    /// The list's path.
    pub(crate) path: &'c std::path::Path,
    /// The ids of the mutations the command runs; every mutation of the list when empty.
    only: &'c [String],
}

impl RunList<'_> {
    /// Whether the command runs the mutation `id`.
    fn runs(&self, id: &str) -> bool {
        self.only.is_empty() || self.only.iter().any(|only| only == id)
    }
}

/// The mutation list `command` reads for `run` (the mutations `--only` names, or all), a `fuzz`
/// kill job (the one mutation it kills) or `prune` (all, where it has a list).
pub(crate) fn run_list(command: &kink_flow::FlowCommand) -> Option<RunList<'_>> {
    match command {
        kink_flow::FlowCommand::Run {
            mutations, options, ..
        } => Some(RunList {
            path: mutations.as_path(),
            only: &options.only,
        }),
        kink_flow::FlowCommand::Prune {
            mutations: Some(mutations),
            ..
        } => Some(RunList {
            path: mutations.as_path(),
            only: &[],
        }),
        kink_flow::FlowCommand::Fuzz { request, .. } => match &request.job {
            kink_flow::cli::FuzzJobRequest::Kill {
                mutation,
                mutations,
            } => Some(RunList {
                path: mutations.as_path(),
                only: std::slice::from_ref(mutation),
            }),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use krs_diagnostic::codes::static_spelling;

    use super::{KEdit, changed_range, construct_end, krs_next, quote, touches};

    #[test]
    fn a_changed_range_drops_the_common_prefix_and_suffix() {
        let source = "rule plus(N, zero) => N:Nat";
        let start = source.find("N:Nat").unwrap();
        let edit = KEdit::new(start..start + 5, "zero");
        assert_eq!(&source[changed_range(source, &edit)], "N:Nat");
        let edit = KEdit::new(start..start + 5, "N:Nat ");
        assert_eq!(changed_range(source, &edit), start + 5..start + 5);
    }

    #[test]
    fn an_insertion_touches_the_node_it_lies_inside() {
        assert!(touches(&(3..3), &(1..5)));
        assert!(!touches(&(5..5), &(1..5)));
        assert!(touches(&(4..6), &(1..5)));
        assert!(!touches(&(5..6), &(1..5)));
    }

    /// An application's head path extends through the argument group written after it, in a
    /// Rust expression and inside a term macro, when K places its arguments there; any other
    /// range is its own construct, including a variable K renders with no node below it that is
    /// followed by a block, as an `if` condition's operand and a `match` scrutinee are.
    #[test]
    fn an_application_head_extends_through_its_arguments() {
        let source = "fn plus_succ(k::term![Plus(NatSyntax::Succ(m), n)]: Term<Nat>) -> Term<Nat> {\n    \
                      NatSyntax::Succ(Plus(m, n))\n}\n\
                      fn below(value: Term<Int>, limit: Term<Int>) -> Term<Int> {\n    \
                      if value < limit { value } else { limit }\n}\n\
                      fn zero(value: Term<Int>) -> Term<Int> {\n    \
                      match value { 0 => 1, _ => value }\n}\n";
        let tokens = source.parse().unwrap();
        // `len` bytes at `offset` into the `nth` occurrence of `text`.
        let inside = |text: &str, nth: usize, offset: usize, len: usize| {
            let start = source.match_indices(text).nth(nth).unwrap().0 + offset;
            start..start + len
        };
        let at = |text: &str, nth: usize| inside(text, nth, 0, text.len());
        let construct = |range: std::ops::Range<usize>, arguments: &[std::ops::Range<usize>]| {
            let end = construct_end(&tokens, &range, arguments).unwrap_or(range.end);
            &source[range.start..end]
        };
        // Applications, with the arguments K's nodes below them place in the group.
        assert_eq!(
            construct(
                at("Plus", 0),
                &[at("NatSyntax::Succ", 0), inside("), n)", 0, 3, 1)]
            ),
            "Plus(NatSyntax::Succ(m), n)"
        );
        assert_eq!(
            construct(at("NatSyntax::Succ", 0), &[inside("Succ(m)", 0, 5, 1)]),
            "NatSyntax::Succ(m)"
        );
        assert_eq!(
            construct(at("NatSyntax::Succ", 1), &[at("Plus", 1)]),
            "NatSyntax::Succ(Plus(m, n))"
        );
        let arguments = [inside("Plus(m, n)", 0, 5, 1), inside("Plus(m, n)", 0, 8, 1)];
        assert_eq!(construct(at("Plus", 1), &arguments), "Plus(m, n)");
        // An `if` condition's operand and a `match` scrutinee are variables, with no node below
        // them in K, so the block written after them is not theirs.
        let limit = inside("limit {", 0, 0, "limit".len());
        assert_eq!(construct(limit.clone(), &[]), "limit");
        let value = inside("match value {", 0, "match ".len(), "value".len());
        assert_eq!(construct(value, &[]), "value");
        // Nor is a group that holds none of the node's arguments.
        assert_eq!(construct_end(&tokens, &limit, &[at("value", 0)]), None);
        // A reference, a part of a path and a type path followed by no group are their own.
        let reference = arguments[0].clone();
        assert_eq!(construct_end(&tokens, &reference, &arguments), None);
        let succ = inside("Succ(m)", 0, 0, "Succ".len());
        assert_eq!(construct_end(&tokens, &succ, &arguments), None);
        assert_eq!(construct_end(&tokens, &at("Term", 0), &arguments), None);
    }

    #[test]
    fn quotes_are_cut_on_a_character_boundary() {
        let long = "é".repeat(150);
        let quoted = quote(&long);
        assert!(quoted.ends_with('…'));
        assert!(quoted.len() <= 200 + '…'.len_utf8());
    }

    #[test]
    fn krs_codes_are_reasons_with_their_own_next_step() {
        for code in [
            "krs::analysis::overlapping-rule-heads",
            "krs::analysis::nondet-group",
            "krs::analysis::priority-after-owise",
            "krs::analysis::overlapping-equations",
            "krs::analysis::overlapping-match-arms",
        ] {
            assert_eq!(static_spelling(code), Some(code), "{code} is registered");
            for siblings in [false, true] {
                for one_item in [false, true] {
                    assert!(
                        !krs_next(code, siblings, one_item)
                            .starts_with("the detail is KRS's message")
                    );
                }
            }
        }
        // Without siblings in the detail, the next step does not send the author to them.
        for code in [
            "krs::analysis::overlapping-rule-heads",
            "krs::analysis::overlapping-equations",
            "krs::analysis::overlapping-match-arms",
        ] {
            for one_item in [false, true] {
                assert!(
                    krs_next(code, true, one_item).contains("siblings"),
                    "{code}"
                );
                assert!(
                    !krs_next(code, false, one_item).contains("siblings"),
                    "{code}"
                );
            }
            assert!(
                krs_next(code, false, false).contains("a correlated edit"),
                "{code}"
            );
        }
        // One equation that applies to one argument in two ways has no other equation to
        // change, so its step names neither another equation nor a correlated edit.
        for code in [
            "krs::analysis::overlapping-equations",
            "krs::analysis::overlapping-match-arms",
        ] {
            for siblings in [false, true] {
                let next = krs_next(code, siblings, true);
                assert!(next.contains("in two ways"), "{code}: {next}");
                assert!(!next.contains("other equation"), "{code}: {next}");
                assert!(!next.contains("correlated"), "{code}: {next}");
                assert_ne!(next, krs_next(code, siblings, false), "{code}");
            }
        }
        assert_eq!(static_spelling("krs::analysis::no-such-code"), None);
    }
}
