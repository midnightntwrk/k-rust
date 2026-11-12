//! A `cells!` sentence's entries judged by the one entry-admission table (design S5, §2.3):
//! each entry's spelling, read from the authored source as the shared reader reads it
//! ([`krs_syntax::cell_entry::cells_fields`]), against its cell's kind
//! ([`krs_ir::cell_kind::CellKind::entry`]: the layers of the cell's `?` and `*` ancestors and
//! its own), then paired with the other side's entry of the same cell, each step over the whole
//! sentence before the next ([`krs_syntax::cell_entries::Sentence::judge`]).
//!
//! The collector is where both are known: the spelling is the author's, which the descriptor
//! no longer holds, and the kind is the collected declaration's. What the spelling alone
//! refuses is the macro's, and what the sorts refuse and the rule-level checks are the
//! compiler's, after the entries are admitted.

use std::collections::BTreeMap;

use krs_diagnostic::{Diagnostic, Location, Severity};
use krs_ir::cell_kind::{
    CellKind, DescriptorCell, EntryKind, GroupKind, Layer, Multiplicity, Notation, Order,
};
use krs_ir::{
    ConfigurationSentenceKind, DescriptorBundle, DescriptorCellDeclaration, DescriptorCellIdentity,
    DescriptorIndex, DescriptorPayload, ProtocolCellContent, SourceRange, StableItemId,
};
use krs_syntax::cell_entries::{self, EntrySide, Lint, Refusal, Rewrite, Sentence, SentenceEntry};
use krs_syntax::cell_entry::{EntryForm, EntryRest, EntrySpelling};

use super::provenance::Coordinates;
use super::resolve::MarkedAncestor;
use super::source::SourceDocument;
use crate::{CollectionError, CollectionErrorKind};

/// One authored field of a `cells!` payload: the name of the cell its key ends in, its value's
/// spelling where the shared reader reads one, and where the value is.
#[derive(Clone, Debug)]
pub(super) struct ParsedField<R> {
    name: String,
    spelling: Option<EntrySpelling>,
    range: Option<R>,
    /// Where the key's last segment is, the name that names the field's cell.
    name_range: Option<R>,
    /// Where each spelling inside the value is, by its path
    /// ([`krs_syntax::cell_entry::located_spellings`]).
    located: Vec<(Vec<usize>, R)>,
    /// Where the reader reads no spelling, whether the value's frame is a `KCell(..)` with the
    /// anonymous rest `..` ([`krs_syntax::cell_entry::CellsField::anonymous_rest`]).
    anonymous_rest: bool,
}

/// A `cells!` sentence's authored fields: its subject's, its result's (none for a single-body
/// rule), the names its parameters bind, and the refusals the parser leaves until the entries
/// are admitted: an item after a computation's rest, then a result remainder that reuses no
/// subject frame of its kind, or a readable cell whose two entries no lowering pairs.
#[derive(Clone, Debug)]
pub(super) struct ParsedCells<R> {
    /// The form the entries are written in: `cells!`, or a readable record or claim.
    form: EntryForm,
    subject: Vec<ParsedField<R>>,
    result: Option<Vec<ParsedField<R>>>,
    parameters: Vec<String>,
    after: Vec<After<R>>,
}

/// A refusal the parser leaves until the entries are admitted: a `KCell(..)` entry's item after
/// its sequence's tail ([`krs_syntax::StateRuleItem::misplaced_tail`]), a result remainder's
/// ([`krs_syntax::StateRuleItem::reuse_refusal`]), or a readable clause's pairing
/// ([`krs_syntax::RuleClause::pairing_refusal`]) or entry part's
/// ([`krs_syntax::RuleClause::part_refusal`]); its kind, the parser's message, and where it is.
#[derive(Clone, Debug)]
struct After<R> {
    kind: CollectionErrorKind,
    detail: String,
    range: Option<R>,
    /// Whether it is raised once the subject's entries are admitted, before the result's are
    /// judged: a readable subject's map read of a cell the result writes
    /// ([`krs_syntax::RuleClause::subject_refusal`]). Every other one waits for every entry.
    subject: bool,
    /// The cell whose declaration decides whether it is raised at all: a readable bracketed
    /// value's term reading, refused, where the value is read as a List collection's instances
    /// ([`krs_syntax::RuleClause::instances_only_refusals`]). It is the refusal only where the
    /// cell holds no collection, and is asked once the table admits the entries.
    cell: Option<String>,
}

/// The kind of a refusal the parser left until the entries are admitted: its own registered
/// code, which the collector only raises later (the source's syntax where the parser's code is
/// no registered one).
fn deferred(error: &krs_syntax::SyntaxError) -> CollectionErrorKind {
    let code = error.kind().code();
    krs_diagnostic::codes::REGISTRY
        .iter()
        .position(|info| info.code == code)
        .and_then(|place| u16::try_from(place).ok())
        .map_or(
            CollectionErrorKind::SourceSyntax,
            CollectionErrorKind::DeferredSyntax,
        )
}

impl After<Coordinates> {
    fn of(kind: CollectionErrorKind, error: &krs_syntax::SyntaxError) -> Self {
        Self {
            kind,
            detail: error.to_string(),
            range: super::provenance::token_coordinates(krs_syntax::TokenRange::new(
                error.span(),
                error.span(),
            ))
            .ok(),
            subject: false,
            cell: None,
        }
    }
}

impl After<SourceRange> {
    fn refused(&self) -> CollectionError {
        let error = CollectionError::new(self.kind, &self.detail);
        match &self.range {
            Some(range) => error.with_source_range(range.clone()),
            None => error,
        }
    }
}

/// The refusals `rule`'s parser leaves until its entries are admitted, in the order they are
/// asked: an item after a computation's rest, which the entry's kind answers first, then a result
/// remainder that reuses no subject frame of its kind, which pairs the result with the subject.
fn after_admission(
    rule: &krs_syntax::StateRuleItem,
) -> Vec<(CollectionErrorKind, krs_syntax::SyntaxError)> {
    rule.misplaced_tail()
        .map(|error| (deferred(&error), error))
        .into_iter()
        .chain(
            rule.reuse_refusal()
                .map(|error| (CollectionErrorKind::ResultRemainderReuse, error)),
        )
        .collect()
}

/// The first refusal `rule`'s parser leaves until its entries are admitted, at once: for a
/// sentence whose entries no admission judges first.
pub(super) fn refused_without_admission(
    rule: &krs_syntax::StateRuleItem,
) -> Result<(), CollectionError> {
    match after_admission(rule).into_iter().next() {
        Some((kind, error)) => {
            Err(CollectionError::new(kind, error.to_string()).with_span(error.span()))
        }
        None => Ok(()),
    }
}

/// The authored fields of a sentence, located in its source document.
pub(super) type LocatedCells = ParsedCells<SourceRange>;

fn fields(expression: &krs_syntax::CellsExpression) -> Option<Vec<ParsedField<Coordinates>>> {
    read_fields(expression.tokens(), EntryForm::Cells)
}

fn read_fields(
    tokens: &proc_macro2::TokenStream,
    form: EntryForm,
) -> Option<Vec<ParsedField<Coordinates>>> {
    located_fields(krs_syntax::cell_entry::entry_fields(tokens, form)?)
}

/// [`read_fields`] of a result's record, whose `|` is the bitwise operator, no alternatives.
fn read_result_fields(
    tokens: &proc_macro2::TokenStream,
    form: EntryForm,
) -> Option<Vec<ParsedField<Coordinates>>> {
    located_fields(krs_syntax::cell_entry::entry_result_fields(tokens, form)?)
}

fn located_fields(
    fields: Vec<krs_syntax::cell_entry::CellsField>,
) -> Option<Vec<ParsedField<Coordinates>>> {
    fields
        .into_iter()
        .map(|field| {
            let name = &field.key.segments.last()?.ident;
            Some(ParsedField {
                name: name.to_string(),
                name_range: super::provenance::token_coordinates(krs_syntax::TokenRange::new(
                    name.span(),
                    name.span(),
                ))
                .ok(),
                spelling: field.spelling,
                anonymous_rest: field.anonymous_rest,
                range: field
                    .value
                    .and_then(|range| super::provenance::token_coordinates(range).ok()),
                located: field
                    .located
                    .into_iter()
                    .filter_map(|(path, range)| {
                        Some((path, super::provenance::token_coordinates(range).ok()?))
                    })
                    .collect(),
            })
        })
        .collect()
}

impl ParsedCells<Coordinates> {
    /// The fields of a one-sided `cells!` pattern the sentence keeps as it matched it (a
    /// function context, a context alias), with the names `parameters` bind, and the refusal its
    /// parser left until the entries are admitted (an item after a computation's rest, or an
    /// entry part's fault, [`krs_syntax::CellsExpression::misplaced_tail`]); `None` where the
    /// payload is no list of fields and the parser left none. Where it left one, the payload
    /// has no entries to judge, so the refusal is raised at once ([`judge`]) rather than dropped.
    pub(super) fn of_pattern(
        pattern: &krs_syntax::CellsExpression,
        parameters: impl IntoIterator<Item = String>,
    ) -> Option<Self> {
        let after = pattern
            .misplaced_tail()
            .map(|error| After::of(deferred(error), error))
            .into_iter()
            .collect::<Vec<_>>();
        let subject = match fields(pattern) {
            Some(subject) => subject,
            None if !after.is_empty() => Vec::new(),
            None => return None,
        };
        Some(Self {
            form: EntryForm::Cells,
            subject,
            result: None,
            parameters: parameters.into_iter().collect(),
            after,
        })
    }

    /// The fields of a `cells!` rule, with its result remainders' refusal; `None` where a
    /// payload is no list of fields.
    pub(super) fn of_rule(rule: &krs_syntax::StateRuleItem) -> Option<Self> {
        Some(Self {
            form: EntryForm::Cells,
            subject: fields(rule.subject())?,
            result: match rule.result() {
                Some(result) => Some(read_result_fields(result.tokens(), EntryForm::Cells)?),
                None => None,
            },
            parameters: rule
                .bindings()
                .iter()
                .map(|binding| binding.name().to_string())
                .collect(),
            after: after_admission(rule)
                .iter()
                .map(|(kind, error)| After::of(*kind, error))
                .collect(),
        })
    }

    /// The fields of a readable cell-record clause, written in `form` (a readable record or a
    /// claim): its subject record's and its result record's; `None` for a clause of a term table,
    /// or where a record's part is no field.
    ///
    /// A clause whose parser left a refusal until its entries are admitted always has fields:
    /// where its records read as none, it has no entries, so the refusal is raised at once
    /// ([`judge_readable`]) rather than dropped.
    pub(super) fn of_readable(clause: &krs_syntax::RuleClause, form: EntryForm) -> Option<Self> {
        let after = clause
            .subject_refusal()
            .map(|error| After {
                subject: true,
                ..After::of(deferred(error), error)
            })
            .into_iter()
            .chain(
                clause
                    .pairing_refusal()
                    .map(|error| After::of(deferred(error), error)),
            )
            // A part's fault waits for the whole it is in, which the pairing judges too.
            .chain(
                clause
                    .part_refusal()
                    .map(|error| After::of(deferred(error), error)),
            )
            .chain(clause.instances_only_refusals().map(|(cell, error)| After {
                cell: Some(cell),
                ..After::of(deferred(error), error)
            }))
            .collect::<Vec<_>>();
        let fields = clause.records().and_then(|(subject, result)| {
            Some((
                read_fields(subject, form)?,
                read_result_fields(result, form)?,
            ))
        });
        let (subject, result) = match fields {
            Some(fields) => fields,
            None if !after.is_empty() => (Vec::new(), Vec::new()),
            None => return None,
        };
        Some(Self {
            form,
            subject,
            result: Some(result),
            parameters: Vec::new(),
            after,
        })
    }

    /// The fields of an initializer's body, each read with the initializer's configuration
    /// variables as such, the names they bind, and the refusal its reader left until the entries
    /// are judged (a group record update, [`krs_syntax::InitializerFunction::deferred_refusal`]);
    /// `None` where the body is no list of fields and the reader left none.
    pub(super) fn of_initializer(initializer: &krs_syntax::InitializerFunction) -> Option<Self> {
        let after = initializer
            .deferred_refusal()
            .map(|error| After::of(deferred(&error), &error))
            .into_iter()
            .collect::<Vec<_>>();
        let subject = match initializer.entry_fields().and_then(located_fields) {
            Some(subject) => subject,
            None if !after.is_empty() => Vec::new(),
            None => return None,
        };
        Some(Self {
            form: EntryForm::Initializer,
            subject,
            result: None,
            parameters: initializer.variable_names(),
            after,
        })
    }

    /// Whether these are an initializer's fields.
    pub(super) fn is_initializer(&self) -> bool {
        self.form == EntryForm::Initializer
    }

    /// The fields located in `document`.
    pub(super) fn locate(&self, document: &SourceDocument) -> LocatedCells {
        let locate = |fields: &[ParsedField<Coordinates>]| {
            fields
                .iter()
                .map(|field| ParsedField {
                    name: field.name.clone(),
                    spelling: field.spelling.clone(),
                    anonymous_rest: field.anonymous_rest,
                    range: field
                        .range
                        .as_ref()
                        .and_then(|coordinates| coordinates.range_in(document)),
                    name_range: field
                        .name_range
                        .as_ref()
                        .and_then(|coordinates| coordinates.range_in(document)),
                    located: field
                        .located
                        .iter()
                        .filter_map(|(path, coordinates)| {
                            Some((path.clone(), coordinates.range_in(document)?))
                        })
                        .collect(),
                })
                .collect()
        };
        ParsedCells {
            form: self.form,
            subject: locate(&self.subject),
            result: self.result.as_deref().map(locate),
            parameters: self.parameters.clone(),
            after: self
                .after
                .iter()
                .map(|after| After {
                    kind: after.kind,
                    detail: after.detail.clone(),
                    range: after
                        .range
                        .as_ref()
                        .and_then(|coordinates| coordinates.range_in(document)),
                    subject: after.subject,
                    cell: after.cell.clone(),
                })
                .collect(),
        }
    }
}

impl LocatedCells {
    /// The first refusal a readable clause's reader left until every entry is admitted, raised
    /// then: neither the subject's limit, raised once the subject's entries are, nor a bracketed
    /// value's term reading, which its cell's declaration decides ([`instances_only`]).
    fn left_after_every_entry(&self) -> Option<&After<SourceRange>> {
        self.after
            .iter()
            .find(|after| !after.subject && after.cell.is_none())
    }

    /// The first refusal the reader left until the entries were judged, where it is: raised once
    /// they are admitted.
    pub(super) fn left_after_admission(&self) -> Option<CollectionError> {
        self.after.first().map(After::refused)
    }
}

/// Judges the `cells!` entries of every sentence of `bundle` whose authored fields `cells`
/// holds: a `cells!` rule's or claim's, pairing a result's with its subject's, or a single-body
/// rule's in place; and the one-sided pattern of a context, a context alias or an equation's
/// function context, which the sentence keeps as it matched it ([`Rewrite::Kept`]). Then, once
/// a rule's entries are admitted, what its parser left until then: an item after a
/// computation's rest, which the entry's kind answers first, then its result remainders, each
/// against the subject frame it reuses, which pairs the result with the subject.
///
/// Returns the warnings of the admitted entries' lints, in the sentences' order and each
/// sentence's source order: one per entry that owes one, at its value ([`linted`]).
///
/// # Errors
///
/// The first refused entry, with its class's code, at its value; else the first sentence's
/// refusal its parser left until its entries were admitted, where it is.
pub(super) fn judge(
    bundle: &DescriptorBundle,
    cells: &BTreeMap<StableItemId, LocatedCells>,
) -> Result<Vec<Diagnostic>, CollectionError> {
    let index = DescriptorIndex::new(bundle);
    let mut warnings = Vec::new();
    for (id, authored) in cells {
        if authored.form.is_readable() || authored.form == EntryForm::Initializer {
            // Judged before its payload is resolved ([`judge_readable`], [`judge_initializer`]).
            // A readable clause that judgement did not reach (no head-rule target, or a field no
            // single cell has) still owes the refusals its parser left: its payload resolved, so
            // nothing else refuses it, and dropping them would admit a result the parser could
            // not pair as only read. A bracketed value's term reading is a refusal only by its
            // cell's declaration, which that judgement asks ([`instances_only`]).
            if let Some(after) = authored.after.iter().find(|after| after.cell.is_none()) {
                return Err(after.refused());
            }
            continue;
        }
        warnings.extend(judge_entries(&index, id, authored)?);
        if let Some(after) = authored.after.first() {
            return Err(after.refused());
        }
    }
    Ok(warnings)
}

/// Judges the entries of the readable record clause or claim `id` against the configuration
/// `target` it names, before its payload is resolved: the table's answer is the first one an
/// author meets, ahead of the readable route's own readings of the entries (a bracketed value
/// read as a list, a braced one as instances), which assume the kinds the table checks. A clause
/// whose fields the reader does not read, or which names a cell no single cell of the
/// configuration has, is left to the rule's resolution, which reports the name.
///
/// Returns the warnings of the admitted entries' lints, in source order, each at its entry's
/// value ([`linted`]), as [`judge`] gives a `cells!` sentence's.
///
/// # Errors
///
/// The first refused entry, with its class's code, at what it refuses; else the refusal of the
/// first cell whose two entries the parser could not pair
/// ([`krs_syntax::RuleClause::pairing_refusal`]).
pub(super) fn judge_readable(
    id: &StableItemId,
    target: &super::resolve::HeadRuleTarget,
    authored: &LocatedCells,
) -> Result<Vec<Diagnostic>, CollectionError> {
    if !authored.form.is_readable() {
        return Ok(Vec::new());
    }
    let Some(subject) = readable_entries(target, &authored.subject) else {
        return Ok(Vec::new());
    };
    let Some(result) = authored
        .result
        .as_deref()
        .map_or(Some(Vec::new()), |fields| readable_entries(target, fields))
    else {
        return Ok(Vec::new());
    };
    let sentence = subject
        .iter()
        .map(|entry| (EntrySide::Subject, entry))
        .chain(result.iter().map(|entry| (EntrySide::Result, entry)))
        .map(|(side, entry)| SentenceEntry {
            side,
            cell: entry.cell,
            kind: &entry.kind,
            spelling: entry.field.spelling.as_ref(),
            anonymous_rest: entry.field.anonymous_rest,
        })
        .collect::<Vec<_>>();
    let judged = Sentence {
        form: authored.form,
        entries: &sentence,
        rewrite: Rewrite::Result,
        parameters: &authored.parameters,
        groups: target.groups(),
    }
    .judge_located();
    if judged.is_ok() {
        instances_only(subject.iter().chain(&result), authored)?;
        group_record_on_leaf(subject.iter().chain(&result), target.groups())?;
        items_off_the_computation(subject.iter().chain(&result), true)?;
        instance_child_items(subject.iter().chain(&result), target)?;
        presence_in_constructor_record(subject.iter().chain(&result), target.groups())?;
    }
    subject_limit(&judged, authored)?;
    if judged.is_ok() {
        collection_in_named_cell(id, &subject, &result, |cell, holder| {
            target.lies_in(cell, holder)
        })?;
        overwritten_collection(&subject, &result)?;
        for key in target
            .instance_key()
            .into_iter()
            .chain(target.nested_instance_keys())
        {
            kept_key(&InstanceKey::of(key), &subject, &result)?;
        }
        instance_child_multiplicity(&subject, &result)?;
        // A cell whose two entries the parser could not pair (a presence over a term, ..) is
        // refused only now: the table admitted both entries against the cell's kind, first.
        if let Some(pairing) = authored.left_after_every_entry() {
            return Err(pairing.refused());
        }
    }
    match judged {
        Ok(lints) => Ok(lints
            .into_iter()
            .map(|(at, lint)| {
                let entry = subject
                    .iter()
                    .chain(&result)
                    .nth(at)
                    .expect("a judged entry is the sentence's");
                linted(
                    id,
                    unraw(&entry.cell.field),
                    entry.field.range.clone(),
                    lint,
                )
            })
            .collect()),
        Err((at, refusal)) => {
            let side = if at < subject.len() {
                EntrySide::Subject
            } else {
                EntrySide::Result
            };
            let entry = subject
                .iter()
                .chain(&result)
                .nth(at)
                .expect("the refused entry is the sentence's");
            Err(refused(
                authored.form,
                entry,
                subject_twin(&subject, entry, side),
                side,
                Rewrite::Result,
                authored.form.is_claim(),
                &refusal,
                target.groups(),
            ))
        }
    }
}

/// Refuses the first admitted entry whose bracketed value the parser read only as a List
/// collection's instances, its term reading refused ([`After::cell`]), where its cell holds no
/// collection: brackets there are a list's elements or the computation's items, which are terms,
/// so the term reader's refusal is the value's, as it is for any such value. On a collection the
/// brackets are its instances, judged as a braced instance list's children are
/// ([`instance_child_items`]), and the term reading is no reading of them.
fn instances_only<'e, 'a: 'e>(
    entries: impl IntoIterator<Item = &'e Entry<'a>>,
    authored: &LocatedCells,
) -> Result<(), CollectionError> {
    for entry in entries {
        if matches!(entry.kind.own.layers.first(), Some(Layer::Instances(_))) {
            continue;
        }
        let cell = unraw(&entry.cell.field);
        if let Some(after) = authored
            .after
            .iter()
            .find(|after| after.cell.as_deref() == Some(cell))
        {
            return Err(after.refused());
        }
    }
    Ok(())
}

/// The refusal `authored`'s parser left until the sentence's entries are admitted, a subject's
/// map read of a cell the result writes (M3): a limit, which never hides a principle, so it
/// answers only where `judged` admits every entry, the result's as well as the subject's, and
/// before the parser's other deferred refusals.
fn subject_limit<T, U>(
    judged: &Result<T, U>,
    authored: &LocatedCells,
) -> Result<(), CollectionError> {
    match authored.after.iter().find(|after| after.subject) {
        Some(limit) if judged.is_ok() => Err(limit.refused()),
        _ => Ok(()),
    }
}

/// Judges the entries of an initializer, each against its cell: `cells` gives each cell, its
/// kind and its leaf's sort. An initializer's value is its cell's whole initial content, of the
/// cell's declared kind, and the macro, which does not know that kind, checks none of it, so the
/// table answers every entry here: where it refuses one, the refusal is the author's answer, at
/// what it refuses. Where it admits an entry with brackets on a cell the kind alone does not
/// decide, they are the mark of the kind below its presence or instances (an optional list's
/// `Some([..])`, a template's list), which the caller then decides. An entry whose value the
/// reader does not read (one that names a Rust wrapper, `Cell::new(..)`, which rustc checks) is
/// not judged.
///
/// # Errors
///
/// The first refused entry, in source order, with its class's code.
pub(super) fn judge_initializer(
    cells: &[(&DescriptorCellIdentity, EntryKind, Option<&str>)],
    groups: &[GroupKind],
    authored: &LocatedCells,
) -> Result<(), CollectionError> {
    let entries = authored
        .subject
        .iter()
        .filter_map(|field| {
            let (cell, kind, sort) = cells
                .iter()
                .find(|(cell, ..)| unraw(&cell.field) == unraw(&field.name))?;
            Some(Entry {
                cell,
                kind: kind.clone(),
                field,
                ancestor: None,
                sort: sort.map(str::to_owned),
            })
        })
        .collect::<Vec<_>>();
    let sentence = entries
        .iter()
        .map(|entry| SentenceEntry {
            side: EntrySide::Initializer,
            cell: entry.cell,
            kind: &entry.kind,
            spelling: entry.field.spelling.as_ref(),
            anonymous_rest: entry.field.anonymous_rest,
        })
        .collect::<Vec<_>>();
    // An initializer's entry pairs with nothing: it is the cell's whole initial content.
    Sentence {
        form: EntryForm::Initializer,
        entries: &sentence,
        rewrite: Rewrite::Result,
        parameters: &authored.parameters,
        groups,
    }
    .judge_located()
    .map_err(|(at, refusal)| {
        refused(
            EntryForm::Initializer,
            &entries[at],
            None,
            EntrySide::Initializer,
            Rewrite::Result,
            false,
            &refusal,
            groups,
        )
    })?;
    // `k::k![..]` off the computation is a term of sort `K`, as in a sentence: a `KSequence`
    // leaf starts holding it, a leaf of another sort or a group does not.
    items_off_the_computation(&entries, false)
}

/// The content-sort refusal of an initializer value the table admits by its marks but whose
/// sort is not below its cell's ([`super::resolve::ShapeMismatch`]): at the value of the cell
/// `path` names, the top-level entry's name, then each group child's below it.
pub(super) fn initializer_content_sort(
    authored: &LocatedCells,
    path: &[String],
    mismatch: super::resolve::ShapeMismatch,
) -> CollectionError {
    use super::resolve::ShapeMismatch;
    let cell = path.last().map_or("", |name| unraw(name));
    let detail = match mismatch {
        ShapeMismatch::TermOnGroup { group } => format!(
            "the cell `{cell}` holds a `{group}` group, and the initializer gives it a term, whose sort is no group's: a group's initial content is the record of its children, `{group} {{ .. }}`"
        ),
        ShapeMismatch::RecordOnLeaf { record } => format!(
            "the initializer gives `{cell}` a `{record}` record, a group's content, whose sort is not below the cell's: `{cell}` holds a term of its declared sort"
        ),
        ShapeMismatch::RecordOfAnotherGroup { record, group } => format!(
            "the cell `{cell}` holds a `{group}` group, and the initializer gives it a `{record}` record, another group's content, whose sort is not below the cell's"
        ),
    };
    let error = CollectionError::new(CollectionErrorKind::ContentSort, detail);
    let range = path.split_first().and_then(|(top, children)| {
        let field = authored
            .subject
            .iter()
            .find(|field| unraw(&field.name) == unraw(top))?;
        let Some(spelling) = &field.spelling else {
            return field.range.clone();
        };
        let mut at = Vec::new();
        let mut spelling = spelling;
        for child in children {
            while let EntrySpelling::Present(inner) | EntrySpelling::Absent(inner) = spelling {
                at.push(0);
                spelling = inner;
            }
            let EntrySpelling::Record(record) = spelling else {
                return field.range.clone();
            };
            let Some((step, (_, value))) = record
                .fields
                .iter()
                .enumerate()
                .find(|(_, (name, _))| unraw(name) == unraw(child))
            else {
                return field.range.clone();
            };
            at.push(step);
            spelling = value;
        }
        field
            .located
            .iter()
            .find(|(located, _)| *located == at)
            .map(|(_, range)| range.clone())
            .or_else(|| field.range.clone())
    });
    match range {
        Some(range) => error.with_source_range(range),
        None => error,
    }
}

/// Refuses the first admitted entry whose whole value, below its presence, `Cell(..)` and an
/// alias, is a record of a group (`Core { .. }`, `k::fragment![crate::Core { .. }]`) on a leaf
/// whose sort holds no cell term, at the record. A group record there is the group's cell term,
/// a value of its cell sort, which is below `KItem` (and `K`) only, so on any other leaf it is
/// no term of the leaf's sort: the whole entry's mistake, told before the faults of its parts (a
/// `?` child's presence, whose limit waits for the entry), as the table tells an entry's kind
/// before them. On a `KItem` leaf the record is a value of the leaf, judged as a term is.
fn group_record_on_leaf<'e, 'a: 'e>(
    entries: impl IntoIterator<Item = &'e Entry<'a>>,
    groups: &[GroupKind],
) -> Result<(), CollectionError> {
    for entry in entries {
        let (Some(sort), Some(spelling)) = (&entry.sort, &entry.field.spelling) else {
            continue;
        };
        if matches!(sort.as_str(), "KItem" | "KSequence") {
            continue;
        }
        let mut at = Vec::new();
        let mut value = spelling;
        while let EntrySpelling::Present(inner)
        | EntrySpelling::Absent(inner)
        | EntrySpelling::Cell(inner)
        | EntrySpelling::Alias(_, inner) = value
        {
            at.push(0);
            value = inner;
        }
        let (EntrySpelling::Record(record) | EntrySpelling::Fragment(record)) = value else {
            continue;
        };
        if !groups.iter().any(|group| group.name == record.head) {
            continue;
        }
        let cell = unraw(&entry.cell.field);
        let error = CollectionError::new(
            CollectionErrorKind::ContentSort,
            format!(
                "the cell `{cell}` holds a `{sort}` leaf, and the entry gives it a `{head}` record, the `{head}` group's cell term, whose sort is not below the leaf's: a group's cell sort is below `KItem` only, so a leaf holds a group's record only where its sort is `KItem`",
                head = record.head
            ),
        );
        let range = entry
            .field
            .located
            .iter()
            .find(|(path, _)| *path == at)
            .map(|(_, range)| range)
            .or(entry.field.range.as_ref());
        return Err(match range {
            Some(range) => error.with_source_range(range.clone()),
            None => error,
        });
    }
    Ok(())
}

/// Refuses the first admitted entry of a sentence whose value is `k::k![..]` on a cell that is not
/// the computation, through its presence and its `Cell(..)`: the computation's item notation,
/// which denotes the term of sort `K` its items make in order (`a ~> b ~> rest`). On a leaf or a
/// group of another sort it is a term whose sort is not below the cell's (`ContentSort`). On a
/// leaf of sort `KSequence` it is that leaf's own sort: `cells!` lowers it as it lowers the
/// computation's items, and a readable record (`readable`), which writes a computation's items in
/// its brackets, has no reading of the notation, a limit (`LeafItems`). The table admits it as the
/// term it is ([`cell_entries`]'s marks: the computation's mark only where the cell holds a
/// computation).
fn items_off_the_computation<'e, 'a: 'e>(
    entries: impl IntoIterator<Item = &'e Entry<'a>>,
    readable: bool,
) -> Result<(), CollectionError> {
    for entry in entries {
        let Some(spelling) = &entry.field.spelling else {
            continue;
        };
        let mut at = Vec::new();
        let mut value = spelling;
        while let EntrySpelling::Present(inner)
        | EntrySpelling::Cell(inner)
        | EntrySpelling::Alias(_, inner) = value
        {
            at.push(0);
            value = inner;
        }
        if !matches!(value, EntrySpelling::KMacro(_)) {
            continue;
        }
        let Some((kind, detail)) = items_verdict(
            unraw(&entry.cell.field),
            &entry.kind.own.layers,
            entry.sort.as_deref(),
            readable,
        ) else {
            continue;
        };
        let error = CollectionError::new(kind, detail);
        let range = entry
            .field
            .located
            .iter()
            .find(|(path, _)| *path == at)
            .map(|(_, range)| range)
            .or(entry.field.range.as_ref());
        return Err(match range {
            Some(range) => error.with_source_range(range.clone()),
            None => error,
        });
    }
    Ok(())
}

/// What `k::k![..]` is on the cell `cell` of the layers `layers` and the leaf sort `sort`, read
/// through its presence ([`items_off_the_computation`]): `None` where it is admitted (the
/// computation, whose mark it is, and a `KSequence` leaf off the readable route) or another
/// judge's (an optional cell's missing presence, a collection's instances).
fn items_verdict(
    cell: &str,
    layers: &[Layer],
    sort: Option<&str>,
    readable: bool,
) -> Option<(CollectionErrorKind, String)> {
    let content = layers
        .iter()
        .find(|layer| !matches!(layer, Layer::Optional));
    match (content, sort) {
        (Some(Layer::Leaf(_)), Some("KSequence")) if !readable => None,
        (Some(Layer::Leaf(_)), Some("KSequence")) => Some((
            CollectionErrorKind::LeafItems,
            format!(
                "the cell `{cell}` holds a leaf of sort `KSequence`, and `k::k![..]` writes a term of that sort by its items (`a ~> b ~> rest`), which a leaf holds; a readable record writes a computation's items in its brackets (`k: [a, b, ..]`) and does not read `k::k![..]` yet: write the leaf with a name bound to such a value, or the sentence with `k::cells!`, which writes it by its items"
            ),
        )),
        (Some(Layer::Leaf(_)), Some(sort)) => Some((
            CollectionErrorKind::ContentSort,
            format!(
                "the cell `{cell}` holds a leaf of sort `{sort}`, and the entry gives it `k::k![..]`, the computation's item notation, a term of sort `K` (its items in order), whose sort is not below the leaf's"
            ),
        )),
        (Some(Layer::Group(group)), _) => Some((
            CollectionErrorKind::ContentSort,
            format!(
                "the cell `{cell}` holds a group `{}`, and the entry gives it `k::k![..]`, the computation's item notation, a term of sort `K` (its items in order), which is no group's cell term",
                group.name
            ),
        )),
        _ => None,
    }
}

/// [`items_off_the_computation`] of a readable record's instance children: a child an instance
/// record writes `k::k![..]` for, through its presence, is judged by the child cell's own kind
/// and sort as a readable leaf entry is, at the notation. The child is found by its name among
/// the target's cells; a name no single cell has is left to the lowering, which checks the
/// sequence against the child's declared sort.
fn instance_child_items<'e, 'a: 'e>(
    entries: impl IntoIterator<Item = &'e Entry<'a>>,
    target: &super::resolve::HeadRuleTarget,
) -> Result<(), CollectionError> {
    for entry in entries {
        // A sequence's records are instances only on a collection; a list's elements and the
        // computation's items are terms, which the term reader judges.
        if !matches!(entry.kind.own.layers.first(), Some(Layer::Instances(_))) {
            continue;
        }
        let Some(spelling) = &entry.field.spelling else {
            continue;
        };
        let (aliased, inner) = match spelling {
            EntrySpelling::Alias(_, inner) => (true, &**inner),
            other => (false, other),
        };
        let (EntrySpelling::Brackets(seq)
        | EntrySpelling::Braces(seq)
        | EntrySpelling::InstanceList(seq)
        | EntrySpelling::InstanceSet(seq)) = inner
        else {
            continue;
        };
        for (step, item) in seq.items.iter().enumerate() {
            let (labelled, item) = match item {
                EntrySpelling::Alias(_, inner) => (true, &**inner),
                other => (false, other),
            };
            let (EntrySpelling::Record(record) | EntrySpelling::Fragment(record)) = item else {
                continue;
            };
            for (child, (name, value)) in record.fields.iter().enumerate() {
                let mut at = std::iter::repeat_n(0, usize::from(aliased))
                    .chain([step])
                    .chain(labelled.then_some(0))
                    .chain([child])
                    .collect::<Vec<_>>();
                let mut value = value;
                while let EntrySpelling::Present(inner) | EntrySpelling::Alias(_, inner) = value {
                    at.push(0);
                    value = inner;
                }
                if !matches!(value, EntrySpelling::KMacro(_)) {
                    continue;
                }
                let Some((_, kind, _, sort)) = target.entry(name) else {
                    continue;
                };
                let Some((kind, detail)) = items_verdict(name, &kind.own.layers, sort, true) else {
                    continue;
                };
                let error = CollectionError::new(kind, detail);
                let range = entry
                    .field
                    .located
                    .iter()
                    .find(|(path, _)| *path == at)
                    .map(|(_, range)| range)
                    .or(entry.field.range.as_ref());
                return Err(match range {
                    Some(range) => error.with_source_range(range.clone()),
                    None => error,
                });
            }
        }
    }
    Ok(())
}

/// Refuses the first admitted entry that writes `Some(..)` or `None` as a field of a constructor
/// record, a record whose head names no group, at a configuration position: the macro, which
/// resolves no path, reads every `Path { .. }` there as a group record and carries such a field
/// as a group record's `?` child presence, whose limit waits for the entries
/// ([`krs_syntax::RuleClause::part_refusal`]). A constructor record is a term, its field a term
/// position that is no cell's, and `Some(..)` and `None` are a `?` cell's presence, never a term,
/// so the field names no KRS declaration, as `Hold(Some(_))` does: a principle, told before the
/// limit. A group record's own `?` child stays the limit's, at any depth, a constructor's field
/// included.
fn presence_in_constructor_record<'e, 'a: 'e>(
    entries: impl IntoIterator<Item = &'e Entry<'a>>,
    groups: &[GroupKind],
) -> Result<(), CollectionError> {
    for entry in entries {
        let Some(spelling) = &entry.field.spelling else {
            continue;
        };
        let mut at = Vec::new();
        let Some((field, head, present)) = constructor_presence(spelling, groups, &mut at) else {
            continue;
        };
        let written = if present { "Some(..)" } else { "None" };
        let error = CollectionError::new(
            CollectionErrorKind::NotADeclaration,
            format!(
                "`{written}` is not a KRS declaration of this name: the field `{field}` of the constructor record `{head} {{ .. }}` holds a term, and `Some(..)` and `None` are a `?` cell's presence, which names a cell's entry and never a term (KRS has no `Option` term); a term names a constructor, function, constant, cell group or builtin operation"
            ),
        );
        let range = entry
            .field
            .located
            .iter()
            .find(|(path, _)| *path == at)
            .map(|(_, range)| range)
            .or(entry.field.range.as_ref());
        return Err(match range {
            Some(range) => error.with_source_range(range.clone()),
            None => error,
        });
    }
    Ok(())
}

/// The first field of a constructor record in `spelling`, below its presence, `Cell(..)`, aliases
/// and group records' children, whose value is `Some(..)` or `None`: its name, the record's head,
/// and whether it is `Some(..)`; `at` is left at its spelling. A record whose head names one of
/// `groups` is a group record; any other is a constructor's.
fn constructor_presence(
    spelling: &EntrySpelling,
    groups: &[GroupKind],
    at: &mut Vec<usize>,
) -> Option<(String, String, bool)> {
    match spelling {
        EntrySpelling::Present(inner)
        | EntrySpelling::Absent(inner)
        | EntrySpelling::Cell(inner)
        | EntrySpelling::Alias(_, inner) => {
            at.push(0);
            let found = constructor_presence(inner, groups, at);
            if found.is_none() {
                at.pop();
            }
            found
        }
        EntrySpelling::Record(record) | EntrySpelling::Fragment(record) => {
            let constructor = !groups.iter().any(|group| group.name == record.head);
            record
                .fields
                .iter()
                .enumerate()
                .find_map(|(step, (name, value))| {
                    at.push(step);
                    let mut value = value;
                    let mut aliased = 0;
                    while let EntrySpelling::Alias(_, inner) = value {
                        at.push(0);
                        aliased += 1;
                        value = inner;
                    }
                    let found = match value {
                        EntrySpelling::Present(_) if constructor => {
                            Some((name.clone(), record.head.clone(), true))
                        }
                        EntrySpelling::Missing if constructor => {
                            Some((name.clone(), record.head.clone(), false))
                        }
                        EntrySpelling::Record(_) | EntrySpelling::Fragment(_) => {
                            constructor_presence(value, groups, at)
                        }
                        EntrySpelling::Present(inner) => {
                            at.push(0);
                            let found = constructor_presence(inner, groups, at);
                            if found.is_none() {
                                at.pop();
                            }
                            found
                        }
                        _ => None,
                    };
                    if found.is_none() {
                        at.truncate(at.len() - 1 - aliased);
                    }
                    found
                })
        }
        _ => None,
    }
}

/// The refusal of an admitted result entry over a collection that lies inside a cell the
/// sentence names (`lies_in`), such as its group bound whole in the subject (`objs: o` beside
/// `Objs::obj: { .. }`): that cell's entry already names every cell below it, the collection's
/// instances included, so the sentence names the collection twice, as a rule naming a group and
/// a leaf inside it does (`group-and-descendant`, which the rule's lowering gives the leaf). It
/// is asked before [`overwritten_collection`]: the subject does match the collection's
/// instances, through the cell, so the entry overwrites no collection the subject leaves out. At
/// the collection's name in its entry, the cell the sentence names twice, where the rule's
/// lowering puts the refusal of a leaf named twice.
fn collection_in_named_cell(
    id: &StableItemId,
    subject: &[Entry<'_>],
    result: &[Entry<'_>],
    lies_in: impl Fn(&DescriptorCellIdentity, &DescriptorCellIdentity) -> bool,
) -> Result<(), CollectionError> {
    for entry in result
        .iter()
        .filter(|entry| matches!(entry.kind.own.layers.first(), Some(Layer::Instances(_))))
    {
        let Some(holder) = subject
            .iter()
            .chain(result)
            .find(|named| lies_in(entry.cell, named.cell))
        else {
            continue;
        };
        let error = CollectionError::new(
            CollectionErrorKind::GroupAndDescendant,
            cell_entries::group_and_descendant_reason(
                id.item_name(),
                unraw(&holder.cell.field),
                unraw(&entry.cell.field),
            ),
        );
        return Err(
            match entry
                .field
                .name_range
                .as_ref()
                .or(entry.field.range.as_ref())
            {
                Some(range) => error.with_source_range(range.clone()),
                None => error,
            },
        );
    }
    Ok(())
}

/// The refusal of an admitted result entry over a collection the subject does not match (Q1's
/// overwrite of a `*` cell, design S5 §2.3). The entry replaces every instance the collection
/// holds, whatever they are, which needs a pattern over the whole collection; a readable
/// clause's collection entry matches instances one by one and keeps the others with `..` or
/// names every one, so the overwrite has no lowering yet, and is refused rather than read as
/// another rule. The entry means that in a readable clause and a `cells!` sentence alike, so
/// both judges ask it once their entries are admitted.
fn overwritten_collection(
    subject: &[Entry<'_>],
    result: &[Entry<'_>],
) -> Result<(), CollectionError> {
    let Some(entry) = result.iter().find(|entry| {
        matches!(entry.kind.own.layers.first(), Some(Layer::Instances(_)))
            && !subject.iter().any(|matched| matched.cell == entry.cell)
    }) else {
        return Ok(());
    };
    let name = unraw(&entry.cell.field);
    let error = CollectionError::new(
        CollectionErrorKind::CollectionOverwrite,
        format!(
            "the result writes the collection `{name}`, whose instances the subject does not match, so the rule replaces every instance `{name}` holds, whatever they are; a collection's instances are matched one by one, the others kept by `..`, so a rule that drops instances it never matched is not lowered yet: match the instances the rule replaces in the subject"
        ),
    );
    Err(match &entry.field.range {
        Some(range) => error.with_source_range(range.clone()),
        None => error,
    })
}

/// Refuses the first admitted entry, of the subject's then the result's, that names a child of a
/// collection's instance record as a `?` cell's `Some(..)` or `None`
/// ([`cell_entries::instance_child_presence`]), at the child: inside one instance it means whether
/// that instance holds the cell, and an instance record does not name a `?` or `*` child yet. It
/// is asked after the entries' form, kind and pairing, so a principle the same entry breaks (a
/// subject `None` the result does not create, an update with no base) answers first; the macros
/// carry such a child as a state for it.
fn instance_child_multiplicity(
    subject: &[Entry<'_>],
    result: &[Entry<'_>],
) -> Result<(), CollectionError> {
    for entry in subject.iter().chain(result) {
        let Some(spelling) = &entry.field.spelling else {
            continue;
        };
        let Some((at, reason)) =
            cell_entries::instance_child_presence(&entry.kind.own.layers, spelling)
        else {
            continue;
        };
        let error = CollectionError::new(CollectionErrorKind::InstanceChildMultiplicity, reason);
        let range = entry
            .field
            .located
            .iter()
            .find(|(path, _)| *path == at)
            .map(|(_, range)| range)
            .or(entry.field.range.as_ref());
        return Err(match range {
            Some(range) => error.with_source_range(range.clone()),
            None => error,
        });
    }
    Ok(())
}

/// The entries of one side of a readable clause, each field beside the one cell its name names;
/// `None` where a name names no single cell.
fn readable_entries<'a>(
    target: &'a super::resolve::HeadRuleTarget,
    fields: &'a [ParsedField<SourceRange>],
) -> Option<Vec<Entry<'a>>> {
    fields
        .iter()
        .map(|field| {
            let name = field.name.strip_prefix("r#").unwrap_or(&field.name);
            let (cell, kind, ancestor, sort) = target.entry(name)?;
            Some(Entry {
                cell,
                kind,
                field,
                sort: sort.map(str::to_owned),
                ancestor: ancestor.map(|marked| Ancestor {
                    marked: marked.clone(),
                    path: None,
                }),
            })
        })
        .collect()
}

/// Judges the entries of the sentence `id`, where the bundle holds it as a sentence with
/// `cells!` entries, and gives the warnings of the lints its admitted entries owe.
///
/// A subject record without `..` is the whole state: it names every cell of its configuration,
/// so each of its entries is what names its cell, and without the entry the record leaves the
/// cell out and is refused (`record-missing-children`). Such an entry has an effect, the cell's
/// naming, so it owes no [`Lint::NoEffectEntry`], whatever it matches. The record's choice to
/// name every cell is the author's, and `_` is how it names one it does not constrain: a lint
/// that advised the open record instead would answer every exact record that names such a cell.
fn judge_entries(
    index: &DescriptorIndex<'_>,
    id: &StableItemId,
    authored: &LocatedCells,
) -> Result<Vec<Diagnostic>, CollectionError> {
    let Some(descriptor) = index.get(id) else {
        return Ok(Vec::new());
    };
    let (reference, (subject, rest), result, rewrite, claim) = match descriptor.payload() {
        DescriptorPayload::ConfigurationRule(rule) => (
            &rule.subject_configuration,
            (&rule.subject.cells, &rule.subject.remainder),
            rule.result.as_ref().map(|cells| cells.cells.as_slice()),
            match (&rule.result, rule.sentence_kind) {
                (_, ConfigurationSentenceKind::Context) => Rewrite::Kept { as_rule: true },
                (Some(_), _) => Rewrite::Result,
                (None, _) => Rewrite::InPlace,
            },
            matches!(rule.sentence_kind, ConfigurationSentenceKind::Claim),
        ),
        DescriptorPayload::ContextAlias(alias) => (
            &alias.configuration,
            (&alias.pattern.cells, &alias.pattern.remainder),
            None,
            Rewrite::Kept { as_rule: false },
            false,
        ),
        DescriptorPayload::StructuredRule(rule) => {
            let Some(context) = &rule.function_context else {
                return Ok(Vec::new());
            };
            (
                &context.configuration,
                (&context.cells.cells, &context.cells.remainder),
                None,
                Rewrite::Kept { as_rule: false },
                false,
            )
        }
        _ => return Ok(Vec::new()),
    };
    let lints = judge_sentence(
        index,
        (id, reference),
        (subject, result),
        rewrite,
        claim,
        authored,
    )?;
    let exact = matches!(rest, krs_ir::ProtocolRuleFrame::Exact);
    Ok(lints
        .into_iter()
        .filter(|(_, _, lint)| !(exact && *lint == Lint::NoEffectEntry))
        .map(|(cell, range, lint)| linted(id, &cell, range, lint))
        .collect())
}

/// The warning of `lint`, owed by the entry of the cell `cell` of the sentence `id`: at the
/// entry's value, or naming the sentence where the value has no exact range.
fn linted(id: &StableItemId, cell: &str, range: Option<SourceRange>, lint: Lint) -> Diagnostic {
    let location = range.map_or(Location::None, Location::Source);
    let mut warning = Diagnostic::error(lint.code(), lint.reason(cell), location);
    warning.severity = Severity::Warning;
    if matches!(warning.primary.location, Location::None) {
        warning = warning.with_item(id.to_string());
    }
    warning
}

/// The cells of one side of a sentence, as the descriptor holds them.
type DescriptorCells =
    [krs_ir::ProtocolRuleCell<krs_ir::DescriptorCellReference, krs_ir::DescriptorTerm>];

/// An admitted entry's lint: the entry's cell, where its value is, and the lint.
type EntryLint = (String, Option<SourceRange>, Lint);

/// Judges one sentence's entries over the configuration `reference` names, from the level of
/// the one instance its subject is about ([`Tree::scoped`]), and gives the lints its admitted
/// entries owe ([`Sentence::judge`]). A sentence about one instance of a Map collection then
/// writes the instance's key only as it matched it ([`kept_key`]).
fn judge_sentence(
    index: &DescriptorIndex<'_>,
    (id, reference): (&StableItemId, &krs_ir::DescriptorConfigurationReference),
    (subject, result): (&DescriptorCells, Option<&DescriptorCells>),
    rewrite: Rewrite,
    claim: bool,
    authored: &LocatedCells,
) -> Result<Vec<EntryLint>, CollectionError> {
    let configuration = &reference.configuration;
    let Ok(declaration) = index.configuration(configuration) else {
        return Ok(Vec::new());
    };
    let tree = Tree::new(configuration, &declaration.declaration, index).scoped(
        reference.subject.as_ref(),
        rewrite != (Rewrite::Kept { as_rule: false }),
    );
    let subject_cells = subject;
    let subject = entries(&tree, subject, &authored.subject);
    let result = result
        .zip(authored.result.as_ref())
        .map(|(cells, authored)| entries(&tree, cells, authored));
    let (Some(subject), Some(result)) = (subject, result.unwrap_or(Some(Vec::new()))) else {
        return Ok(Vec::new());
    };
    let sentence = subject
        .iter()
        .map(|entry| (EntrySide::Subject, entry))
        .chain(result.iter().map(|entry| (EntrySide::Result, entry)))
        .map(|(side, entry)| SentenceEntry {
            side,
            cell: entry.cell,
            kind: &entry.kind,
            spelling: entry.field.spelling.as_ref(),
            anonymous_rest: entry.field.anonymous_rest,
        })
        .collect::<Vec<_>>();
    let judged = Sentence {
        form: EntryForm::Cells,
        entries: &sentence,
        rewrite,
        parameters: &authored.parameters,
        groups: &tree.groups,
    }
    .judge_located();
    let entry = |at: usize| {
        subject
            .iter()
            .chain(&result)
            .nth(at)
            .expect("a judged entry is the sentence's")
    };
    if judged.is_ok() {
        group_record_on_leaf(subject.iter().chain(&result), &tree.groups)?;
        items_off_the_computation(subject.iter().chain(&result), false)?;
        presence_in_constructor_record(subject.iter().chain(&result), &tree.groups)?;
        collection_in_named_cell(id, &subject, &result, |cell, holder| {
            tree.lies_in(cell, holder)
        })?;
        overwritten_collection(&subject, &result)?;
        for key in &tree.keys {
            kept_key(key, &subject, &result)?;
            kept_key_in_place(key, subject_cells, &subject)?;
        }
        if rewrite == (Rewrite::Kept { as_rule: false }) {
            fixed_cells_only(subject_cells, &subject)?;
        }
        instance_child_multiplicity(&subject, &result)?;
    }
    match judged {
        Ok(lints) => Ok(lints
            .into_iter()
            .map(|(at, lint)| {
                let entry = entry(at);
                (
                    unraw(&entry.cell.field).to_owned(),
                    entry.field.range.clone(),
                    lint,
                )
            })
            .collect()),
        Err((at, refusal)) => {
            let side = if at < subject.len() {
                EntrySide::Subject
            } else {
                EntrySide::Result
            };
            Err(refused(
                EntryForm::Cells,
                entry(at),
                subject_twin(&subject, entry(at), side),
                side,
                rewrite,
                claim,
                &refusal,
                &tree.groups,
            ))
        }
    }
}

/// Refuses the first admitted entry of a context alias's or an equation's function context's
/// pattern ([`Rewrite::Kept`], lowered as no rule's pattern is) that is a `?` cell's `Some(..)`,
/// a collection's instance list, or the entry of a fixed group cell. The entry means what it
/// means in a rule's subject, the present cell, the instances it names or the group's cell term,
/// matched and kept, but those two sentences' lowerings read the content of fixed leaf cells
/// only, so it is a limit, raised once the entries' kinds and pairing admit the pattern: a
/// `None`, which tests absence without creating the cell, is refused as such before.
fn fixed_cells_only(cells: &DescriptorCells, subject: &[Entry<'_>]) -> Result<(), CollectionError> {
    let Some((entry, unread)) = cells.iter().zip(subject).find_map(|(cell, entry)| {
        let unread = match (&cell.value, entry.kind.own.layers.first()) {
            (
                krs_ir::ProtocolRuleStateTerm::Present { .. }
                | krs_ir::ProtocolRuleStateTerm::Instances(_),
                _,
            ) => cell_entries::UnreadEntry::PresentOrInstances,
            (_, Some(Layer::Group(_))) => cell_entries::UnreadEntry::Group,
            _ => return None,
        };
        Some((entry, unread))
    }) else {
        return Ok(());
    };
    let error = CollectionError::new(
        CollectionErrorKind::FixedCellsOnly,
        cell_entries::fixed_cells_only_reason(unraw(&entry.cell.field), unread),
    );
    match &entry.field.range {
        Some(range) => Err(error.with_source_range(range.clone())),
        None => Err(error),
    }
}

/// The key of the Map collection instance a sentence is about: its key cell
/// ([`krs_ir::cell_kind::CellKind::instance_key`]) and every cell inside it, the whole of the
/// instance's identity.
struct InstanceKey {
    /// The key cell, then the cells inside it.
    cells: Vec<DescriptorCellIdentity>,
    /// The collection cell's field name, as a message names it.
    holder: String,
    /// The collection cell itself.
    holder_cell: DescriptorCellIdentity,
    /// The group the sentence is about, the collection's instance type.
    group: String,
}

impl InstanceKey {
    /// The key a readable target gives ([`super::resolve::TargetKey`]).
    fn of((cells, holder, holder_cell, group): super::resolve::TargetKey<'_>) -> Self {
        Self {
            cells: cells.to_vec(),
            holder: holder.to_owned(),
            holder_cell: holder_cell.clone(),
            group: group.to_owned(),
        }
    }

    fn holds(&self, cell: &DescriptorCellIdentity) -> bool {
        self.cells.contains(cell)
    }

    /// The refusal of a write of `cell`, at or inside the key, located at `range`.
    fn refusal(
        &self,
        cell: &DescriptorCellIdentity,
        range: Option<&SourceRange>,
    ) -> CollectionError {
        let error = CollectionError::new(
            CollectionErrorKind::CellEntry(Refusal::MapCollectionKey),
            krs_ir::subject::key_write_reason(
                &self.group,
                unraw(&self.holder),
                unraw(&self.cells[0].field),
                unraw(&cell.field),
            ),
        );
        match range {
            Some(range) => error.with_source_range(range.clone()),
            None => error,
        }
    }
}

/// Refuses a result entry at or inside the key of the instance the sentence is about that is
/// not provably what its subject matched for the same cell ([`cell_entries::keeps_key`], the
/// predicate an instance update's key is judged by): a sentence about one instance of a Map
/// collection is a local step of that instance, and the whole key is the instance's identity,
/// which a step that writes another key, or another value inside it, would change into another
/// instance. A result that leaves such a cell out keeps it.
fn kept_key(
    key: &InstanceKey,
    subject: &[Entry<'_>],
    result: &[Entry<'_>],
) -> Result<(), CollectionError> {
    // A leaf's value: inside its `Cell(..)` in `cells!`, as written in a readable record.
    fn value<'e>(entry: &Entry<'e>) -> Option<&'e EntrySpelling> {
        entry
            .field
            .spelling
            .as_ref()
            .map(|spelling| match spelling {
                EntrySpelling::Cell(inner) => &**inner,
                other => other,
            })
    }
    if names_holder(key, subject.iter().chain(result)) {
        return Ok(());
    }
    for written in result.iter().filter(|entry| key.holds(entry.cell)) {
        let matched = subject
            .iter()
            .find(|entry| entry.cell == written.cell)
            .and_then(value);
        if !value(written).is_some_and(|value| cell_entries::keeps_key(value, matched)) {
            return Err(key.refusal(written.cell, written.field.range.as_ref()));
        }
    }
    Ok(())
}

/// Whether one of `entries` names the collection cell that holds the instance `key` is the key
/// of, by the cell's identity (two groups may each have a cell of one field name).
/// Such a sentence names the key twice, through the holder's instance list and directly, which
/// the rule-level `group-and-descendant` refuses once every entry is admitted: until the two are
/// one, what the subject matched for the key is not stated once, so the key is not judged.
fn names_holder<'e>(key: &InstanceKey, mut entries: impl Iterator<Item = &'e Entry<'e>>) -> bool {
    entries.any(|entry| *entry.cell == key.holder_cell)
}

/// Refuses an in-place rewrite (`k::rewrite!`) at or inside the key of the instance the sentence
/// is about, unless it keeps what it matched ([`krs_ir::subject::rewrites_keep`]): a single-body
/// rule writes its cells where its subject rewrites them. The authored spelling reads a
/// `k::rewrite!` as an opaque macro, so the descriptor's terms are judged, beside the entries
/// they correspond to.
fn kept_key_in_place(
    key: &InstanceKey,
    cells: &DescriptorCells,
    entries: &[Entry<'_>],
) -> Result<(), CollectionError> {
    if names_holder(key, entries.iter()) {
        return Ok(());
    }
    for (cell, entry) in cells.iter().zip(entries) {
        if key.holds(&cell.field.cell)
            && !cell
                .value
                .terms()
                .into_iter()
                .all(krs_ir::subject::rewrites_keep)
        {
            return Err(key.refusal(entry.cell, entry.field.range.as_ref()));
        }
    }
    Ok(())
}

/// A field's name without its raw-identifier prefix.
fn unraw(name: &str) -> &str {
    name.strip_prefix("r#").unwrap_or(name)
}

/// One entry: its cell, the cell's kind, its authored field, and the cell's outermost `?` or
/// `*` ancestor.
struct Entry<'a> {
    cell: &'a DescriptorCellIdentity,
    kind: EntryKind,
    field: &'a ParsedField<SourceRange>,
    ancestor: Option<Ancestor>,
    /// A leaf's sort, as its declaration names it.
    sort: Option<String>,
}

/// A cell's outermost `?` or `*` ancestor, with the path of its group's struct where a
/// `cells!` fragment names it (`crate::Account`).
struct Ancestor {
    marked: MarkedAncestor,
    path: Option<String>,
}

/// The entries of one side, the descriptor's cells beside their authored fields; `None` where
/// they do not correspond one to one, or a cell has no place in the configuration.
fn entries<'a>(
    tree: &Tree<'_, '_>,
    cells: &'a DescriptorCells,
    fields: &'a [ParsedField<SourceRange>],
) -> Option<Vec<Entry<'a>>> {
    if cells.len() != fields.len() {
        return None;
    }
    cells
        .iter()
        .zip(fields)
        .map(|(cell, field)| {
            let identity = &cell.field.cell;
            let wanted = identity.field.strip_prefix("r#").unwrap_or(&identity.field);
            (field.name.strip_prefix("r#").unwrap_or(&field.name) == wanted).then_some(())?;
            Some(Entry {
                cell: identity,
                kind: tree.kind(identity)?,
                field,
                ancestor: tree.ancestor(identity),
                sort: tree.sort(identity),
            })
        })
        .collect()
}

/// A cell of a [`Tree`]: its ancestors, outermost first, the cell, and its owner.
type TreeEntry<'i, 'a> = (
    Vec<DescriptorCell<'i, 'a>>,
    DescriptorCell<'i, 'a>,
    &'a StableItemId,
);

/// A configuration's cells, each with the cells above it and the declaration that owns it.
struct Tree<'i, 'a> {
    /// Each cell's ancestors, outermost first, the cell, and its owner.
    cells: Vec<TreeEntry<'i, 'a>>,
    /// Each cell's enclosing cell, by its index in `cells`; absent for a top-level cell.
    parents: Vec<Option<usize>>,
    groups: Vec<GroupKind>,
    /// Where the sentence is about a cell group, the cell that holds it ([`Self::scoped`]).
    anchor: Option<usize>,
    /// Where that cell is a Map collection, its instance's key, then the key of each Map
    /// collection's instance inside it ([`Self::scoped`]); for a step typed by the
    /// configuration, the key of each Map collection's instance.
    keys: Vec<InstanceKey>,
    /// Whether the sentence is a step typed by the configuration, whose entries name the cells
    /// of Map collections' instances directly ([`Self::scoped`]).
    through_maps: bool,
}

impl<'i, 'a> Tree<'i, 'a> {
    fn new(
        owner: &'a StableItemId,
        declaration: &'a DescriptorCellDeclaration,
        index: &'i DescriptorIndex<'a>,
    ) -> Self {
        let mut tree = Self {
            cells: Vec::new(),
            parents: Vec::new(),
            groups: Vec::new(),
            anchor: None,
            keys: Vec::new(),
            through_maps: false,
        };
        tree.walk(owner, declaration, index, (&[], None), &[owner]);
        let mut groups = Vec::new();
        for (ancestors, cell, _) in &tree.cells {
            if ancestors.is_empty() {
                cell_entries::collect_groups(&cell.kind().layers, &mut groups);
            }
        }
        tree.groups = groups;
        tree
    }

    /// The tree judged from the level of the one instance a sentence about `subject` is a step
    /// of ([`krs_ir::subject::scope`]): an entry naming a cell below the group's cell is judged
    /// against the marks strictly below that cell, and a further `?` or `*` inside the instance
    /// keeps its mark. A subject without a scope, which resolution refuses first, leaves every
    /// cell judged from the configuration's level.
    ///
    /// The whole configuration (`None`) is judged from its own level. Where `steps`, the
    /// sentence is a rule, a claim or a context, whose cells lie in one instance of each holder
    /// on their deepest chain, so it names the cells of Map collections' instances directly
    /// ([`Self::judged_ancestors`]) and writes each such instance's key only as matched. A
    /// context alias and an equation's function context are evaluated in no instance (a
    /// function has one value for its arguments), so they keep every mark.
    fn scoped(mut self, subject: Option<&krs_ir::DescriptorSubject>, steps: bool) -> Self {
        if subject.is_none() && !steps {
            return self;
        }
        let cells = self
            .cells
            .iter()
            .zip(&self.parents)
            .map(|((_, cell, owner), parent)| krs_ir::TreeCell {
                identity: DescriptorCellIdentity {
                    owner: (*owner).clone(),
                    field: cell.field().rust_field.clone(),
                },
                parent: *parent,
                group: match &cell.field().content {
                    ProtocolCellContent::Nested { declaration } => {
                        Some(declaration.declaration.clone())
                    }
                    ProtocolCellContent::Leaf { .. } => None,
                },
                multiplicity: cell.kind().multiplicity(),
                computation: cell.kind().is_computation(),
                key: cell.kind().instance_key().map(str::to_owned),
            })
            .collect::<Vec<_>>();
        if subject.is_none() {
            self.through_maps = true;
            let holders = (0..cells.len())
                .filter_map(|holder| {
                    let group = cells[holder].group.as_ref()?;
                    (cells[holder].multiplicity == Multiplicity::Many(Order::Map))
                        .then(|| (holder, group.item_name().to_owned()))
                })
                .collect::<Vec<_>>();
            self.push_keys(&cells, holders);
            return self;
        }
        let Ok(krs_ir::SubjectScope {
            anchor: Some(anchor),
            ..
        }) = krs_ir::subject::scope(&cells, subject)
        else {
            return self;
        };
        self.anchor = Some(anchor);
        // The instance the sentence is about, and each instance of a Map collection inside it
        // whose cells it may name ([`Self::judged_ancestors`]): each of their keys is written
        // only as matched.
        let own = match subject {
            Some(krs_ir::DescriptorSubject::Group { declaration }) => {
                Some((anchor, declaration.item_name().to_owned()))
            }
            _ => None,
        };
        let nested = (anchor + 1..cells.len()).filter_map(|holder| {
            let group = cells[holder].group.as_ref()?;
            (cells[holder].multiplicity == Multiplicity::Many(Order::Map)
                && dropped(&self.parents, Some(anchor), holder) > 0)
                .then(|| (holder, group.item_name().to_owned()))
        });
        let holders = own.into_iter().chain(nested).collect::<Vec<_>>();
        self.push_keys(&cells, holders);
        self
    }

    /// Adds the key of each instance of the holders `holders` (each with its group's name) to
    /// the keys a sentence writes only as matched.
    fn push_keys(&mut self, cells: &[krs_ir::TreeCell], holders: Vec<(usize, String)>) {
        for (holder, group) in holders {
            let key = (0..cells.len())
                .filter(|&index| {
                    krs_ir::subject::keys_on_path(cells, index)
                        .iter()
                        .any(|&(on, _)| on == holder)
                })
                .map(|index| cells[index].identity.clone())
                .collect::<Vec<_>>();
            if !key.is_empty() {
                self.keys.push(InstanceKey {
                    cells: key,
                    holder: cells[holder].identity.field.clone(),
                    holder_cell: cells[holder].identity.clone(),
                    group,
                });
            }
        }
    }

    /// The ancestors of the cell at `index` an entry naming it is judged against: those
    /// strictly below the anchor, where the cell is inside the group the sentence is about, else
    /// all of them.
    ///
    /// Inside the group, and in a step typed by the configuration, the Map collections the cell
    /// lies in below the anchor (the configuration's level), outermost first up to the first
    /// other `?` or `*`, are not judged either: the sentence's cells lie in one instance of each
    /// holder on their deepest chain, so naming a cell of a nested instance matches one instance
    /// of each such collection, the one whose cell matches, as naming a cell of the group
    /// matches one instance of the group. Its key is matched where the sentence names it and
    /// written only as matched ([`Self::scoped`]). A Set or List collection, or an optional
    /// cell, keeps its mark.
    fn judged_ancestors<'t>(
        &'t self,
        index: usize,
        ancestors: &'t [DescriptorCell<'i, 'a>],
    ) -> &'t [DescriptorCell<'i, 'a>] {
        let dropped = dropped(&self.parents, self.anchor, index).min(ancestors.len());
        let below = &ancestors[dropped..];
        if dropped == 0 && !self.through_maps {
            return below;
        }
        let mut nested = 0;
        for (at, ancestor) in below.iter().enumerate() {
            match ancestor.kind().multiplicity() {
                Multiplicity::One => {}
                Multiplicity::Many(Order::Map) => nested = at + 1,
                _ => break,
            }
        }
        &below[nested..]
    }

    fn walk(
        &mut self,
        owner: &'a StableItemId,
        declaration: &'a DescriptorCellDeclaration,
        index: &'i DescriptorIndex<'a>,
        (ancestors, parent): (&[DescriptorCell<'i, 'a>], Option<usize>),
        seen: &[&'a StableItemId],
    ) {
        for field in &declaration.fields {
            let cell = DescriptorCell::new(field, index);
            let at = self.cells.len();
            self.cells.push((ancestors.to_vec(), cell.clone(), owner));
            self.parents.push(parent);
            if let ProtocolCellContent::Nested { declaration } = &field.content {
                let nested = &declaration.declaration;
                if seen.contains(&nested) {
                    continue;
                }
                let Ok(inner) = index.cell(nested) else {
                    continue;
                };
                let mut below = ancestors.to_vec();
                below.push(cell);
                let mut deeper = seen.to_vec();
                deeper.push(nested);
                self.walk(nested, inner, index, (&below, Some(at)), &deeper);
            }
        }
    }

    /// Whether the cell `cell` lies inside the cell `holder`, at any depth.
    fn lies_in(&self, cell: &DescriptorCellIdentity, holder: &DescriptorCellIdentity) -> bool {
        let Some((index, _)) = self.cell(cell) else {
            return false;
        };
        std::iter::successors(self.parents[index], |&parent| {
            self.parents[parent].filter(|&above| above < parent)
        })
        .any(|parent| {
            let (_, above, owner) = &self.cells[parent];
            **owner == holder.owner && above.field().rust_field == holder.field
        })
    }

    /// The cell `identity` names: its index, its ancestors, outermost first, itself, and its
    /// owner.
    fn cell(&self, identity: &DescriptorCellIdentity) -> Option<(usize, &TreeEntry<'i, 'a>)> {
        self.cells.iter().enumerate().find(|(_, (_, cell, owner))| {
            *owner == &identity.owner && cell.field().rust_field == identity.field
        })
    }

    /// The kind an entry naming `identity` is judged against: the layers of its `?` and `*`
    /// ancestors below the anchor ([`Self::judged_ancestors`]) and its own.
    fn kind(&self, identity: &DescriptorCellIdentity) -> Option<EntryKind> {
        let (index, (ancestors, cell, _)) = self.cell(identity)?;
        Some(CellKind::entry(
            self.judged_ancestors(index, ancestors),
            cell,
        ))
    }

    /// The sort of the cell `identity`, where it is a leaf, as its declaration names it.
    fn sort(&self, identity: &DescriptorCellIdentity) -> Option<String> {
        let (_, (_, cell, _)) = self.cell(identity)?;
        match &cell.field().content {
            ProtocolCellContent::Leaf { sort, .. } => Some(match &sort.sort {
                krs_ir::DescriptorSortRef::Declared(id) | krs_ir::DescriptorSortRef::Cell(id) => {
                    id.item_name().to_owned()
                }
                krs_ir::DescriptorSortRef::Builtin(builtin) => {
                    builtin.spec().marker_name.to_owned()
                }
                krs_ir::DescriptorSortRef::LeafCell(cell)
                | krs_ir::DescriptorSortRef::CellCollection(cell) => cell.field.clone(),
                krs_ir::DescriptorSortRef::Parameter(name) => name.clone(),
            }),
            ProtocolCellContent::Nested { .. } => None,
        }
    }

    /// The outermost `?` or `*` ancestor of the cell `identity` below the anchor
    /// ([`Self::judged_ancestors`]), if it has one.
    fn ancestor(&self, identity: &DescriptorCellIdentity) -> Option<Ancestor> {
        let (index, (ancestors, _, owner)) = self.cell(identity)?;
        let marked = self
            .judged_ancestors(index, ancestors)
            .iter()
            .find(|ancestor| ancestor.kind().multiplicity() != Multiplicity::One)?;
        let kind = marked.kind();
        let (layer, group) = match kind.layers.as_slice() {
            [layer, Layer::Group(group), ..] => (layer.clone(), group.name.clone()),
            _ => return None,
        };
        let field = marked.field();
        let ProtocolCellContent::Nested { declaration } = &field.content else {
            return None;
        };
        let instance = &declaration.declaration;
        let path = std::iter::once("crate")
            .chain(instance.module_path().iter().map(String::as_str))
            .chain(std::iter::once(instance.item_name()))
            .collect::<Vec<_>>()
            .join("::");
        Some(Ancestor {
            marked: MarkedAncestor {
                name: unraw(&field.rust_field).to_owned(),
                layer,
                group,
                direct: *owner == instance,
            },
            path: Some(path),
        })
    }
}

/// How many of the outermost ancestors of the cell at `index` an entry naming it is judged
/// without, the cells' enclosing cells being `parents`: the anchor and every cell above it,
/// where the cell is below the anchor; none where it is not, or the sentence has no anchor (it
/// is about the whole configuration).
fn dropped(parents: &[Option<usize>], anchor: Option<usize>, index: usize) -> usize {
    let Some(anchor) = anchor else {
        return 0;
    };
    // The enclosing cells, innermost first; parents precede their children.
    let above = std::iter::successors(parents[index], |&parent| {
        parents[parent].filter(|&outer| outer < parent)
    })
    .collect::<Vec<_>>();
    above
        .iter()
        .position(|&ancestor| ancestor == anchor)
        .map_or(0, |at| above.len() - at)
}

/// What the author is told to write instead of a refused entry, in the form `form` the entry is
/// written in, where the refusal's class has one spelling to advise (design §2.7):
/// - `cell-wrapper`, `optional-without-presence`, `collection-without-instances` and
///   `instance-list-shape`: the spelling of the cell's own kind, its marks outermost first;
/// - a path refusal (S1 (b)): the entry inside its outermost `?` or `*` ancestor's mark, at the
///   ancestor's level. A subject names the cell inside the ancestor's record; a result updates
///   the group or instance its subject names, through its record (`..me`), which is the
///   spelling for a child of the ancestor's own record other than a Map collection's key (the
///   instance's identity, which no update writes another of);
/// - `rest-mismatch`: the rest on both sides;
/// - `map-collection-key`: a created instance's key, its first child; an update keeps it;
/// - `record-update-base`: the label its subject gives the instance the update keeps;
/// - `list-back-kept`: the back instance named whole on both sides ([`list_back_kept`]).
fn advice(
    form: EntryForm,
    entry: &RefusedCell<'_>,
    side: EntrySide,
    rewrite: Rewrite,
    claim: bool,
    refusal: Refusal,
    groups: &[GroupKind],
) -> Option<String> {
    let own = entry.layers;
    match refusal {
        Refusal::CellWrapper | Refusal::InstanceListShape => {
            Some(format!("write its entry as `{}`", spelled(form, own)))
        }
        Refusal::CollectionWithoutInstances => Some(format!(
            "write its entry as its instances, `{}`",
            spelled(form, own)
        )),
        // An initializer gives an absent cell its template, `None` none (`none-in-initializer`).
        Refusal::OptionalWithoutPresence if side == EntrySide::Initializer => Some(
            "write its value inside `Some(..)`, or inside `k::absent!(..)` for a cell that starts absent"
                .to_owned(),
        ),
        Refusal::OptionalWithoutPresence => {
            Some("write its entry inside `Some(..)`, or as `None` for its absence".to_owned())
        }
        Refusal::BelowOptionalAncestor | Refusal::BelowCollectionAncestor => {
            below_ancestor(form, entry, entry.ancestor?, side, rewrite, claim, groups)
        }
        Refusal::RestMismatch => Some(rest_mismatch_advice(form, entry)),
        Refusal::MapCollectionKey => {
            let key = match own {
                [Layer::Instances(order), Layer::Group(group), ..] => group.key(*order)?,
                _ => return None,
            };
            Some(format!("write its key first, `{key}: ..`"))
        }
        Refusal::ListBackKept => list_back_kept(own, rewrite, claim),
        Refusal::RecordUpdateBase => {
            let label = entry.spelling.and_then(update_label)?;
            let group = match own {
                [Layer::Instances(_), Layer::Group(group), ..] => group.name.as_str(),
                _ => return None,
            };
            let instance = if form == EntryForm::Cells {
                "k::fragment![..]".to_owned()
            } else {
                format!("{group} {{ .. }}")
            };
            Some(format!(
                "no subject instance is labelled `{label} @`; label the one the result updates where the subject matches it, `{label} @ {instance}`, or create the instance from a record of its own"
            ))
        }
        _ => None,
    }
}

/// The advice of a List collection's back instance matched in place (`list-back-kept`), whose
/// collection has the layers `layers`: the way, accepted today, to state the same step. A record
/// naming every child of the instance, on both sides, is no update in place: the sentence removes
/// the subject's instance and creates the result's at the back, which leaves the list the step in
/// place would, a read included (the result restating the instance). A single-body rule states
/// it as a rule with a result. A context has no result, so none.
fn list_back_kept(layers: &[Layer], rewrite: Rewrite, claim: bool) -> Option<String> {
    let [Layer::Instances(Order::List), Layer::Group(group), ..] = layers else {
        return None;
    };
    let children = group
        .children
        .iter()
        .map(|(child, _)| format!("`{}`", unraw(child)))
        .collect::<Vec<_>>()
        .join(", ");
    let (write, sentence) = match rewrite {
        Rewrite::Result if claim => ("", "the claim"),
        Rewrite::Result => ("", "the rule"),
        Rewrite::InPlace => ("write the rule with a result, and ", "it"),
        Rewrite::Kept { .. } => return None,
    };
    Some(format!(
        "{write}name every child of the back instance ({children}) without `..`, in the subject and again in the result's list: {sentence} then removes the instance and creates the result's at the back, which leaves the same list as the step in place"
    ))
}

/// The advice of a path refusal of the entry `entry`, below its outermost `?` or `*` ancestor
/// `ancestor` ([`advice`]).
///
/// The record of the ancestor (its group's inside `Some(..)`, or its instance record) is the
/// form an entry for the cell takes, except where no record writes it: a record names no `?` or
/// `*` child yet, so a cell that is one, or that lies below one inside the ancestor's group, is
/// out of every record's reach; and a context alias or an equation's function context reads
/// fixed cells only, so no `Some(..)` or instance list is a form there at all.
fn below_ancestor(
    form: EntryForm,
    entry: &RefusedCell<'_>,
    ancestor: &Ancestor,
    side: EntrySide,
    rewrite: Rewrite,
    claim: bool,
    groups: &[GroupKind],
) -> Option<String> {
    let name = entry.name;
    let marked = &ancestor.marked;
    let holder = &marked.name;
    let of = match &marked.layer {
        Layer::Optional => format!("`{name}` is a cell of the optional group `{holder}`"),
        _ => format!("`{name}` is a cell of an instance of the collection `{holder}`"),
    };
    let own_mark = matches!(
        entry.layers.first(),
        Some(Layer::Optional | Layer::Instances(_))
    );
    let below_another = entry.path.len() > 1;
    if rewrite == (Rewrite::Kept { as_rule: false }) {
        return Some(read_fixed_cells_only(
            &of,
            name,
            marked,
            own_mark || below_another,
        ));
    }
    if own_mark || (!marked.direct && below_another) {
        return Some(out_of_records(&of, name, marked, own_mark, claim));
    }
    let key = match &marked.layer {
        Layer::Instances(order) => groups
            .iter()
            .find(|group| group.name == marked.group)
            .and_then(|group| group.key(*order))
            .is_some_and(|key| key == name),
        _ => false,
    };
    let cells = form == EntryForm::Cells;
    if cells && ancestor.path.is_none() {
        return Some(format!("{of}; name it inside the record of `{holder}`"));
    }
    // A record of the ancestor's group whose fields are `fields`, in the form's spelling.
    let record = |fields: &str| match &ancestor.path {
        Some(path) if cells => format!("k::fragment![{path} {{ {fields} }}]"),
        _ => format!("{} {{ {fields} }}", marked.group),
    };
    // The ancestor's mark around `inner`.
    let marked_around = |inner: &str| match &marked.layer {
        Layer::Optional => format!("Some({inner})"),
        Layer::Instances(Order::List) => format!("[{inner}, ..]"),
        _ => format!("{{ {inner}, .. }}"),
    };
    match side {
        EntrySide::Result if !marked.direct || key => Some(format!(
            "{of}; a result updates {} through the record its subject names (`me @ ..`) and puts back with `..me` after the children it writes",
            match &marked.layer {
                Layer::Optional => "such a group",
                _ => "such an instance",
            }
        )),
        EntrySide::Result => {
            if cells && !matches!(marked.layer, Layer::Optional) {
                // The `cells!` spelling the path sweep's reviewed advice states.
                let path = ancestor.path.as_deref()?;
                let (open, close) = match &marked.layer {
                    Layer::Instances(Order::List) => ("[", "]"),
                    _ => ("{ ", " }"),
                };
                return Some(format!(
                    "{of}, and a result updates the instance its subject names, `{holder}: {open}me @ k::fragment![{path} {{ .. }}], ..{close}`; so write the result's entry as `{holder}: {open}k::fragment![{path} {{ {name}: v, ..me }}], ..{close}`"
                ));
            }
            Some(format!(
                "{of}, and a result updates the {} its subject names, `{holder}: {}`; so write the result's entry as `{holder}: {}`",
                match &marked.layer {
                    Layer::Optional => "group",
                    _ => "instance",
                },
                marked_around(&format!("me @ {}", record(".."))),
                marked_around(&record(&format!("{name}: v, ..me"))),
            ))
        }
        _ if !marked.direct => Some(format!(
            "{of}; name it inside the record of `{holder}`, nested as its declaration nests it"
        )),
        _ => Some(format!(
            "{of}; so write the entry inside its record, `{holder}: {}`",
            marked_around(&record(&format!("{name}: .., .."))),
        )),
    }
}

/// The advice of a path refusal in a context alias or an equation's function context, which read
/// fixed leaf cells only ([`cell_entries::fixed_cells_only_reason`]): a sentence of either form reads
/// one instance's cells only where it is typed by the instance's group, which an optional cell
/// and a Map collection admit (the instance it is evaluated in, the one present or the one its
/// key names), and then names a cell of that group at its own level, unless the cell holds
/// presence or instances itself or lies below a further holder (`marked_below`). A Set's or a
/// List's instance is no sentence's subject.
fn read_fixed_cells_only(
    of: &str,
    name: &str,
    marked: &MarkedAncestor,
    marked_below: bool,
) -> String {
    let limit = format!(
        "{of}; a context alias and an equation's function context read fixed leaf cells only, which a record of `{}` is not",
        marked.name
    );
    let typed = matches!(marked.layer, Layer::Optional | Layer::Instances(Order::Map));
    if !typed || marked_below {
        return limit;
    }
    format!(
        "{limit}: such a sentence reads one `{group}`'s cells where it is typed by `{group}`, which names `{name}` at its own level",
        group = marked.group
    )
}

/// The advice of a path refusal of a cell outside every record's reach ([`below_ancestor`]): it
/// holds presence or instances itself, a child of the ancestor's group or of a group child of it,
/// or lies below a further `?` or `*` cell there, and a record names no `?` or `*` child yet. A
/// rule for the group of an optional cell or a Map collection is a step of the one instance it is
/// about and names that instance's cells from its own level; a Set's or a List's instance is no
/// rule's subject, and a Map collection's instance cells are named at the record's level instead.
/// A claim (`claim`) is typed by the configuration, never by a group: it names a Map
/// collection's instance cells at the record's level as a rule for the configuration does, and
/// nothing else reaches the cell.
fn out_of_records(
    of: &str,
    name: &str,
    marked: &MarkedAncestor,
    own_mark: bool,
    claim: bool,
) -> String {
    let unreached = format!(
        "{of}, {}, and a record names no `?` or `*` cell yet, so no entry inside the record of `{}` reaches `{name}`",
        if own_mark {
            "and is a `?` or `*` cell itself"
        } else {
            "below a further `?` or `*` cell there"
        },
        marked.name
    );
    let group = &marked.group;
    match (&marked.layer, claim) {
        (Layer::Instances(Order::List | Order::Set), true) => format!(
            "{unreached}; a claim is typed by the configuration, never by `{group}`, and names the cells of a Map collection's instance at the record's level, so hold the instances in a Map collection keyed by an id"
        ),
        (Layer::Instances(order @ (Order::List | Order::Set)), false) => format!(
            "{unreached}; a rule for `{group}` is refused for a {} collection's instance, so hold the instances in a Map collection keyed by an id, whose instances' cells a rule names at the record's level",
            match order {
                Order::List => "List",
                _ => "Set",
            }
        ),
        (Layer::Optional, true) => format!(
            "{unreached}; a claim is typed by the configuration, never by `{group}`, so no claim names `{name}` yet"
        ),
        (Layer::Optional, false) => format!(
            "{unreached}; a rule for `{group}` is a step of the present `{group}` and names its cells from that level"
        ),
        (_, true) => format!(
            "{unreached}; a claim is typed by the configuration, never by `{group}`, and names one `{group}`'s cells at the record's level"
        ),
        (_, false) => format!(
            "{unreached}; a rule for `{group}` is a step of one `{group}` and names its cells from that level"
        ),
    }
}

/// The label of the first instance update (`..label`) the entry `spelling` writes.
fn update_label(spelling: &EntrySpelling) -> Option<&str> {
    use krs_syntax::cell_entry::RecordTail;
    match spelling {
        EntrySpelling::Record(record) | EntrySpelling::Fragment(record) => match &record.tail {
            RecordTail::Update(label) => Some(label),
            _ => record
                .fields
                .iter()
                .find_map(|(_, value)| update_label(value)),
        },
        EntrySpelling::Present(inner)
        | EntrySpelling::Alias(_, inner)
        | EntrySpelling::Cell(inner) => update_label(inner),
        EntrySpelling::Brackets(seq)
        | EntrySpelling::Braces(seq)
        | EntrySpelling::InstanceList(seq)
        | EntrySpelling::InstanceSet(seq) => seq.items.iter().find_map(update_label),
        _ => None,
    }
}

/// The spelling of a cell of the layers `layers`, outermost first (P2), in the form `form`:
/// `Some(..)`, instance records in brackets (List) or braces (Set, Map), the computation's
/// `KCell(..)` (its items in brackets in a readable record), a leaf's `Cell(..)` (its value
/// alone in a readable record), or a group's record.
fn spelled(form: EntryForm, layers: &[Layer]) -> String {
    let group = |inner: &[Layer]| match inner.first() {
        Some(Layer::Group(group)) => group.name.clone(),
        _ => "G".to_owned(),
    };
    match (form, layers.split_first()) {
        (_, Some((Layer::Optional, inner))) => format!("Some({})", spelled(form, inner)),
        (EntryForm::Cells, Some((Layer::Instances(Order::List), _))) => {
            "[k::fragment![..], ..]".to_owned()
        }
        (EntryForm::Cells, Some((Layer::Instances(Order::Set | Order::Map), _))) => {
            "{ k::fragment![..], .. }".to_owned()
        }
        (EntryForm::Cells, Some((Layer::Computation, _))) => {
            "k::configuration::KCell(..)".to_owned()
        }
        (EntryForm::Cells, Some((Layer::Leaf(_), _))) => "k::configuration::Cell(..)".to_owned(),
        (EntryForm::Cells, Some((Layer::Group(_), _)) | None) => "k::fragment![..]".to_owned(),
        // An initializer's value for a collection is one instance's template.
        (EntryForm::Initializer, Some((Layer::Instances(_), inner))) => spelled(form, inner),
        (_, Some((Layer::Instances(Order::List), inner))) => {
            format!("[{} {{ .. }}, ..]", group(inner))
        }
        (_, Some((Layer::Instances(Order::Set | Order::Map), inner))) => {
            format!("{{ {} {{ .. }}, .. }}", group(inner))
        }
        // An initializer's computation lists every item: it keeps no rest.
        (EntryForm::Initializer, Some((Layer::Computation, _))) => "k::k![x]".to_owned(),
        (_, Some((Layer::Computation, _))) => "[x, ..]".to_owned(),
        (_, Some((Layer::Leaf(_), _))) => "x".to_owned(),
        (_, Some((Layer::Group(group), _))) => format!("{} {{ .. }}", group.name),
        (_, None) => "G { .. }".to_owned(),
    }
}

/// The cell a refusal is about: the refused entry's own, or the child of a group or instance
/// record inside it whose content the refusal is raised in ([`cell_entries::nested_cell`]).
struct RefusedCell<'a> {
    /// The cell's name.
    name: &'a str,
    /// The cell's own layers.
    layers: &'a [Layer],
    /// The layers its `?` and `*` ancestors put above it, outermost first.
    path: &'a [Layer],
    /// Its outermost `?` or `*` ancestor above the record's level (the refused entry's own).
    ancestor: Option<&'a Ancestor>,
    /// The cell's content as written.
    spelling: Option<&'a EntrySpelling>,
    /// A result entry's subject twin, the same cell's subject entry as written, which a
    /// pairing refusal's advice reads.
    twin: Option<&'a EntrySpelling>,
}

/// The subject entry of the cell of the result entry `entry` (on `side`), as written: what a
/// pairing refusal at the result reads of the subject.
fn subject_twin<'e>(
    subject: &'e [Entry<'_>],
    entry: &Entry<'_>,
    side: EntrySide,
) -> Option<&'e EntrySpelling> {
    if side != EntrySide::Result {
        return None;
    }
    subject
        .iter()
        .find(|twin| twin.cell == entry.cell)
        .and_then(|twin| twin.field.spelling.as_ref())
}

/// What a rest on one side of a cell is fixed by, in a spelling its kind and route admit; a
/// present `?` cell's rest is its content's (`Some(..)`).
/// - A computation, fixed or present `?`, keeps its rest with `..` on both sides. A readable rule
///   keeps a fixed computation's rest always, and reads no `?` computation's items yet; a
///   `cells!` rule names it in the subject (`rest @ ..`) and then puts it back (`..rest`),
///   writes it after another computation cell's items (`aux: KCell(..rest)`), which moves it,
///   or reads it in a condition, which drops it from the cell (a named rest it neither puts
///   back nor uses is refused).
/// - A list keeps its rest with `..` on both sides. Matched by brackets of its rest alone
///   (`[..]`, where `[rest @ ..]` is refused) it is matched whole, by `_` to drop it or by a
///   binder to move it; otherwise its subject names the rest (`rest @ ..`) to drop or move it.
/// - A map's result writes the whole map and has no `..` (the reason says so). A `cells!`
///   subject names the rest (`rest @ ..`), as for a computation: the result puts it back under
///   other entries (`..rest`), another cell's result writes it (`Cell(rest)`), or a condition
///   reads it. A readable record names no map rest a result can write, so its rule matches the
///   map whole and builds the new map from it.
/// - A collection keeps its other instances with `..` on both sides: a rule does not remove
///   them yet.
/// - Any other content keeps its rest with `..` on both sides.
///
/// A record child's subject twin is its other side as the pairing pairs it
/// ([`cell_entries::paired_subject`]).
fn rest_mismatch_advice(form: EntryForm, entry: &RefusedCell<'_>) -> String {
    let keep = "write `..` on both sides to keep the rest";
    let mut twin = entry.twin;
    while let Some(EntrySpelling::Present(inner)) = twin {
        twin = Some(inner);
    }
    let item_less = matches!(
        twin,
        Some(EntrySpelling::Brackets(seq))
            if seq.items.is_empty() && matches!(seq.rest, Some((EntryRest::Anonymous, _)))
    );
    let content = {
        let mut layers = entry.layers;
        while let [Layer::Optional, inner @ ..] = layers {
            layers = inner;
        }
        layers
    };
    match (entry.layers, content) {
        // A readable record reads no `?` computation's items yet: its brackets there are read as
        // a list's.
        ([Layer::Optional, ..], [Layer::Computation]) if form.is_readable() => "a readable record does not read the items of a `?` computation cell yet; a `cells!` rule writes them in `Some(KCell(..))`, where `..` on both sides keeps the rest and a subject that names it (`Some(KCell(x, rest @ ..))`) may put it back after other items (`KCell(y, ..rest)`), move it into another computation cell (`aux: KCell(..rest)`), or drop it where a condition reads it".to_owned(),
        (_, [Layer::Computation]) if form.is_readable() => format!(
            "{keep}: a readable rule keeps a computation's rest, and a `cells!` rule whose subject names it (`KCell(x, rest @ ..)`) may put it back after other items (`KCell(y, ..rest)`), move it into another computation cell (`aux: KCell(..rest)`), or drop it where a condition reads it"
        ),
        (_, [Layer::Computation]) => format!(
            "{keep}, or name it in the subject (`KCell(x, rest @ ..)`) to put it back after other items (`KCell(y, ..rest)`), to move it into another computation cell (`aux: KCell(..rest)`), or to drop it where a condition reads it: a named rest the rule neither puts back nor uses is refused"
        ),
        (_, [Layer::Leaf(Notation::List | Notation::Cons)]) if item_less => format!(
            "{keep}, or match the list whole to drop or move it: `_` drops it, and a binder `rest` moves it (`..rest`)"
        ),
        (_, [Layer::Leaf(Notation::List | Notation::Cons)]) => {
            format!("{keep}, or name it in the subject (`rest @ ..`) to drop or move it")
        }
        (_, [Layer::Leaf(Notation::Map)]) if form.is_readable() => "a readable record names no rest of a map that a result can write, so match the map whole with a binder `m` and build its new map from it (`map::update(m, k, w)`); a `cells!` rule whose subject names the rest (`map![k -> v, rest @ ..]`) may put it back under other entries (`map![k -> w, ..rest]`), move it into another cell (`Cell(rest)`), or drop it where a condition reads it".to_owned(),
        (_, [Layer::Leaf(Notation::Map)]) => "name the rest in the subject (`map![k -> v, rest @ ..]`) to put it back under other entries (`map![k -> w, ..rest]`), to move it into another cell (`Cell(rest)`), or to drop it where a condition reads it: a named rest the rule neither puts back nor uses is refused".to_owned(),
        (_, [Layer::Instances(_), ..]) => {
            format!("{keep}: a rule does not remove a collection's other instances yet")
        }
        _ => keep.to_owned(),
    }
}

/// The refusal `located` of the entry `entry`, on the side `side` of a sentence written in
/// `form`, a claim where `claim` says so: why ([`Refusal::reason`]), then what to write instead
/// where its class advises it ([`advice`]). A refusal raised inside the content of a child of a
/// group or instance record the entry writes names that child, the cell whose content is wrong
/// (P1, P7), but for a form refusal, which is judged without the declaration and names the entry's
/// cell ([`Refusal::is_form`]); it stands at the spelling it is raised at, or at the entry's value
/// where that spelling has no range.
#[expect(
    clippy::too_many_arguments,
    reason = "a refusal reads its entry, the entry's subject twin and the sentence around it"
)]
fn refused(
    form: EntryForm,
    entry: &Entry<'_>,
    twin: Option<&EntrySpelling>,
    side: EntrySide,
    rewrite: Rewrite,
    claim: bool,
    located: &cell_entries::Located,
    groups: &[GroupKind],
) -> CollectionError {
    let refusal = located.refusal;
    let spelling = entry.field.spelling.as_ref();
    let nested = spelling
        .filter(|_| !refusal.is_form())
        .and_then(|spelling| {
            cell_entries::nested_cell(&entry.kind.own.layers, spelling, &located.at)
        });
    let nested_kind = nested.map(|nested| EntryKind {
        path: CellKind::default(),
        own: nested.kind.clone(),
    });
    let (cell, kind, sort) = match (nested, &nested_kind) {
        (Some(nested), Some(kind)) => (
            RefusedCell {
                name: unraw(nested.name),
                layers: &nested.kind.layers,
                path: &[],
                ancestor: None,
                spelling: spelling.and_then(|spelling| {
                    cell_entries::spelling_at(spelling, &located.at[..nested.depth])
                }),
                twin: twin.zip(spelling).and_then(|(twin, spelling)| {
                    cell_entries::paired_subject(
                        &entry.kind.own.layers,
                        twin,
                        spelling,
                        &located.at[..nested.depth],
                    )
                }),
            },
            kind,
            None,
        ),
        _ => (
            RefusedCell {
                name: unraw(&entry.cell.field),
                layers: &entry.kind.own.layers,
                path: &entry.kind.path.layers,
                ancestor: entry.ancestor.as_ref(),
                spelling,
                twin,
            },
            &entry.kind,
            entry.sort.as_deref(),
        ),
    };
    let mut detail = refusal.reason(form, cell.name, kind, sort);
    if let Some(advice) = advice(form, &cell, side, rewrite, claim, refusal, groups) {
        detail = format!("{detail}; {advice}");
    }
    let error = CollectionError::new(CollectionErrorKind::CellEntry(refusal), detail);
    // The spelling the refusal is raised at, or the nearest one around it that has a range.
    let range = (0..=located.at.len()).rev().find_map(|depth| {
        entry
            .field
            .located
            .iter()
            .find(|(path, _)| path[..] == located.at[..depth])
            .map(|(_, range)| range)
    });
    match range.or(entry.field.range.as_ref()) {
        Some(range) => error.with_source_range(range.clone()),
        None => error,
    }
}

#[cfg(test)]
mod tests {
    use krs_ir::cell_kind::{CellKind, EntryKind};
    use krs_ir::{DescriptorCellIdentity, ItemKind, PackageId, StableItemId};
    use krs_syntax::cell_entry::EntrySpelling;

    use super::{Entry, InstanceKey, ParsedField, dropped, kept_key};
    use crate::CollectionErrorKind;

    /// `Machine { harts: Harts { hart*: Hart { id, k, fpu?: Fpu { f } } }, mem }`, by parent.
    const PARENTS: [Option<usize>; 7] = [
        None,    // 0 harts
        Some(0), // 1 hart*
        Some(1), // 2 id
        Some(1), // 3 k
        Some(1), // 4 fpu?
        Some(4), // 5 f
        None,    // 6 mem
    ];

    #[test]
    fn a_sentence_without_a_subject_judges_every_cell_from_the_configuration() {
        for index in 0..PARENTS.len() {
            assert_eq!(dropped(&PARENTS, None, index), 0, "{index}");
        }
    }

    #[test]
    fn a_sentence_about_an_instance_drops_the_anchor_and_the_cells_above_it() {
        // About `Hart`, held by `hart`: its cells drop `harts` and `hart`; a cell of the optional
        // group inside keeps `fpu`.
        assert_eq!(dropped(&PARENTS, Some(1), 2), 2);
        assert_eq!(dropped(&PARENTS, Some(1), 3), 2);
        assert_eq!(dropped(&PARENTS, Some(1), 5), 2);
        // About `Fpu`, held by `fpu`: `f` drops all three.
        assert_eq!(dropped(&PARENTS, Some(4), 5), 3);
        // A cell outside the group keeps every ancestor.
        assert_eq!(dropped(&PARENTS, Some(1), 6), 0);
        assert_eq!(dropped(&PARENTS, Some(4), 3), 0);
    }

    fn identity(field: &str) -> DescriptorCellIdentity {
        DescriptorCellIdentity {
            owner: StableItemId::new(
                PackageId::new("ORG-EXAMPLE", "test", "0.1.0", "workspace").unwrap(),
                ["state"],
                "Hart",
                ItemKind::Cell,
                "",
            )
            .unwrap(),
            field: field.to_owned(),
        }
    }

    fn field(name: &str, spelling: EntrySpelling) -> ParsedField<krs_ir::SourceRange> {
        ParsedField {
            name: name.to_owned(),
            spelling: Some(spelling),
            range: None,
            name_range: None,
            located: Vec::new(),
            anonymous_rest: false,
        }
    }

    fn entry<'a>(
        cell: &'a DescriptorCellIdentity,
        field: &'a ParsedField<krs_ir::SourceRange>,
    ) -> Entry<'a> {
        Entry {
            cell,
            kind: EntryKind {
                path: CellKind::default(),
                own: CellKind::default(),
            },
            field,
            ancestor: None,
            sort: None,
        }
    }

    /// A Map instance's key entry is kept where the result leaves it out, restates the binder
    /// its subject matched it with (inside `Cell(..)` in `cells!`, bare in a readable record), or
    /// the same literal; any other value, or a key the subject does not name, is refused as
    /// `map-collection-key`.
    #[test]
    fn a_sentence_about_a_map_instance_writes_its_key_only_as_it_matched_it() {
        let (id, pc) = (identity("id"), identity("pc"));
        let key = InstanceKey {
            cells: vec![id.clone()],
            holder: "hart".to_owned(),
            holder_cell: identity("hart"),
            group: "Hart".to_owned(),
        };
        let binder = |name: &str| EntrySpelling::Binder(name.to_owned());
        let literal = |text: &str| EntrySpelling::Literal(text.to_owned());
        let cell = |inner: EntrySpelling| EntrySpelling::Cell(Box::new(inner));
        let judge = |subject: Option<EntrySpelling>, result: Option<EntrySpelling>| {
            let pc_field = field("pc", binder("p"));
            let subject_field = subject.map(|spelling| field("id", spelling));
            let result_field = result.map(|spelling| field("id", spelling));
            let mut subject = vec![entry(&pc, &pc_field)];
            subject.extend(subject_field.as_ref().map(|field| entry(&id, field)));
            let mut result = vec![entry(&pc, &pc_field)];
            result.extend(result_field.as_ref().map(|field| entry(&id, field)));
            kept_key(&key, &subject, &result).map_err(|error| error.kind())
        };
        let refused = Err(CollectionErrorKind::CellEntry(
            krs_syntax::cell_entries::Refusal::MapCollectionKey,
        ));
        assert_eq!(judge(Some(binder("me")), None), Ok(()));
        assert_eq!(judge(None, None), Ok(()));
        assert_eq!(judge(Some(binder("me")), Some(binder("me"))), Ok(()));
        assert_eq!(
            judge(Some(cell(binder("me"))), Some(cell(binder("me")))),
            Ok(())
        );
        assert_eq!(judge(Some(literal("0")), Some(literal("0"))), Ok(()));
        assert_eq!(judge(Some(binder("me")), Some(binder("other"))), refused);
        assert_eq!(judge(Some(literal("0")), Some(literal("1"))), refused);
        assert_eq!(
            judge(
                Some(cell(binder("me"))),
                Some(cell(EntrySpelling::Call(vec![binder("me")])))
            ),
            refused
        );
        assert_eq!(judge(None, Some(binder("me"))), refused);
        // A cell inside a composite key is part of the identity: restated it is kept, written
        // anew it is refused.
        let composite = InstanceKey {
            cells: vec![identity("cpu"), pc.clone()],
            holder: "hart".to_owned(),
            holder_cell: identity("hart"),
            group: "Hart".to_owned(),
        };
        let (matched, kept, moved) = (
            field("pc", binder("p")),
            field("pc", binder("p")),
            field("pc", literal("1")),
        );
        let subject = [entry(&pc, &matched)];
        assert!(kept_key(&composite, &subject, &[entry(&pc, &kept)]).is_ok());
        let error = kept_key(&composite, &subject, &[entry(&pc, &moved)]).unwrap_err();
        assert!(
            error
                .detail()
                .starts_with("the rule writes `pc`, a cell inside the key `cpu`,"),
            "{}",
            error.detail()
        );
    }

    /// A readable clause's carried refusals are kept in the order they are asked: a subject's
    /// map read of a cell the result writes (M3), raised once the subject's entries are admitted,
    /// then the pairing's, raised once every entry is.
    #[test]
    fn a_readable_clauses_subject_limit_is_carried_before_its_pairing() {
        use krs_syntax::KrsSyntax as _;
        let block = krs_syntax::RuleBlock::parse_source(
            "for Machine; x: { k: [Go(), ..], env: { y -> z, .. }, pc: [.., x] } => { k: [..], env: x, pc: 0 };",
        )
        .expect("the clause parses, its refusals carried");
        let cells = super::ParsedCells::of_readable(
            &block.clauses()[0],
            krs_syntax::cell_entry::EntryForm::Readable,
        )
        .expect("the records read as fields");
        let carried = cells
            .after
            .iter()
            .map(|after| (after.subject, after.detail.as_str()))
            .collect::<Vec<_>>();
        assert!(
            matches!(
                carried.as_slice(),
                [(true, limit), (false, pairing)]
                    if limit.contains("a preserved map-item cell is omitted")
                        && pairing.contains("the pattern's `..` keeps the rest of the list")
            ),
            "{carried:?}"
        );
    }
}
