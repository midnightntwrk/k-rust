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
    CellKind, DescriptorCell, EntryKind, GroupKind, Layer, Multiplicity, Order,
};
use krs_ir::{
    ConfigurationSentenceKind, DescriptorBundle, DescriptorCellDeclaration, DescriptorCellIdentity,
    DescriptorIndex, DescriptorPayload, ProtocolCellContent, SourceRange, StableItemId,
};
use krs_syntax::cell_entries::{self, EntrySide, Lint, Refusal, Rewrite, Sentence, SentenceEntry};
use krs_syntax::cell_entry::{EntryForm, EntrySpelling};

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
/// subject frame of its kind.
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
/// its sequence's tail ([`krs_syntax::StateRuleItem::misplaced_tail`]), or a result remainder's
/// ([`krs_syntax::StateRuleItem::reuse_refusal`]); the parser's message, and where it is.
#[derive(Clone, Debug)]
struct After<R> {
    kind: CollectionErrorKind,
    detail: String,
    range: Option<R>,
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
        .map(|error| (CollectionErrorKind::SourceSyntax, error))
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

fn located_fields(
    fields: Vec<krs_syntax::cell_entry::CellsField>,
) -> Option<Vec<ParsedField<Coordinates>>> {
    fields
        .into_iter()
        .map(|field| {
            Some(ParsedField {
                name: field.key.segments.last()?.ident.to_string(),
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
    /// function context, a context alias, a context), with the names `parameters` bind; `None`
    /// where the payload is no list of fields.
    pub(super) fn of_pattern(
        pattern: &krs_syntax::CellsExpression,
        parameters: impl IntoIterator<Item = String>,
    ) -> Option<Self> {
        Some(Self {
            form: EntryForm::Cells,
            subject: fields(pattern)?,
            result: None,
            parameters: parameters.into_iter().collect(),
            after: Vec::new(),
        })
    }

    /// The fields of a `cells!` rule, with its result remainders' refusal; `None` where a
    /// payload is no list of fields.
    pub(super) fn of_rule(rule: &krs_syntax::StateRuleItem) -> Option<Self> {
        Some(Self {
            form: EntryForm::Cells,
            subject: fields(rule.subject())?,
            result: match rule.result() {
                Some(result) => Some(fields(result)?),
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
    pub(super) fn of_readable(clause: &krs_syntax::RuleClause, form: EntryForm) -> Option<Self> {
        let (subject, result) = clause.records()?;
        Some(Self {
            form,
            subject: read_fields(subject, form)?,
            result: Some(read_fields(result, form)?),
            parameters: Vec::new(),
            after: Vec::new(),
        })
    }

    /// The fields of an initializer's body, each read with the initializer's configuration
    /// variables as such, and the names they bind; `None` where the body is no list of fields.
    pub(super) fn of_initializer(initializer: &krs_syntax::InitializerFunction) -> Option<Self> {
        Some(Self {
            form: EntryForm::Initializer,
            subject: located_fields(initializer.entry_fields()?)?,
            result: None,
            parameters: initializer.variable_names(),
            after: Vec::new(),
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
                })
                .collect(),
        }
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
/// The first refused entry, with its class's code, at what it refuses.
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
    if judged.is_ok()
        && let Some(entry) = result.iter().find(|entry| {
            matches!(entry.kind.own.layers.first(), Some(Layer::Instances(_)))
                && !subject.iter().any(|matched| matched.cell == entry.cell)
        })
    {
        return Err(overwritten_collection(entry));
    }
    if judged.is_ok() {
        for (cells, holder, group) in target
            .instance_key()
            .into_iter()
            .chain(target.nested_instance_keys())
        {
            kept_key(
                &InstanceKey {
                    cells: cells.to_vec(),
                    holder: holder.to_owned(),
                    group: group.to_owned(),
                },
                &subject,
                &result,
            )?;
        }
        instance_child_multiplicity(&subject, &result)?;
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
                side,
                &refusal,
                target.groups(),
            ))
        }
    }
}

/// Judges the entries of an initializer that hold a value its cell's kind alone could not decide
/// (a bracketed value on a cell that is neither the computation nor a list leaf), each against
/// its cell: `cells` gives each such cell, its kind and its leaf's sort. Where the table admits
/// such an entry, its brackets are the mark of the kind below its presence or instances (an
/// optional list's `Some([..])`, a template's list), which the caller then decides; where it
/// refuses one, the refusal is the author's answer, at what it refuses. The initializer's other
/// entries are not judged here: their values state their own wrappers. An entry whose value the
/// reader does not read is left undecided.
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
    .map(drop)
    .map_err(|(at, refusal)| {
        refused(
            EntryForm::Initializer,
            &entries[at],
            EntrySide::Initializer,
            &refusal,
            groups,
        )
    })
}

/// The refusal of an admitted result entry over a collection the subject does not match (Q1's
/// overwrite of a `*` cell, design S5 §2.3). The entry replaces every instance the collection
/// holds, whatever they are, which needs a pattern over the whole collection; a readable
/// clause's collection entry matches instances one by one and keeps the others with `..` or
/// names every one, so the overwrite has no lowering yet, and is refused rather than read as
/// another rule.
fn overwritten_collection(entry: &Entry<'_>) -> CollectionError {
    let name = unraw(&entry.cell.field);
    let error = CollectionError::new(
        CollectionErrorKind::CollectionOverwrite,
        format!(
            "the result writes the collection `{name}`, whose instances the subject does not match, so the rule replaces every instance `{name}` holds, whatever they are; a collection's instances are matched one by one, the others kept by `..`, so a rule that drops instances it never matched is not lowered yet: match the instances the rule replaces in the subject"
        ),
    );
    match &entry.field.range {
        Some(range) => error.with_source_range(range.clone()),
        None => error,
    }
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
        let Some((at, child, present)) =
            cell_entries::instance_child_presence(&entry.kind.own.layers, spelling)
        else {
            continue;
        };
        let error = CollectionError::new(
            CollectionErrorKind::InstanceChildMultiplicity,
            krs_syntax::instance_child_multiplicity_reason(unraw(child), present),
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
fn judge_entries(
    index: &DescriptorIndex<'_>,
    id: &StableItemId,
    authored: &LocatedCells,
) -> Result<Vec<Diagnostic>, CollectionError> {
    let Some(descriptor) = index.get(id) else {
        return Ok(Vec::new());
    };
    let (reference, subject, result, rewrite) = match descriptor.payload() {
        DescriptorPayload::ConfigurationRule(rule) => (
            &rule.subject_configuration,
            &rule.subject.cells,
            rule.result.as_ref().map(|cells| cells.cells.as_slice()),
            match (&rule.result, rule.sentence_kind) {
                (_, ConfigurationSentenceKind::Context) => Rewrite::Kept { as_rule: true },
                (Some(_), _) => Rewrite::Result,
                (None, _) => Rewrite::InPlace,
            },
        ),
        DescriptorPayload::ContextAlias(alias) => (
            &alias.configuration,
            &alias.pattern.cells,
            None,
            Rewrite::Kept { as_rule: false },
        ),
        DescriptorPayload::StructuredRule(rule) => {
            let Some(context) = &rule.function_context else {
                return Ok(Vec::new());
            };
            (
                &context.configuration,
                &context.cells.cells,
                None,
                Rewrite::Kept { as_rule: false },
            )
        }
        _ => return Ok(Vec::new()),
    };
    let lints = judge_sentence(index, reference, subject, result, rewrite, authored)?;
    Ok(lints
        .into_iter()
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
    reference: &krs_ir::DescriptorConfigurationReference,
    subject: &DescriptorCells,
    result: Option<&DescriptorCells>,
    rewrite: Rewrite,
    authored: &LocatedCells,
) -> Result<Vec<EntryLint>, CollectionError> {
    let configuration = &reference.configuration;
    let Ok(declaration) = index.configuration(configuration) else {
        return Ok(Vec::new());
    };
    let tree = Tree::new(configuration, &declaration.declaration, index)
        .scoped(reference.subject.as_ref());
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
                side,
                &refusal,
                &tree.groups,
            ))
        }
    }
}

/// Refuses the first admitted entry of a context alias's or an equation's function context's
/// pattern ([`Rewrite::Kept`], lowered as no rule's pattern is) that is a `?` cell's `Some(..)`
/// or a collection's instance list. The entry means what it means in a rule's subject, the
/// present cell or the instances it names, matched and kept, but those two sentences' lowerings
/// read fixed cells only, so it is a limit, raised once the entries' kinds and pairing admit the
/// pattern: a `None`, which tests absence without creating the cell, is refused as such before.
fn fixed_cells_only(cells: &DescriptorCells, subject: &[Entry<'_>]) -> Result<(), CollectionError> {
    let Some((_, entry)) = cells.iter().zip(subject).find(|(cell, _)| {
        matches!(
            cell.value,
            krs_ir::ProtocolRuleStateTerm::Present { .. }
                | krs_ir::ProtocolRuleStateTerm::Instances(_)
        )
    }) else {
        return Ok(());
    };
    let error = CollectionError::new(
        CollectionErrorKind::FixedCellsOnly,
        cell_entries::fixed_cells_only_reason(unraw(&entry.cell.field)),
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
    /// The collection cell's field name.
    holder: String,
    /// The group the sentence is about, the collection's instance type.
    group: String,
}

impl InstanceKey {
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
    /// collection's instance inside it ([`Self::scoped`]).
    keys: Vec<InstanceKey>,
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
    /// keeps its mark. The whole configuration (`None`), or a subject without a scope, which
    /// resolution refuses first, leaves every cell judged from the configuration's level.
    fn scoped(mut self, subject: Option<&krs_ir::DescriptorSubject>) -> Self {
        if subject.is_none() {
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
        for (holder, group) in own.into_iter().chain(nested) {
            let key = (0..cells.len())
                .filter(|&index| {
                    krs_ir::subject::keys_on_path(&cells, index)
                        .iter()
                        .any(|&(on, _)| on == holder)
                })
                .map(|index| cells[index].identity.clone())
                .collect::<Vec<_>>();
            if !key.is_empty() {
                self.keys.push(InstanceKey {
                    cells: key,
                    holder: cells[holder].identity.field.clone(),
                    group,
                });
            }
        }
        self
    }

    /// The ancestors of the cell at `index` an entry naming it is judged against: those
    /// strictly below the anchor, where the cell is inside the group the sentence is about, else
    /// all of them.
    ///
    /// Inside the group, the Map collections the cell lies in below the anchor, outermost first
    /// up to the first other `?` or `*`, are not judged either: the sentence's cells lie in one
    /// instance of each holder on their deepest chain, so naming a cell of a nested instance
    /// matches one instance of each such collection, the one whose cell matches, as naming a
    /// cell of the group matches one instance of the group. Its key is matched where the
    /// sentence names it and written only as matched ([`Self::scoped`]). A Set or List
    /// collection, or an optional cell, keeps its mark.
    fn judged_ancestors<'t>(
        &'t self,
        index: usize,
        ancestors: &'t [DescriptorCell<'i, 'a>],
    ) -> &'t [DescriptorCell<'i, 'a>] {
        let dropped = dropped(&self.parents, self.anchor, index).min(ancestors.len());
        let below = &ancestors[dropped..];
        if dropped == 0 {
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
/// - `record-update-base`: the label its subject gives the instance the update keeps.
fn advice(
    form: EntryForm,
    entry: &RefusedCell<'_>,
    side: EntrySide,
    refusal: Refusal,
    groups: &[GroupKind],
) -> Option<String> {
    let name = entry.name;
    let own = entry.layers;
    match refusal {
        Refusal::CellWrapper | Refusal::InstanceListShape => {
            Some(format!("write its entry as `{}`", spelled(form, own)))
        }
        Refusal::CollectionWithoutInstances => Some(format!(
            "write its entry as its instances, `{}`",
            spelled(form, own)
        )),
        Refusal::OptionalWithoutPresence => {
            Some("write its entry inside `Some(..)`, or as `None` for its absence".to_owned())
        }
        Refusal::BelowOptionalAncestor | Refusal::BelowCollectionAncestor => {
            below_ancestor(form, name, entry.ancestor?, side, groups)
        }
        Refusal::RestMismatch => Some(
            "write `..` on both sides to keep the rest, or name it in the subject (`rest @ ..`) to drop or move it"
                .to_owned(),
        ),
        Refusal::MapCollectionKey => {
            if entry.spelling.and_then(update_label).is_some() {
                return Some(
                    "leave the key out of the update, which keeps it, or write it as its subject matched it"
                        .to_owned(),
                );
            }
            let key = match own {
                [Layer::Instances(order), Layer::Group(group), ..] => group.key(*order)?,
                _ => return None,
            };
            Some(format!("write its key first, `{key}: ..`"))
        }
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

/// The advice of a path refusal of the entry naming `name`, below its outermost `?` or `*`
/// ancestor `ancestor` ([`advice`]).
fn below_ancestor(
    form: EntryForm,
    name: &str,
    ancestor: &Ancestor,
    side: EntrySide,
    groups: &[GroupKind],
) -> Option<String> {
    let marked = &ancestor.marked;
    let holder = &marked.name;
    let of = match &marked.layer {
        Layer::Optional => format!("`{name}` is a cell of the optional group `{holder}`"),
        _ => format!("`{name}` is a cell of an instance of the collection `{holder}`"),
    };
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
        (_, Some((Layer::Instances(Order::List), inner))) => {
            format!("[{} {{ .. }}, ..]", group(inner))
        }
        (_, Some((Layer::Instances(Order::Set | Order::Map), inner))) => {
            format!("{{ {} {{ .. }}, .. }}", group(inner))
        }
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
    /// Its outermost `?` or `*` ancestor above the record's level (the refused entry's own).
    ancestor: Option<&'a Ancestor>,
    /// The cell's content as written.
    spelling: Option<&'a EntrySpelling>,
}

/// The refusal `located` of the entry `entry`, on the side `side` of a sentence written in
/// `form`: why ([`Refusal::reason`]), then what to write instead where its class advises it
/// ([`advice`]). A refusal raised inside the content of a child of a group or instance record
/// the entry writes names that child, the cell whose content is wrong (P1, P7), but for a form
/// refusal, which is judged without the declaration and names the entry's cell
/// ([`Refusal::is_form`]); it stands at the spelling it is raised at, or at the entry's value
/// where that spelling has no range.
fn refused(
    form: EntryForm,
    entry: &Entry<'_>,
    side: EntrySide,
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
                ancestor: None,
                spelling: spelling.and_then(|spelling| {
                    cell_entries::spelling_at(spelling, &located.at[..nested.depth])
                }),
            },
            kind,
            None,
        ),
        _ => (
            RefusedCell {
                name: unraw(&entry.cell.field),
                layers: &entry.kind.own.layers,
                ancestor: entry.ancestor.as_ref(),
                spelling,
            },
            &entry.kind,
            entry.sort.as_deref(),
        ),
    };
    let mut detail = refusal.reason(form, cell.name, kind, sort);
    if let Some(advice) = advice(form, &cell, side, refusal, groups) {
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
}
