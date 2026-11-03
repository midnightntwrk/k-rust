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

use krs_ir::cell_kind::{CellKind, DescriptorCell, EntryKind, GroupKind};
use krs_ir::{
    ConfigurationSentenceKind, DescriptorBundle, DescriptorCellDeclaration, DescriptorCellIdentity,
    DescriptorIndex, DescriptorPayload, ProtocolCellContent, SourceRange, StableItemId,
};
use krs_syntax::cell_entries::{self, EntrySide, Refusal, Rewrite, Sentence, SentenceEntry};
use krs_syntax::cell_entry::{EntryForm, EntrySpelling};

use super::provenance::Coordinates;
use super::source::SourceDocument;
use crate::{CollectionError, CollectionErrorKind};

/// One authored field of a `cells!` payload: the name of the cell its key ends in, its value's
/// spelling where the shared reader reads one, and where the value is.
#[derive(Clone, Debug)]
pub(super) struct ParsedField<R> {
    name: String,
    spelling: Option<EntrySpelling>,
    range: Option<R>,
}

/// A `cells!` sentence's authored fields: its subject's, its result's (none for a single-body
/// rule), and the names its parameters bind.
#[derive(Clone, Debug)]
pub(super) struct ParsedCells<R> {
    subject: Vec<ParsedField<R>>,
    result: Option<Vec<ParsedField<R>>>,
    parameters: Vec<String>,
}

/// The authored fields of a sentence, located in its source document.
pub(super) type LocatedCells = ParsedCells<SourceRange>;

fn fields(expression: &krs_syntax::CellsExpression) -> Option<Vec<ParsedField<Coordinates>>> {
    krs_syntax::cell_entry::cells_fields(expression.tokens())?
        .into_iter()
        .map(|field| {
            Some(ParsedField {
                name: field.key.segments.last()?.ident.to_string(),
                spelling: field.spelling,
                range: field
                    .value
                    .and_then(|range| super::provenance::token_coordinates(range).ok()),
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
            subject: fields(pattern)?,
            result: None,
            parameters: parameters.into_iter().collect(),
        })
    }

    /// The fields of a `cells!` rule; `None` where a payload is no list of fields.
    pub(super) fn of_rule(rule: &krs_syntax::StateRuleItem) -> Option<Self> {
        Some(Self {
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
        })
    }

    /// The fields located in `document`.
    pub(super) fn locate(&self, document: &SourceDocument) -> LocatedCells {
        let locate = |fields: &[ParsedField<Coordinates>]| {
            fields
                .iter()
                .map(|field| ParsedField {
                    name: field.name.clone(),
                    spelling: field.spelling.clone(),
                    range: field
                        .range
                        .as_ref()
                        .and_then(|coordinates| coordinates.range_in(document)),
                })
                .collect()
        };
        ParsedCells {
            subject: locate(&self.subject),
            result: self.result.as_deref().map(locate),
            parameters: self.parameters.clone(),
        }
    }
}

/// Judges the `cells!` entries of every sentence of `bundle` whose authored fields `cells`
/// holds: a `cells!` rule's or claim's, pairing a result's with its subject's, or a single-body
/// rule's in place; and the one-sided pattern of a context, a context alias or an equation's
/// function context, which the sentence keeps as it matched it ([`Rewrite::Kept`]).
///
/// # Errors
///
/// The first refused entry, with its class's code, at its value.
pub(super) fn judge(
    bundle: &DescriptorBundle,
    cells: &BTreeMap<StableItemId, LocatedCells>,
) -> Result<(), CollectionError> {
    let index = DescriptorIndex::new(bundle);
    for (id, authored) in cells {
        let Some(descriptor) = index.get(id) else {
            continue;
        };
        let (configuration, subject, result, rewrite) = match descriptor.payload() {
            DescriptorPayload::ConfigurationRule(rule) => (
                &rule.subject_configuration.configuration,
                &rule.subject.cells,
                rule.result.as_ref().map(|cells| cells.cells.as_slice()),
                match (&rule.result, rule.sentence_kind) {
                    (_, ConfigurationSentenceKind::Context) => Rewrite::Kept,
                    (Some(_), _) => Rewrite::Result,
                    (None, _) => Rewrite::InPlace,
                },
            ),
            DescriptorPayload::ContextAlias(alias) => (
                &alias.configuration.configuration,
                &alias.pattern.cells,
                None,
                Rewrite::Kept,
            ),
            DescriptorPayload::StructuredRule(rule) => {
                let Some(context) = &rule.function_context else {
                    continue;
                };
                (
                    &context.configuration.configuration,
                    &context.cells.cells,
                    None,
                    Rewrite::Kept,
                )
            }
            _ => continue,
        };
        judge_sentence(&index, configuration, subject, result, rewrite, authored)?;
    }
    Ok(())
}

/// The cells of one side of a sentence, as the descriptor holds them.
type DescriptorCells =
    [krs_ir::ProtocolRuleCell<krs_ir::DescriptorCellReference, krs_ir::DescriptorTerm>];

/// Judges one sentence's entries over the configuration `configuration`.
fn judge_sentence(
    index: &DescriptorIndex<'_>,
    configuration: &StableItemId,
    subject: &DescriptorCells,
    result: Option<&DescriptorCells>,
    rewrite: Rewrite,
    authored: &LocatedCells,
) -> Result<(), CollectionError> {
    let Ok(declaration) = index.configuration(configuration) else {
        return Ok(());
    };
    let tree = Tree::new(configuration, &declaration.declaration, index);
    let subject = entries(&tree, subject, &authored.subject);
    let result = result
        .zip(authored.result.as_ref())
        .map(|(cells, authored)| entries(&tree, cells, authored));
    let (Some(subject), Some(result)) = (subject, result.unwrap_or(Some(Vec::new()))) else {
        return Ok(());
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
        })
        .collect::<Vec<_>>();
    let judged = Sentence {
        form: EntryForm::Cells,
        entries: &sentence,
        rewrite,
        parameters: &authored.parameters,
        groups: &tree.groups,
    }
    .judge();
    if let Err((at, refusal)) = judged {
        let entry = subject
            .iter()
            .chain(&result)
            .nth(at)
            .expect("the refused entry is the sentence's");
        return Err(refused(entry, refusal));
    }
    Ok(())
}

/// One entry: its cell, the cell's kind, and its authored field.
struct Entry<'a> {
    cell: &'a DescriptorCellIdentity,
    kind: EntryKind,
    field: &'a ParsedField<SourceRange>,
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
            })
        })
        .collect()
}

/// A configuration's cells, each with the cells above it and the declaration that owns it.
struct Tree<'i, 'a> {
    /// Each cell's ancestors, outermost first, the cell, and its owner.
    cells: Vec<(
        Vec<DescriptorCell<'i, 'a>>,
        DescriptorCell<'i, 'a>,
        &'a StableItemId,
    )>,
    groups: Vec<GroupKind>,
}

impl<'i, 'a> Tree<'i, 'a> {
    fn new(
        owner: &'a StableItemId,
        declaration: &'a DescriptorCellDeclaration,
        index: &'i DescriptorIndex<'a>,
    ) -> Self {
        let mut tree = Self {
            cells: Vec::new(),
            groups: Vec::new(),
        };
        tree.walk(owner, declaration, index, &[], &[owner]);
        let mut groups = Vec::new();
        for (ancestors, cell, _) in &tree.cells {
            if ancestors.is_empty() {
                cell_entries::collect_groups(&cell.kind().layers, &mut groups);
            }
        }
        tree.groups = groups;
        tree
    }

    fn walk(
        &mut self,
        owner: &'a StableItemId,
        declaration: &'a DescriptorCellDeclaration,
        index: &'i DescriptorIndex<'a>,
        ancestors: &[DescriptorCell<'i, 'a>],
        seen: &[&'a StableItemId],
    ) {
        for field in &declaration.fields {
            let cell = DescriptorCell::new(field, index);
            self.cells.push((ancestors.to_vec(), cell.clone(), owner));
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
                self.walk(nested, inner, index, &below, &deeper);
            }
        }
    }

    /// The kind an entry naming `identity` is judged against.
    fn kind(&self, identity: &DescriptorCellIdentity) -> Option<EntryKind> {
        let (ancestors, cell, _) = self.cells.iter().find(|(_, cell, owner)| {
            *owner == &identity.owner && cell.field().rust_field == identity.field
        })?;
        Some(CellKind::entry(ancestors, cell))
    }
}

fn refused(entry: &Entry<'_>, refusal: Refusal) -> CollectionError {
    let error = CollectionError::new(
        CollectionErrorKind::CellEntry(refusal),
        refusal.reason(&entry.cell.field).unwrap_or_else(|| {
            format!(
                "the entry of the cell `{}` is refused: {}",
                entry.cell.field,
                refusal.class()
            )
        }),
    );
    match &entry.field.range {
        Some(range) => error.with_source_range(range.clone()),
        None => error,
    }
}
