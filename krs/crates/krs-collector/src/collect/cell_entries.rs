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
    DescriptorBundle, DescriptorCellDeclaration, DescriptorCellIdentity, DescriptorIndex,
    DescriptorPayload, ProtocolCellContent, SourceRange, StableItemId,
};
use krs_syntax::cell_entries::{self, EntrySide, Refusal, Sentence, SentenceEntry};
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

/// Judges every `cells!` rule's entries of `bundle` whose authored fields `cells` holds.
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
        let DescriptorPayload::ConfigurationRule(rule) = descriptor.payload() else {
            continue;
        };
        let Ok(configuration) = index.configuration(&rule.subject_configuration.configuration)
        else {
            continue;
        };
        let tree = Tree::new(
            &rule.subject_configuration.configuration,
            &configuration.declaration,
            &index,
        );
        let subject = entries(&tree, &rule.subject.cells, &authored.subject);
        let result = rule
            .result
            .as_ref()
            .zip(authored.result.as_ref())
            .map(|(cells, authored)| entries(&tree, &cells.cells, authored));
        let (Some(subject), Some(result)) = (subject, result.unwrap_or(Some(Vec::new()))) else {
            continue;
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
            result: rule.result.is_some(),
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
    cells: &'a [krs_ir::ProtocolRuleCell<
        krs_ir::DescriptorCellReference,
        krs_ir::DescriptorTerm,
    >],
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
