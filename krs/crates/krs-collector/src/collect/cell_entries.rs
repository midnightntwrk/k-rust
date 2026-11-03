//! A `cells!` sentence's entries judged by the one entry-admission table (design S5, §2.3):
//! each entry's spelling, read from the authored source as the shared reader reads it
//! ([`krs_syntax::cell_entry::cells_fields`]), against its cell's kind
//! ([`krs_ir::cell_kind::CellKind::entry`]: the layers of the cell's `?` and `*` ancestors and
//! its own), then paired with the other side's entry of the same cell
//! ([`krs_syntax::cell_entries::{admit, pair}`]).
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
use krs_syntax::cell_entries::{self, Bound, EntrySide, Refusal};
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
        Sentence {
            subject: &subject,
            result: rule.result.as_ref().map(|_| result.as_slice()),
            parameters: &authored.parameters,
            groups: &tree.groups,
        }
        .judge()?;
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

/// One `cells!` sentence's entries.
struct Sentence<'s, 'a> {
    subject: &'s [Entry<'a>],
    result: Option<&'s [Entry<'a>]>,
    parameters: &'s [String],
    groups: &'s [GroupKind],
}

impl Sentence<'_, '_> {
    /// What `name` binds outside an entry: a record where a subject alias labels one of a
    /// head, a value where a parameter binds it.
    fn bound(&self, name: &str) -> Option<Bound> {
        self.subject
            .iter()
            .filter_map(|entry| entry.field.spelling.as_ref())
            .find_map(|spelling| record_alias(spelling, name))
            .map(Bound::Record)
            .or_else(|| {
                (self.parameters.iter().any(|parameter| parameter == name)
                    || self
                        .subject
                        .iter()
                        .filter_map(|entry| entry.field.spelling.as_ref())
                        .any(|spelling| binds(spelling, name)))
                .then_some(Bound::Value)
            })
    }

    /// The table's steps over the whole sentence, each over every entry, the subject's first:
    /// the form and the kind, then the path, then the pairing. A step's refusal is the
    /// sentence's before a later step's on any entry: an entry named below a `?` or `*`
    /// ancestor is refused for the ancestor only once every entry's own marks are admitted,
    /// since the ancestor's advice writes the entry inside the ancestor's mark, where an entry
    /// its own cell refuses would be refused again.
    fn judge(&self) -> Result<(), CollectionError> {
        let bound = |name: &str| self.bound(name);
        let entries = || {
            self.subject
                .iter()
                .map(|entry| (EntrySide::Subject, entry))
                .chain(
                    self.result
                        .unwrap_or_default()
                        .iter()
                        .map(|entry| (EntrySide::Result, entry)),
                )
                .filter_map(|(side, entry)| Some((side, entry, entry.field.spelling.as_ref()?)))
        };
        for whole_path in [false, true] {
            for (side, entry, spelling) in entries() {
                if whole_path && entry.kind.path.layers.is_empty() {
                    continue;
                }
                cell_entries::admit(
                    EntryForm::Cells,
                    side,
                    if whole_path {
                        &entry.kind.path.layers
                    } else {
                        &[]
                    },
                    &entry.kind.own.layers,
                    spelling,
                    &bound,
                    self.groups,
                )
                .map_err(|refusal| refused(entry, refusal))?;
            }
        }
        // A single-body rule rewrites its cells in place: there is no other side.
        let Some(result) = self.result else {
            return Ok(());
        };
        for (side, entry, spelling) in entries() {
            let others = match side {
                EntrySide::Subject => result,
                _ => self.subject,
            };
            let other = others.iter().find(|other| other.cell == entry.cell);
            if other.is_some_and(|other| other.field.spelling.is_none()) {
                continue;
            }
            cell_entries::pair(
                EntryForm::Cells,
                side,
                &entry.kind.own.layers,
                spelling,
                other.and_then(|other| other.field.spelling.as_ref()),
                side == EntrySide::Subject && other.is_some(),
                &bound,
            )
            .map_err(|refusal| refused(entry, refusal))?;
        }
        Ok(())
    }
}

fn refused(entry: &Entry<'_>, refusal: Refusal) -> CollectionError {
    let error = CollectionError::new(
        CollectionErrorKind::CellEntry(refusal),
        format!(
            "the entry of the cell `{}` is refused: {}",
            entry.cell.field,
            refusal.class()
        ),
    );
    match &entry.field.range {
        Some(range) => error.with_source_range(range.clone()),
        None => error,
    }
}

/// The head of the record `name` labels in `spelling`, `name @ Head { .. }` or its fragment.
fn record_alias(spelling: &EntrySpelling, name: &str) -> Option<String> {
    match spelling {
        EntrySpelling::Alias(alias, inner) if alias == name => match &**inner {
            EntrySpelling::Record(record) | EntrySpelling::Fragment(record) => {
                Some(record.head.clone())
            }
            _ => None,
        },
        _ => children(spelling).find_map(|child| record_alias(child, name)),
    }
}

/// Whether `spelling` binds `name`.
fn binds(spelling: &EntrySpelling, name: &str) -> bool {
    match spelling {
        EntrySpelling::Binder(binder) => binder == name,
        EntrySpelling::Alias(alias, _) if alias == name => true,
        _ => {
            rests(spelling).any(|rest| rest == name)
                || children(spelling).any(|child| binds(child, name))
        }
    }
}

/// The names of the rests `spelling` writes at its own level.
fn rests(spelling: &EntrySpelling) -> impl Iterator<Item = &str> {
    use krs_syntax::cell_entry::EntryRest;
    let rest = match spelling {
        EntrySpelling::Brackets(seq)
        | EntrySpelling::Braces(seq)
        | EntrySpelling::KCell(seq)
        | EntrySpelling::InstanceList(seq)
        | EntrySpelling::InstanceSet(seq)
        | EntrySpelling::KMacro(seq) => seq.rest.as_ref().map(|(rest, _)| rest),
        EntrySpelling::MapRead(map) | EntrySpelling::MapLiteral(map) => map.rest.as_ref(),
        _ => None,
    };
    rest.and_then(|rest| match rest {
        EntryRest::Named(name) => Some(name.as_str()),
        EntryRest::Anonymous | EntryRest::Splice(_) => None,
    })
    .into_iter()
}

/// The spellings `spelling` holds directly.
fn children(spelling: &EntrySpelling) -> Box<dyn Iterator<Item = &EntrySpelling> + '_> {
    match spelling {
        EntrySpelling::Call(items) => Box::new(items.iter()),
        EntrySpelling::Present(inner)
        | EntrySpelling::Absent(inner)
        | EntrySpelling::Alias(_, inner)
        | EntrySpelling::Cell(inner) => Box::new(std::iter::once(&**inner)),
        EntrySpelling::Brackets(seq)
        | EntrySpelling::Braces(seq)
        | EntrySpelling::KCell(seq)
        | EntrySpelling::InstanceList(seq)
        | EntrySpelling::InstanceSet(seq)
        | EntrySpelling::KMacro(seq) => Box::new(seq.items.iter()),
        EntrySpelling::MapRead(map) | EntrySpelling::MapLiteral(map) => {
            Box::new(map.entries.iter().flat_map(|(key, value)| [key, value]))
        }
        EntrySpelling::Record(record) | EntrySpelling::Fragment(record) => {
            Box::new(record.fields.iter().map(|(_, value)| value))
        }
        EntrySpelling::Wild
        | EntrySpelling::Binder(_)
        | EntrySpelling::Literal(_)
        | EntrySpelling::ConfigVar(_)
        | EntrySpelling::Missing => Box::new(std::iter::empty()),
    }
}
