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
/// rule), the names its parameters bind, and the refusal of a result remainder that reuses no
/// subject frame of its kind, which is asked once the entries are admitted.
#[derive(Clone, Debug)]
pub(super) struct ParsedCells<R> {
    subject: Vec<ParsedField<R>>,
    result: Option<Vec<ParsedField<R>>>,
    parameters: Vec<String>,
    reuse: Option<Reuse<R>>,
}

/// A result remainder's refusal ([`krs_syntax::StateRuleItem::reuse_refusal`]): the parser's
/// message and where the remainder is.
#[derive(Clone, Debug)]
struct Reuse<R> {
    detail: String,
    range: Option<R>,
}

impl Reuse<Coordinates> {
    fn of(error: &krs_syntax::SyntaxError) -> Self {
        Self {
            detail: error.to_string(),
            range: super::provenance::token_coordinates(krs_syntax::TokenRange::new(
                error.span(),
                error.span(),
            ))
            .ok(),
        }
    }
}

impl Reuse<SourceRange> {
    fn refused(&self) -> CollectionError {
        let error = CollectionError::new(CollectionErrorKind::ResultRemainderReuse, &self.detail);
        match &self.range {
            Some(range) => error.with_source_range(range.clone()),
            None => error,
        }
    }
}

/// The refusal of `rule`'s result remainder that reuses no subject frame of its kind, at once:
/// for a sentence whose entries no admission judges first.
pub(super) fn reuse_refused(rule: &krs_syntax::StateRuleItem) -> Result<(), CollectionError> {
    match rule.reuse_refusal() {
        Some(error) => {
            let error =
                CollectionError::new(CollectionErrorKind::ResultRemainderReuse, error.to_string())
                    .with_span(error.span());
            Err(error)
        }
        None => Ok(()),
    }
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
            reuse: None,
        })
    }

    /// The fields of a `cells!` rule, with its result remainders' refusal; `None` where a
    /// payload is no list of fields.
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
            reuse: rule.reuse_refusal().as_ref().map(Reuse::of),
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
            reuse: self.reuse.as_ref().map(|reuse| Reuse {
                detail: reuse.detail.clone(),
                range: reuse
                    .range
                    .as_ref()
                    .and_then(|coordinates| coordinates.range_in(document)),
            }),
        }
    }
}

/// Judges the `cells!` entries of every sentence of `bundle` whose authored fields `cells`
/// holds: a `cells!` rule's or claim's, pairing a result's with its subject's, or a single-body
/// rule's in place; and the one-sided pattern of a context, a context alias or an equation's
/// function context, which the sentence keeps as it matched it ([`Rewrite::Kept`]). Then, once
/// a rule's entries are admitted, its result remainders, each against the subject frame it
/// reuses: that pairs the result with the subject, after each entry's form and kind.
///
/// Returns the warnings of the admitted entries' lints, in the sentences' order and each
/// sentence's source order: one per entry that owes one, at its value ([`linted`]).
///
/// # Errors
///
/// The first refused entry, with its class's code, at its value; else the first sentence's
/// result remainder that reuses no subject frame of its kind, at the remainder.
pub(super) fn judge(
    bundle: &DescriptorBundle,
    cells: &BTreeMap<StableItemId, LocatedCells>,
) -> Result<Vec<Diagnostic>, CollectionError> {
    let index = DescriptorIndex::new(bundle);
    let mut warnings = Vec::new();
    for (id, authored) in cells {
        warnings.extend(judge_entries(&index, id, authored)?);
        if let Some(reuse) = &authored.reuse {
            return Err(reuse.refused());
        }
    }
    Ok(warnings)
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
    let (configuration, subject, result, rewrite) = match descriptor.payload() {
        DescriptorPayload::ConfigurationRule(rule) => (
            &rule.subject_configuration.configuration,
            &rule.subject.cells,
            rule.result.as_ref().map(|cells| cells.cells.as_slice()),
            match (&rule.result, rule.sentence_kind) {
                (_, ConfigurationSentenceKind::Context) => Rewrite::Kept { as_rule: true },
                (Some(_), _) => Rewrite::Result,
                (None, _) => Rewrite::InPlace,
            },
        ),
        DescriptorPayload::ContextAlias(alias) => (
            &alias.configuration.configuration,
            &alias.pattern.cells,
            None,
            Rewrite::Kept { as_rule: false },
        ),
        DescriptorPayload::StructuredRule(rule) => {
            let Some(context) = &rule.function_context else {
                return Ok(Vec::new());
            };
            (
                &context.configuration.configuration,
                &context.cells.cells,
                None,
                Rewrite::Kept { as_rule: false },
            )
        }
        _ => return Ok(Vec::new()),
    };
    let lints = judge_sentence(index, configuration, subject, result, rewrite, authored)?;
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

/// Judges one sentence's entries over the configuration `configuration`, and gives the lints
/// its admitted entries owe ([`Sentence::judge`]).
fn judge_sentence(
    index: &DescriptorIndex<'_>,
    configuration: &StableItemId,
    subject: &DescriptorCells,
    result: Option<&DescriptorCells>,
    rewrite: Rewrite,
    authored: &LocatedCells,
) -> Result<Vec<EntryLint>, CollectionError> {
    let Ok(declaration) = index.configuration(configuration) else {
        return Ok(Vec::new());
    };
    let tree = Tree::new(configuration, &declaration.declaration, index);
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
    let entry = |at: usize| {
        subject
            .iter()
            .chain(&result)
            .nth(at)
            .expect("a judged entry is the sentence's")
    };
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
            let entry = entry(at);
            Err(refused(entry, refusal, advice(&tree, entry, side, refusal)))
        }
    }
}

/// A field's name without its raw-identifier prefix.
fn unraw(name: &str) -> &str {
    name.strip_prefix("r#").unwrap_or(name)
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

    /// The cell `identity` names: its ancestors, outermost first, itself, and its owner.
    fn cell(
        &self,
        identity: &DescriptorCellIdentity,
    ) -> Option<&(
        Vec<DescriptorCell<'i, 'a>>,
        DescriptorCell<'i, 'a>,
        &'a StableItemId,
    )> {
        self.cells.iter().find(|(_, cell, owner)| {
            *owner == &identity.owner && cell.field().rust_field == identity.field
        })
    }

    /// The kind an entry naming `identity` is judged against.
    fn kind(&self, identity: &DescriptorCellIdentity) -> Option<EntryKind> {
        let (ancestors, cell, _) = self.cell(identity)?;
        Some(CellKind::entry(ancestors, cell))
    }
}

/// What the author is told to write instead of a refused entry, where the refusal's class has
/// one spelling to advise:
/// - `cell-wrapper`: the `cells!` spelling of the cell's own kind, its marks outermost first;
/// - the result side of a path refusal below `*` (S1 (b)): an entry can name a cell only at a
///   record's level, so the result updates the instance of the outermost collection that its
///   subject names (`me @ ..` there), through the instance's record (`..me`). That is the
///   spelling for a child of the instance's own record other than a Map collection's key,
///   which is the instance's identity and so no update writes another.
fn advice(
    tree: &Tree<'_, '_>,
    entry: &Entry<'_>,
    side: EntrySide,
    refusal: Refusal,
) -> Option<String> {
    let name = entry
        .cell
        .field
        .strip_prefix("r#")
        .unwrap_or(&entry.cell.field);
    match refusal {
        Refusal::CellWrapper => {
            let own = &entry.kind.own.layers;
            Some(format!(
                "`{name}` holds {}, so write its entry as `{}`",
                described(own),
                spelled(own)
            ))
        }
        Refusal::BelowCollectionAncestor if side == EntrySide::Result => {
            let (ancestors, _, owner) = tree.cell(entry.cell)?;
            let collection = ancestors
                .iter()
                .find(|ancestor| ancestor.kind().multiplicity() != Multiplicity::One)?;
            let Multiplicity::Many(order) = collection.kind().multiplicity() else {
                return None;
            };
            let field = collection.field();
            let ProtocolCellContent::Nested { declaration } = &field.content else {
                return None;
            };
            let instance = &declaration.declaration;
            let collection_name = field
                .rust_field
                .strip_prefix("r#")
                .unwrap_or(&field.rust_field);
            let of =
                format!("`{name}` is a cell of an instance of the collection `{collection_name}`");
            let key = collection
                .kind()
                .group()
                .and_then(|group| group.key(order))
                .is_some_and(|key| key == name);
            if *owner != instance || key {
                return Some(format!(
                    "{of}; a result updates such an instance through the record of the collection's entry, which its subject names (`me @ ..`) and the result puts back with `..me` after the children it writes"
                ));
            }
            let path = std::iter::once("crate")
                .chain(instance.module_path().iter().map(String::as_str))
                .chain(std::iter::once(instance.item_name()))
                .collect::<Vec<_>>()
                .join("::");
            let (open, close) = match order {
                Order::List => ("[", "]"),
                Order::Set | Order::Map => ("{ ", " }"),
            };
            Some(format!(
                "{of}, and a result updates the instance its subject names, `{collection_name}: {open}me @ k::fragment![{path} {{ .. }}], ..{close}`; so write the result's entry as `{collection_name}: {open}k::fragment![{path} {{ {name}: v, ..me }}], ..{close}`"
            ))
        }
        _ => None,
    }
}

/// The `cells!` spelling of a cell of the layers `layers`, outermost first (P2): `Some(..)`,
/// instance records in brackets (List) or braces (Set, Map), `KCell(..)`, `Cell(..)`, or a
/// group's record.
fn spelled(layers: &[Layer]) -> String {
    match layers.split_first() {
        Some((Layer::Optional, inner)) => format!("Some({})", spelled(inner)),
        Some((Layer::Instances(Order::List), _)) => "[k::fragment![..], ..]".to_owned(),
        Some((Layer::Instances(Order::Set | Order::Map), _)) => {
            "{ k::fragment![..], .. }".to_owned()
        }
        Some((Layer::Computation, _)) => "k::configuration::KCell(..)".to_owned(),
        Some((Layer::Leaf(_), _)) => "k::configuration::Cell(..)".to_owned(),
        Some((Layer::Group(_), _)) | None => "k::fragment![..]".to_owned(),
    }
}

/// The layers `layers` in words, with their article.
fn described(layers: &[Layer]) -> String {
    let noun = noun(layers);
    let article = if noun.starts_with('o') { "an" } else { "a" };
    format!("{article} {noun}")
}

/// The layers `layers` in words.
fn noun(layers: &[Layer]) -> String {
    match layers.split_first() {
        Some((Layer::Optional, inner)) => format!("optional {}", noun(inner)),
        Some((Layer::Instances(order), _)) => format!(
            "{} collection of instances",
            match order {
                Order::List => "List",
                Order::Set => "Set",
                Order::Map => "Map",
            }
        ),
        Some((Layer::Computation, _)) => "computation".to_owned(),
        Some((Layer::Leaf(_), _)) => "leaf".to_owned(),
        Some((Layer::Group(_), _)) | None => "group".to_owned(),
    }
}

fn refused(entry: &Entry<'_>, refusal: Refusal, advice: Option<String>) -> CollectionError {
    let mut detail = refusal.reason(&entry.cell.field).unwrap_or_else(|| {
        format!(
            "the entry of the cell `{}` is refused: {}",
            entry.cell.field,
            refusal.class()
        )
    });
    if let Some(advice) = advice {
        detail = format!("{detail}: {advice}");
    }
    let error = CollectionError::new(CollectionErrorKind::CellEntry(refusal), detail);
    match &entry.field.range {
        Some(range) => error.with_source_range(range.clone()),
        None => error,
    }
}
