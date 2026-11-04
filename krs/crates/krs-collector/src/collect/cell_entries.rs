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
}

/// A `cells!` sentence's authored fields: its subject's, its result's (none for a single-body
/// rule), the names its parameters bind, and the refusal of a result remainder that reuses no
/// subject frame of its kind, which is asked once the entries are admitted.
#[derive(Clone, Debug)]
pub(super) struct ParsedCells<R> {
    /// The form the entries are written in: `cells!`, or a readable record or claim.
    form: EntryForm,
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
    read_fields(expression.tokens(), EntryForm::Cells)
}

fn read_fields(
    tokens: &proc_macro2::TokenStream,
    form: EntryForm,
) -> Option<Vec<ParsedField<Coordinates>>> {
    krs_syntax::cell_entry::entry_fields(tokens, form)?
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
            form: EntryForm::Cells,
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
            reuse: rule.reuse_refusal().as_ref().map(Reuse::of),
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
            reuse: None,
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
            form: self.form,
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
        if authored.form.is_readable() {
            // Judged before its payload is resolved ([`judge_readable`]).
            continue;
        }
        warnings.extend(judge_entries(&index, id, authored)?);
        if let Some(reuse) = &authored.reuse {
            return Err(reuse.refused());
        }
    }
    Ok(warnings)
}

/// Judges the entries of a readable record clause or claim against the configuration `target`
/// it names, before its payload is resolved: the table's answer is the first one an author meets,
/// ahead of the readable route's own readings of the entries (a bracketed value read as a list,
/// a braced one as instances), which assume the kinds the table checks. A clause whose fields the
/// reader does not read, or which names a cell no single cell of the configuration has, is left
/// to the rule's resolution, which reports the name.
///
/// # Errors
///
/// The first refused entry, with its class's code, at its value.
pub(super) fn judge_readable(
    target: &super::resolve::HeadRuleTarget,
    authored: &LocatedCells,
) -> Result<(), CollectionError> {
    if !authored.form.is_readable() {
        return Ok(());
    }
    let Some(subject) = readable_entries(target, &authored.subject) else {
        return Ok(());
    };
    let Some(result) = authored
        .result
        .as_deref()
        .map_or(Some(Vec::new()), |fields| readable_entries(target, fields))
    else {
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
    // The form step is the macro's and the term walker's, which locate a misplaced construct
    // where it stands inside the entry (design §2.4): a sentence with a form mistake is theirs to
    // answer first, and the kinds are not asked before it is. A record left open outside a
    // pattern is placed by the term walker too, at the record, wherever the entry holds it; the
    // collector knows only the entry's value, so it leaves that refusal to the walker.
    if sentence.iter().any(|entry| {
        entry.spelling.is_some_and(|spelling| {
            cell_entries::admit_form(authored.form, entry.side, spelling).is_err()
        })
    }) {
        return Ok(());
    }
    let judged = Sentence {
        form: authored.form,
        entries: &sentence,
        rewrite: Rewrite::Result,
        parameters: &authored.parameters,
        groups: target.groups(),
    }
    .judge();
    match judged {
        Err((_, Refusal::OpenRecordOutsidePattern)) | Ok(_) => Ok(()),
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
                refusal,
                target.groups(),
            ))
        }
    }
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
            Err(refused(
                EntryForm::Cells,
                entry(at),
                side,
                refusal,
                &tree.groups,
            ))
        }
    }
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

    /// The sort of the cell `identity`, where it is a leaf, as its declaration names it.
    fn sort(&self, identity: &DescriptorCellIdentity) -> Option<String> {
        let (_, cell, _) = self.cell(identity)?;
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

    /// The outermost `?` or `*` ancestor of the cell `identity`, if it has one.
    fn ancestor(&self, identity: &DescriptorCellIdentity) -> Option<Ancestor> {
        let (ancestors, _, owner) = self.cell(identity)?;
        let marked = ancestors
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
    entry: &Entry<'_>,
    side: EntrySide,
    refusal: Refusal,
    groups: &[GroupKind],
) -> Option<String> {
    let name = unraw(&entry.cell.field);
    let own = &entry.kind.own.layers;
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
            below_ancestor(form, name, entry.ancestor.as_ref()?, side, groups)
        }
        Refusal::RestMismatch => Some(
            "write `..` on both sides to keep the rest, or name it in the subject (`rest @ ..`) to drop or move it"
                .to_owned(),
        ),
        Refusal::MapCollectionKey => {
            if entry.field.spelling.as_ref().and_then(update_label).is_some() {
                return Some(
                    "leave the key out of the update, which keeps it, or write it as its subject matched it"
                        .to_owned(),
                );
            }
            let key = match own.as_slice() {
                [Layer::Instances(order), Layer::Group(group), ..] => group.key(*order)?,
                _ => return None,
            };
            Some(format!("write its key first, `{key}: ..`"))
        }
        Refusal::RecordUpdateBase => {
            let label = entry.field.spelling.as_ref().and_then(update_label)?;
            let group = match own.as_slice() {
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

/// The refusal `refusal` of the entry `entry`, on the side `side` of a sentence written in
/// `form`: why ([`Refusal::reason`]), then what to write instead where its class advises it
/// ([`advice`]), at the entry's value.
fn refused(
    form: EntryForm,
    entry: &Entry<'_>,
    side: EntrySide,
    refusal: Refusal,
    groups: &[GroupKind],
) -> CollectionError {
    let mut detail = refusal.reason(
        form,
        unraw(&entry.cell.field),
        &entry.kind,
        entry.sort.as_deref(),
    );
    if let Some(advice) = advice(form, entry, side, refusal, groups) {
        detail = format!("{detail}; {advice}");
    }
    let error = CollectionError::new(CollectionErrorKind::CellEntry(refusal), detail);
    match &entry.field.range {
        Some(range) => error.with_source_range(range.clone()),
        None => error,
    }
}
