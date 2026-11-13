//! Group records at a configuration position (ruling R4, TRI-D2): a group cell's entry written
//! as the record of its children, [`ProtocolRuleStateTerm::Record`], whose every child is that
//! child cell's entry.
//!
//! A record means its children's entries, each as if written as its own cell. Where every
//! child's entry is a term of the child's content, those entries are also the group's term over
//! them, the cell term `k::fragment![Group { .. }]` a whole group clause matches or writes, and
//! [`record_term`] gives it. A child whose entry is no term (a map, a `?` cell's presence) has no
//! place in that term: the Semantic IR builds no map with a frame inside a term, and a group
//! term holds no map pattern. Such a record's children are lowered as their own cells' clauses
//! instead ([`with_group_records`]). Both say the same of each of the group's cells, so a
//! record has one meaning whichever lowering takes it.

use krs_ir::{
    CellWrapper, Descriptor, DescriptorCellField, DescriptorIndex, DescriptorTerm,
    ProtocolCellContent, ProtocolRuleRecord, ProtocolRuleStateTerm, StableItemId,
};

use super::error::DescriptorLoweringError;
use super::origin::key_range;
use super::references::{declared_multiplicity, require_cell_field};

type DescriptorRuleCell = krs_ir::ProtocolRuleCell<krs_ir::DescriptorCellReference, DescriptorTerm>;
type Record = ProtocolRuleRecord<DescriptorTerm>;
type State = ProtocolRuleStateTerm<DescriptorTerm>;

/// The record of the group `group` that the cell term `term` is ([`Record::of_group_term`]).
pub(super) fn record_of_cell(
    term: &DescriptorTerm,
    group: &StableItemId,
    declarations: &DescriptorIndex<'_>,
) -> Option<Record> {
    Record::of_group_term(term, group, declarations)
}

/// The group cell term a record is when every child's entry is a term of its content
/// ([`Record::group_term`]).
pub(crate) fn record_term(record: &Record) -> Option<DescriptorTerm> {
    record.group_term()
}

/// A readable rule with each record written as the entry of a leaf cell, a constructor's record
/// the macro read as a group's because a field writes a map in braces naming every entry
/// (`cur: Load { m: { 0 -> v } }`), read as the constructor's term it is, each such field the map
/// it names: a leaf holds a term of its sort, braces naming every entry denote the map exactly
/// those entries (in a pattern the map pattern `0 |-> V`, in a result the map built), and a
/// constructor's field holds a term, so the record means `Load { m: k::map![0 -> v] }`, as that
/// spelling does. A record with a field no term spells (a map with a rest, a computation's items,
/// instance braces) is left as it is, refused on the leaf as before
/// ([`super::cell_states::record_on_leaf`]). `None` where the rule has no such record.
///
/// # Errors
///
/// A cell the declarations lack.
pub(super) fn with_leaf_constructor_records(
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &DescriptorIndex<'_>,
) -> Result<Option<krs_ir::DescriptorHeadRule>, DescriptorLoweringError> {
    let mut rewritten = rule.clone();
    let mut changed = false;
    for extra in &mut rewritten.extras {
        let krs_ir::ProtocolHeadRuleExtra::RewriteState {
            cell,
            before,
            after,
            ..
        } = extra
        else {
            continue;
        };
        let declared = require_cell_field(&cell.cell, declarations)?;
        if !matches!(declared.content, ProtocolCellContent::Leaf { .. }) {
            continue;
        }
        for (state, subject) in
            std::iter::once((before, true)).chain(after.iter_mut().map(|after| (after, false)))
        {
            let State::Record(record) = &*state else {
                continue;
            };
            if let Some(term) = constructor_record_term(record, subject) {
                *state = State::Term(term);
                changed = true;
            }
        }
    }
    Ok(changed.then_some(rewritten))
}

/// The constructor's term a record is whose head names a constructor (`Load { .. }`) and each of
/// whose fields is a term or a map naming every entry, that map written as the term it is on the
/// subject's side if `subject` ([`super::cell_states::map_term`]): the head's application with
/// those named fields, open where the record ends in `..`. `None` for any other record.
fn constructor_record_term(record: &Record, subject: bool) -> Option<DescriptorTerm> {
    let DescriptorTerm::Application {
        head_class,
        reference,
        path_key,
        arguments,
        instance,
        update: None,
        ..
    } = &record.head
    else {
        return None;
    };
    if !matches!(arguments, krs_ir::Arguments::Positional(values) if values.is_empty()) {
        return None;
    }
    let mut held = Vec::new();
    let fields = record
        .fields
        .iter()
        .map(|field| {
            let value = match &field.value {
                State::Term(term) | State::Group(term) => term.clone(),
                State::Map(krs_ir::ProtocolRuleMap {
                    body:
                        krs_ir::ProtocolRuleMapBody::Items {
                            remainder: krs_ir::ProtocolRuleFrame::Exact,
                            ..
                        },
                    ..
                }) => super::cell_states::map_term(&field.value, subject, &mut held)?,
                _ => return None,
            };
            Some(krs_ir::NamedTermArgument {
                key: field.key.clone(),
                field: krs_ir::ProductionFieldId::new(field.field.clone()).ok()?,
                value: Box::new(value),
            })
        })
        .collect::<Option<Vec<_>>>()?;
    held.is_empty().then(|| DescriptorTerm::Application {
        head_class: head_class.clone(),
        reference: reference.clone(),
        path_key: path_key.clone(),
        arguments: krs_ir::Arguments::named(fields),
        instance: instance.clone(),
        update: None,
        open: matches!(record.rest, krs_ir::ProtocolRecordRest::Open),
    })
}

/// `rule` with each computation child that a group record or an instance record writes in
/// brackets read as that child's K sequence (ruling R4). A record's child is its cell's entry,
/// read by the child's declared kind, and brackets on a computation cell are its items wherever
/// the cell is declared: `C { cc: [y, ..], .. }` matches what `cc: KCell(y, ..)` would. The macros
/// read such a child by its spelling, as list notation, since they cannot see that `cc` is a
/// computation cell, and list notation names a list, which a computation cell never holds: the
/// reading by kind is this one. Only brackets a K sequence spells are read so, the items and an
/// exact end or an anonymous `..`; any other list notation keeps its reading. `None` when no
/// child is read anew.
///
/// # Errors
///
/// A cell the declarations lack.
pub(super) fn with_computation_brackets(
    rule: &krs_ir::DescriptorConfigurationRule,
    declarations: &DescriptorIndex<'_>,
) -> Result<Option<krs_ir::DescriptorConfigurationRule>, DescriptorLoweringError> {
    let holds_records = |cells: &[DescriptorRuleCell]| {
        cells.iter().any(|cell| {
            matches!(
                cell.value,
                State::Record(_) | State::Instances(_) | State::Present { .. }
            )
        })
    };
    if !holds_records(&rule.subject.cells)
        && !rule
            .result
            .as_ref()
            .is_some_and(|result| holds_records(&result.cells))
    {
        return Ok(None);
    }
    let mut rule = rule.clone();
    let mut changed = false;
    for cell in rule
        .subject
        .cells
        .iter_mut()
        .chain(rule.result.iter_mut().flat_map(|result| &mut result.cells))
    {
        let declared = require_cell_field(&cell.field.cell, declarations)?;
        changed |= read_computation_brackets(&mut cell.value, declared, declarations);
    }
    Ok(changed.then_some(rule))
}

/// The record of its children's entries that the cell term `term` of the group cell `declared`
/// is when a computation child of it, or of a group it holds, is written in brackets, which only
/// that record reads as the child's K sequence ([`with_computation_brackets`]). `None` for every
/// other term, which keeps its reading as the group's term.
pub(super) fn bracketed_record(
    term: &DescriptorTerm,
    declared: &DescriptorCellField,
    declarations: &DescriptorIndex<'_>,
) -> Option<Record> {
    let ProtocolCellContent::Nested { declaration } = &declared.content else {
        return None;
    };
    let mut record = Record::of_group_term(term, &declaration.declaration, declarations)?;
    read_children_brackets(&mut record.fields, &declaration.declaration, declarations)
        .then_some(record)
}

/// The items of the K sequences that `record`'s children, and those of the groups it holds,
/// are entries of, in authored order.
pub(super) fn computation_items(record: &Record) -> Vec<DescriptorTerm> {
    record
        .fields
        .iter()
        .flat_map(|field| match &field.value {
            State::KSequence(sequence) => sequence
                .items
                .iter()
                .map(|item| item.value.clone())
                .collect(),
            State::Record(record) => computation_items(record),
            _ => Vec::new(),
        })
        .collect()
}

/// Reads the computation children's brackets of the records `state` holds as their K
/// sequences ([`with_computation_brackets`]); `declared` is the cell `state` is the entry of.
/// Whether any was read.
fn read_computation_brackets(
    state: &mut State,
    declared: &DescriptorCellField,
    declarations: &DescriptorIndex<'_>,
) -> bool {
    match state {
        State::Present { value } => read_computation_brackets(value, declared, declarations),
        State::Record(record) => match &record.head {
            DescriptorTerm::Cell { declaration, .. } => {
                let group = declaration.clone();
                read_children_brackets(&mut record.fields, &group, declarations)
            }
            _ => false,
        },
        State::Instances(instances) => {
            let ProtocolCellContent::Nested { declaration } = &declared.content else {
                return false;
            };
            let mut changed = false;
            for instance in instances.front.iter_mut().chain(&mut instances.back) {
                changed |= read_children_brackets(
                    &mut instance.fields,
                    &declaration.declaration,
                    declarations,
                );
            }
            changed
        }
        _ => false,
    }
}

/// [`read_computation_brackets`] over the children `fields` of a record of the group `group`.
fn read_children_brackets(
    fields: &mut [krs_ir::ProtocolRuleInstanceField<DescriptorTerm>],
    group: &StableItemId,
    declarations: &DescriptorIndex<'_>,
) -> bool {
    let Ok(declaration) = declarations.cell(group) else {
        return false;
    };
    // A record with a field that names no child is no record of `group`: its children are not
    // read anew, and the record's lowering refuses it ([`super::cell_states::record_children`]).
    let Ok(named) = super::cell_states::named_children(&declaration.fields, fields) else {
        return false;
    };
    let children = named
        .into_iter()
        .map(|(_, child)| child)
        .collect::<Vec<_>>();
    let mut changed = false;
    for (field, child) in fields.iter_mut().zip(children) {
        if let Some(sequence) = computation_sequence(&field.value, child) {
            field.value = State::KSequence(sequence);
            changed = true;
        } else {
            changed |= read_computation_brackets(&mut field.value, child, declarations);
        }
    }
    changed
}

/// The K sequence that the entry `value` of the record child `child` is, where the child is a
/// computation cell and the macros read its brackets as list notation ([`bracket_sequence`]):
/// brackets on a computation are its items. `None` for every other entry.
pub(super) fn computation_sequence(
    value: &State,
    child: &DescriptorCellField,
) -> Option<krs_ir::ProtocolRuleKSequence<DescriptorTerm>> {
    let computation = matches!(
        child.content,
        ProtocolCellContent::Leaf {
            wrapper: CellWrapper::KCell,
            ..
        }
    );
    match value {
        State::Term(term) if computation => bracket_sequence(term),
        _ => None,
    }
}

/// The K sequence that the list notation `term` spells: its levels' heads are the items, and the
/// brackets end exactly (`[x]`, `[]`) or in an anonymous `..` (`[y, ..]`), which a pattern's list
/// notation writes as `_` in the last level's tail and a result's as the kept rest that ends its
/// root spine (`[..]` alone is that rest). Each item keeps its own key, the sequence is located at
/// the brackets' outer level, and its `..` at the `_` or rest the macro wrote at it; brackets that
/// end in a term `..t` write it after their items. `None` for any other term, a level taken from
/// the back included.
fn bracket_sequence(
    term: &DescriptorTerm,
) -> Option<krs_ir::ProtocolRuleKSequence<DescriptorTerm>> {
    use krs_ir::{DescriptorApplicationRef, ListNotation};
    if let DescriptorTerm::KeptRest { key } = term {
        return Some(krs_ir::ProtocolRuleKSequence {
            payload_key: key.clone(),
            dot_k_key: None,
            notation: krs_ir::DescriptorKSequenceNotation::Comma,
            items: Vec::new(),
            tail: krs_ir::ProtocolRuleFrame::Anonymous { key: key.clone() },
        });
    }
    let DescriptorTerm::Application { reference, .. } = term else {
        return None;
    };
    if !matches!(
        reference.application,
        DescriptorApplicationRef::ListNotation(ListNotation::Cons | ListNotation::Empty)
    ) {
        return None;
    }
    let mut items = Vec::new();
    let mut level = term;
    let tail = loop {
        match level {
            DescriptorTerm::Application {
                reference,
                arguments: krs_ir::Arguments::Positional(arguments),
                update: None,
                ..
            } => match (&reference.application, arguments.as_slice()) {
                (DescriptorApplicationRef::ListNotation(ListNotation::Cons), [head, tail]) => {
                    items.push(krs_ir::ProtocolRuleKSequenceItem {
                        key: super::collection_types::term_key(head).clone(),
                        value: (**head).clone(),
                    });
                    level = tail;
                }
                (DescriptorApplicationRef::ListNotation(ListNotation::Empty), []) => {
                    break krs_ir::ProtocolRuleFrame::Exact;
                }
                _ => return None,
            },
            DescriptorTerm::Wildcard { key } if !items.is_empty() => {
                break krs_ir::ProtocolRuleFrame::Anonymous { key: key.clone() };
            }
            DescriptorTerm::KeptRest { key } => {
                break krs_ir::ProtocolRuleFrame::Anonymous { key: key.clone() };
            }
            // A result's `..t` of a term `t` (a declared binder of sort `K`) writes that
            // computation after the items, as `KCell(y, ..t)` does; a pattern's declared rest is
            // refused before ([`super::configuration_rules`] `check_child_rests`).
            DescriptorTerm::Variable { key, name, .. } if !items.is_empty() => {
                break krs_ir::ProtocolRuleFrame::Reuse {
                    key: key.clone(),
                    binding: name.clone(),
                };
            }
            _ => return None,
        }
    };
    Some(krs_ir::ProtocolRuleKSequence {
        payload_key: reference.key.clone(),
        dot_k_key: None,
        notation: krs_ir::DescriptorKSequenceNotation::Comma,
        items,
        tail,
    })
}

/// `rule` with each group record of entries ([`ProtocolRuleStateTerm::Record`]) lowered to the
/// entries the clauses lower: the group's cell term where every child's entry on both sides is
/// a term ([`record_term`]), else each child's own entry. `None` when the rule holds no record.
///
/// # Errors
///
/// A record whose head names another struct than its cell's group, or no `#[k::cell]` struct; a
/// record on a cell that is no group; a child that is no child of the group, or a `?` or `*`
/// child; and, as a limit, a record whose children are lowered as their own cells beside a whole
/// group entry (a binder or `_`) of the same cell on the other side.
#[expect(
    clippy::too_many_lines,
    reason = "Each cell's records are paired, checked and lowered in one ordered pass."
)]
pub(super) fn with_group_records(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorConfigurationRule,
    declarations: &DescriptorIndex<'_>,
) -> Result<Option<krs_ir::DescriptorConfigurationRule>, DescriptorLoweringError> {
    let holds_record = |cells: &[DescriptorRuleCell]| {
        cells.iter().any(|cell| match &cell.value {
            State::Record(_) => true,
            State::Present { value } => matches!(**value, State::Record(_)),
            _ => false,
        })
    };
    if !holds_record(&rule.subject.cells)
        && !rule
            .result
            .as_ref()
            .is_some_and(|result| holds_record(&result.cells))
    {
        return Ok(None);
    }
    let mut rule = rule.clone();
    present_group_terms(descriptor, &mut rule, declarations)?;
    // Each pass lowers the records at the cells' own level; a child's record is lowered by the
    // next, once its children are entries of their own.
    loop {
        let identities = rule
            .subject
            .cells
            .iter()
            .chain(rule.result.iter().flat_map(|result| &result.cells))
            .filter(|cell| matches!(cell.value, State::Record(_)))
            .map(|cell| cell.field.cell.clone())
            .collect::<Vec<_>>();
        let Some(identity) = identities.first() else {
            break;
        };
        let subject = rule
            .subject
            .cells
            .iter()
            .position(|cell| cell.field.cell == *identity);
        let result = rule.result.as_ref().and_then(|result| {
            result
                .cells
                .iter()
                .position(|cell| cell.field.cell == *identity)
        });
        let subject_cell = subject.map(|index| rule.subject.cells[index].clone());
        let result_cell =
            result.and_then(|index| rule.result.as_ref().map(|cells| cells.cells[index].clone()));
        let declared = require_cell_field(identity, declarations)?;
        let group = group_of(descriptor, declared, [&subject_cell, &result_cell])?;
        let records = [&subject_cell, &result_cell]
            .into_iter()
            .flatten()
            .filter_map(|cell| match &cell.value {
                State::Record(record) => Some((cell, record)),
                _ => None,
            })
            .collect::<Vec<_>>();
        for (_, record) in &records {
            check_head(descriptor, record, declared, &group)?;
        }
        // The one place a record's lowering is chosen. Where every child's entry on both sides
        // is a term of its content, the record is the group's cell term over those terms, the
        // whole group clause K has always been given; otherwise its children are lowered as
        // their own cells' clauses, exactly as if each were written as its own cell (R4). A
        // fixed group's cells are matched and written the same either way: an unnamed child of
        // a subject record is unconstrained in both. A result record whose `..` leaves a child
        // unnamed, here or in a group child it writes, keeps that child's content: the record
        // of a group that is there writes only the children it names, which its children's own
        // cells say and no group term does, since a term names every child.
        let kept = result_cell.as_ref().is_some_and(|cell| match &cell.value {
            State::Record(record) => leaves_children(record, declarations),
            _ => false,
        });
        let whole = !kept
            && records
                .iter()
                .all(|(_, record)| record_term(record).is_some());
        if whole {
            for (index, side) in [(subject, true), (result, false)] {
                let Some(index) = index else { continue };
                let cell = cell_mut(&mut rule, index, side);
                if let State::Record(record) = &cell.value {
                    let term = record_term(record).expect("checked above");
                    cell.value = State::Group(term);
                }
            }
            continue;
        }
        // A subject's `_` matches the group whatever its children hold, as the record naming
        // none of them does, so beside a result whose children are their own cells it names no
        // cell, and each child the result writes is overwritten (`with_overwritten_cells`).
        let subject_cell = subject_cell.filter(|cell| {
            !(kept
                && matches!(
                    &cell.value,
                    State::Term(DescriptorTerm::Wildcard { .. })
                        | State::Group(DescriptorTerm::Wildcard { .. })
                ))
        });
        // Beside a term of the whole group on the other side, a record is that group's term too:
        // where each child is a term once its map entries are read as the map terms they are
        // ([`super::cell_states::group_state_term`]), it is written so, and the group is one term
        // on both sides.
        let mut termed = false;
        for (cell, other, on_subject) in [
            (&subject_cell, &result_cell, true),
            (&result_cell, &subject_cell, false),
        ] {
            if let (Some(cell), Some(other)) = (cell, other)
                && matches!(cell.value, State::Record(_))
                && !matches!(other.value, State::Record(_))
            {
                let State::Record(record) = &cell.value else {
                    unreachable!("matched as a record above")
                };
                let mut held = Vec::new();
                if !kept
                    && let Some(term) = super::cell_states::group_state_term(
                        &cell.value,
                        on_subject,
                        declarations,
                        &mut held,
                    )
                {
                    let index = if on_subject { subject } else { result }
                        .expect("the cell was found at an index");
                    cell_mut(&mut rule, index, on_subject).value = State::Group(term);
                    super::cell_states::declare_map_rests(
                        &mut rule.bindings,
                        &held,
                        &rule.pattern_key,
                    );
                    termed = true;
                    break;
                }
                let (child, entry) = no_term_entry(
                    descriptor,
                    record,
                    on_subject,
                    declarations,
                    &cell.field.key,
                )?;
                let reason = if kept {
                    format!(
                        "not supported yet: the result's record of `{0}` leaves children unnamed, which keep what the subject's match of the whole group holds, so it is an update of that match, a term of the whole group; but it writes its child `{child}` as {entry}; match the group with a record of its children, so that each child is its own cell",
                        identity.field
                    )
                } else {
                    format!(
                        "not supported yet: the record of `{0}` writes its child `{child}` as {entry}, so its children are matched and written as their own cells, and the other side writes the group whole, as one term, which the Semantic IR cannot build from those children; write a record of the group's children on both sides",
                        identity.field
                    )
                };
                return Err(super::cell_states::collection_error(
                    descriptor,
                    krs_diagnostic::codes::analysis::COLLECTION_ENTRY,
                    &other.field.key,
                    reason,
                ));
            }
        }
        if termed {
            continue;
        }
        let mut subject_children = match &subject_cell {
            Some(cell) => children(descriptor, cell, &group, declarations)?,
            None => Vec::new(),
        };
        let result_children = match &result_cell {
            Some(cell) => children(descriptor, cell, &group, declarations)?,
            None => Vec::new(),
        };
        if let Some(index) = subject {
            rule.subject
                .cells
                .splice(index..=index, subject_children.drain(..));
        }
        if let (Some(index), Some(cells)) = (result, rule.result.as_mut()) {
            cells.cells.splice(index..=index, result_children);
        }
    }
    Ok(Some(rule))
}

/// The record of its children's entries that the cell term `term`, a result's entry of the
/// group cell `declared`, is when its `..` leaves a child unnamed ([`leaves_children`]): the
/// children it names are written and the others keep their content, which only the children's
/// own cells say ([`with_group_records`]). `None` for every other term.
pub(super) fn kept_record(
    term: &DescriptorTerm,
    declared: &DescriptorCellField,
    declarations: &DescriptorIndex<'_>,
) -> Option<Record> {
    let ProtocolCellContent::Nested { declaration } = &declared.content else {
        return None;
    };
    Record::of_group_term(term, &declaration.declaration, declarations)
        .filter(|record| leaves_children(record, declarations))
}

/// Whether `record`, a record a result writes, ends in a `..` that leaves a child of its group
/// unnamed, at its own level or in a group child record it holds. A `..` after every child
/// leaves none, and the record is the exact one.
fn leaves_children(record: &Record, declarations: &DescriptorIndex<'_>) -> bool {
    let open = matches!(record.rest, krs_ir::ProtocolRecordRest::Open)
        && match &record.head {
            DescriptorTerm::Cell { declaration, .. } => declarations
                .cell(declaration)
                .is_ok_and(|group| record.fields.len() < group.fields.len()),
            _ => false,
        };
    open || record.fields.iter().any(|field| match &field.value {
        State::Record(child) => leaves_children(child, declarations),
        _ => false,
    })
}

/// Writes each present optional group's record as the group's term: an optional cell's entry is
/// its presence around its content, and only a content term has a lowering there.
fn present_group_terms(
    descriptor: &Descriptor,
    rule: &mut krs_ir::DescriptorConfigurationRule,
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    let mut held = Vec::new();
    let result_cells = rule.result.iter_mut().flat_map(|result| &mut result.cells);
    for (cell, on_subject) in rule
        .subject
        .cells
        .iter_mut()
        .map(|cell| (cell, true))
        .chain(result_cells.map(|cell| (cell, false)))
    {
        let State::Present { value } = &cell.value else {
            continue;
        };
        let State::Record(record) = &**value else {
            continue;
        };
        let declared = require_cell_field(&cell.field.cell, declarations)?;
        let ProtocolCellContent::Nested { declaration } = &declared.content else {
            continue;
        };
        check_head(descriptor, record, declared, &declaration.declaration)?;
        let record = record.clone();
        let State::Present { value } = &mut cell.value else {
            continue;
        };
        // A map child's entries are the map term they are ([`super::cell_states::map_term`]).
        let state = State::Record(record.clone());
        let Some(term) =
            super::cell_states::group_state_term(&state, on_subject, declarations, &mut held)
        else {
            let (child, entry) = no_term_entry(
                descriptor,
                &record,
                on_subject,
                declarations,
                &cell.field.key,
            )?;
            return Err(super::cell_states::collection_error(
                descriptor,
                krs_diagnostic::codes::analysis::COLLECTION_ENTRY,
                &cell.field.key,
                format!(
                    "not supported yet: the present group `{}` is written whole, as one term naming every child, and its record writes the child `{child}` as {entry}",
                    declared.rust_field
                ),
            ));
        };
        **value = State::Group(term);
    }
    super::cell_states::declare_map_rests(&mut rule.bindings, &held, &rule.pattern_key);
    Ok(())
}

/// The child of `record`, on the subject's side if `on_subject`, that no term of the whole group
/// can hold, and what its entry is, as a stated limit's text says it
/// ([`super::cell_states::no_term_child`]).
///
/// # Errors
///
/// A map entry on a child whose sort is not the builtin `Map`: the author's mistake, which no
/// lowering admits, refused as a term of another sort than its place's, at the entry `key`.
fn no_term_entry(
    descriptor: &Descriptor,
    record: &Record,
    on_subject: bool,
    declarations: &DescriptorIndex<'_>,
    key: &krs_ir::ProvenanceKey,
) -> Result<(String, &'static str), DescriptorLoweringError> {
    use super::cell_states::NoTerm;
    let (child, why) = super::cell_states::no_term_child(record, on_subject, declarations)
        .unwrap_or(("?", NoTerm::Other));
    let entry = match why {
        NoTerm::UnnamedRest => {
            return Err(DescriptorLoweringError::invalid_term(
                descriptor.id(),
                format!(
                    "the result writes the child `{child}` as a map over an anonymous `..`, which names no map in a result: a result's map is written over a map it names, `k::map![k -> v, ..r]` with `r` the subject's `r @ ..`, or the child is left out of the record to keep it"
                ),
            )
            .within(descriptor.id(), key_range(descriptor, key).as_ref()));
        }
        NoTerm::Computation => "a computation's items, which no term of the group holds yet",
        NoTerm::NotMapSort => {
            return Err(DescriptorLoweringError::invalid_term(
                descriptor.id(),
                format!(
                    "the child `{child}` is written as a map's entries, but its sort is not the builtin `Map`: map notation denotes the entries of a cell whose sort is `Map`"
                ),
            )
            .within(descriptor.id(), key_range(descriptor, key).as_ref()));
        }
        NoTerm::Other => "an entry no term of the group holds yet",
    };
    Ok((child.to_owned(), entry))
}

fn cell_mut(
    rule: &mut krs_ir::DescriptorConfigurationRule,
    index: usize,
    subject: bool,
) -> &mut DescriptorRuleCell {
    if subject {
        &mut rule.subject.cells[index]
    } else {
        &mut rule.result.as_mut().expect("a result cell was found").cells[index]
    }
}

/// The group a record's cell holds, or the refusal of a record on a leaf, which holds none
/// ([`super::cell_states::record_on_leaf`]).
fn group_of(
    descriptor: &Descriptor,
    declared: &DescriptorCellField,
    cells: [&Option<DescriptorRuleCell>; 2],
) -> Result<StableItemId, DescriptorLoweringError> {
    if let ProtocolCellContent::Nested { declaration } = &declared.content {
        return Ok(declaration.declaration.clone());
    }
    let record = cells
        .into_iter()
        .flatten()
        .find_map(|cell| match &cell.value {
            State::Record(record) => Some(record),
            _ => None,
        })
        .expect("a record was found");
    Err(super::cell_states::record_on_leaf(
        descriptor,
        declared,
        &record.key,
    ))
}

/// Refuses a record whose head names another struct than the cell's group
/// ([`super::cell_states::foreign_record`]).
fn check_head(
    descriptor: &Descriptor,
    record: &Record,
    declared: &DescriptorCellField,
    group: &StableItemId,
) -> Result<(), DescriptorLoweringError> {
    super::cell_states::foreign_record(
        descriptor,
        super::cell_states::RecordOf::Group,
        &declared.rust_field,
        &record.head,
        &record.key,
        group,
    )
    .map_or(Ok(()), Err)
}

/// A record's children as their own cells' entries, in authored order.
fn children(
    descriptor: &Descriptor,
    cell: &DescriptorRuleCell,
    group: &StableItemId,
    declarations: &DescriptorIndex<'_>,
) -> Result<Vec<DescriptorRuleCell>, DescriptorLoweringError> {
    let State::Record(record) = &cell.value else {
        return Ok(vec![cell.clone()]);
    };
    let declaration = declarations.cell(group)?;
    super::cell_states::record_children(
        descriptor,
        super::cell_states::RecordOf::Group,
        group.item_name(),
        &declaration.fields,
        &record.fields,
        declarations,
    )?
    .into_iter()
    .map(|(field, child)| {
            let presence = matches!(field.value, State::Present { .. } | State::Absent);
            if presence
                || declared_multiplicity(child, declarations) != krs_ir::cell_kind::Multiplicity::One
            {
                return Err(super::cell_states::collection_error(
                    descriptor,
                    krs_diagnostic::codes::analysis::COLLECTION_ENTRY,
                    &field.key,
                    format!(
                        "the child `{}` of `{}` is a `?` or `*` cell, whose entry a group record does not name yet, as {}",
                        field.field,
                        group.item_name(),
                        krs_syntax::INSTANCE_CHILD_MULTIPLICITY
                    ),
                ));
            }
            // A group child's cell term of another struct is a term of another cell sort than
            // the child's, as a record of another struct is at the record's own level.
            if let State::Term(term) = &field.value
                && let Some(refusal) =
                    super::cell_states::foreign_group_term(descriptor, child, term)
            {
                return Err(refusal);
            }
            let nested = matches!(child.content, ProtocolCellContent::Nested { .. });
            let (wrapper, value) = match (&field.value, nested) {
                (State::Term(term), true) => (None, State::Group(term.clone())),
                (value, true) => (None, value.clone()),
                (value @ State::KSequence(_), false) => (Some(CellWrapper::KCell), value.clone()),
                (value, false) => (Some(CellWrapper::Cell), value.clone()),
            };
            Ok(DescriptorRuleCell {
                field: krs_ir::DescriptorCellReference {
                    key: field.key.clone(),
                    cell: child.reference.cell.clone(),
                },
                wrapper_key: wrapper.map(|_| field.key.clone()),
                wrapper,
                value,
            })
        })
        .collect()
}
