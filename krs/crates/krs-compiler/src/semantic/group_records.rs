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
    let mut changed = false;
    for field in fields {
        let Some(child) = declaration
            .fields
            .iter()
            .find(|child| child.rust_field == field.field)
        else {
            continue;
        };
        let computation = matches!(
            child.content,
            ProtocolCellContent::Leaf {
                wrapper: CellWrapper::KCell,
                ..
            }
        );
        if computation
            && let State::Term(term) = &field.value
            && let Some(sequence) = bracket_sequence(term)
        {
            field.value = State::KSequence(sequence);
            changed = true;
        } else {
            changed |= read_computation_brackets(&mut field.value, child, declarations);
        }
    }
    changed
}

/// The K sequence that the list notation `term` spells: its levels' heads are the items, and the
/// brackets end exactly (`[x]`, `[]`) or in an anonymous `..` (`[y, ..]`), which a pattern's list
/// notation writes as `_` in the last level's tail. Each item keeps its own key, the sequence is
/// located at the brackets' outer level, and its `..` at the `_` the macro wrote at it. `None`
/// for any other term, a named rest or a level taken from the back included.
fn bracket_sequence(
    term: &DescriptorTerm,
) -> Option<krs_ir::ProtocolRuleKSequence<DescriptorTerm>> {
    use krs_ir::{DescriptorApplicationRef, ListNotation};
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

/// The struct a record's head names, for a message: its `#[k::cell]` struct, else none.
fn head_name(record: &Record) -> String {
    match &record.head {
        DescriptorTerm::Cell { declaration, .. } => {
            format!("`{}`", declaration.item_name())
        }
        _ => "no `#[k::cell]` struct".to_owned(),
    }
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
        for (cell, record) in &records {
            check_head(descriptor, cell, record, declared, &group)?;
        }
        // The one place a record's lowering is chosen. Where every child's entry on both sides
        // is a term of its content, the record is the group's cell term over those terms, the
        // whole group clause K has always been given; otherwise its children are lowered as
        // their own cells' clauses, exactly as if each were written as its own cell (R4). A
        // fixed group's cells are matched and written the same either way: an unnamed child of
        // a subject record is unconstrained in both, and a result record names every child.
        let whole = records
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
        for (cell, other) in [(&subject_cell, &result_cell), (&result_cell, &subject_cell)] {
            if let (Some(cell), Some(other)) = (cell, other)
                && matches!(cell.value, State::Record(_))
                && !matches!(other.value, State::Record(_))
            {
                return Err(DescriptorLoweringError::unsupported_shape(
                    "group record",
                    format!(
                        "not supported yet: the record of `{}` writes a child as an entry no term spells, so its children are matched and written as their own cells, and the other side writes the group whole, which the Semantic IR cannot build from those children (it has no map concatenation); write a record of the group's children on both sides",
                        identity.field
                    ),
                )
                .within(descriptor.id(), key_range(descriptor, &other.field.key).as_ref()));
            }
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

/// Writes each present optional group's record as the group's term: an optional cell's entry is
/// its presence around its content, and only a content term has a lowering there.
fn present_group_terms(
    descriptor: &Descriptor,
    rule: &mut krs_ir::DescriptorConfigurationRule,
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    for cell in rule
        .subject
        .cells
        .iter_mut()
        .chain(rule.result.iter_mut().flat_map(|result| &mut result.cells))
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
        check_head(descriptor, cell, record, declared, &declaration.declaration)?;
        let record = record.clone();
        let State::Present { value } = &mut cell.value else {
            continue;
        };
        let Some(term) = record_term(&record) else {
            return Err(DescriptorLoweringError::unsupported_shape(
                "group record",
                format!(
                    "not supported yet: the present group `{}` is written as a record whose child is an entry no term spells",
                    declared.rust_field
                ),
            )
            .within(descriptor.id(), key_range(descriptor, &cell.field.key).as_ref()));
        };
        **value = State::Group(term);
    }
    Ok(())
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

/// The group a record's cell holds, or the refusal of a record on a cell that holds none.
fn group_of(
    descriptor: &Descriptor,
    declared: &DescriptorCellField,
    cells: [&Option<DescriptorRuleCell>; 2],
) -> Result<StableItemId, DescriptorLoweringError> {
    if let ProtocolCellContent::Nested { declaration } = &declared.content {
        return Ok(declaration.declaration.clone());
    }
    let cell = cells
        .into_iter()
        .flatten()
        .find(|cell| matches!(cell.value, State::Record(_)))
        .expect("a record was found");
    Err(DescriptorLoweringError::invalid_term(
        descriptor.id(),
        format!(
            "`{}` is a leaf cell, whose content is a term, and a record whose field is written as a map entry, `{{ k -> v, .. }}`, is no term: a map is the entry of a Map cell",
            declared.rust_field
        ),
    )
    .within(descriptor.id(), key_range(descriptor, &cell.field.key).as_ref()))
}

/// Refuses a record whose head names another struct than the cell's group.
fn check_head(
    descriptor: &Descriptor,
    cell: &DescriptorRuleCell,
    record: &Record,
    declared: &DescriptorCellField,
    group: &StableItemId,
) -> Result<(), DescriptorLoweringError> {
    if matches!(&record.head, DescriptorTerm::Cell { declaration, .. } if declaration == group) {
        return Ok(());
    }
    Err(DescriptorLoweringError::invalid_term(
        descriptor.id(),
        format!(
            "the record names {}, and `{}` holds `{}`",
            head_name(record),
            declared.rust_field,
            group.item_name()
        ),
    )
    .within(
        descriptor.id(),
        key_range(descriptor, &cell.field.key).as_ref(),
    ))
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
    record
        .fields
        .iter()
        .map(|field| {
            let at = || key_range(descriptor, &field.key);
            let Some(child) = declaration
                .fields
                .iter()
                .find(|child| child.rust_field == field.field)
            else {
                return Err(DescriptorLoweringError::invalid_term(
                    descriptor.id(),
                    format!(
                        "the group `{}` has no child `{}`",
                        group.item_name(),
                        field.field
                    ),
                )
                .within(descriptor.id(), at().as_ref()));
            };
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
