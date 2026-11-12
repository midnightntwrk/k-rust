//! Optional (`?`) cells and cell collections (`*`) in configuration rules
//! (KF-023): `Some`/`None` entries and instance lists, shared by `cells!`
//! rules and readable records.

use std::collections::{BTreeMap, BTreeSet};

use krs_diagnostic::codes;
use krs_ir::{
    CellClauseKind, CellCollectionType, CellContentFrame, CellPost, ConfigurationClause,
    Descriptor, DescriptorCellField, DescriptorCellReference, DescriptorFixedConfiguration,
    DescriptorIndex, DescriptorInitializerCell, DescriptorTerm, FixedCellClause, InstanceChild,
    InstanceClause, InstanceDelimiter, InstanceOrdering, InstancesClause, OptionalCellClause,
    Presence, ProtocolCellContent, ProtocolInitializerCellContent, ProtocolInstanceRest,
    ProtocolRuleFrame, ProtocolRuleInstance, ProtocolRuleInstances, ProtocolRuleStateTerm,
    ProvenanceKey, SemanticId, StableItemId,
};
use krs_ir_levels::{IrTermKind, SemanticSortRef, SemanticTerm};

use super::built_maps::{MapBase, writes_over_whole_map};
use super::catalog::semantic_sort_ref;
use super::error::DescriptorLoweringError;
use super::origin::{semantic_cell_id, semantic_origin};
use super::references::{declared_kind, declared_multiplicity, require_cell_field};
use krs_ir::cell_kind::{CellKind, Layer, Multiplicity, Order, ResultInstance};
use krs_ir::subject::KeySpelling;

/// A rule cell state as transported.
pub(super) type DescriptorState = ProtocolRuleStateTerm<DescriptorTerm>;

/// Lowers the terms of optional and collection states for one rule.
pub(super) trait StateLowering {
    /// The rule's descriptor.
    fn descriptor(&self) -> &Descriptor;

    /// Lowers one leaf, group, `k!`, or `map!` state at its cell's sort; an
    /// error that names no narrower node may be located at the entry,
    /// `entry_key`.
    fn lower_state(
        &mut self,
        state: &DescriptorState,
        sort: &SemanticSortRef,
        entry_key: &ProvenanceKey,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError>;

    /// Lowers a result's state, whose whole map is built over `base`
    /// ([`super::built_maps`]).
    fn lower_result(
        &mut self,
        state: &DescriptorState,
        sort: &SemanticSortRef,
        entry_key: &ProvenanceKey,
        base: &MapBase<'_>,
    ) -> Result<SemanticTerm, DescriptorLoweringError>;

    /// Lowers one cell of a Set collection's instance that a pattern looks
    /// up: as a key is, each construct it computes written as a fresh
    /// variable a guard equates with its value ([`super::set_instances`]).
    fn lower_looked_up(
        &mut self,
        state: &DescriptorState,
        sort: &SemanticSortRef,
        entry_key: &ProvenanceKey,
    ) -> Result<SemanticTerm, DescriptorLoweringError>;

    /// Whether two lowered terms are the same term, ignoring origins.
    fn same(&self, left: &SemanticTerm, right: &SemanticTerm) -> bool;

    /// Records the computation rest `tail` a clause moves, which the rule must use
    /// ([`super::configuration_rules::MovedComputation`]).
    fn moved_computation_remainder(&mut self, tail: SemanticId);

    /// The sort the rule binds `name` at, where it binds it, and whether every term of `sort`
    /// is a term of it.
    fn bound_sort(&self, name: &str, sort: &SemanticSortRef) -> Option<(SemanticSortRef, bool)>;

    /// Allocates and declares a binder the sentence's long form adds for `field` of the record
    /// labelled `label`, as a variable of `sort`: named as a record update's hidden binder is
    /// ([`super::record_updates::hidden_binder_name`]), by one allocation for the whole sentence,
    /// so it is no other binder of the sentence, a record update's included.
    fn hidden_binder(
        &mut self,
        label: &str,
        field: &str,
        sort: &SemanticSortRef,
    ) -> Result<SemanticId, DescriptorLoweringError>;
}

/// The diagnostic for an optional or collection entry K cannot express.
pub(super) fn collection_error(
    descriptor: &Descriptor,
    code: krs_diagnostic::Code,
    key: &ProvenanceKey,
    reason: String,
) -> DescriptorLoweringError {
    let range = semantic_origin(descriptor, key.clone(), "cell-collection-entry")
        .ok()
        .and_then(|origin| origin.origin().exact_authored_range().map(Box::new));
    DescriptorLoweringError::CellCollection {
        code,
        reason,
        range,
        item: None,
    }
}

/// Why a record of the group `group`, whose declared children are `children`, cannot name the
/// cell `name`, which is none of them: the reason a record's refusal of the field gives after
/// "`group` has no child `name`".
///
/// A record at a configuration position, a group's or an instance's, is the record of its
/// struct, as `k::fragment![crate::G { .. }]` writes it: each field is one of the struct's own
/// children, written as that child's entry and read by the child's kind (R4). A cell deeper in
/// the group is no field of it, so the record cannot name it, whatever its depth: a cell inside a
/// group child is written in that child's record, and one inside a `?` or `*` cell below
/// through that cell's entry, which a record does not name yet. Only a sentence's own record
/// names a cell at any depth by its name, because it is no struct's record but the sentence's set
/// of cells (the `k::cells!` entries, each named through its group struct, `crate::Thread::tenv:`),
/// placed by the instances its cells lie in; so that is where the advice sends the author.
///
/// Empty where no cell of the group's tree has that name.
pub(super) fn descendant_reason(
    group: &str,
    children: &[DescriptorCellField],
    name: &str,
    declarations: &DescriptorIndex<'_>,
) -> String {
    /// The fields from one of `children` down to the cell named `name`, outermost first.
    fn path<'d>(
        children: &'d [DescriptorCellField],
        name: &str,
        declarations: &DescriptorIndex<'d>,
    ) -> Option<Vec<&'d DescriptorCellField>> {
        children.iter().find_map(|child| {
            let ProtocolCellContent::Nested { declaration } = &child.content else {
                return None;
            };
            let grandchildren = &declarations.cell(&declaration.declaration).ok()?.fields;
            let below = match grandchildren.iter().find(|cell| cell.rust_field == name) {
                Some(found) => vec![found],
                None => path(grandchildren, name, declarations)?,
            };
            Some(std::iter::once(child).chain(below).collect())
        })
    }
    let Some(found) = path(children, name, declarations) else {
        return String::new();
    };
    let head = format!(
        ": a record names its struct's own children, each as that child's entry, and `{name}`"
    );
    let marked = found.iter().find_map(|cell| {
        let (kind, inside) = match declared_multiplicity(cell, declarations) {
            Multiplicity::One => return None,
            Multiplicity::Optional => ("optional cell".to_owned(), "the"),
            Multiplicity::Many(order) => (
                format!(
                    "{} collection",
                    match order {
                        krs_ir::cell_kind::Order::Map => "Map",
                        krs_ir::cell_kind::Order::Set => "Set",
                        krs_ir::cell_kind::Order::List => "List",
                    }
                ),
                "an instance of the",
            ),
        };
        Some((cell.rust_field.as_str(), kind, inside))
    });
    if let Some((holder, kind, inside)) = marked {
        let (place, named) = if holder == name {
            (format!("is the {kind} `{name}`"), format!("`{name}`"))
        } else {
            (
                format!("lies in {inside} {kind} `{holder}`"),
                format!("`{name}`, or `{holder}`, which holds it,"),
            )
        };
        return format!(
            "{head} {place} inside `{group}`, whose entry a record does not name yet; a sentence's own record names a cell at any depth by its name, so name {named} there, beside `{group}`'s other cells, as a rule for `{group}` does"
        );
    }
    // Every cell on the way is a group child at a fixed position: the record of each names the
    // next, down to the cell.
    let (cell, groups) = found.split_last().expect("the path ends at the cell");
    let mut written = format!("{}: ..", cell.rust_field);
    for child in groups.iter().rev() {
        let ProtocolCellContent::Nested { declaration } = &child.content else {
            unreachable!("each cell on the way holds the next");
        };
        written = format!(
            "{}: {} {{ {written}, .. }}",
            child.rust_field,
            declaration.declaration.item_name()
        );
    }
    format!(
        "{head} is a cell of its child `{}`, so write it inside that child's record, `{written}`",
        groups[0].rust_field
    )
}

/// Which record at a configuration position a refusal is of: a group record, the entry of a
/// group cell, or an instance record in a collection's instance list.
#[derive(Clone, Copy)]
pub(super) enum RecordOf {
    Group,
    Instance,
}

/// A field of a record at a configuration position or of a group's cell term: the child it
/// names and where it is written.
pub(super) trait RecordField {
    /// The Rust field name of the child the field names.
    fn child_name(&self) -> &str;
    /// The field's provenance.
    fn child_key(&self) -> &ProvenanceKey;
}

impl RecordField for krs_ir::ProtocolRuleInstanceField<DescriptorTerm> {
    fn child_name(&self) -> &str {
        &self.field
    }
    fn child_key(&self) -> &ProvenanceKey {
        &self.key
    }
}

impl RecordField for krs_ir::DescriptorCellTermField {
    fn child_name(&self) -> &str {
        self.field.as_str()
    }
    fn child_key(&self) -> &ProvenanceKey {
        &self.key
    }
}

/// Each of a record's `fields` with the declared child of `children` it names, in written
/// order, or the first field that names none.
///
/// A field that names no child makes the record no record of its struct ([`no_child`]), so
/// every reader of a record's children reads them through this, and none reads the fields of a
/// record that is not one.
pub(super) fn named_children<'f, 'd, F: RecordField>(
    children: &'d [DescriptorCellField],
    fields: &'f [F],
) -> Result<Vec<(&'f F, &'d DescriptorCellField)>, &'f F> {
    fields
        .iter()
        .map(|field| {
            children
                .iter()
                .find(|child| child.rust_field == field.child_name())
                .map(|child| (field, child))
                .ok_or(field)
        })
        .collect()
}

/// [`named_children`] of a record of the struct `group`, declared `children`, refusing the
/// first field that names none ([`no_child`]) before any field is read.
pub(super) fn record_children<'f, 'd, F: RecordField>(
    descriptor: &Descriptor,
    of: RecordOf,
    group: &str,
    children: &'d [DescriptorCellField],
    fields: &'f [F],
    declarations: &DescriptorIndex<'_>,
) -> Result<Vec<(&'f F, &'d DescriptorCellField)>, DescriptorLoweringError> {
    named_children(children, fields).map_err(|field| {
        no_child(
            descriptor,
            of,
            group,
            children,
            field.child_name(),
            field.child_key(),
            declarations,
        )
    })
}

/// The refusal of a record's field `field` that names none of the children of the struct
/// `group`, declared `children`, whose record it is.
///
/// A record at a configuration position is the record of its struct, as a constructor record is
/// its constructor's ([`descendant_reason`]), so a field its struct lacks is the one mistake a
/// constructor record makes with a field its constructor lacks: a term whose fields disagree with
/// its struct's (`krs::analysis::invalid-term`), a group's record and an instance's alike.
pub(super) fn no_child(
    descriptor: &Descriptor,
    of: RecordOf,
    group: &str,
    children: &[DescriptorCellField],
    field: &str,
    key: &ProvenanceKey,
    declarations: &DescriptorIndex<'_>,
) -> DescriptorLoweringError {
    let record = match of {
        RecordOf::Group => format!("the group `{group}`"),
        RecordOf::Instance => format!("the instance cell `{group}`"),
    };
    collection_error(
        descriptor,
        codes::analysis::INVALID_TERM,
        key,
        format!(
            "{record} has no child `{field}`{}",
            descendant_reason(group, children, field, declarations)
        ),
    )
}

/// The refusal of a group record at `key` written as the entry of the leaf cell `declared`.
///
/// A leaf holds a term of its sort. A record reaches lowering as a record, not as the group's
/// cell term, only when it writes a child as a map's entries or a map read, which no term
/// spells: such a child is the entry of the child's own cell, which only the group's cell holds,
/// so the record is no term and no leaf's content, whatever the leaf's sort
/// (`krs::analysis::invalid-term`).
pub(super) fn record_on_leaf(
    descriptor: &Descriptor,
    declared: &DescriptorCellField,
    key: &ProvenanceKey,
) -> DescriptorLoweringError {
    collection_error(
        descriptor,
        codes::analysis::INVALID_TERM,
        key,
        format!(
            "`{}` is a leaf cell, whose content is a term, and this record writes a child as a map's entries or a map read (`{{ k -> v, .. }}`, `k::map![..]`), which no term spells, so it is no term: such a child is the entry of its own cell, which only the group's cell holds",
            declared.rust_field
        ),
    )
}

/// The refusal of a group record's child `declared`, a `?` cell, written as a bare value at
/// `key`, wherever the record stands.
///
/// The child's place in its parent holds the cell or its absence, so a value there says which:
/// `Some(..)` the cell with its content, `None` its absence. A bare term, binder or `_` says
/// neither, as the same value written as the optional cell's own entry does not, and a group
/// record means the same cell at a configuration position and as a value, so the refusal is
/// the entry's (`krs::analysis::optional-presence`), with its reason and advice.
pub(super) fn optional_child_without_presence(
    descriptor: &Descriptor,
    declared: &DescriptorCellField,
    declarations: &DescriptorIndex<'_>,
    key: &ProvenanceKey,
) -> DescriptorLoweringError {
    let kind = krs_ir::cell_kind::EntryKind {
        path: CellKind::default(),
        own: declared_kind(declared, declarations),
    };
    let reason = krs_syntax::cell_entries::Refusal::OptionalWithoutPresence.reason(
        krs_syntax::cell_entry::EntryForm::Cells,
        &declared.rust_field,
        &kind,
        None,
    );
    collection_error(
        descriptor,
        codes::analysis::OPTIONAL_PRESENCE,
        key,
        format!("{reason}; write its entry inside `Some(..)`, or as `None` for its absence"),
    )
}

/// The refusal of the term `term` written for the group cell `declared` when it is a group
/// record (or an alias over one) of another struct than the cell's group ([`foreign_record`]);
/// `None` for any other term or cell. A record whose children are all terms reaches the cell as
/// its cell term, so this is the record's own refusal in that spelling.
pub(super) fn foreign_group_term(
    descriptor: &Descriptor,
    declared: &DescriptorCellField,
    term: &DescriptorTerm,
) -> Option<DescriptorLoweringError> {
    let ProtocolCellContent::Nested { declaration } = &declared.content else {
        return None;
    };
    let record = match term {
        DescriptorTerm::As { pattern, .. } => pattern.as_ref(),
        _ => term,
    };
    let DescriptorTerm::Cell { key, .. } = record else {
        return None;
    };
    foreign_record(
        descriptor,
        RecordOf::Group,
        &declared.rust_field,
        record,
        key,
        &declaration.declaration,
    )
}

/// The refusal of a record whose head names another struct than `group`, the struct the cell
/// `cell` holds (or its collection's instances are), or no `#[k::cell]` struct; `None` when it
/// names `group`.
///
/// The record says which struct it is the record of, and that struct's records are terms of its
/// cell sort, which is not the cell's: the mistake of a term of another sort than its position's
/// (`krs::analysis::invalid-term`), a group's record and an instance's alike.
pub(super) fn foreign_record(
    descriptor: &Descriptor,
    of: RecordOf,
    cell: &str,
    head: &DescriptorTerm,
    key: &ProvenanceKey,
    group: &StableItemId,
) -> Option<DescriptorLoweringError> {
    let named = match head {
        DescriptorTerm::Cell { declaration, .. } if declaration == group => return None,
        DescriptorTerm::Cell { declaration, .. } => format!("`{}`", declaration.item_name()),
        _ => "no `#[k::cell]` struct".to_owned(),
    };
    let reason = match of {
        RecordOf::Group => format!(
            "the record names {named}, and `{cell}` holds `{}`",
            group.item_name()
        ),
        RecordOf::Instance => format!(
            "the instance record names {named}, and `{cell}`'s instances are `{}`",
            group.item_name()
        ),
    };
    Some(collection_error(
        descriptor,
        codes::analysis::INVALID_TERM,
        key,
        reason,
    ))
}

/// A result's `..` over a subject with no unnamed rest of the computation for it to keep (P6):
/// an exact subject has none, and a named one (`rest @ ..`, `named`) that the result does not
/// put back with `..rest` is dropped (D2). The entry table answers it as `rest-mismatch` at the
/// author's entry; this answers it for a sentence the table does not judge, a `cells!` claim.
pub(super) fn kept_rest_mismatch(
    descriptor: &Descriptor,
    key: &ProvenanceKey,
    named: Option<&str>,
) -> DescriptorLoweringError {
    let reason = match named {
        None => "the result keeps the rest of the computation with `..`, and the subject matched no rest: a result's `..` keeps the rest its subject's `..` matched; write `..` in the subject too, or list the computation's whole new content without `..`".to_owned(),
        Some(rest) => format!(
            "the subject names the rest of the computation `..{rest}`, and the result's `..` keeps no named rest, so the rule would drop it: put it back with `..{rest}`, or keep it unnamed with `..` in the subject"
        ),
    };
    collection_error(
        descriptor,
        krs_diagnostic::codes::syntax::INVALID_LIST_NOTATION,
        key,
        reason,
    )
}

/// A result's `..` in a list cell's brackets over a subject that left no unnamed rest of the
/// cell for it to keep (P6): the subject's entry names the whole list, names its rest (`named`),
/// or does not match the cell. The entry table answers it as `rest-mismatch` at the author's
/// entry; this answers it for a sentence the table does not judge.
pub(super) fn kept_list_rest_mismatch(
    descriptor: &Descriptor,
    key: &ProvenanceKey,
    named: Option<&str>,
) -> DescriptorLoweringError {
    let reason = match named {
        None => "the result keeps the rest of the list with `..`, and the subject matched no unnamed rest of it: a result's `..` keeps the rest its subject's `..` matched; write `..` in the subject's brackets too, or name the rest (`rest @ ..`, `..rest`)".to_owned(),
        Some(rest) => format!(
            "the subject names the rest of the list `..{rest}`, and the result's `..` keeps no named rest, so the rule would drop it: put it back with `..{rest}`, or keep it unnamed with `..` in the subject"
        ),
    };
    collection_error(
        descriptor,
        krs_diagnostic::codes::syntax::INVALID_LIST_NOTATION,
        key,
        reason,
    )
}

/// Exact result brackets in a list cell over a subject whose brackets end in `..`: the rest the
/// subject matched is dropped, which the result's brackets say nothing of (P6, D2). The entry
/// table answers it as `rest-mismatch` at the author's entry; this answers it for a sentence the
/// table does not judge.
pub(super) fn dropped_list_rest(
    descriptor: &Descriptor,
    key: &ProvenanceKey,
) -> DescriptorLoweringError {
    collection_error(
        descriptor,
        krs_diagnostic::codes::syntax::INVALID_LIST_NOTATION,
        key,
        "the subject matches the rest of the list with `..`, and the result's brackets are exact, so the sentence would drop that rest: keep it with `..` in the result's brackets too, or name it in the subject (`rest @ ..`) and leave it out of the result".to_owned(),
    )
}

/// Why an optional cell's entry written as a bare value is a mistake.
pub(super) fn bare_optional(name: &str) -> String {
    format!(
        "the optional cell `{name}` takes `Some(..)` when present and `None` when absent, not a bare value: write `Some(k::configuration::Cell(..))` for a leaf, `Some(..)` around a group, or `None`"
    )
}

/// The wrapper an entry writes around a cell of `kind`'s content: a computation's `KCell(..)`,
/// a leaf's `Cell(..)`; none for a group, which is written as a record.
pub(super) fn content_wrapper(kind: &CellKind) -> Option<krs_ir::CellWrapper> {
    match kind.content() {
        Some(Layer::Computation) => Some(krs_ir::CellWrapper::KCell),
        Some(Layer::Leaf(_)) => Some(krs_ir::CellWrapper::Cell),
        Some(Layer::Group(_) | Layer::Optional | Layer::Instances(_)) | None => None,
    }
}

/// The wrapper of a leaf cell of `sort`: the computation cell's `KCell(..)`, a leaf's `Cell(..)`.
pub(super) fn leaf_wrapper(sort: &SemanticSortRef) -> krs_ir::CellWrapper {
    if *sort == SemanticSortRef::k_sequence() {
        krs_ir::CellWrapper::KCell
    } else {
        krs_ir::CellWrapper::Cell
    }
}

/// Checks that an entry's state is one its declared cell's kind has: `Some`/`None` only on an
/// optional cell, an instance list only on a collection. The entry that disagrees with the
/// declaration is the mistake, so the error names `cell`, the entry, whichever side it is on.
pub(super) fn check_state_kind(
    descriptor: &Descriptor,
    kind: &CellKind,
    cell: &DescriptorCellReference,
    state: &DescriptorState,
) -> Result<(), DescriptorLoweringError> {
    let name = &cell.cell.field;
    match (state, kind.multiplicity()) {
        (ProtocolRuleStateTerm::Present { .. } | ProtocolRuleStateTerm::Absent, multiplicity)
            if multiplicity != Multiplicity::Optional =>
        {
            Err(collection_error(
                descriptor,
                codes::analysis::OPTIONAL_PRESENCE,
                &cell.key,
                format!(
                    "`{name}` is not an optional cell: `Some`/`None` entries name a cell declared `#[k::cell(multiplicity = \"?\")]` with an `Option<T>` field"
                ),
            ))
        }
        (ProtocolRuleStateTerm::Instances(_), multiplicity)
            if !matches!(multiplicity, Multiplicity::Many(_)) =>
        {
            Err(collection_error(
                descriptor,
                codes::analysis::COLLECTION_ENTRY,
                &cell.key,
                format!(
                    "`{name}` is not a cell collection: an instance list names a cell declared `#[k::cell(multiplicity = \"*\", cell_type = .., nested)]`; the empty Map or Set a leaf cell holds is `map::empty()` or `set::empty()`, and its empty List is `[]`"
                ),
            ))
        }
        _ => Ok(()),
    }
}

/// Whether a cell entry's state is optional or a collection (KF-023).
pub(super) fn is_cell_state(state: &DescriptorState) -> bool {
    matches!(
        state,
        ProtocolRuleStateTerm::Present { .. }
            | ProtocolRuleStateTerm::Absent
            | ProtocolRuleStateTerm::Instances(_)
    )
}

/// The clause kind and term sort of a declared child or optional cell.
fn cell_kind_sort(field: &DescriptorCellField) -> (CellClauseKind, SemanticSortRef) {
    match &field.content {
        ProtocolCellContent::Leaf { sort, .. } => {
            (CellClauseKind::Content, semantic_sort_ref(&sort.sort))
        }
        ProtocolCellContent::Nested { declaration } => (
            CellClauseKind::Whole,
            SemanticSortRef::Cell(declaration.declaration.clone()),
        ),
    }
}

/// The content frame of a matched state, and its compatibility with the
/// result state: a bound tail is reused, an anonymous tail stays anonymous
/// or is written exactly, an exact state stays exact. A map's bound
/// remainder the result writes exactly, without `..rest`, has been moved: the
/// result is the cell's whole new content, and the remainder is bound on the
/// left only, which the rule must then use
/// (`configuration_rules::moved_remainders_unused_by`).
fn state_frame(
    descriptor: &Descriptor,
    before: &DescriptorState,
    after: Option<&DescriptorState>,
) -> Result<CellContentFrame, DescriptorLoweringError> {
    let (family, frame) = match before {
        ProtocolRuleStateTerm::KSequence(sequence) => ("k", &sequence.tail),
        ProtocolRuleStateTerm::Map(map) => match &map.body {
            krs_ir::ProtocolRuleMapBody::Items { remainder, .. } => ("map", remainder),
            _ => ("map", &ProtocolRuleFrame::Exact),
        },
        _ => ("term", &ProtocolRuleFrame::Exact),
    };
    let result_frame = after.map(|after| match after {
        // `map![k -> v, ..m]` over a map the subject bound whole is the cell's whole content.
        after if writes_over_whole_map(before, after) => &ProtocolRuleFrame::Exact,
        ProtocolRuleStateTerm::KSequence(sequence) => &sequence.tail,
        ProtocolRuleStateTerm::Map(map) => match &map.body {
            krs_ir::ProtocolRuleMapBody::Items { remainder, .. } => remainder,
            _ => &ProtocolRuleFrame::Exact,
        },
        _ => &ProtocolRuleFrame::Exact,
    });
    if let ("map", ProtocolRuleFrame::Bind { key, binding }, Some(ProtocolRuleFrame::Exact)) =
        (family, frame, result_frame)
    {
        return Ok(CellContentFrame::MovedMapRemainder {
            origin: semantic_origin(descriptor, key.clone(), "rule-map-frame")?,
            binding: SemanticId::new(binding.clone())?,
        });
    }
    let compatible = match (frame, result_frame) {
        (_, None)
        | (
            ProtocolRuleFrame::Exact | ProtocolRuleFrame::Anonymous { .. },
            Some(ProtocolRuleFrame::Exact),
        )
        | (ProtocolRuleFrame::Anonymous { .. }, Some(ProtocolRuleFrame::Anonymous { .. })) => true,
        // A result's `..` keeps only the subject's unnamed rest (P6, D2).
        (ProtocolRuleFrame::Exact, Some(ProtocolRuleFrame::Anonymous { key })) if family == "k" => {
            return Err(kept_rest_mismatch(descriptor, key, None));
        }
        (ProtocolRuleFrame::Bind { binding, .. }, Some(ProtocolRuleFrame::Anonymous { key }))
            if family == "k" =>
        {
            return Err(kept_rest_mismatch(descriptor, key, Some(binding)));
        }
        (
            ProtocolRuleFrame::Bind { binding, .. },
            Some(ProtocolRuleFrame::Reuse {
                binding: reused, ..
            }),
        ) => binding == reused,
        _ => false,
    };
    if !compatible {
        return Err(DescriptorLoweringError::unsupported_shape(
            "cell content frame",
            format!(
                "rule {} uses incompatible subject/result associative state frames",
                descriptor.id()
            ),
        ));
    }
    let binding =
        |frame: &ProtocolRuleFrame| -> Result<Option<SemanticId>, DescriptorLoweringError> {
            match frame {
                ProtocolRuleFrame::Bind { binding, .. } => {
                    Ok(Some(SemanticId::new(binding.clone())?))
                }
                _ => Ok(None),
            }
        };
    let key = match frame {
        ProtocolRuleFrame::Exact => return Ok(CellContentFrame::Exact),
        ProtocolRuleFrame::Anonymous { key }
        | ProtocolRuleFrame::Bind { key, .. }
        | ProtocolRuleFrame::Reuse { key, .. } => key,
    };
    if matches!(frame, ProtocolRuleFrame::Reuse { .. }) {
        return Err(DescriptorLoweringError::unsupported_shape(
            "subject cell frame",
            "a subject frame cannot reuse a result binding",
        ));
    }
    Ok(match family {
        "k" => CellContentFrame::KSequenceTail {
            origin: semantic_origin(descriptor, key.clone(), "rule-k-frame")?,
            binding: binding(frame)?,
        },
        _ => CellContentFrame::MapRemainder {
            origin: semantic_origin(descriptor, key.clone(), "rule-map-frame")?,
            binding: binding(frame)?,
        },
    })
}

/// `frame`, or the remainder it leaves bound on the left only when the result was built as the
/// update chain over it ([`MapBase::moved_remainder`]).
fn with_moved_remainder(
    frame: CellContentFrame,
    base: &MapBase<'_>,
) -> Result<CellContentFrame, DescriptorLoweringError> {
    match base.moved_remainder() {
        Some(remainder) => super::configuration_rules::moved_map_frame(&frame, remainder.binding()),
        None => Ok(frame),
    }
}

/// Whether an optional cell's state is `Some(..)` or `None`.
fn is_presence(state: &DescriptorState) -> bool {
    matches!(
        state,
        ProtocolRuleStateTerm::Present { .. } | ProtocolRuleStateTerm::Absent
    )
}

/// The content of a `Some(..)` state; `None` for an absent cell.
fn present_content(state: &DescriptorState) -> Option<&DescriptorState> {
    match state {
        ProtocolRuleStateTerm::Present { value } => Some(value),
        _ => None,
    }
}

/// The group an optional group cell `declared` holds; `None` for any other cell.
fn optional_group<'d>(
    declared: &'d DescriptorCellField,
    declarations: &DescriptorIndex<'_>,
) -> Option<&'d StableItemId> {
    match (
        declared_multiplicity(declared, declarations),
        &declared.content,
    ) {
        (Multiplicity::Optional, ProtocolCellContent::Nested { declaration }) => {
            Some(&declaration.declaration)
        }
        _ => None,
    }
}

/// The pattern of the present group `group` with every child unconstrained, `G { .. }` (the
/// record that names none of them), at the authored node `key`.
fn present_group(group: &StableItemId, key: &ProvenanceKey) -> DescriptorTerm {
    DescriptorTerm::Cell {
        key: key.clone(),
        path_key: key.clone(),
        declaration: group.clone(),
        fields: Vec::new(),
        open: true,
        update: None,
    }
}

/// The pattern `x @ G { .. }` the binder `x` at `key` names in `Some(x)` of the group `group`.
fn present_group_alias(group: &StableItemId, key: &ProvenanceKey, name: &str) -> DescriptorTerm {
    DescriptorTerm::As {
        key: key.clone(),
        binding_key: key.clone(),
        name: name.to_owned(),
        pattern: Box::new(present_group(group, key)),
    }
}

/// The whole binder or `_` a subject's `Some(..)` holds, written bare or as a whole group.
fn present_whole(state: &DescriptorState) -> Option<&DescriptorTerm> {
    match present_content(state)? {
        ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term)
            if matches!(
                term,
                DescriptorTerm::Variable { .. } | DescriptorTerm::Wildcard { .. }
            ) =>
        {
            Some(term)
        }
        _ => None,
    }
}

/// A readable rule with each subject `Some(x)` and `Some(_)` of an optional group written as the
/// pattern it states; `None` where the rule has none.
///
/// `Some(..)` states that the cell is present. A variable of the group's cell sort does not: the
/// sort's values are the present group and its absence, the sort's unit, which is what the
/// cell's place in its parent holds while the cell is absent. The present group is the group's
/// cell with every child unconstrained, `G { .. }`, so `Some(_)` is `Some(G { .. })` and `Some(x)`
/// is `Some(x @ G { .. })`, which binds `x` to the present group's cell term; a result that puts
/// the group back unchanged (`Some(x) => Some(x)`) leaves the cell as it was. The record update
/// long form then takes `x` as it takes any alias over a group record (N7): matched by its
/// children's binders, and each use of `x` the group rebuilt from them. The new nodes stand at
/// the authored binder's or `_`'s key.
///
/// # Errors
///
/// A cell the declarations lack.
pub(super) fn with_stated_present_groups(
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &DescriptorIndex<'_>,
) -> Result<Option<krs_ir::DescriptorHeadRule>, DescriptorLoweringError> {
    let mut stated = rule.clone();
    let mut changed = false;
    for extra in &mut stated.extras {
        let krs_ir::ProtocolHeadRuleExtra::RewriteState {
            cell,
            before,
            after,
            result_key,
        } = extra
        else {
            continue;
        };
        let declared = require_cell_field(&cell.cell, declarations)?;
        let (Some(group), Some(whole)) = (
            optional_group(declared, declarations),
            present_whole(before),
        ) else {
            continue;
        };
        let pattern = match whole {
            DescriptorTerm::Variable { key, name, .. } => {
                // A result that puts the group back unchanged leaves the cell as it was.
                if after.as_ref().and_then(present_whole).is_some_and(
                    |other| matches!(other, DescriptorTerm::Variable { name: other, .. } if other == name),
                ) {
                    *after = None;
                    *result_key = None;
                }
                present_group_alias(group, key, name)
            }
            DescriptorTerm::Wildcard { key } => present_group(group, key),
            _ => continue,
        };
        *before = ProtocolRuleStateTerm::Present {
            value: Box::new(ProtocolRuleStateTerm::Group(pattern)),
        };
        changed = true;
    }
    Ok(changed.then_some(stated))
}

/// A `cells!` rule with each subject `Some(x)` and `Some(_)` of an optional group written as the
/// pattern it states, as [`with_stated_present_groups`] writes a readable rule's, and whether it
/// holds an alias the record update long form rebuilds; `None` where the rule has none.
///
/// `Some(_)` is `Some(G { .. })`, and so is `Some(x)` where nothing else reads `x`, a result that
/// puts the group back unchanged (`Some(x) => Some(x)`) included, which leaves the cell as it
/// was. Where the rule reads `x` elsewhere, `x` is the alias of the present group, `Some(x @ G {
/// .. })`: K's `( <g> .. </g> #as X )` where the result leaves the cell as it was. An alias of a
/// cell does not stand inside that cell's rewrite, so where the result rewrites the group the
/// alias is the one the long form rebuilds, as a readable rule's is: matched by its children's
/// binders, and each use of `x` the group rebuilt from them (N7).
///
/// # Errors
///
/// A cell the declarations lack.
pub(super) fn with_present_groups(
    rule: &krs_ir::DescriptorConfigurationRule,
    declarations: &DescriptorIndex<'_>,
) -> Result<Option<(krs_ir::DescriptorConfigurationRule, bool)>, DescriptorLoweringError> {
    let mut stated = rule.clone();
    let mut changed = false;
    let mut rebuilt = false;
    for index in 0..rule.subject.cells.len() {
        let subject = &rule.subject.cells[index];
        let declared = require_cell_field(&subject.field.cell, declarations)?;
        let (Some(group), Some(whole)) = (
            optional_group(declared, declarations),
            present_whole(&subject.value),
        ) else {
            continue;
        };
        let pattern = match whole {
            DescriptorTerm::Wildcard { key } => present_group(group, key),
            DescriptorTerm::Variable { key, name, .. } => {
                let result = stated.result.as_ref().and_then(|result| {
                    result
                        .cells
                        .iter()
                        .position(|cell| cell.field.cell == subject.field.cell)
                });
                let restated = result.is_some_and(|position| {
                    stated.result.as_ref().is_some_and(|cells| {
                        matches!(
                            present_whole(&cells.cells[position].value),
                            Some(DescriptorTerm::Variable { name: other, .. }) if other == name
                        )
                    })
                });
                if restated && let (Some(position), Some(cells)) = (result, stated.result.as_mut())
                {
                    cells.cells.remove(position);
                }
                if variable_occurrences(&stated, name) <= 1 {
                    // The binder names nothing the rule reads, so it is no binder of the rule.
                    stated.bindings.retain(|binding| binding.name != *name);
                    if let Some(claim) = stated.claim.as_mut() {
                        claim.universals.retain(|binder| binder.name != *name);
                    }
                    present_group(group, key)
                } else {
                    // A group the result rewrites holds no alias of itself: the long form
                    // rebuilds `x` from its children.
                    rebuilt |= result.is_some() && !restated;
                    present_group_alias(group, key, name)
                }
            }
            _ => continue,
        };
        stated.subject.cells[index].value = ProtocolRuleStateTerm::Present {
            value: Box::new(ProtocolRuleStateTerm::Group(pattern)),
        };
        changed = true;
    }
    Ok(changed.then_some((stated, rebuilt)))
}

/// How many times the rule's terms read or bind the variable `name`.
fn variable_occurrences(rule: &krs_ir::DescriptorConfigurationRule, name: &str) -> usize {
    fn walk(value: &serde_json::Value, name: &str) -> usize {
        match value {
            serde_json::Value::Object(object) => {
                let here = object.get("term_kind").and_then(serde_json::Value::as_str)
                    == Some("variable")
                    && object.get("name").and_then(serde_json::Value::as_str) == Some(name);
                usize::from(here)
                    + object
                        .values()
                        .map(|value| walk(value, name))
                        .sum::<usize>()
            }
            serde_json::Value::Array(values) => values.iter().map(|value| walk(value, name)).sum(),
            _ => 0,
        }
    }
    // A rule that does not serialize reads its binder wherever it could.
    serde_json::to_value(rule).map_or(usize::MAX, |value| walk(&value, name))
}

/// A readable rule with each result group record whose `..` leaves children unnamed over a group
/// the subject matches whole given the base that `..` keeps ([`ImplicitBases`]); `None` where the
/// rule has none.
///
/// # Errors
///
/// A cell the declarations lack.
pub(super) fn with_implicit_bases_in_head_rule(
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &DescriptorIndex<'_>,
) -> Result<Option<krs_ir::DescriptorHeadRule>, DescriptorLoweringError> {
    let mut rewritten = rule.clone();
    let mut bases = ImplicitBases::new(declarations, &rewritten);
    for extra in &mut rewritten.extras {
        match extra {
            krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                cell,
                before,
                after: Some(after),
                ..
            } => {
                let declared = require_cell_field(&cell.cell, declarations)?;
                if matches!(declared.content, ProtocolCellContent::Nested { .. }) {
                    bases.place(Some(before), after, false, &declared.rust_field)?;
                }
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteState {
                cell,
                before,
                after: Some(after),
                ..
            } => {
                let declared = require_cell_field(&cell.cell, declarations)?;
                bases.state(declared, Some(before), after)?;
            }
            _ => {}
        }
    }
    // A head rule declares its binders by their refinements: each map rest a group term now
    // holds as a variable is declared the term of the builtin `Map` sort it is, as
    // [`declare_map_rests`] declares a `cells!` rule's.
    for binding in rewritten
        .bindings
        .iter_mut()
        .filter(|binding| bases.held.contains(&binding.name))
    {
        binding.refinement = Some(krs_ir::DescriptorSortReference {
            key: rule.pattern_key.clone(),
            sort: krs_ir::DescriptorSortRef::Builtin(krs_ir::BuiltinSort::Map),
        });
    }
    Ok(bases.changed.then_some(rewritten))
}

/// A `cells!` rule with each result group record whose `..` leaves children unnamed over a group
/// the subject matches whole given the base that `..` keeps, as [`with_implicit_bases_in_head_rule`]
/// gives a readable rule's; `None` where the rule has none.
///
/// # Errors
///
/// A cell the declarations lack.
pub(super) fn with_implicit_bases(
    rule: &krs_ir::DescriptorConfigurationRule,
    declarations: &DescriptorIndex<'_>,
) -> Result<Option<krs_ir::DescriptorConfigurationRule>, DescriptorLoweringError> {
    if rule.result.is_none() {
        return Ok(None);
    }
    let mut rewritten = rule.clone();
    let mut bases = ImplicitBases::new(declarations, &rewritten);
    let krs_ir::DescriptorConfigurationRule {
        subject, result, ..
    } = &mut rewritten;
    for cell in result.iter_mut().flat_map(|result| &mut result.cells) {
        let declared = require_cell_field(&cell.field.cell, declarations)?;
        let matched = subject
            .cells
            .iter_mut()
            .find(|matched| matched.field.cell == cell.field.cell)
            .map(|matched| &mut matched.value);
        bases.state(declared, matched, &mut cell.value)?;
    }
    declare_map_rests(&mut rewritten.bindings, &bases.held, &rule.pattern_key);
    Ok(bases.changed.then_some(rewritten))
}

/// The base a result's group record keeps where its `..` leaves children unnamed (one rule for
/// every place: `..` in a result's record over a cell that is there means its unnamed children
/// are unchanged).
///
/// The record is then `..b`, where `b` is the subject's match of the same place. Where that place
/// is written as its own cells, the subject matching it by a record of its children, by `_`, or
/// not at all, the record's children are written as their own cells and the others are left as
/// they were, which needs no base. Elsewhere the place is written as one term naming every child:
/// beside a subject that matches the group whole, by a binder or an alias; inside a `?` group's
/// `Some(..)`; as an instance record's group child; and below a record so written. There the
/// subject's match is named and the record updates it: a binder `f` is `f @ G { .. }`, an alias
/// is its own name, and a record, `_` or a child an open subject record leaves out is the alias of
/// a name of the sentence's own, which no other binder has. The record update long form then
/// names every child from that base (N7). A place nothing matched, such as a created instance's
/// child, has no base: its `..` is the template's.
struct ImplicitBases<'a, 'b> {
    declarations: &'a DescriptorIndex<'b>,
    /// Every name the sentence holds, its binders' included, and each base name given so far.
    taken: BTreeSet<String>,
    changed: bool,
    /// The named map rests of the subject's group terms written so far, each a variable of its
    /// term, which the sentence declares as a term ([`declare_map_rests`]).
    held: Vec<String>,
}

impl<'a, 'b> ImplicitBases<'a, 'b> {
    fn new(declarations: &'a DescriptorIndex<'b>, rule: &impl serde::Serialize) -> Self {
        fn names(value: &serde_json::Value, taken: &mut BTreeSet<String>) {
            match value {
                serde_json::Value::Object(object) => {
                    for (field, value) in object {
                        if let (true, serde_json::Value::String(name)) = (
                            matches!(field.as_str(), "name" | "label" | "binding"),
                            value,
                        ) {
                            taken.insert(name.clone());
                        }
                        names(value, taken);
                    }
                }
                serde_json::Value::Array(values) => {
                    for value in values {
                        names(value, taken);
                    }
                }
                _ => {}
            }
        }
        let mut taken = BTreeSet::new();
        if let Ok(value) = serde_json::to_value(rule) {
            names(&value, &mut taken);
        }
        Self {
            declarations,
            taken,
            changed: false,
            held: Vec::new(),
        }
    }

    /// The name of the base of the place `hint` names (the path of fields from its cell, its
    /// instance's label or its parent's base, joined by `.`), as the sentence's one allocator of
    /// generated binders names it ([`super::record_updates::hidden_binder_name`]): reserved, so no
    /// authored binder has it, and none of the sentence's other names either.
    fn fresh(&mut self, hint: &str) -> String {
        let (parent, field) = hint.rsplit_once('.').unwrap_or(("", hint));
        let name = super::record_updates::hidden_binder_name(parent, field, |name| {
            self.taken.contains(name)
        });
        self.taken.insert(name.clone());
        name
    }

    /// The bases of the result's state `result` of the cell `declared`, whose subject state is
    /// `subject`: a fixed group's, a present `?` group's content, or the group children of the
    /// result instances a collection's subject instances are.
    fn state(
        &mut self,
        declared: &DescriptorCellField,
        subject: Option<&mut DescriptorState>,
        result: &mut DescriptorState,
    ) -> Result<(), DescriptorLoweringError> {
        let ProtocolCellContent::Nested { declaration } = &declared.content else {
            return Ok(());
        };
        let hint = declared.rust_field.as_str();
        match declared_multiplicity(declared, self.declarations) {
            Multiplicity::One => self.group_state(subject, result, false, hint),
            Multiplicity::Optional => match (subject, result) {
                (
                    Some(ProtocolRuleStateTerm::Present { value: subject }),
                    ProtocolRuleStateTerm::Present { value: result },
                ) => self.group_state(Some(subject), result, true, hint),
                _ => Ok(()),
            },
            Multiplicity::Many(order) => match (subject, result) {
                (
                    Some(ProtocolRuleStateTerm::Instances(subject)),
                    ProtocolRuleStateTerm::Instances(result),
                ) => {
                    let declarations = self.declarations;
                    let children = &declarations.cell(&declaration.declaration)?.fields;
                    let twins = result_subjects(order, children, subject, result);
                    let mut subjects = subject
                        .front
                        .iter_mut()
                        .chain(&mut subject.back)
                        .collect::<Vec<_>>();
                    for (back, items) in [(false, &mut result.front), (true, &mut result.back)] {
                        for (position, instance) in items.iter_mut().enumerate() {
                            let Some(&index) = twins.get(&(back, position)) else {
                                continue;
                            };
                            self.instance(children, &mut *subjects[index], instance)?;
                        }
                    }
                    Ok(())
                }
                _ => Ok(()),
            },
        }
    }

    /// The bases of the group children `result`, a result instance, writes, against those of
    /// `subject`, the subject instance it is: an instance record writes each group child whole.
    fn instance(
        &mut self,
        children: &[DescriptorCellField],
        subject: &mut ProtocolRuleInstance<DescriptorTerm>,
        result: &mut ProtocolRuleInstance<DescriptorTerm>,
    ) -> Result<(), DescriptorLoweringError> {
        let label = subject.label.clone();
        for field in &mut result.fields {
            let Some(child) = children
                .iter()
                .find(|child| child.rust_field == field.field)
            else {
                continue;
            };
            if !matches!(child.content, ProtocolCellContent::Nested { .. })
                || declared_multiplicity(child, self.declarations) != Multiplicity::One
                || !group_state_term(&field.value, false, self.declarations, &mut Vec::new())
                    .is_some_and(|term| self.needs_base(&term))
            {
                continue;
            }
            let hint = label.as_ref().map_or_else(
                || field.field.clone(),
                |label| format!("{label}.{}", field.field),
            );
            // A child the subject instance leaves out, where it is open, is matched by `_`, which
            // its base then names.
            let position = match subject
                .fields
                .iter()
                .position(|matched| matched.field == field.field)
            {
                Some(position) => position,
                None if !matches!(subject.rest, ProtocolInstanceRest::Exact) => {
                    subject.fields.push(krs_ir::ProtocolRuleInstanceField {
                        key: subject.key.clone(),
                        field: field.field.clone(),
                        value: ProtocolRuleStateTerm::Group(DescriptorTerm::Wildcard {
                            key: subject.key.clone(),
                        }),
                    });
                    subject.fields.len() - 1
                }
                None => continue,
            };
            self.group_state(
                Some(&mut subject.fields[position].value),
                &mut field.value,
                true,
                &hint,
            )?;
        }
        Ok(())
    }

    /// The bases of the result's group state `result` of a place whose subject state is
    /// `subject`, written whole there if `whole`: each state as its group term, written back as
    /// that term where a base was given. A record of entries at a place written as its own cells
    /// is one entry per child, each child its own place, whether or not its children are terms.
    fn group_state(
        &mut self,
        subject: Option<&mut DescriptorState>,
        result: &mut DescriptorState,
        whole: bool,
        hint: &str,
    ) -> Result<(), DescriptorLoweringError> {
        let matched_whole = |state: &DescriptorState| {
            matches!(
                state,
                ProtocolRuleStateTerm::Term(
                    DescriptorTerm::Variable { .. } | DescriptorTerm::As { .. }
                ) | ProtocolRuleStateTerm::Group(
                    DescriptorTerm::Variable { .. } | DescriptorTerm::As { .. }
                )
            )
        };
        if !whole
            && !subject.as_deref().is_some_and(matched_whole)
            && let ProtocolRuleStateTerm::Record(record) = result
        {
            let mut matched = match subject {
                Some(ProtocolRuleStateTerm::Record(matched)) => Some(&mut matched.fields),
                _ => None,
            };
            for field in &mut record.fields {
                let child = matched.as_mut().and_then(|fields| {
                    fields
                        .iter_mut()
                        .find(|child| child.field == field.field)
                        .map(|child| &mut child.value)
                });
                let hint = format!("{hint}.{}", field.field);
                self.group_state(child, &mut field.value, false, &hint)?;
            }
            return Ok(());
        }
        let Some(mut result_term) =
            group_state_term(result, false, self.declarations, &mut Vec::new())
        else {
            return Ok(());
        };
        if !self.needs_base(&result_term) {
            return Ok(());
        }
        let declarations = self.declarations;
        let mut held = Vec::new();
        let mut subject_term = subject
            .as_deref()
            .and_then(|state| group_state_term(state, true, declarations, &mut held));
        let unbased = subject_term.clone();
        let changed = std::mem::replace(&mut self.changed, false);
        self.place(subject_term.as_mut(), &mut result_term, whole, hint)?;
        if self.changed {
            *result = ProtocolRuleStateTerm::Group(result_term);
            if subject_term != unbased
                && let (Some(state), Some(term)) = (subject, subject_term)
            {
                *state = ProtocolRuleStateTerm::Group(term);
                self.held.append(&mut held);
            }
        }
        self.changed |= changed;
        Ok(())
    }

    /// Whether `result`, a result's term of a group place, is a group record that leaves children
    /// unnamed with `..` and takes them from no base, or holds such a record as a group child.
    fn needs_base(&self, result: &DescriptorTerm) -> bool {
        let DescriptorTerm::Cell {
            declaration,
            fields,
            open,
            update: None,
            ..
        } = result
        else {
            return false;
        };
        (*open
            && self
                .declarations
                .cell(declaration)
                .is_ok_and(|group| fields.len() < group.fields.len()))
            || fields.iter().any(|field| self.needs_base(&field.value))
    }

    /// Gives `result`, the result's term of a group place, and the group records it holds, the
    /// base their `..` keeps, where `subject` is the subject's term of the same place; `whole`
    /// says that the place is written as one term ([`ImplicitBases`]).
    fn place(
        &mut self,
        subject: Option<&mut DescriptorTerm>,
        result: &mut DescriptorTerm,
        whole: bool,
        hint: &str,
    ) -> Result<(), DescriptorLoweringError> {
        if !self.needs_base(result) {
            return Ok(());
        }
        let DescriptorTerm::Cell {
            key,
            declaration,
            fields,
            open,
            update,
            ..
        } = result
        else {
            return Ok(());
        };
        let group = declaration.clone();
        let whole = whole
            || matches!(
                subject,
                Some(DescriptorTerm::Variable { .. } | DescriptorTerm::As { .. })
            );
        if !whole {
            // Each child is its own cell's entry, against the subject record's same child.
            let mut subject = subject;
            for field in fields.iter_mut() {
                let matched = match subject.as_deref_mut() {
                    Some(DescriptorTerm::Cell {
                        declaration,
                        fields,
                        ..
                    }) if *declaration == group => fields
                        .iter_mut()
                        .find(|matched| matched.field == field.field)
                        .map(|matched| &mut *matched.value),
                    _ => None,
                };
                let hint = format!("{hint}.{}", field.field.as_str());
                self.place(matched, &mut field.value, false, &hint)?;
            }
            return Ok(());
        }
        let Some(subject) = subject else {
            return Ok(());
        };
        let leaves = *open
            && self
                .declarations
                .cell(&group)
                .is_ok_and(|declared| fields.len() < declared.fields.len());
        let named = if leaves {
            let Some(base) = self.base(subject, &group, hint) else {
                return Ok(());
            };
            *update = Some(Box::new(DescriptorTerm::Variable {
                key: key.clone(),
                path_key: key.clone(),
                name: base.clone(),
            }));
            *open = false;
            self.changed = true;
            Some(base)
        } else {
            None
        };
        // The record is written whole, so each group child it writes is too, against the subject
        // record's same child, which an open subject record leaving it out matches by `_`; each
        // child's base is named after the subject's own name where it has one.
        let Some((alias, matched, matched_open, matched_key)) = record_fields(subject, &group)
        else {
            return Ok(());
        };
        let hint = named.or(alias).unwrap_or_else(|| hint.to_owned());
        for field in fields.iter_mut() {
            if !self.needs_base(&field.value) {
                continue;
            }
            let position = match matched.iter().position(|one| one.field == field.field) {
                Some(position) => position,
                None if matched_open => {
                    matched.push(krs_ir::DescriptorCellTermField {
                        key: matched_key.clone(),
                        field: field.field.clone(),
                        value: Box::new(DescriptorTerm::Wildcard {
                            key: matched_key.clone(),
                        }),
                    });
                    matched.len() - 1
                }
                None => continue,
            };
            let hint = format!("{hint}.{}", field.field.as_str());
            self.place(
                Some(&mut matched[position].value),
                &mut field.value,
                true,
                &hint,
            )?;
        }
        Ok(())
    }

    /// Names `subject`, the subject's term of a place of the group `group`, as a base: a binder
    /// is the alias of the group's record that names no child, an alias names its own pattern,
    /// and a record or `_` becomes the alias of a fresh name from `hint`. `None` for a term that
    /// is no match of the group.
    fn base(
        &mut self,
        subject: &mut DescriptorTerm,
        group: &StableItemId,
        hint: &str,
    ) -> Option<String> {
        match subject {
            DescriptorTerm::As { name, pattern, .. } if matches!(&**pattern, DescriptorTerm::Cell { declaration, .. } if declaration == group) => {
                Some(name.clone())
            }
            DescriptorTerm::Variable { key, name, .. } => {
                let name = name.clone();
                *subject = present_group_alias(group, &key.clone(), &name);
                Some(name)
            }
            DescriptorTerm::Wildcard { key } => {
                let name = self.fresh(hint);
                *subject = present_group_alias(group, &key.clone(), &name);
                Some(name)
            }
            DescriptorTerm::Cell {
                key, declaration, ..
            } if declaration == group => {
                let name = self.fresh(hint);
                let key = key.clone();
                let pattern =
                    std::mem::replace(subject, DescriptorTerm::Wildcard { key: key.clone() });
                *subject = DescriptorTerm::As {
                    key: key.clone(),
                    binding_key: key,
                    name: name.clone(),
                    pattern: Box::new(pattern),
                };
                Some(name)
            }
            _ => None,
        }
    }
}

/// The children a subject's record of a group matches, with the record's alias, whether it
/// leaves other children unconstrained, and where it stands.
type MatchedChildren<'t> = (
    Option<String>,
    &'t mut Vec<krs_ir::DescriptorCellTermField>,
    bool,
    ProvenanceKey,
);

/// The children `subject`, the subject's term of a place of `group` written whole, matches
/// ([`MatchedChildren`]); a binder or `_` is made the group's record that names no child (aliased
/// by the binder). `None` for a term that is no match of the group.
fn record_fields<'t>(
    subject: &'t mut DescriptorTerm,
    group: &StableItemId,
) -> Option<MatchedChildren<'t>> {
    if let DescriptorTerm::Variable { key, name, .. } = subject {
        let name = name.clone();
        *subject = present_group_alias(group, &key.clone(), &name);
    } else if let DescriptorTerm::Wildcard { key } = subject {
        *subject = present_group(group, &key.clone());
    }
    let (alias, record) = match subject {
        DescriptorTerm::As { name, pattern, .. } => (Some(name.clone()), &mut **pattern),
        other => (None, other),
    };
    match record {
        DescriptorTerm::Cell {
            key,
            declaration,
            fields,
            open,
            ..
        } if declaration == group => Some((alias, fields, *open, key.clone())),
        _ => None,
    }
}

/// The group term a state of a group place writes, on the subject's side if `subject`: its term,
/// or its record's ([`ProtocolRuleRecord::group_term`]), each child of the builtin `Map` sort
/// written as the map term its entries are ([`map_term`]); `None` for a record a child of which
/// is no term ([`no_term_child`]), and for any other state. `held` gains each named map rest the
/// term holds as a variable ([`map_term`]), which a caller writing the term declares
/// ([`declare_map_rests`]).
pub(super) fn group_state_term(
    state: &DescriptorState,
    subject: bool,
    declarations: &DescriptorIndex<'_>,
    held: &mut Vec<String>,
) -> Option<DescriptorTerm> {
    match state {
        ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
            Some(term.clone())
        }
        ProtocolRuleStateTerm::Record(record) => {
            let mut record = record.clone();
            let children = record_declared_children(&record, declarations);
            for field in &mut record.fields {
                let map_child = children
                    .iter()
                    .find(|child| child.rust_field == field.field)
                    .is_some_and(is_map_leaf);
                if let (true, Some(term)) = (map_child, map_term(&field.value, subject, held)) {
                    field.value = ProtocolRuleStateTerm::Term(term);
                } else if let ProtocolRuleStateTerm::Record(_) = &field.value
                    && let Some(term) = group_state_term(&field.value, subject, declarations, held)
                {
                    field.value = ProtocolRuleStateTerm::Group(term);
                }
            }
            record.group_term()
        }
        _ => None,
    }
}

/// The declared children of the group a record's head names; none for a head that names no
/// group of `declarations`.
fn record_declared_children(
    record: &krs_ir::ProtocolRuleRecord<DescriptorTerm>,
    declarations: &DescriptorIndex<'_>,
) -> Vec<DescriptorCellField> {
    match &record.head {
        DescriptorTerm::Cell { declaration, .. } => declarations
            .cell(declaration)
            .map(|group| group.fields.clone())
            .unwrap_or_default(),
        _ => Vec::new(),
    }
}

/// Whether `child` is a leaf of the builtin `Map` sort, typed or not: the one child whose `map!`
/// entry [`map_term`] reads. A map entry on a child of another sort is the cell's kind's mistake,
/// which the entry's own lowering refuses ("map occurs in a non-Map rule cell").
fn is_map_leaf(child: &DescriptorCellField) -> bool {
    matches!(
        &child.content,
        ProtocolCellContent::Leaf { sort, .. } if semantic_sort_ref(&sort.sort) == SemanticSortRef::map()
    )
}

/// Why a child of a record is no term of the group ([`no_term_child`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NoTerm {
    /// A result's map written over an anonymous `..`, which names no map there.
    UnnamedRest,
    /// A computation written as its items.
    Computation,
    /// A map entry on a child whose sort is not the builtin `Map`.
    NotMapSort,
    /// Any other entry no term spells.
    Other,
}

/// The first child of `record`, a record of a group on the subject's side if `subject`, at any
/// depth, whose entry no term spells, the one [`group_state_term`] fails on, with why.
pub(super) fn no_term_child<'r>(
    record: &'r krs_ir::ProtocolRuleRecord<DescriptorTerm>,
    subject: bool,
    declarations: &DescriptorIndex<'_>,
) -> Option<(&'r str, NoTerm)> {
    let children = record_declared_children(record, declarations);
    record.fields.iter().find_map(|field| {
        let map_child = children
            .iter()
            .find(|child| child.rust_field == field.field)
            .is_some_and(is_map_leaf);
        match &field.value {
            ProtocolRuleStateTerm::Term(_) | ProtocolRuleStateTerm::Group(_) => None,
            ProtocolRuleStateTerm::Record(child) => no_term_child(child, subject, declarations),
            ProtocolRuleStateTerm::Map(_) if !map_child => {
                Some((field.field.as_str(), NoTerm::NotMapSort))
            }
            ProtocolRuleStateTerm::Map(map)
                if !subject
                    && matches!(
                        &map.body,
                        krs_ir::ProtocolRuleMapBody::Items {
                            remainder: ProtocolRuleFrame::Anonymous { .. },
                            ..
                        }
                    ) =>
            {
                Some((field.field.as_str(), NoTerm::UnnamedRest))
            }
            state @ ProtocolRuleStateTerm::Map(_) => map_term(state, subject, &mut Vec::new())
                .is_none()
                .then_some((field.field.as_str(), NoTerm::Other)),
            ProtocolRuleStateTerm::KSequence(_) => {
                Some((field.field.as_str(), NoTerm::Computation))
            }
            _ => Some((field.field.as_str(), NoTerm::Other)),
        }
    })
}

/// The term a map child's entry is, on the subject's side if `subject`, where one is.
///
/// In a pattern the entries are the map pattern they match: `k::map![0 -> v]` is `0 |-> V`
/// exactly, `k::map![0 -> v, ..]` and `k::map![0 -> v, r @ ..]` the same over the rest `_` or `r`,
/// and with no entries the rest itself, `_` or `r`; `k::map![]` is the empty map. A named rest is
/// then a variable of the term, the value of the `Map` sort the rest is, which `held` gains.
///
/// In a result the entries are the built map ([`super::built_maps`]): each entry written over the
/// map before it, starting from the map it is written over, `k::map![0 -> x, ..r]` being
/// `map::update(r, 0, x)` and `k::map![0 -> x]` the same over the empty map; with no entries the
/// map is that base, `k::map![..r]` being `r`.
///
/// `None` for a result's anonymous `..`, which names no map, for a pattern's `..r`, and for any
/// other state.
pub(super) fn map_term(
    state: &DescriptorState,
    subject: bool,
    held: &mut Vec<String>,
) -> Option<DescriptorTerm> {
    let ProtocolRuleStateTerm::Map(map) = state else {
        return None;
    };
    let application = |key: &ProvenanceKey,
                       operation: krs_ir::TermMapOperation,
                       arguments: Vec<DescriptorTerm>| {
        DescriptorTerm::Application {
            head_class: krs_ir::DescriptorApplicationHeadClass::Applied,
            reference: krs_ir::DescriptorApplicationReference {
                key: key.clone(),
                application: krs_ir::DescriptorApplicationRef::Map(operation),
            },
            path_key: key.clone(),
            arguments: krs_ir::Arguments::Positional(arguments.into_iter().map(Box::new).collect()),
            instance: Vec::new(),
            update: None,
            open: false,
        }
    };
    let empty = || {
        application(
            &map.payload_key,
            krs_ir::TermMapOperation::Empty,
            Vec::new(),
        )
    };
    let variable = |key: &ProvenanceKey, name: &str| DescriptorTerm::Variable {
        key: key.clone(),
        path_key: key.clone(),
        name: name.to_owned(),
    };
    let krs_ir::ProtocolRuleMapBody::Items { items, remainder } = &map.body else {
        return matches!(map.body, krs_ir::ProtocolRuleMapBody::Empty { .. }).then(empty);
    };
    let rest = match (remainder, subject) {
        (ProtocolRuleFrame::Exact, _) => None,
        (ProtocolRuleFrame::Anonymous { key }, true) => {
            Some(DescriptorTerm::Wildcard { key: key.clone() })
        }
        (ProtocolRuleFrame::Bind { key, binding }, true) => {
            held.push(binding.clone());
            Some(variable(key, binding))
        }
        (ProtocolRuleFrame::Reuse { key, binding }, false) => Some(variable(key, binding)),
        _ => return None,
    };
    match (items.is_empty(), rest, subject) {
        (true, None, _) => Some(empty()),
        (true, Some(rest), _) => Some(rest),
        (false, rest, false) => Some(items.iter().fold(
            rest.unwrap_or_else(empty),
            |built, item| {
                application(
                    &item.key_key,
                    krs_ir::TermMapOperation::Update,
                    vec![built, item.key.clone(), item.value.clone()],
                )
            },
        )),
        (false, rest, true) => Some(DescriptorTerm::MapEntries {
            key: map.payload_key.clone(),
            entries: items
                .iter()
                .map(|item| krs_ir::DescriptorMapTermEntry {
                    key: Box::new(item.key.clone()),
                    value: Box::new(item.value.clone()),
                })
                .collect(),
            rest: rest.map(Box::new),
        }),
    }
}

/// Declares each of `held`, the named map rests a subject's group term holds as variables
/// ([`map_term`]), as the term of the builtin `Map` sort it is: the rest of a map, which a map
/// cell's entry binds as its frame, is there a variable of the group's term.
pub(super) fn declare_map_rests(
    bindings: &mut [krs_ir::DescriptorRuleBinding],
    held: &[String],
    key: &ProvenanceKey,
) {
    for binding in bindings
        .iter_mut()
        .filter(|binding| held.contains(&binding.name))
    {
        binding.kind = krs_ir::ProtocolRuleBindingKind::Term {
            sort: krs_ir::DescriptorSortReference {
                key: key.clone(),
                sort: krs_ir::DescriptorSortRef::Builtin(krs_ir::BuiltinSort::Map),
            },
        };
    }
}

/// Lowers an optional (`?`) cell's entry (KF-023, R7): read, update, create
/// (`None => Some(..)`), or delete (`Some(..) => None`).
#[expect(
    clippy::too_many_lines,
    reason = "one optional entry: its presences, its terms, and the rests its present content moves"
)]
pub(super) fn lower_optional_clause(
    lowering: &mut impl StateLowering,
    declarations: &DescriptorIndex<'_>,
    cell: &DescriptorCellReference,
    before: &DescriptorState,
    after: Option<&DescriptorState>,
    result_key: Option<&ProvenanceKey>,
) -> Result<ConfigurationClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = lowering.descriptor().clone();
    let declared = require_cell_field(&cell.cell, declarations)?;
    let name = &cell.cell.field;
    let presence_error = |key: &ProvenanceKey, reason: String| {
        collection_error(&descriptor, codes::analysis::OPTIONAL_PRESENCE, key, reason)
    };
    if declared_multiplicity(declared, declarations) != Multiplicity::Optional {
        return Err(presence_error(
            &cell.key,
            format!(
                "`{name}` is not an optional cell: `Some`/`None` entries name a cell declared `#[k::cell(multiplicity = \"?\")]` with an `Option<T>` field"
            ),
        ));
    }
    let (kind, sort) = cell_kind_sort(declared);
    if !is_presence(before) {
        return Err(presence_error(&cell.key, bare_optional(name)));
    }
    let before_inner = present_content(before);
    // `Some(P1 | P2)` of an optional group joins whole cells, as a group
    // entry's `P1 | P2` does.
    if let (
        ProtocolCellContent::Nested { declaration },
        Some(ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term)),
    ) = (&declared.content, before_inner)
    {
        super::cell_alternatives::reject_cell_alternatives(
            &descriptor,
            term,
            name,
            &declaration.declaration,
            declarations.cell(&declaration.declaration)?,
        )?;
    }
    let after_inner = match after {
        None => None,
        Some(after) if is_presence(after) => Some(present_content(after)),
        Some(_) => {
            return Err(presence_error(
                result_key.unwrap_or(&cell.key),
                format!("the optional cell `{name}` is written `Some(..)` or `None`"),
            ));
        }
    };
    if before_inner.is_none() && !matches!(after_inner, Some(Some(_))) {
        return Err(presence_error(
            &cell.key,
            format!(
                "`{name}: None` must be created by the rule: K tests that an optional cell is absent only by creating it (`None => Some(..)`)"
            ),
        ));
    }
    let before_presence = match before_inner {
        Some(state) => Presence::Present {
            term: lowering.lower_state(state, &sort, &cell.key, true)?,
        },
        None => Presence::Absent,
    };
    // A present result's whole `map![..]` is built over what the subject leaves of the map.
    let base = MapBase::of(before_presence.term(), before_inner, after_inner.flatten())?;
    let after_presence = after_inner
        .map(|state| -> Result<_, DescriptorLoweringError> {
            Ok(match state {
                Some(state) => Presence::Present {
                    term: lowering.lower_result(
                        state,
                        &sort,
                        result_key.unwrap_or(&cell.key),
                        &base,
                    )?,
                },
                None => Presence::Absent,
            })
        })
        .transpose()?;
    // A created computation's `..tail` writes that computation after its items, as over an exact
    // subject.
    let after_presence = match (before_inner, after_inner.flatten(), after_presence) {
        (None, Some(result), Some(Presence::Present { term })) => Some(Presence::Present {
            term: super::configuration_rules::created_computation(&descriptor, result, term)?,
        }),
        (_, _, after) => after,
    };
    // A present computation's rests move as a fixed cell's do.
    let moved = match (before_inner, after_inner.flatten()) {
        (Some(subject), Some(result)) => moved_presence(
            &descriptor,
            (subject, result),
            &before_presence,
            after_presence.as_ref(),
        )?,
        _ => None,
    };
    let frame = match before_inner {
        Some(state) if moved.is_none() => with_moved_remainder(
            state_frame(&descriptor, state, after_inner.flatten())?,
            &base,
        )?,
        _ => CellContentFrame::Exact,
    };
    let (before_presence, after_presence) = match moved {
        Some(moved) => {
            if let Some(tail) = moved.moved {
                lowering.moved_computation_remainder(tail);
            }
            (
                Presence::Present { term: moved.before },
                Some(Presence::Present { term: moved.after }),
            )
        }
        None => (before_presence, after_presence),
    };
    // A present cell restated unchanged is read only, unless its remainder moved into the
    // result.
    let after_presence = match (&before_presence, after_presence) {
        (Presence::Present { term: left }, Some(Presence::Present { term: right }))
            if lowering.same(left, &right)
                && !matches!(frame, CellContentFrame::MovedMapRemainder { .. }) =>
        {
            None
        }
        (_, after) => after,
    };
    let (before_presence, after_presence) =
        rewritten_presence(&descriptor, cell, before_presence, after_presence)?;
    Ok(ConfigurationClause::Optional(OptionalCellClause::new(
        semantic_origin(&descriptor, cell.key.clone(), "rule-optional-clause")?,
        semantic_cell_id(&cell.cell)?,
        kind,
        before_presence,
        after_presence,
        frame,
    )))
}

/// The moves of a present `?` computation's rests, its subject and result states `states`
/// lowered to `before` and `after` ([`super::configuration_rules::moved_computation`]), where
/// its result moves one; `None` where it moves none, or the cell is absent on a side.
fn moved_presence(
    descriptor: &Descriptor,
    (subject, result): (&DescriptorState, &DescriptorState),
    before: &Presence<SemanticTerm>,
    after: Option<&Presence<SemanticTerm>>,
) -> Result<Option<super::configuration_rules::MovedComputation>, DescriptorLoweringError> {
    let (Presence::Present { term: before }, Some(Presence::Present { term: after })) =
        (before, after)
    else {
        return Ok(None);
    };
    let moved = super::configuration_rules::moved_computation(
        descriptor,
        subject,
        result,
        before,
        after.clone(),
    )?;
    Ok(moved.exact.then_some(moved))
}

/// An optional cell's states in a single-body rule (KF-011), which has no result: a `k::rewrite!`
/// that is the present content changes it and leaves the cell present, `<opt> O => X </opt>`.
fn rewritten_presence(
    descriptor: &Descriptor,
    cell: &DescriptorCellReference,
    before: Presence<SemanticTerm>,
    after: Option<Presence<SemanticTerm>>,
) -> Result<(Presence<SemanticTerm>, Option<Presence<SemanticTerm>>), DescriptorLoweringError> {
    match (before, after) {
        (Presence::Present { term }, None) if term.contains_rewrite() => {
            let Some((from, to)) = whole_rewrite(&term) else {
                return Err(rewrite_inside(
                    descriptor,
                    codes::analysis::OPTIONAL_PRESENCE,
                    &cell.key,
                    &format!(
                        "the present content of the optional cell `{}`",
                        cell.cell.field
                    ),
                ));
            };
            Ok((
                Presence::Present { term: from },
                Some(Presence::Present { term: to }),
            ))
        }
        presences => Ok(presences),
    }
}

/// The two sides of a `k::rewrite!` (KF-011) that is a cell's whole content, `Cell(k::rewrite!(a
/// => x))`: the change from the content its left side matches to the one its right side writes.
pub(super) fn whole_rewrite(content: &SemanticTerm) -> Option<(SemanticTerm, SemanticTerm)> {
    match content.kind() {
        IrTermKind::Rewrite { from, to } => Some(((**from).clone(), (**to).clone())),
        _ => None,
    }
}

/// A `k::rewrite!` below the root of an optional cell's present content or of a kept instance's
/// child, which only a fixed cell's clause states in place: the cell's whole content rewritten,
/// or a rule with a result, states the same change.
fn rewrite_inside(
    descriptor: &Descriptor,
    code: krs_diagnostic::Code,
    key: &ProvenanceKey,
    place: &str,
) -> DescriptorLoweringError {
    collection_error(
        descriptor,
        code,
        key,
        format!(
            "{place} holds a `k::rewrite!` below its root, and a single-body rule rewrites in place only inside a cell that is neither optional nor in a collection instance, which KRS does not lower yet: rewrite the whole content, `k::rewrite!(.. => ..)`, or write the rule with a result"
        ),
    )
}

/// One collection instance's resolved children: the declaration's fields by
/// Rust name.
struct InstanceDeclaration<'a> {
    id: StableItemId,
    name: String,
    fields: &'a [DescriptorCellField],
}

impl InstanceDeclaration<'_> {
    fn child(&self, name: &str) -> Option<&DescriptorCellField> {
        self.fields.iter().find(|field| field.rust_field == name)
    }
}

/// The subject instance each result instance that updates no label is, by its collection's
/// identity of an instance ([`Order::twins`]): `order` is the collection's, `children` its
/// instance's declared children, whose first is a Map collection's key. Each pair is
/// `(subject index, (back, position))`, the subject's instances counted front then back.
pub(super) fn instance_twins(
    order: Order,
    children: &[DescriptorCellField],
    before: &ProtocolRuleInstances<DescriptorTerm>,
    after: &ProtocolRuleInstances<DescriptorTerm>,
) -> Vec<(usize, (bool, usize))> {
    let child = instance_child;
    // A label is updated by a result instance that keeps it in place; one that moves it to
    // another key leaves it to be kept by another result instance, or removed.
    let moved = moved_instances(order, children, before, after);
    let updated = |label: &str| {
        [(false, &after.front), (true, &after.back)]
            .into_iter()
            .flat_map(|(back, items)| {
                items
                    .iter()
                    .enumerate()
                    .map(move |(position, instance)| ((back, position), instance))
            })
            .any(|(at, instance)| {
                !moved.contains_key(&at)
                    && matches!(&instance.rest, ProtocolInstanceRest::Update { label: base } if base == label)
            })
    };
    let subjects = before.front.iter().chain(&before.back).collect::<Vec<_>>();
    let free = subjects
        .iter()
        .map(|subject| !subject.label.as_deref().is_some_and(updated))
        .collect::<Vec<_>>();
    let reading = |items: &[ProtocolRuleInstance<DescriptorTerm>]| {
        items
            .iter()
            .map(|instance| ResultInstance {
                free: !matches!(instance.rest, ProtocolInstanceRest::Update { .. }),
                open: matches!(instance.rest, ProtocolInstanceRest::Open),
            })
            .collect::<Vec<_>>()
    };
    let (front, back) = (reading(&after.front), reading(&after.back));
    let key = children.first().map(|key| key.rust_field.as_str());
    order.twins(
        &free,
        before.front.len(),
        [&front, &back],
        |index, back, position| {
            let result = if back {
                &after.back[position]
            } else {
                &after.front[position]
            };
            key.is_some_and(|key| {
                child(result, key).is_some_and(|written| {
                    child(subjects[index], key).is_some_and(|matched| keeps_key(written, matched))
                })
            })
        },
    )
}

/// The subject instance of each result instance of an instance list, by its `(back, position)`.
pub(super) type ResultSubjects = BTreeMap<(bool, usize), usize>;

/// The subject instance each result instance is, by its `(back, position)`, as an index into the
/// subject's instances counted front then back: the one its label's update names (`..label`),
/// else the one its collection identifies with it ([`instance_twins`]).
pub(super) fn result_subjects(
    order: Order,
    children: &[krs_ir::DescriptorCellField],
    before: &ProtocolRuleInstances<DescriptorTerm>,
    after: &ProtocolRuleInstances<DescriptorTerm>,
) -> ResultSubjects {
    let subjects = before.front.iter().chain(&before.back).collect::<Vec<_>>();
    let mut twin_of = BTreeMap::new();
    for (back, items) in [(false, &after.front), (true, &after.back)] {
        for (position, instance) in items.iter().enumerate() {
            let ProtocolInstanceRest::Update { label } = &instance.rest else {
                continue;
            };
            if let Some(index) = subjects
                .iter()
                .position(|subject| subject.label.as_ref() == Some(label))
            {
                twin_of.insert((back, position), index);
            }
        }
    }
    for (index, at) in super::cell_states::instance_twins(order, children, before, after) {
        twin_of.insert(at, index);
    }
    twin_of
}

/// The child `name` an instance record writes, as written.
fn instance_child<'i>(
    instance: &'i ProtocolRuleInstance<DescriptorTerm>,
    name: &str,
) -> Option<&'i DescriptorState> {
    instance
        .fields
        .iter()
        .find(|field| field.field == name)
        .map(|field| &field.value)
}

/// The result instances of a Map collection that move a subject instance to another key, each
/// with the index of the subject instance it moves, the subject's instances counted front then
/// back: an update `..label` that writes the key as anything that is not provably the key the
/// labelled instance matched ([`krs_ir::subject::moves_instance`]; a key the labelled instance
/// does not name is not).
/// A Map instance is identified by its key, so such a record is no update of the labelled
/// instance in place: it builds a new instance under the key it writes, whose other children are
/// the labelled instance's (`..label` gives them, as `..` gives a created instance the template's
/// defaults), and the labelled instance itself is removed unless another result instance keeps it.
/// Removal and creation state the step whatever the two keys are, so the key need not be shown
/// to differ.
fn moved_instances(
    order: Order,
    children: &[DescriptorCellField],
    before: &ProtocolRuleInstances<DescriptorTerm>,
    after: &ProtocolRuleInstances<DescriptorTerm>,
) -> BTreeMap<(bool, usize), usize> {
    let Some(key) = children.first().filter(|_| order == Order::Map) else {
        return BTreeMap::new();
    };
    let key = key.rust_field.as_str();
    let subjects = before.front.iter().chain(&before.back).collect::<Vec<_>>();
    let mut moved = BTreeMap::new();
    for (back, items) in [(false, &after.front), (true, &after.back)] {
        for (position, instance) in items.iter().enumerate() {
            let ProtocolInstanceRest::Update { label } = &instance.rest else {
                continue;
            };
            let Some(index) = subjects
                .iter()
                .position(|subject| subject.label.as_ref() == Some(label))
            else {
                continue;
            };
            let written = instance_child(instance, key).map(KeySpelling::of_state);
            let matched = instance_child(subjects[index], key).map(KeySpelling::of_state);
            if krs_ir::subject::moves_instance(written.as_ref(), matched.as_ref()) {
                moved.insert((back, position), index);
            }
        }
    }
    moved
}

/// Whether a result instance's key `written` is provably the key `matched` its subject instance
/// matched, so that the two are one instance: the one definition of a kept key
/// ([`krs_ir::subject::key_kept`]), over a leaf's term or a group key's whole-group term.
fn keeps_key(written: &DescriptorState, matched: &DescriptorState) -> bool {
    krs_ir::subject::key_kept(
        &KeySpelling::of_state(written),
        Some(&KeySpelling::of_state(matched)),
    )
}

/// Lowers a collection (`*`) cell's entry (KF-023, R8).
#[expect(
    clippy::too_many_lines,
    reason = "The instance pairing, its checks, and the emission order are computed in one ordered pass."
)]
pub(super) fn lower_instances_clause(
    lowering: &mut impl StateLowering,
    declarations: &DescriptorIndex<'_>,
    configuration: &DescriptorFixedConfiguration,
    cell: &DescriptorCellReference,
    before: &ProtocolRuleInstances<DescriptorTerm>,
    after: Option<&ProtocolRuleInstances<DescriptorTerm>>,
    result_key: Option<&ProvenanceKey>,
) -> Result<ConfigurationClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = lowering.descriptor().clone();
    let declared = require_cell_field(&cell.cell, declarations)?;
    let name = &cell.cell.field;
    let entry_error = |key: &ProvenanceKey, reason: String| {
        collection_error(&descriptor, codes::analysis::COLLECTION_ENTRY, key, reason)
    };
    // A collection's instances are groups: the kind's instances layer holds a group, and the
    // content names its declaration.
    let kind = declared_kind(declared, declarations);
    let (Multiplicity::Many(order), Some(_), ProtocolCellContent::Nested { declaration }) =
        (kind.multiplicity(), kind.group(), &declared.content)
    else {
        return Err(entry_error(
            &cell.key,
            format!(
                "`{name}` is not a cell collection: an instance list names a cell declared `#[k::cell(multiplicity = \"*\", cell_type = .., nested)]`; the empty Map or Set a leaf cell holds is `map::empty()` or `set::empty()`, and its empty List is `[]`"
            ),
        ));
    };
    let collection = CellCollectionType::from(order);
    let list = collection == CellCollectionType::List;
    for (instances, key) in [
        (Some(before), &cell.key),
        (after, result_key.unwrap_or(&cell.key)),
    ] {
        let Some(instances) = instances else { continue };
        match (list, instances.delimiter) {
            (true, InstanceDelimiter::Brace) => {
                return Err(entry_error(
                    key,
                    format!(
                        "List collections are positional: write `{name}: [ .. ]`, with instances at the front before `..` and at the back after it"
                    ),
                ));
            }
            (false, InstanceDelimiter::Bracket) => {
                return Err(entry_error(
                    key,
                    format!(
                        "Set and Map collections are unordered: write `{name}: {{ .. }}`, which matches some instances"
                    ),
                ));
            }
            _ => {}
        }
    }
    let instance_declaration = InstanceDeclaration {
        id: declaration.declaration.clone(),
        name: declaration.declaration.item_name().to_owned(),
        fields: &declarations.cell(&declaration.declaration)?.fields,
    };
    // Labels name subject instances; a result instance updates one with `..label`.
    let mut labels = BTreeMap::new();
    for (index, instance) in before.front.iter().chain(&before.back).enumerate() {
        if let Some(label) = &instance.label
            && labels.insert(label.clone(), index).is_some()
        {
            return Err(collection_error(
                &descriptor,
                codes::analysis::DUPLICATE_INSTANCE_LABEL,
                &instance.key,
                format!(
                    "the entry of the collection `{name}` labels two subject instances `{label} @`: a label names exactly one instance the subject matches, the one a result instance updates with `..{label}`, so a second instance labelled alike leaves that update with two bases; give each instance its own label"
                ),
            ));
        }
    }
    let subject_open = !matches!(before.rest, ProtocolRuleFrame::Exact);
    if let Some(after) = after {
        let result_open = !matches!(after.rest, ProtocolRuleFrame::Exact);
        // A rest the pattern names, `r @ ..`, binds the other instances, so a result that does
        // not put them back removes them: a meaning, which the Semantic IR's collection clause,
        // whose other instances are framed or none, cannot state yet.
        if let (ProtocolRuleFrame::Bind { binding, .. }, false) = (&before.rest, result_open) {
            return Err(entry_error(
                result_key.unwrap_or(&cell.key),
                format!(
                    "not supported yet: the pattern binds the other instances of the collection `{name}` to `{binding}` (`{binding} @ ..`), and a result that does not put them back with `..{binding}` removes them, which a rule does not state yet"
                ),
            ));
        }
        if subject_open != result_open {
            return Err(entry_error(
                result_key.unwrap_or(&cell.key),
                format!(
                    "the collection `{name}` has `..` on one side only: with `..` in the pattern, write `..` in the result to keep the other instances"
                ),
            ));
        }
    }
    // Pair each result instance with the subject instance it updates.
    let subject_count = before.front.len() + before.back.len();
    let mut kept_by: Vec<Option<(bool, usize)>> = vec![None; subject_count];
    let moved = after.map_or_else(BTreeMap::new, |after| {
        moved_instances(order, instance_declaration.fields, before, after)
    });
    if let Some(after) = after {
        for (back, items) in [(false, &after.front), (true, &after.back)] {
            for (position, instance) in items.iter().enumerate() {
                let ProtocolInstanceRest::Update { label } = &instance.rest else {
                    continue;
                };
                // A move builds a new instance from its label's, which it does not update.
                if moved.contains_key(&(back, position)) {
                    continue;
                }
                // An update whose label no subject instance has has no base (the table's
                // `record-update-base`), whatever form wrote it. A label the rule binds at a
                // sort no instance of the collection has is a binder of the wrong sort before
                // that: a binder's sort is the term's kind, and the base an update needs is the
                // notation's own rule over a term of the instance's kind.
                let Some(&index) = labels.get(label) else {
                    let group = SemanticSortRef::Cell(declaration.declaration.clone());
                    if let Some((bound, false)) = lowering.bound_sort(label, &group) {
                        let bound = super::overload::sort_name(&bound);
                        let group = &instance_declaration.name;
                        return Err(DescriptorLoweringError::IncompatibleBinder {
                            item: Box::new(descriptor.id().clone()),
                            reason: format!(
                                "binder `{label}` is bound at `{bound}`, but the instance update `..{label}` of the collection `{name}` needs an instance of `{group}`"
                            ),
                            range: semantic_origin(
                                &descriptor,
                                instance.key.clone(),
                                "cell-collection-entry",
                            )
                            .ok()
                            .and_then(|origin| {
                                origin.origin().exact_authored_range().map(Box::new)
                            }),
                            occurrence: None,
                            help: Some(format!(
                                "no term is both a `{bound}` and a `{group}` instance"
                            )),
                        });
                    }
                    return Err(collection_error(
                        &descriptor,
                        codes::analysis::INVALID_RECORD_UPDATE,
                        &instance.key,
                        format!(
                            "`..{label}` names no instance of `{name}` labelled `{label} @` in the pattern, so the update has no instance of the collection as its base: an instance update keeps an instance its pattern labels, in place"
                        ),
                    ));
                };
                if kept_by[index].replace((back, position)).is_some() {
                    return Err(collection_error(
                        &descriptor,
                        codes::analysis::DUPLICATE_INSTANCE_LABEL,
                        &instance.key,
                        format!(
                            "two result instances of the collection `{name}` update the subject instance labelled `{label}` (`..{label}`): an update rewrites the one instance its label names in place, so that instance is the base of one update at most, and a second would give it two new contents at once"
                        ),
                    ));
                }
                if (index >= before.front.len()) != back {
                    return Err(entry_error(
                        &instance.key,
                        format!(
                            "`..{label}` moves an instance of the List collection `{name}` between its front and its back; KRS emits List rewrites in place"
                        ),
                    ));
                }
            }
        }
        // A result instance that updates no label is the subject instance its collection
        // identifies it with, if any: that instance updated, whose `..` keeps its children.
        for (index, at) in instance_twins(order, instance_declaration.fields, before, after) {
            kept_by[index] = Some(at);
        }
    }
    // The result instances a subject instance is, each emitted with it.
    let paired = kept_by.iter().flatten().copied().collect::<BTreeSet<_>>();
    let subjects = before.front.iter().chain(&before.back).collect::<Vec<_>>();
    let carried = match after {
        Some(after) => carried_children(
            lowering,
            &descriptor,
            declarations,
            (&instance_declaration, name.as_str()),
            &subjects,
            after,
            &moved,
        )?,
        None => BTreeMap::new(),
    };
    let mut lowered = LoweredInstances {
        lowering,
        descriptor: &descriptor,
        declarations,
        declaration: &instance_declaration,
        configuration,
        collection: cell,
        map: collection == CellCollectionType::Map,
        // A rule's, an equation's and a context's pattern looks a Set
        // collection up by an instance; a claim's states hold terms.
        looked_up: collection == CellCollectionType::Set
            && super::function_patterns::matches_evaluated_sentence(descriptor.payload()),
        carried,
        ordinal: 0,
    };
    let mut segments = Vec::new();
    for (back, subject_items, result_items, offset) in [
        (false, &before.front, after.map(|after| &after.front), 0),
        (
            true,
            &before.back,
            after.map(|after| &after.back),
            before.front.len(),
        ),
    ] {
        let mut segment = Vec::new();
        let mut next_result = 0_usize;
        for (position, subject) in subject_items.iter().enumerate() {
            let index = offset + position;
            match (after, kept_by[index]) {
                // A read-only collection entry keeps every instance it names.
                (None, _) => segment.push(lowered.kept(subject, None)?),
                (Some(_), None) => segment.push(lowered.removed(subject)?),
                (Some(_), Some((_, result_position))) => {
                    let result_items = result_items.expect("a result was given");
                    // A Set's or Map's instances have no order, so only a List's result can
                    // reorder its matched instances.
                    if result_position < next_result && list {
                        return Err(entry_error(
                            &result_items[result_position].key,
                            format!(
                                "the result reorders matched instances of the List collection `{name}`; KRS emits List rewrites in place"
                            ),
                        ));
                    }
                    for (position, created) in result_items
                        .iter()
                        .enumerate()
                        .take(result_position)
                        .skip(next_result)
                    {
                        if !paired.contains(&(back, position)) {
                            let base = moved.get(&(back, position)).map(|&index| subjects[index]);
                            segment.push(lowered.created(created, base)?);
                        }
                    }
                    segment.push(lowered.kept(subject, Some(&result_items[result_position]))?);
                    next_result = next_result.max(result_position + 1);
                }
            }
        }
        if let Some(result_items) = result_items {
            for (position, created) in result_items.iter().enumerate().skip(next_result) {
                if !paired.contains(&(back, position)) {
                    let base = moved.get(&(back, position)).map(|&index| subjects[index]);
                    segment.push(lowered.created(created, base)?);
                }
            }
        }
        segments.push(segment);
    }
    let back = segments.pop().unwrap_or_default();
    let front = segments.pop().unwrap_or_default();
    // An entry that names no instance is about the collection as a whole: `[]` or `{}` is the
    // parent holding no instance, and `[..]` or `{ .. }` matches whatever instances it holds.
    if !subject_open {
        // An exact entry spells out the parent cell; it must hold only the
        // collection.
        let parent = declarations.cell_owner(&cell.cell.owner)?;
        if parent.fields.len() != 1
            || cell.cell.owner == configuration_owner(configuration, declarations)
        {
            return Err(entry_error(
                &cell.key,
                format!(
                    "an entry without `..` names every instance of `{name}`, which KRS writes as its parent cell; that cell must be a `#[k::cell]` struct holding only `{name}`"
                ),
            ));
        }
    }
    if list && !back.is_empty() {
        // Java K closes a List parent on the right, so the back is reached
        // through a leading rest variable; a rule that also names front
        // instances, or keeps a back instance in place, is outside what
        // both backends agree on.
        if !front.is_empty() {
            // The subject names one end; the result that names the other is the entry to split.
            let key = if before.front.is_empty() || before.back.is_empty() {
                result_key.unwrap_or(&cell.key)
            } else {
                &cell.key
            };
            return Err(entry_error(
                key,
                format!(
                    "this entry names instances at both ends of the List collection `{name}`; a KRS rule changes either the front (before `..`) or the back (after it), so split it into two rules"
                ),
            ));
        }
        if back
            .iter()
            .any(|instance| matches!(instance, InstanceClause::Kept { .. }))
        {
            return Err(entry_error(
                &cell.key,
                format!(
                    "a back instance of the List collection `{name}` is matched in place; KRS creates or removes instances at the back, and reads and updates them at the front"
                ),
            ));
        }
        let parent = declarations.cell_owner(&cell.cell.owner)?;
        if parent.fields.len() != 1 {
            return Err(entry_error(
                &cell.key,
                format!(
                    "back instances of `{name}` sit after the other instances, which KRS writes inside its parent cell; that cell must hold only `{name}`"
                ),
            ));
        }
    }
    Ok(ConfigurationClause::Instances(InstancesClause::new(
        semantic_origin(&descriptor, cell.key.clone(), "rule-instances-clause")?,
        semantic_cell_id(&cell.cell)?,
        if list {
            InstanceOrdering::List
        } else {
            InstanceOrdering::Unordered
        },
        front,
        back,
        subject_open,
    )))
}

/// The configuration's own nominal identity.
fn configuration_owner(
    configuration: &DescriptorFixedConfiguration,
    _declarations: &DescriptorIndex<'_>,
) -> StableItemId {
    configuration
        .declaration
        .fields
        .first()
        .map(|field| field.reference.cell.owner.clone())
        .expect("a configuration declares cells")
}

struct LoweredInstances<'a, 'b, L: StateLowering> {
    lowering: &'a mut L,
    descriptor: &'a Descriptor,
    declarations: &'a DescriptorIndex<'b>,
    declaration: &'a InstanceDeclaration<'b>,
    configuration: &'a DescriptorFixedConfiguration,
    collection: &'a DescriptorCellReference,
    map: bool,
    /// Whether the pattern looks the collection up by its instances: a Set
    /// collection's, in a sentence that matches evaluated terms.
    looked_up: bool,
    /// The children a result instance moving each labelled subject instance to another key
    /// takes from it ([`moved_instances`]), by label: the long form binds each in the subject.
    carried: BTreeMap<String, BTreeMap<String, Carried>>,
    /// The next ordinal of a carried child's binder occurrence's origin.
    ordinal: usize,
}

impl<L: StateLowering> LoweredInstances<'_, '_, L> {
    /// One cell of a subject instance.
    fn subject_state(
        &mut self,
        field: &krs_ir::ProtocolRuleInstanceField<DescriptorTerm>,
        sort: &SemanticSortRef,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        if self.looked_up {
            self.lowering
                .lower_looked_up(&field.value, sort, &field.key)
        } else {
            self.lowering
                .lower_state(&field.value, sort, &field.key, true)
        }
    }

    /// A fresh origin at `key` for a node a move's long form adds ([`moved_instances`]).
    fn carried_origin(
        &mut self,
        key: &ProvenanceKey,
    ) -> Result<krs_ir::NodeOrigin, DescriptorLoweringError> {
        let origin = semantic_origin(
            self.descriptor,
            key.clone(),
            &format!("moved-instance-child-{}", self.ordinal),
        )?;
        self.ordinal += 1;
        Ok(origin)
    }

    /// One occurrence, located at `key`, of the binder the long form of a move matches and
    /// writes a carried child with.
    fn carried_occurrence(
        &mut self,
        carried: &Carried,
        key: &ProvenanceKey,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let (id, sort) = carried.binder();
        let origin = self.carried_origin(key)?;
        Ok(SemanticTerm::variable(origin, sort.clone(), id.clone()))
    }

    /// How a move takes `subject`'s child `child`, if one does ([`carried_children`]).
    fn carried(
        &self,
        subject: &ProtocolRuleInstance<DescriptorTerm>,
        child: &str,
    ) -> Option<Carried> {
        self.carried
            .get(subject.label.as_ref()?)?
            .get(child)
            .cloned()
    }

    /// A subject instance's child `field`, lowered in the long form of the moves that take it
    /// ([`carried_children`]): a child a move takes by an added binder is matched by it, `_` by
    /// the binder alone and another pattern `p` by `p #as Binder`.
    fn carried_child(
        &mut self,
        subject: &ProtocolRuleInstance<DescriptorTerm>,
        field: &krs_ir::ProtocolRuleInstanceField<DescriptorTerm>,
        sort: &SemanticSortRef,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let Some(carried @ Carried::Hidden { .. }) = self.carried(subject, &field.field) else {
            return self.subject_state(field, sort);
        };
        if matches!(
            &field.value,
            ProtocolRuleStateTerm::Term(DescriptorTerm::Wildcard { .. })
                | ProtocolRuleStateTerm::Group(DescriptorTerm::Wildcard { .. })
        ) {
            return self.carried_occurrence(&carried, &field.key);
        }
        let before = self.subject_state(field, sort)?;
        let (id, sort) = carried.binder();
        let (id, sort) = (id.clone(), sort.clone());
        let origin = self.carried_origin(&field.key)?;
        Ok(SemanticTerm::pattern_as(origin, sort, id, before))
    }

    /// The children of a subject instance a move takes ([`carried_children`]) and the subject does
    /// not name, each matched by its binder, in declaration order; and whether the subject then
    /// names every child.
    #[expect(
        clippy::type_complexity,
        reason = "The cell, its kind, its binder and its origin of each child."
    )]
    fn carried_unnamed(
        &mut self,
        subject: &ProtocolRuleInstance<DescriptorTerm>,
    ) -> Result<
        (
            Vec<(SemanticId, CellClauseKind, SemanticTerm, krs_ir::NodeOrigin)>,
            bool,
        ),
        DescriptorLoweringError,
    > {
        if subject
            .label
            .as_ref()
            .is_none_or(|label| !self.carried.contains_key(label))
        {
            return Ok((Vec::new(), false));
        }
        let mut unnamed = Vec::new();
        let mut every = true;
        for declared in self.declaration.fields {
            let named = subject
                .fields
                .iter()
                .any(|field| field.field == declared.rust_field);
            if named {
                continue;
            }
            let Some(carried) = self.carried(subject, &declared.rust_field) else {
                every = false;
                continue;
            };
            let (kind, _) = cell_kind_sort(declared);
            let binder = self.carried_occurrence(&carried, &subject.key)?;
            let origin = self.carried_origin(&subject.key)?;
            unnamed.push((
                semantic_cell_id(&declared.reference.cell)?,
                kind,
                binder,
                origin,
            ));
        }
        Ok((unnamed, every))
    }

    /// Refuses an instance record whose head names another struct than the collection's
    /// instance cell: the record says which struct it is of, and a collection holds instances of
    /// one (TRI-D2, [`foreign_record`]).
    fn head(
        &self,
        instance: &ProtocolRuleInstance<DescriptorTerm>,
    ) -> Result<(), DescriptorLoweringError> {
        let Some(head) = &instance.head else {
            return Ok(());
        };
        foreign_record(
            self.descriptor,
            RecordOf::Instance,
            &self.collection.cell.field,
            head,
            &instance.key,
            &self.declaration.id,
        )
        .map_or(Ok(()), Err)
    }

    fn child<'d>(
        &self,
        instance: &ProtocolRuleInstance<DescriptorTerm>,
        field: &'d krs_ir::ProtocolRuleInstanceField<DescriptorTerm>,
    ) -> Result<&'d krs_ir::ProtocolRuleInstanceField<DescriptorTerm>, DescriptorLoweringError>
    {
        let Some(declared) = self.declaration.child(&field.field) else {
            return Err(no_child(
                self.descriptor,
                RecordOf::Instance,
                &self.declaration.name,
                self.declaration.fields,
                &field.field,
                &field.key,
                self.declarations,
            ));
        };
        if declared_multiplicity(declared, self.declarations) != Multiplicity::One {
            return Err(collection_error(
                self.descriptor,
                codes::analysis::COLLECTION_ENTRY,
                &field.key,
                format!(
                    "the child `{}` of `{}` is a `?` or `*` cell: {}",
                    field.field,
                    self.declaration.name,
                    krs_syntax::INSTANCE_CHILD_MULTIPLICITY
                ),
            ));
        }
        let _ = instance;
        Ok(field)
    }

    /// A matched instance that stays: its children are read or rewritten in place.
    #[expect(
        clippy::too_many_lines,
        reason = "Pairing each child with its result, frame, and kind is one ordered pass."
    )]
    fn kept(
        &mut self,
        subject: &ProtocolRuleInstance<DescriptorTerm>,
        result: Option<&ProtocolRuleInstance<DescriptorTerm>>,
    ) -> Result<InstanceClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
        let descriptor = self.descriptor;
        self.head(subject)?;
        if let Some(result) = result {
            self.head(result)?;
        }
        // A child the result writes and the pattern instance does not name is overwritten
        // inside the matched instance (Q1): the pattern matches it by any content, `<c> _ => v
        // </c>`. A Map collection's key the result writes is provably the key matched, since
        // another one moves the instance ([`moved_instances`]), so it is kept as matched.
        let overwritten;
        let subject = match result.map(|result| overwritten_children(subject, result)) {
            Some(Ok(Some(with_children))) => {
                overwritten = with_children;
                &overwritten
            }
            // A rest kept in a child the pattern instance does not name keeps content nothing
            // matched; lowering only the named children would drop the write.
            Some(Err(field)) => {
                return Err(collection_error(
                    descriptor,
                    codes::analysis::COLLECTION_ENTRY,
                    &field.key,
                    format!(
                        "the result keeps a rest of `{}`, which the pattern instance does not name, so no matched content is kept: name `{}` in the pattern instance, or write its whole new content",
                        field.field, field.field
                    ),
                ));
            }
            _ => subject,
        };
        if let Some(result) = result {
            for field in &result.fields {
                self.child(result, field)?;
            }
        }
        let key = self
            .declaration
            .fields
            .first()
            .filter(|_| self.map)
            .map(|key| key.rust_field.clone());
        let mut children = Vec::new();
        for field in &subject.fields {
            self.child(subject, field)?;
            let declaration = self.declaration;
            let declared = declaration
                .child(&field.field)
                .expect("children are checked before lowering");
            let (kind, sort) = cell_kind_sort(declared);
            let result_field = result.and_then(|result| {
                result
                    .fields
                    .iter()
                    .find(|candidate| candidate.field == field.field)
            });
            let before = self.carried_child(subject, field, &sort)?;
            // A kept child's computation rests move as a fixed cell's do.
            let moved = match result_field {
                Some(result_field)
                    if key.as_deref() != Some(field.field.as_str())
                        && super::configuration_rules::moves_computation(
                            &field.value,
                            &result_field.value,
                        ) =>
                {
                    let after = self.lowering.lower_result(
                        &result_field.value,
                        &sort,
                        &result_field.key,
                        &MapBase::of(Some(&before), Some(&field.value), Some(&result_field.value))?,
                    )?;
                    Some(super::configuration_rules::moved_computation(
                        descriptor,
                        &field.value,
                        &result_field.value,
                        &before,
                        after,
                    )?)
                    .filter(|moved| moved.exact)
                }
                _ => None,
            };
            let mut frame = if moved.is_some() {
                CellContentFrame::Exact
            } else {
                state_frame(
                    descriptor,
                    &field.value,
                    result_field.map(|field| &field.value),
                )?
            };
            let (before, after) = match result_field {
                Some(_) if let Some(moved) = moved => {
                    if let Some(tail) = moved.moved {
                        self.lowering.moved_computation_remainder(tail);
                    }
                    (moved.before, CellPost::Replace { term: moved.after })
                }
                // A single-body rule (KF-011) has no result: a `k::rewrite!` that is the child's
                // whole content changes it, `<val> V => X </val>`, and a key is kept only by a
                // rewrite whose sides are the same, as by a result.
                None if before.contains_rewrite() => {
                    let Some((from, to)) = whole_rewrite(&before) else {
                        return Err(rewrite_inside(
                            descriptor,
                            codes::analysis::COLLECTION_ENTRY,
                            &field.key,
                            &format!(
                                "the child `{}` of an instance of the collection `{}`",
                                field.field, self.collection.cell.field
                            ),
                        ));
                    };
                    let key = self
                        .declaration
                        .fields
                        .first()
                        .is_some_and(|key| key.rust_field == field.field);
                    if self.map && key {
                        if !self.lowering.same(&from, &to) {
                            return Err(collection_error(
                                descriptor,
                                codes::analysis::MAP_COLLECTION_KEY,
                                &field.key,
                                krs_ir::subject::key_update_reason(
                                    &self.collection.cell.field,
                                    &field.field,
                                ),
                            ));
                        }
                        // The key kept is the key read.
                        (from, CellPost::Preserve)
                    } else {
                        (from, CellPost::Replace { term: to })
                    }
                }
                None => (before, CellPost::Preserve),
                // The key a kept instance's result writes is the key matched (`moved_instances`).
                Some(_) if key.as_deref() == Some(field.field.as_str()) => {
                    (before, CellPost::Preserve)
                }
                Some(result_field) => {
                    // A child's whole `map![..]` is built over what the subject leaves of it.
                    let base =
                        MapBase::of(Some(&before), Some(&field.value), Some(&result_field.value))?;
                    let after = self.lowering.lower_result(
                        &result_field.value,
                        &sort,
                        &result_field.key,
                        &base,
                    )?;
                    frame = with_moved_remainder(frame, &base)?;
                    // A moved remainder leaves the child, so the result is its whole content.
                    if self.lowering.same(&before, &after)
                        && !matches!(frame, CellContentFrame::MovedMapRemainder { .. })
                    {
                        (before, CellPost::Preserve)
                    } else {
                        (before, CellPost::Replace { term: after })
                    }
                }
            };
            let origin = semantic_origin(descriptor, field.key.clone(), "rule-instance-child")?;
            let clause = FixedCellClause::new(
                origin,
                semantic_cell_id(&declared.reference.cell)?,
                before,
                after,
                frame,
            );
            children.push(if kind == CellClauseKind::Whole {
                if !matches!(clause.frame(), CellContentFrame::Exact) {
                    return Err(DescriptorLoweringError::unsupported_shape(
                        "collection instance",
                        "a whole nested child has no frame",
                    ));
                }
                clause.with_kind(CellClauseKind::Whole)
            } else {
                clause
            });
        }
        let (unnamed, every) = self.carried_unnamed(subject)?;
        for (cell, kind, binder, origin) in unnamed {
            let clause = FixedCellClause::new(
                origin,
                cell,
                binder,
                CellPost::Preserve,
                CellContentFrame::Exact,
            );
            children.push(if kind == CellClauseKind::Whole {
                clause.with_kind(CellClauseKind::Whole)
            } else {
                clause
            });
        }
        Ok(InstanceClause::Kept {
            origin: semantic_origin(descriptor, subject.key.clone(), "rule-instance")?,
            label: subject.label.clone(),
            children,
            open: matches!(subject.rest, ProtocolInstanceRest::Open) && !every,
        })
    }

    fn children(
        &mut self,
        instance: &ProtocolRuleInstance<DescriptorTerm>,
        subject: bool,
    ) -> Result<Vec<InstanceChild<SemanticId, SemanticTerm>>, DescriptorLoweringError> {
        let descriptor = self.descriptor;
        let mut children = Vec::new();
        for field in &instance.fields {
            self.child(instance, field)?;
            let declaration = self.declaration;
            let declared = declaration
                .child(&field.field)
                .expect("children are checked before lowering");
            let (kind, sort) = cell_kind_sort(declared);
            // A new instance's whole `map![..]` is built over the empty map.
            let term = if subject {
                self.carried_child(instance, field, &sort)?
            } else {
                let term = self.lowering.lower_result(
                    &field.value,
                    &sort,
                    &field.key,
                    &MapBase::Unmatched,
                )?;
                // A created child's `..tail` writes that computation after its items.
                super::configuration_rules::created_computation(descriptor, &field.value, term)?
            };
            let frame = if subject {
                state_frame(descriptor, &field.value, None)?
            } else {
                if !written_exactly(&field.value) {
                    return Err(collection_error(
                        descriptor,
                        codes::analysis::COLLECTION_ENTRY,
                        &field.key,
                        format!(
                            "a new instance's `{}` is written exactly: it has no matched content to keep",
                            field.field
                        ),
                    ));
                }
                CellContentFrame::Exact
            };
            children.push(InstanceChild::new(
                semantic_origin(descriptor, field.key.clone(), "rule-instance-child")?,
                semantic_cell_id(&declared.reference.cell)?,
                kind,
                term,
                frame,
            ));
        }
        Ok(children)
    }

    /// A matched instance the rule removes.
    fn removed(
        &mut self,
        subject: &ProtocolRuleInstance<DescriptorTerm>,
    ) -> Result<InstanceClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
        self.head(subject)?;
        let mut children = self.children(subject, true)?;
        let (unnamed, every) = self.carried_unnamed(subject)?;
        children.extend(unnamed.into_iter().map(|(cell, kind, binder, origin)| {
            InstanceChild::new(origin, cell, kind, binder, CellContentFrame::Exact)
        }));
        Ok(InstanceClause::Removed {
            origin: semantic_origin(self.descriptor, subject.key.clone(), "rule-instance")?,
            label: subject.label.clone(),
            children,
            open: matches!(subject.rest, ProtocolInstanceRest::Open) && !every,
        })
    }

    /// A new instance: its children, and `..` defaults for the others; or, where `base` is the
    /// subject instance the record moves to another key ([`moved_instances`]), the base's for the
    /// others.
    fn created(
        &mut self,
        result: &ProtocolRuleInstance<DescriptorTerm>,
        base: Option<&ProtocolRuleInstance<DescriptorTerm>>,
    ) -> Result<InstanceClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
        let descriptor = self.descriptor;
        self.head(result)?;
        if let Some(base) = base {
            return self.moved(result, base);
        }
        let named = result
            .fields
            .iter()
            .map(|field| field.field.as_str())
            .collect::<BTreeSet<_>>();
        let defaults = matches!(result.rest, ProtocolInstanceRest::Open);
        let missing = self
            .declaration
            .fields
            .iter()
            .filter(|field| !named.contains(field.rust_field.as_str()))
            .collect::<Vec<_>>();
        if self.map
            && let Some(key) = self.declaration.fields.first()
            && !named.contains(key.rust_field.as_str())
        {
            return Err(collection_error(
                descriptor,
                codes::analysis::MAP_COLLECTION_KEY,
                &result.key,
                format!(
                    "a new instance of the Map collection `{}` states its key: write `{}: ..`, its first child",
                    self.collection.cell.field, key.rust_field
                ),
            ));
        }
        if !defaults && let Some(field) = missing.first() {
            return Err(collection_error(
                descriptor,
                codes::analysis::COLLECTION_ENTRY,
                &result.key,
                format!(
                    "a new instance of `{}` names every child or ends in `..` (template defaults); `{}` is missing",
                    self.collection.cell.field, field.rust_field
                ),
            ));
        }
        if defaults {
            let templates = instance_templates(self.configuration, &self.collection.cell);
            for field in missing {
                let Some(template) = templates.get(&field.reference.cell) else {
                    continue;
                };
                if reads_variable(template) {
                    return Err(collection_error(
                        descriptor,
                        codes::analysis::NO_CELL_DEFAULT,
                        &result.key,
                        format!(
                            "`..` cannot default `{}` of a new `{}`: its template reads a configuration variable, so K has no default for it; write `{}: ..`",
                            field.rust_field, self.declaration.name, field.rust_field
                        ),
                    ));
                }
                // The template says the optional cell is there, and a created instance's `..`
                // leaves its optional cells out; an instance record cannot name one to say
                // otherwise, so the default the template states is not what the rule writes.
                if let Some(optional) = present_optional_cell(template, self.declarations)? {
                    return Err(collection_error(
                        descriptor,
                        codes::analysis::NO_CELL_DEFAULT,
                        &result.key,
                        format!(
                            "`..` cannot default `{}` of a new `{}`: its template starts the optional cell `{optional}` present, which `..` does not write and an instance record cannot name yet; start it absent in the template with `k::absent!(..)`",
                            field.rust_field, self.declaration.name
                        ),
                    ));
                }
            }
        }
        Ok(InstanceClause::Created {
            origin: semantic_origin(descriptor, result.key.clone(), "rule-instance")?,
            children: self.children(result, false)?,
            defaults,
        })
    }
}

impl<L: StateLowering> LoweredInstances<'_, '_, L> {
    /// The instance a result record `..label` builds under a key not provably the one the
    /// instance `base`, labelled `label`, matched ([`moved_instances`]): the children the record
    /// writes, and for the others the binders `base`'s pattern matches them by
    /// ([`carried_children`]), the long form of `..label`, as a record update's.
    fn moved(
        &mut self,
        result: &ProtocolRuleInstance<DescriptorTerm>,
        base: &ProtocolRuleInstance<DescriptorTerm>,
    ) -> Result<InstanceClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
        let descriptor = self.descriptor;
        let mut children = self.children(result, false)?;
        for declared in self.declaration.fields {
            if result
                .fields
                .iter()
                .any(|field| field.field == declared.rust_field)
            {
                continue;
            }
            let carried = self
                .carried(base, &declared.rust_field)
                .expect("a move carries every child its record does not write");
            let (kind, _) = cell_kind_sort(declared);
            let term = self.carried_occurrence(&carried, &result.key)?;
            children.push(InstanceChild::new(
                self.carried_origin(&result.key)?,
                semantic_cell_id(&declared.reference.cell)?,
                kind,
                term,
                CellContentFrame::Exact,
            ));
        }
        Ok(InstanceClause::Created {
            origin: semantic_origin(descriptor, result.key.clone(), "rule-instance")?,
            children,
            defaults: false,
        })
    }
}

/// How the long form of a move ([`moved_instances`]) takes one child of the labelled instance.
#[derive(Clone, Debug)]
enum Carried {
    /// The child the subject matches with the binder or alias `id`, which holds it whole and
    /// which the creation writes.
    Binder {
        id: SemanticId,
        sort: SemanticSortRef,
    },
    /// A binder the long form adds, which matches the child in the subject (alone where the
    /// subject leaves the child out or writes `_`, `p #as` it where it writes another pattern
    /// `p`) and writes it in the creation.
    Hidden {
        id: SemanticId,
        sort: SemanticSortRef,
    },
}

impl Carried {
    fn binder(&self) -> (&SemanticId, &SemanticSortRef) {
        match self {
            Self::Binder { id, sort } | Self::Hidden { id, sort } => (id, sort),
        }
    }
}

/// The children each moved subject instance gives the instances its moves create
/// ([`moved_instances`]), by label, then child: every child some move of the label does not
/// write, with the binder that holds it, computed once so that the subject's pattern and every
/// creation read one binder. A binder the long form adds is allocated for the sentence
/// ([`StateLowering::hidden_binder`]), so no two children, and no other binder, share a name.
/// A move is refused where its long form has no binder for a child yet: a `?` or `*` child, which
/// no instance record names, a child the record writes with a rest (no exact content), and a
/// child the pattern matches with a K sequence, a map or a group record (a pattern with no term
/// that `#as` can hold). A child matched by a name or an alias is carried by that name, by `_` or
/// not at all by an added binder, and by any other term pattern `p` by `p #as Binder`.
fn carried_children(
    lowering: &mut impl StateLowering,
    descriptor: &Descriptor,
    declarations: &DescriptorIndex<'_>,
    (declaration, holder): (&InstanceDeclaration<'_>, &str),
    subjects: &[&ProtocolRuleInstance<DescriptorTerm>],
    after: &ProtocolRuleInstances<DescriptorTerm>,
    moved: &BTreeMap<(bool, usize), usize>,
) -> Result<BTreeMap<String, BTreeMap<String, Carried>>, DescriptorLoweringError> {
    let mut carried = BTreeMap::<String, BTreeMap<String, Carried>>::new();
    for (&(back, position), &index) in moved {
        let result = if back {
            &after.back[position]
        } else {
            &after.front[position]
        };
        let subject = subjects[index];
        let label = subject
            .label
            .clone()
            .expect("a moved instance updates a label");
        let moving = format!(
            "the result instance writes a key not provably the key the instance `{label}` of the Map collection `{holder}` matched, so it moves `{label}` there, a new instance"
        );
        for field in &result.fields {
            if !written_exactly(&field.value) {
                return Err(collection_error(
                    descriptor,
                    codes::analysis::COLLECTION_ENTRY,
                    &field.key,
                    format!(
                        "not supported yet: {moving}, and its `{}` is not written whole: a K sequence with a rest after its items or a map whose remainder is `..` or a name, which a new instance does not write yet; write the child's whole content",
                        field.field
                    ),
                ));
            }
        }
        for declared in declaration.fields {
            let child = &declared.rust_field;
            if instance_child(result, child).is_some()
                || carried
                    .get(&label)
                    .is_some_and(|taken| taken.contains_key(child))
            {
                continue;
            }
            if declared_multiplicity(declared, declarations) != Multiplicity::One {
                return Err(collection_error(
                    descriptor,
                    codes::analysis::COLLECTION_ENTRY,
                    &result.key,
                    format!(
                        "not supported yet: {moving} that takes `{label}`'s other children, and its child `{child}` is a `?` or `*` cell, which a new instance does not take from another yet"
                    ),
                ));
            }
            let (_, sort) = cell_kind_sort(declared);
            let matched = subject.fields.iter().find(|field| field.field == *child);
            let taken = carry_child(
                lowering,
                descriptor,
                (&label, child),
                &sort,
                matched,
                &moving,
            )?;
            carried
                .entry(label.clone())
                .or_default()
                .insert(child.clone(), taken);
        }
    }
    Ok(carried)
}

/// How a move takes one child, `child` of the instance labelled `label`, which the instance's
/// pattern writes as `matched` (`None`: it does not name it), at `sort` ([`carried_children`]).
fn carry_child(
    lowering: &mut impl StateLowering,
    descriptor: &Descriptor,
    (label, child): (&str, &str),
    sort: &SemanticSortRef,
    matched: Option<&krs_ir::ProtocolRuleInstanceField<DescriptorTerm>>,
    moving: &str,
) -> Result<Carried, DescriptorLoweringError> {
    let sort = sort.clone();
    Ok(match matched.map(|field| (field, &field.value)) {
        // A binder, or an alias's name, holds the child whole: the creation writes it.
        Some((
            _,
            ProtocolRuleStateTerm::Term(
                DescriptorTerm::Variable { name, .. } | DescriptorTerm::As { name, .. },
            )
            | ProtocolRuleStateTerm::Group(
                DescriptorTerm::Variable { name, .. } | DescriptorTerm::As { name, .. },
            ),
        )) => {
            let Some((bound, _)) = lowering.bound_sort(name, &sort) else {
                return Err(DescriptorLoweringError::unsupported_shape(
                    "moved collection instance",
                    "a carried child's binder has no sort the result binds it at",
                ));
            };
            Carried::Binder {
                id: SemanticId::new(name.clone())?,
                sort: bound,
            }
        }
        None
        | Some((
            _,
            ProtocolRuleStateTerm::Term(DescriptorTerm::Wildcard { .. })
            | ProtocolRuleStateTerm::Group(DescriptorTerm::Wildcard { .. }),
        )) => Carried::Hidden {
            id: lowering.hidden_binder(label, child, &sort)?,
            sort,
        },
        // Another pattern `p` of a leaf or a group child is held by an added binder,
        // `p #as Binder`, so it still constrains the instance it matches.
        Some((_, ProtocolRuleStateTerm::Term(_) | ProtocolRuleStateTerm::Group(_))) => {
            Carried::Hidden {
                id: lowering.hidden_binder(label, child, &sort)?,
                sort,
            }
        }
        Some((field, _)) => {
            return Err(collection_error(
                descriptor,
                codes::analysis::COLLECTION_ENTRY,
                &field.key,
                format!(
                    "not supported yet: {moving} that takes its child `{child}`, which the pattern matches with a K sequence, a map or a group record, a pattern no binder holds whole yet; write `{child}` in the result, or match it with a name, `_`, or an alias `name @ ..`"
                ),
            ));
        }
    })
}

/// Whether a new instance's child `value` is written exactly, with no rest of matched content
/// to keep.
fn written_exactly(value: &DescriptorState) -> bool {
    match value {
        // A `..tail` writes the computation `tail` after the items, which a new instance's
        // child holds as written.
        ProtocolRuleStateTerm::KSequence(sequence) => matches!(
            sequence.tail,
            ProtocolRuleFrame::Exact | ProtocolRuleFrame::Reuse { .. }
        ),
        ProtocolRuleStateTerm::Map(map) => !matches!(
            &map.body,
            krs_ir::ProtocolRuleMapBody::Items {
                remainder: ProtocolRuleFrame::Anonymous { .. } | ProtocolRuleFrame::Reuse { .. },
                ..
            }
        ),
        _ => true,
    }
}

/// The initializer templates of a collection's instance children, by cell.
fn instance_templates<'a>(
    configuration: &'a DescriptorFixedConfiguration,
    collection: &krs_ir::DescriptorCellIdentity,
) -> BTreeMap<krs_ir::DescriptorCellIdentity, &'a DescriptorInitializerCell> {
    fn find<'a>(
        cells: &'a [DescriptorInitializerCell],
        collection: &krs_ir::DescriptorCellIdentity,
    ) -> Option<&'a [DescriptorInitializerCell]> {
        for cell in cells {
            if let ProtocolInitializerCellContent::Nested { children, .. } = &cell.content {
                if &cell.field.cell == collection {
                    return Some(children);
                }
                if let Some(found) = find(children, collection) {
                    return Some(found);
                }
            }
        }
        None
    }
    find(&configuration.initializer.cells, collection)
        .unwrap_or_default()
        .iter()
        .map(|child| (child.field.cell.clone(), child))
        .collect()
}

/// The first optional cell an instance child's template starts present: the child itself
/// when it is optional, else a cell inside it. An absent optional cell's template and a
/// collection's instance template say what a created cell holds, not what the instance holds,
/// so the search stops at them.
fn present_optional_cell<'t>(
    template: &'t DescriptorInitializerCell,
    declarations: &DescriptorIndex<'_>,
) -> Result<Option<&'t str>, DescriptorLoweringError> {
    let declared = require_cell_field(&template.field.cell, declarations)?;
    match declared_multiplicity(declared, declarations) {
        Multiplicity::Optional => {
            return Ok(template
                .absent
                .is_none()
                .then_some(template.field.cell.field.as_str()));
        }
        Multiplicity::Many(_) => return Ok(None),
        Multiplicity::One => {}
    }
    if let ProtocolInitializerCellContent::Nested { children, .. } = &template.content {
        for child in children {
            if let Some(optional) = present_optional_cell(child, declarations)? {
                return Ok(Some(optional));
            }
        }
    }
    Ok(None)
}

/// Whether an initializer template reads a configuration variable.
fn reads_variable(cell: &DescriptorInitializerCell) -> bool {
    fn walk(value: &serde_json::Value) -> bool {
        match value {
            serde_json::Value::Object(object) => {
                object.get("term_kind").and_then(serde_json::Value::as_str) == Some("variable")
                    || object.values().any(walk)
            }
            serde_json::Value::Array(values) => values.iter().any(walk),
            _ => false,
        }
    }
    serde_json::to_value(&cell.content).is_ok_and(|value| walk(&value))
}

/// `subject` with each child `result` writes and `subject` does not name matched whole by `_`:
/// a leaf, a group, or a computation the result writes exactly; `None` where `result` writes no
/// such child. The child is the error where it is written otherwise: a rest kept from content the
/// pattern never matched.
fn overwritten_children<'r>(
    subject: &ProtocolRuleInstance<DescriptorTerm>,
    result: &'r ProtocolRuleInstance<DescriptorTerm>,
) -> Result<
    Option<ProtocolRuleInstance<DescriptorTerm>>,
    &'r krs_ir::ProtocolRuleInstanceField<DescriptorTerm>,
> {
    let mut with_children = subject.clone();
    for field in &result.fields {
        if subject
            .fields
            .iter()
            .any(|candidate| candidate.field == field.field)
        {
            continue;
        }
        let any = DescriptorTerm::Wildcard {
            key: field.key.clone(),
        };
        // The whole content is matched by `_`, so the result's content replaces all of it (P5,
        // P6): a computation matched by an anonymous tail would keep its rest framed.
        let value = match &field.value {
            ProtocolRuleStateTerm::KSequence(krs_ir::ProtocolRuleKSequence {
                tail: ProtocolRuleFrame::Exact,
                ..
            })
            | ProtocolRuleStateTerm::Term(_)
            | ProtocolRuleStateTerm::Map(_) => ProtocolRuleStateTerm::Term(any),
            ProtocolRuleStateTerm::Group(_) => ProtocolRuleStateTerm::Group(any),
            // A `?` or `*` child is refused where the instance's children are checked.
            ProtocolRuleStateTerm::KSequence(_) => return Err(field),
            _ => return Ok(None),
        };
        with_children
            .fields
            .push(krs_ir::ProtocolRuleInstanceField {
                key: field.key.clone(),
                field: field.field.clone(),
                value,
            });
    }
    Ok((with_children.fields.len() > subject.fields.len()).then_some(with_children))
}
