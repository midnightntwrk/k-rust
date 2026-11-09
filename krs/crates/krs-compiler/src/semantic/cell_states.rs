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
use krs_ir_levels::{SemanticSortRef, SemanticTerm};

use super::built_maps::{MapBase, writes_over_whole_map};
use super::catalog::semantic_sort_ref;
use super::error::DescriptorLoweringError;
use super::origin::{semantic_cell_id, semantic_origin};
use super::references::{declared_kind, declared_multiplicity, require_cell_field};
use krs_ir::cell_kind::{CellKind, Layer, Multiplicity};

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

    /// The sort the rule binds `name` at, where it binds it, and whether every term of `sort`
    /// is a term of it.
    fn bound_sort(&self, name: &str, sort: &SemanticSortRef) -> Option<(SemanticSortRef, bool)>;
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
/// cell for it to keep (P6): the subject's entry names the whole list, names its rest, or does
/// not match the cell. The entry table answers it as `rest-mismatch` at the author's entry; this
/// answers it for a sentence the table does not judge.
pub(super) fn kept_list_rest_mismatch(
    descriptor: &Descriptor,
    key: &ProvenanceKey,
) -> DescriptorLoweringError {
    collection_error(
        descriptor,
        krs_diagnostic::codes::syntax::INVALID_LIST_NOTATION,
        key,
        "the result keeps the rest of the list with `..`, and the subject matched no unnamed rest of it: a result's `..` keeps the rest its subject's `..` matched; write `..` in the subject's brackets too, or name the rest (`rest @ ..`, `..rest`)".to_owned(),
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

/// Lowers an optional (`?`) cell's entry (KF-023, R7): read, update, create
/// (`None => Some(..)`), or delete (`Some(..) => None`).
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
    let frame = match before_inner {
        Some(state) => with_moved_remainder(
            state_frame(&descriptor, state, after_inner.flatten())?,
            &base,
        )?,
        None => CellContentFrame::Exact,
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
    Ok(ConfigurationClause::Optional(OptionalCellClause::new(
        semantic_origin(&descriptor, cell.key.clone(), "rule-optional-clause")?,
        semantic_cell_id(&cell.cell)?,
        kind,
        before_presence,
        after_presence,
        frame,
    )))
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
    if let Some(after) = after {
        for (back, items) in [(false, &after.front), (true, &after.back)] {
            for (position, instance) in items.iter().enumerate() {
                let ProtocolInstanceRest::Update { label } = &instance.rest else {
                    continue;
                };
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
    }
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
                    if result_position < next_result {
                        return Err(entry_error(
                            &result_items[result_position].key,
                            format!(
                                "the result reorders matched instances of the List collection `{name}`; KRS emits List rewrites in place"
                            ),
                        ));
                    }
                    for created in &result_items[next_result..result_position] {
                        segment.push(lowered.created(created)?);
                    }
                    segment.push(lowered.kept(subject, Some(&result_items[result_position]))?);
                    next_result = result_position + 1;
                }
            }
            let _ = back;
        }
        if let Some(result_items) = result_items {
            for created in &result_items[next_result..] {
                if matches!(created.rest, ProtocolInstanceRest::Update { .. }) {
                    continue;
                }
                segment.push(lowered.created(created)?);
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

    /// Refuses an instance record whose head names another struct than the collection's
    /// instance cell: the record says which struct it is of, and a collection holds instances of
    /// one (TRI-D2).
    fn head(
        &self,
        instance: &ProtocolRuleInstance<DescriptorTerm>,
    ) -> Result<(), DescriptorLoweringError> {
        let Some(head) = &instance.head else {
            return Ok(());
        };
        let named = match head {
            DescriptorTerm::Cell { declaration, .. } if *declaration == self.declaration.id => {
                return Ok(());
            }
            DescriptorTerm::Cell { declaration, .. } => format!("`{}`", declaration.item_name()),
            _ => "no `#[k::cell]` struct".to_owned(),
        };
        Err(collection_error(
            self.descriptor,
            codes::analysis::COLLECTION_ENTRY,
            &instance.key,
            format!(
                "the instance record names {named}, and `{}`'s instances are `{}`",
                self.collection.cell.field, self.declaration.name
            ),
        ))
    }

    fn child<'d>(
        &self,
        instance: &ProtocolRuleInstance<DescriptorTerm>,
        field: &'d krs_ir::ProtocolRuleInstanceField<DescriptorTerm>,
    ) -> Result<&'d krs_ir::ProtocolRuleInstanceField<DescriptorTerm>, DescriptorLoweringError>
    {
        let Some(declared) = self.declaration.child(&field.field) else {
            return Err(collection_error(
                self.descriptor,
                codes::analysis::COLLECTION_ENTRY,
                &field.key,
                format!(
                    "the instance cell `{}` has no child `{}`{}",
                    self.declaration.name,
                    field.field,
                    descendant_reason(
                        &self.declaration.name,
                        self.declaration.fields,
                        &field.field,
                        self.declarations,
                    )
                ),
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
        // </c>`. A Map collection's key is the instance's identity, so writing it is the key
        // change refused below.
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
            if self.map
                && let Some(key) = self.declaration.fields.first()
                && let Some(field) = result
                    .fields
                    .iter()
                    .find(|field| field.field == key.rust_field)
            {
                let subject_field = subject
                    .fields
                    .iter()
                    .find(|candidate| candidate.field == key.rust_field)
                    .expect("result children occur in the pattern");
                let (_, sort) = cell_kind_sort(key);
                let before = self.lowering.lower_state(
                    &subject_field.value,
                    &sort,
                    &subject_field.key,
                    true,
                )?;
                let after = self
                    .lowering
                    .lower_state(&field.value, &sort, &field.key, false)?;
                if !self.lowering.same(&before, &after) {
                    return Err(collection_error(
                        descriptor,
                        codes::analysis::MAP_COLLECTION_KEY,
                        &field.key,
                        krs_ir::subject::key_update_reason(
                            &self.collection.cell.field,
                            &key.rust_field,
                        ),
                    ));
                }
            }
        }
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
            let before = self.subject_state(field, &sort)?;
            let mut frame = state_frame(
                descriptor,
                &field.value,
                result_field.map(|field| &field.value),
            )?;
            let after = match result_field {
                None => CellPost::Preserve,
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
                        CellPost::Preserve
                    } else {
                        CellPost::Replace { term: after }
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
        Ok(InstanceClause::Kept {
            origin: semantic_origin(descriptor, subject.key.clone(), "rule-instance")?,
            label: subject.label.clone(),
            children,
            open: matches!(subject.rest, ProtocolInstanceRest::Open),
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
                self.subject_state(field, &sort)?
            } else {
                self.lowering
                    .lower_result(&field.value, &sort, &field.key, &MapBase::Unmatched)?
            };
            let frame = if subject {
                state_frame(descriptor, &field.value, None)?
            } else {
                let exact = match &field.value {
                    ProtocolRuleStateTerm::KSequence(sequence) => {
                        matches!(sequence.tail, ProtocolRuleFrame::Exact)
                    }
                    ProtocolRuleStateTerm::Map(map) => !matches!(
                        &map.body,
                        krs_ir::ProtocolRuleMapBody::Items {
                            remainder: ProtocolRuleFrame::Anonymous { .. }
                                | ProtocolRuleFrame::Reuse { .. },
                            ..
                        }
                    ),
                    _ => true,
                };
                if !exact {
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
        Ok(InstanceClause::Removed {
            origin: semantic_origin(self.descriptor, subject.key.clone(), "rule-instance")?,
            label: subject.label.clone(),
            children: self.children(subject, true)?,
            open: matches!(subject.rest, ProtocolInstanceRest::Open),
        })
    }

    /// A new instance: its children, and `..` defaults for the others.
    fn created(
        &mut self,
        result: &ProtocolRuleInstance<DescriptorTerm>,
    ) -> Result<InstanceClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
        let descriptor = self.descriptor;
        self.head(result)?;
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
