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

use super::catalog::semantic_sort_ref;
use super::error::DescriptorLoweringError;
use super::origin::{semantic_cell_id, semantic_origin};
use super::references::require_cell_field;

/// A rule cell state as transported.
pub(super) type DescriptorState = ProtocolRuleStateTerm<DescriptorTerm>;

/// Lowers the terms of optional and collection states for one rule.
pub(super) trait StateLowering {
    /// The rule's descriptor.
    fn descriptor(&self) -> &Descriptor;

    /// Lowers one leaf, group, `k!`, or `map!` state at its cell's sort.
    fn lower_state(
        &mut self,
        state: &DescriptorState,
        sort: &SemanticSortRef,
        fallback_key: &ProvenanceKey,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError>;

    /// Whether two lowered terms are the same term, ignoring origins.
    fn same(&self, left: &SemanticTerm, right: &SemanticTerm) -> bool;
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

/// The multiplicity spelling of a declared cell.
fn multiplicity(field: &DescriptorCellField) -> Option<&str> {
    field
        .multiplicity
        .as_ref()
        .map(|multiplicity| multiplicity.value.as_str())
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
/// or is written exactly, an exact state stays exact.
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
        ProtocolRuleStateTerm::KSequence(sequence) => &sequence.tail,
        ProtocolRuleStateTerm::Map(map) => match &map.body {
            krs_ir::ProtocolRuleMapBody::Items { remainder, .. } => remainder,
            _ => &ProtocolRuleFrame::Exact,
        },
        _ => &ProtocolRuleFrame::Exact,
    });
    let compatible = match (frame, result_frame) {
        (_, None)
        | (
            ProtocolRuleFrame::Exact | ProtocolRuleFrame::Anonymous { .. },
            Some(ProtocolRuleFrame::Exact),
        )
        | (
            ProtocolRuleFrame::Anonymous { .. } | ProtocolRuleFrame::Bind { .. },
            Some(ProtocolRuleFrame::Anonymous { .. }),
        ) => true,
        (
            ProtocolRuleFrame::Bind { binding, .. },
            Some(ProtocolRuleFrame::Reuse {
                binding: reused, ..
            }),
        ) => binding == reused,
        _ => false,
    };
    if !compatible {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "cell content frame",
            detail: format!(
                "rule {} uses incompatible subject/result associative state frames",
                descriptor.id()
            ),
        });
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
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "subject cell frame",
            detail: "a subject frame cannot reuse a result binding".into(),
        });
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
    if multiplicity(declared) != Some("?") {
        return Err(presence_error(
            &cell.key,
            format!(
                "`{name}` is not an optional cell: `Some`/`None` entries name a cell declared `#[k::cell(multiplicity = \"?\")]` with an `Option<T>` field"
            ),
        ));
    }
    let (kind, sort) = cell_kind_sort(declared);
    if !is_presence(before) {
        return Err(presence_error(
            &cell.key,
            format!("the optional cell `{name}` is matched with `Some(..)` or `None`"),
        ));
    }
    let before_inner = present_content(before);
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
    let lower_presence =
        |lowering: &mut dyn FnMut(
            &DescriptorState,
            bool,
        ) -> Result<SemanticTerm, DescriptorLoweringError>,
         state: Option<&DescriptorState>,
         subject: bool| {
            state.map_or(Ok(Presence::Absent), |state| {
                lowering(state, subject).map(|term| Presence::Present { term })
            })
        };
    let mut lower = |state: &DescriptorState, subject: bool| {
        lowering.lower_state(
            state,
            &sort,
            if subject {
                &cell.key
            } else {
                result_key.unwrap_or(&cell.key)
            },
            subject,
        )
    };
    let before_presence = lower_presence(&mut lower, before_inner, true)?;
    let after_presence = after_inner
        .map(|state| lower_presence(&mut lower, state, false))
        .transpose()?;
    let frame = match before_inner {
        Some(state) => state_frame(&descriptor, state, after_inner.flatten())?,
        None => CellContentFrame::Exact,
    };
    // A present cell restated unchanged is read only.
    let after_presence = match (&before_presence, after_presence) {
        (Presence::Present { term: left }, Some(Presence::Present { term: right }))
            if lowering.same(left, &right) =>
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
    let (ProtocolCellContent::Nested { declaration }, Some("*")) =
        (&declared.content, multiplicity(declared))
    else {
        return Err(entry_error(
            &cell.key,
            format!(
                "`{name}` is not a cell collection: an instance list names a cell declared `#[k::cell(multiplicity = \"*\", cell_type = .., nested)]`"
            ),
        ));
    };
    let collection = declared
        .cell_type
        .as_ref()
        .map(|cell_type| CellCollectionType::from(cell_type.value))
        .ok_or_else(|| {
            entry_error(
                &cell.key,
                format!("the collection `{name}` has no cell_type"),
            )
        })?;
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
                codes::analysis::UNKNOWN_INSTANCE_LABEL,
                &instance.key,
                format!("the instance label `{label}` is used twice in `{name}`"),
            ));
        }
    }
    let subject_open = !matches!(before.rest, ProtocolRuleFrame::Exact);
    if let Some(after) = after {
        let result_open = !matches!(after.rest, ProtocolRuleFrame::Exact);
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
                let Some(&index) = labels.get(label) else {
                    return Err(collection_error(
                        &descriptor,
                        codes::analysis::UNKNOWN_INSTANCE_LABEL,
                        &instance.key,
                        format!(
                            "`..{label}` names no instance of `{name}` labelled `{label} @` in the pattern"
                        ),
                    ));
                };
                if kept_by[index].replace((back, position)).is_some() {
                    return Err(collection_error(
                        &descriptor,
                        codes::analysis::UNKNOWN_INSTANCE_LABEL,
                        &instance.key,
                        format!("two result instances of `{name}` update `{label}`"),
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
        declaration: &instance_declaration,
        configuration,
        collection: cell,
        map: collection == CellCollectionType::Map,
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
    if front.is_empty() && back.is_empty() {
        return Err(entry_error(
            &cell.key,
            format!("the collection entry `{name}` names no instance"),
        ));
    }
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
            return Err(entry_error(
                &cell.key,
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
    declaration: &'a InstanceDeclaration<'b>,
    configuration: &'a DescriptorFixedConfiguration,
    collection: &'a DescriptorCellReference,
    map: bool,
}

impl<L: StateLowering> LoweredInstances<'_, '_, L> {
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
                    "the instance cell `{}` has no child `{}`",
                    self.declaration.name, field.field
                ),
            ));
        };
        if declared.multiplicity.is_some() {
            return Err(collection_error(
                self.descriptor,
                codes::analysis::COLLECTION_ENTRY,
                &field.key,
                format!(
                    "the child `{}` of `{}` is itself optional or a collection, which an instance record cannot name yet",
                    field.field, self.declaration.name
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
        if let Some(result) = result {
            for field in &result.fields {
                self.child(result, field)?;
                if !subject
                    .fields
                    .iter()
                    .any(|candidate| candidate.field == field.field)
                {
                    return Err(collection_error(
                        descriptor,
                        codes::analysis::COLLECTION_ENTRY,
                        &field.key,
                        format!(
                            "the result rewrites `{}` of an instance its pattern does not name; write `{}: _` in the pattern instance",
                            field.field, field.field
                        ),
                    ));
                }
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
                        format!(
                            "an update must not change `{}`, the key of the Map collection `{}`",
                            key.rust_field, self.collection.cell.field
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
            let before = self
                .lowering
                .lower_state(&field.value, &sort, &field.key, true)?;
            let frame = state_frame(
                descriptor,
                &field.value,
                result_field.map(|field| &field.value),
            )?;
            let after = match result_field {
                None => CellPost::Preserve,
                Some(result_field) => {
                    let after = self.lowering.lower_state(
                        &result_field.value,
                        &sort,
                        &result_field.key,
                        false,
                    )?;
                    if self.lowering.same(&before, &after) {
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
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "collection instance",
                        detail: "a whole nested child has no frame".into(),
                    });
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
            let term = self
                .lowering
                .lower_state(&field.value, &sort, &field.key, subject)?;
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
                if templates
                    .get(&field.reference.cell)
                    .is_some_and(|template| reads_variable(template))
                {
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

/// Rejects a rule that names a collection's instances and also a cell inside
/// it as the collection's implicit single instance (KF-023).
pub(super) fn check_implicit_and_explicit_instances(
    descriptor: &Descriptor,
    pattern_key: &ProvenanceKey,
    declarations: &DescriptorIndex<'_>,
    clauses: &[ConfigurationClause<SemanticId, SemanticTerm>],
    selected: &[(DescriptorCellReference, bool)],
) -> Result<(), DescriptorLoweringError> {
    let collections = selected
        .iter()
        .filter(|(_, collection)| *collection)
        .map(|(cell, _)| cell)
        .collect::<Vec<_>>();
    if collections.is_empty() {
        return Ok(());
    }
    let _ = clauses;
    for collection in collections {
        let field = require_cell_field(&collection.cell, declarations)?;
        let ProtocolCellContent::Nested { declaration } = &field.content else {
            continue;
        };
        let mut below = BTreeSet::new();
        collect_below(declarations, &declaration.declaration, &mut below, 0)?;
        if let Some((inside, _)) = selected
            .iter()
            .find(|(cell, collection)| !collection && below.contains(&cell.cell))
        {
            return Err(collection_error(
                descriptor,
                codes::analysis::IMPLICIT_AND_EXPLICIT_INSTANCES,
                &inside.key,
                format!(
                    "rule `{}` names instances of the collection `{}` and also `{}` inside it as its implicit single instance; name `{}` inside an instance record instead",
                    descriptor.id().item_name(),
                    collection.cell.field,
                    inside.cell.field,
                    inside.cell.field
                ),
            ));
        }
    }
    let _ = pattern_key;
    Ok(())
}

fn collect_below(
    declarations: &DescriptorIndex<'_>,
    declaration: &StableItemId,
    below: &mut BTreeSet<krs_ir::DescriptorCellIdentity>,
    depth: usize,
) -> Result<(), DescriptorLoweringError> {
    if depth > 64 {
        return Ok(());
    }
    for field in &declarations.cell(declaration)?.fields {
        below.insert(field.reference.cell.clone());
        if let ProtocolCellContent::Nested { declaration } = &field.content {
            collect_below(declarations, &declaration.declaration, below, depth + 1)?;
        }
    }
    Ok(())
}
