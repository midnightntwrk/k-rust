//! Resolution of host descriptor payloads against the declared items of the selected packages.

use std::any::TypeId;
use std::collections::{HashMap, HashSet};

use krs_ir::{
    ConstructorDescriptor, ConstructorFieldDescriptor, DescriptorApplicationRef,
    DescriptorApplicationReference, DescriptorPayload, DescriptorProduction,
    DescriptorProductionAttribute, DescriptorProductionItem, DescriptorProductionOwner,
    DescriptorSortRef, DescriptorSortReference, DescriptorTerm, DescriptorTermArgument,
    GrammarDescriptor, HostApplicationIdentity, HostBuiltinRegistry, HostDescriptorPayload,
    HostGrammarDescriptor, HostItemId, HostProductionAttribute, HostProductionItem,
    HostProductionOwner, HostSortReference, HostStructuredRuleDescriptor, HostTerm,
    HostTermArgument, HostTypeReference, ItemKind, ProtocolCellContent,
    ProtocolInitializerCellContent, ProtocolInitializerStateTerm, ProtocolMapBody,
    ProtocolRuleFrame, ProtocolRuleMapBody, ProtocolRuleStateTerm, SortDescriptor, StableItemId,
    StructuredRuleDescriptor,
};

use super::PendingDescriptor;
use crate::{CollectionError, CollectionErrorKind};

pub(super) fn declared_type_table(
    pending: &[PendingDescriptor],
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>, CollectionError> {
    let mut declarations = HashMap::new();
    for descriptor in pending {
        let kind = descriptor.id.item_kind();
        let Some(key) = descriptor.host.declared_type else {
            if matches!(
                kind,
                ItemKind::Sort | ItemKind::Constructor | ItemKind::Configuration | ItemKind::Cell
            ) {
                return Err(CollectionError::new(
                    CollectionErrorKind::MissingTypeDeclaration,
                    format!(
                        "type declaration `{}` exposes no build-local Rust type",
                        descriptor.id
                    ),
                ));
            }
            continue;
        };
        if !matches!(
            kind,
            ItemKind::Sort | ItemKind::Constructor | ItemKind::Configuration | ItemKind::Cell
        ) {
            return Err(CollectionError::new(
                CollectionErrorKind::ItemKindMismatch,
                format!(
                    "non-type item `{}` exposes a declared Rust type key",
                    descriptor.id
                ),
            ));
        }
        let resolved = key.resolve();
        if kind != ItemKind::Constructor && !matches!(resolved, HostApplicationIdentity::Nominal(_))
        {
            return Err(CollectionError::new(
                CollectionErrorKind::ItemKindMismatch,
                format!(
                    "non-constructor `{}` exposes an enum-variant declaration identity",
                    descriptor.id
                ),
            ));
        }
        if let Some(registry) = builtins
            && let HostApplicationIdentity::Nominal(type_id) = resolved
            && (registry.resolve_sort(type_id).is_some()
                || registry.resolve_operation(type_id).is_some()
                || registry.resolve_map_operation(type_id).is_some()
                || registry.resolve_list_operation(type_id).is_some()
                || registry.resolve_set_operation(type_id).is_some())
        {
            return Err(CollectionError::new(
                CollectionErrorKind::DeclarationBuiltinCollision,
                format!(
                    "authored declaration `{}` reuses a compiler builtin marker type",
                    descriptor.id
                ),
            ));
        }
        if let Some((previous, _)) = declarations.insert(resolved, (descriptor.id.clone(), kind)) {
            return Err(CollectionError::new(
                CollectionErrorKind::DuplicateTypeDeclaration,
                format!(
                    "items `{}` and `{}` expose the same build-local Rust type",
                    previous, descriptor.id
                ),
            ));
        }
    }
    Ok(declarations)
}

type HostCellKey = (TypeId, TypeId);

pub(super) fn declared_cell_field_table(
    pending: &[PendingDescriptor],
) -> Result<HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>, CollectionError> {
    let mut fields = HashMap::new();
    for descriptor in pending {
        let declaration = match &descriptor.host.payload {
            HostDescriptorPayload::FixedConfiguration(configuration) => &configuration.declaration,
            HostDescriptorPayload::Cell(declaration) => declaration.as_ref(),
            HostDescriptorPayload::Sort(_)
            | HostDescriptorPayload::Constructor(_)
            | HostDescriptorPayload::Grammar(_)
            | HostDescriptorPayload::StructuredRule(_)
            | HostDescriptorPayload::ConfigurationRule(_)
            | HostDescriptorPayload::HeadRule(_)
            | HostDescriptorPayload::ContextAlias(_) => continue,
        };
        for field in &declaration.fields {
            let key = field.reference.cell.resolve();
            let stable = krs_ir::DescriptorCellIdentity {
                owner: descriptor.id.clone(),
                field: field.rust_field.clone(),
            };
            if fields.insert(key, stable).is_some() {
                return Err(CollectionError::new(
                    CollectionErrorKind::DuplicateTypeDeclaration,
                    format!(
                        "fixed cell field `{}` on `{}` reuses an owner/field marker identity",
                        field.rust_field, descriptor.id
                    ),
                ));
            }
        }
    }
    Ok(fields)
}

#[derive(Clone, Debug)]
struct HeadRuleCellTarget {
    identity: krs_ir::DescriptorCellIdentity,
    names: Vec<String>,
    wrapper: krs_ir::CellWrapper,
}

#[derive(Clone, Debug)]
pub(super) struct HeadRuleTarget {
    configuration: StableItemId,
    cells: Vec<HeadRuleCellTarget>,
}

struct HeadRuleSelection<'a> {
    target: &'a HeadRuleTarget,
    computation: &'a HeadRuleCellTarget,
}

fn collect_head_rule_cells(
    declaration: &krs_ir::HostCellDeclaration,
    declarations: &HashMap<TypeId, &krs_ir::HostCellDeclaration>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    visiting: &mut HashSet<TypeId>,
    cells: &mut Vec<HeadRuleCellTarget>,
) -> Result<(), CollectionError> {
    for field in &declaration.fields {
        match &field.content {
            krs_ir::ProtocolCellContent::Leaf { wrapper, .. } => {
                let identity = cell_fields
                    .get(&field.reference.cell.resolve())
                    .cloned()
                    .ok_or_else(|| {
                        CollectionError::new(
                            CollectionErrorKind::UnresolvedTypeReference,
                            format!(
                                "fixed cell `{}` has no stable owner/field identity",
                                field.rust_field
                            ),
                        )
                    })?;
                let mut names = vec![field.rust_field.clone()];
                if let Some(emitted) = &field.emitted_name
                    && !names.contains(&emitted.value)
                {
                    names.push(emitted.value.clone());
                }
                cells.push(HeadRuleCellTarget {
                    identity,
                    names,
                    wrapper: *wrapper,
                });
            }
            krs_ir::ProtocolCellContent::Nested { declaration } => {
                let key = declaration.declaration.key.resolve();
                if !visiting.insert(key) {
                    return Err(CollectionError::new(
                        CollectionErrorKind::InvalidConfiguration,
                        format!(
                            "cyclic nested fixed-cell declaration `{}`",
                            declaration.declaration.authored_path
                        ),
                    ));
                }
                let nested = declarations.get(&key).ok_or_else(|| {
                    CollectionError::new(
                        CollectionErrorKind::UnresolvedTypeReference,
                        format!(
                            "nested fixed-cell declaration `{}` was not collected",
                            declaration.declaration.authored_path
                        ),
                    )
                })?;
                collect_head_rule_cells(nested, declarations, cell_fields, visiting, cells)?;
                visiting.remove(&key);
            }
        }
    }
    Ok(())
}

pub(super) fn resolve_head_rule_targets(
    pending: &[PendingDescriptor],
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
) -> Result<Vec<HeadRuleTarget>, CollectionError> {
    if !pending
        .iter()
        .any(|descriptor| matches!(descriptor.host.payload, HostDescriptorPayload::HeadRule(_)))
    {
        return Ok(Vec::new());
    }
    let configurations = pending
        .iter()
        .filter_map(|descriptor| match &descriptor.host.payload {
            HostDescriptorPayload::FixedConfiguration(configuration) => {
                Some((descriptor, configuration.as_ref()))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let cell_declarations = pending
        .iter()
        .filter_map(|descriptor| {
            let HostDescriptorPayload::Cell(declaration) = &descriptor.host.payload else {
                return None;
            };
            let Some(krs_ir::HostDeclarationIdentity::Nominal(key)) = descriptor.host.declared_type
            else {
                return None;
            };
            Some((key.resolve(), declaration.as_ref()))
        })
        .collect::<HashMap<_, _>>();
    let has_implicit_target = pending.iter().any(|descriptor| {
        matches!(
            &descriptor.host.payload,
            HostDescriptorPayload::HeadRule(rule) if rule.configuration.is_none()
        )
    });
    if has_implicit_target && configurations.len() != 1 {
        let detail = match configurations.len() {
            0 => "a `for Sort` rule requires one fixed configuration, but none was collected"
                .to_owned(),
            count => format!(
                "a `for Sort` rule requires one unambiguous fixed configuration, but {count} candidates were collected"
            ),
        };
        return Err(CollectionError::new(
            CollectionErrorKind::InvalidConfiguration,
            detail,
        ));
    }
    let targets = configurations
        .into_iter()
        .map(|(descriptor, configuration)| {
            let mut cells = Vec::new();
            collect_head_rule_cells(
                &configuration.declaration,
                &cell_declarations,
                cell_fields,
                &mut HashSet::new(),
                &mut cells,
            )?;
            Ok(HeadRuleTarget {
                configuration: descriptor.id.clone(),
                cells,
            })
        })
        .collect::<Result<Vec<_>, CollectionError>>()?;
    if has_implicit_target {
        let computations = targets[0]
            .cells
            .iter()
            .filter(|cell| cell.wrapper == krs_ir::CellWrapper::KCell)
            .count();
        if computations != 1 {
            let detail = match computations {
                0 => "selected fixed configuration has no matching top-level KCell<KSequence> computation cell"
                    .to_owned(),
                count => format!(
                    "selected fixed configuration has {count} matching top-level KCell<KSequence> computation cells"
                ),
            };
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                detail,
            ));
        }
    }
    Ok(targets)
}

fn resolve_head_rule_target<'a>(
    rule: &krs_ir::HostHeadRule,
    targets: &'a [HeadRuleTarget],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<HeadRuleSelection<'a>, CollectionError> {
    let target = if let Some(configuration) = &rule.configuration {
        let selected = resolve_configuration_reference(configuration, declarations)?;
        targets
            .iter()
            .find(|target| target.configuration == selected.configuration)
            .ok_or_else(|| {
                CollectionError::new(
                    CollectionErrorKind::InvalidConfiguration,
                    "cell-record rule names a fixed configuration that was not collected",
                )
            })?
    } else {
        let [target] = targets else {
            let detail = match targets.len() {
                0 => "head-anchored rules require one fixed configuration, but none was collected"
                    .to_owned(),
                count => format!(
                    "a `for Sort` rule requires one unambiguous fixed configuration, but {count} candidates were collected; use a configuration-owned cell-record rule where appropriate"
                ),
            };
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                detail,
            ));
        };
        target
    };
    let computations = target
        .cells
        .iter()
        .filter(|cell| {
            cell.wrapper == krs_ir::CellWrapper::KCell
                && rule
                    .computation_cell_name
                    .as_ref()
                    .is_none_or(|name| cell.names.iter().any(|candidate| candidate == name))
        })
        .collect::<Vec<_>>();
    let [computation] = computations.as_slice() else {
        let detail = match computations.len() {
            0 => "selected fixed configuration has no matching top-level KCell<KSequence> computation cell"
                .to_owned(),
            count => format!(
                "selected fixed configuration has {count} matching top-level KCell<KSequence> computation cells"
            ),
        };
        return Err(CollectionError::new(
            CollectionErrorKind::InvalidConfiguration,
            detail,
        ));
    };
    Ok(HeadRuleSelection {
        target,
        computation,
    })
}

fn resolve_head_rule_extras(
    rule: &krs_ir::HostHeadRule,
    selection: &HeadRuleSelection<'_>,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<Vec<krs_ir::DescriptorHeadRuleExtra>, CollectionError> {
    let resolve_cell = |cell: &krs_ir::HostHeadRuleCellReference| {
        let matches = selection
            .target
            .cells
            .iter()
            .filter(|candidate| candidate.names.iter().any(|name| name == &cell.name))
            .collect::<Vec<_>>();
        let [resolved] = matches.as_slice() else {
            let detail = match matches.len() {
                0 => format!(
                    "readable rule extra names no fixed leaf cell `{}`",
                    cell.name
                ),
                count => format!(
                    "readable rule extra cell name `{}` is ambiguous across {count} fixed leaf cells",
                    cell.name
                ),
            };
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                detail,
            ));
        };
        if resolved.identity == selection.computation.identity {
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                format!(
                    "readable rule extra may not mention computation cell `{}`",
                    cell.name
                ),
            ));
        }
        Ok(krs_ir::DescriptorCellReference {
            key: cell.key.clone(),
            cell: resolved.identity.clone(),
        })
    };
    rule.extras
        .iter()
        .map(|extra| {
            Ok(match extra {
                krs_ir::ProtocolHeadRuleExtra::HaveMap {
                    cell,
                    key,
                    value_binding,
                } => krs_ir::ProtocolHeadRuleExtra::HaveMap {
                    cell: resolve_cell(cell)?,
                    key: resolve_term(key, declarations, builtins)?,
                    value_binding: value_binding.clone(),
                },
                krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                    cell,
                    base_binding,
                    update,
                } => krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                    cell: resolve_cell(cell)?,
                    base_binding: base_binding.clone(),
                    update: resolve_term(update, declarations, builtins)?,
                },
                krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                    cell,
                    result_key,
                    before,
                    after,
                } => krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                    cell: resolve_cell(cell)?,
                    result_key: result_key.clone(),
                    before: resolve_term(before, declarations, builtins)?,
                    after: resolve_term(after, declarations, builtins)?,
                },
            })
        })
        .collect::<Result<Vec<_>, CollectionError>>()
}

fn resolve_head_rule(
    rule: &krs_ir::HostHeadRule,
    targets: &[HeadRuleTarget],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorHeadRule, CollectionError> {
    let selection = resolve_head_rule_target(rule, targets, declarations)?;
    let extras = resolve_head_rule_extras(rule, &selection, declarations, builtins)?;
    let result = match &rule.result {
        krs_ir::ProtocolHeadRuleResult::Replace(term) => {
            krs_ir::ProtocolHeadRuleResult::Replace(resolve_term(term, declarations, builtins)?)
        }
        krs_ir::ProtocolHeadRuleResult::Splice(items) => krs_ir::ProtocolHeadRuleResult::Splice(
            items
                .iter()
                .map(|term| resolve_term(term, declarations, builtins))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        krs_ir::ProtocolHeadRuleResult::Erase => krs_ir::ProtocolHeadRuleResult::Erase,
    };
    Ok(krs_ir::DescriptorHeadRule {
        sentence_kind: rule.sentence_kind,
        label: rule.label.clone(),
        priority: rule.priority.clone(),
        pattern_key: rule.pattern_key.clone(),
        result_key: rule.result_key.clone(),
        head_sort: rule
            .head_sort
            .as_ref()
            .map(|sort| resolve_sort_reference(sort, declarations, builtins))
            .transpose()?,
        configuration: selection.target.configuration.clone(),
        computation_cell: krs_ir::DescriptorCellReference {
            key: rule.pattern_key.clone(),
            cell: selection.computation.identity.clone(),
        },
        bindings: rule
            .bindings
            .iter()
            .map(|binding| {
                Ok(krs_ir::ProtocolHeadRuleBinding {
                    name: binding.name.clone(),
                    refinement: binding
                        .refinement
                        .as_ref()
                        .map(|sort| resolve_sort_reference(sort, declarations, builtins))
                        .transpose()?,
                })
            })
            .collect::<Result<Vec<_>, CollectionError>>()?,
        subject: resolve_term(&rule.subject, declarations, builtins)?,
        result,
        requires: rule
            .requires
            .as_ref()
            .map(|condition| {
                Ok(krs_ir::DescriptorRuleCondition {
                    key: condition.key.clone(),
                    term: resolve_term(&condition.term, declarations, builtins)?,
                })
            })
            .transpose()?,
        extras,
    })
}

pub(super) fn resolve_payload(
    payload: &HostDescriptorPayload,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    context_aliases: &HashMap<HostItemId, StableItemId>,
    builtins: Option<&HostBuiltinRegistry>,
    head_targets: &[HeadRuleTarget],
) -> Result<DescriptorPayload, CollectionError> {
    match payload {
        HostDescriptorPayload::Sort(sort) => {
            let mut parents = sort
                .parents
                .iter()
                .map(|parent| resolve_nominal_reference(parent, ItemKind::Sort, declarations))
                .collect::<Result<Vec<_>, _>>()?;
            parents.sort();
            parents.dedup();
            Ok(DescriptorPayload::Sort(SortDescriptor { parents }))
        }
        HostDescriptorPayload::Constructor(constructor) => {
            Ok(DescriptorPayload::Constructor(ConstructorDescriptor {
                sort: resolve_sort_reference(&constructor.sort, declarations, builtins)?.sort,
                syntax: constructor.syntax.clone(),
                fields: constructor
                    .fields
                    .iter()
                    .map(|field| {
                        Ok(ConstructorFieldDescriptor {
                            name: field.name.clone(),
                            sort: Some(resolve_constructor_field_sort(
                                &field.sort,
                                declarations,
                                builtins,
                            )?),
                        })
                    })
                    .collect::<Result<Vec<_>, CollectionError>>()?,
            }))
        }
        HostDescriptorPayload::Grammar(grammar) => Ok(DescriptorPayload::Grammar(Box::new(
            resolve_grammar(grammar, declarations, context_aliases, builtins)?,
        ))),
        HostDescriptorPayload::StructuredRule(rule) => Ok(DescriptorPayload::StructuredRule(
            Box::new(resolve_structured_rule(rule, declarations, builtins)?),
        )),
        HostDescriptorPayload::FixedConfiguration(configuration) => {
            Ok(DescriptorPayload::FixedConfiguration(Box::new(
                resolve_fixed_configuration(configuration, declarations, cell_fields, builtins)?,
            )))
        }
        HostDescriptorPayload::Cell(declaration) => Ok(DescriptorPayload::Cell(Box::new(
            resolve_cell_declaration(declaration, declarations, cell_fields, builtins)?,
        ))),
        HostDescriptorPayload::ConfigurationRule(rule) => {
            Ok(DescriptorPayload::ConfigurationRule(Box::new(
                resolve_configuration_rule(rule, declarations, cell_fields, builtins)?,
            )))
        }
        HostDescriptorPayload::HeadRule(rule) => Ok(DescriptorPayload::HeadRule(Box::new(
            resolve_head_rule(rule, head_targets, declarations, builtins)?,
        ))),
        HostDescriptorPayload::ContextAlias(alias) => {
            Ok(DescriptorPayload::ContextAlias(Box::new(
                resolve_context_alias(alias, declarations, cell_fields, builtins)?,
            )))
        }
    }
}

fn resolve_context_alias(
    alias: &krs_ir::HostContextAlias,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorContextAlias, CollectionError> {
    Ok(krs_ir::DescriptorContextAlias {
        declaration_key: alias.declaration_key.clone(),
        name_key: alias.name_key.clone(),
        name: alias.name.clone(),
        here_key: alias.here_key.clone(),
        here: alias.here.clone(),
        pattern_key: alias.pattern_key.clone(),
        configuration: resolve_configuration_reference(&alias.configuration, declarations)?,
        bindings: alias
            .bindings
            .iter()
            .map(|binding| {
                Ok(krs_ir::ProtocolContextAliasBinding {
                    name: binding.name.clone(),
                    kind: match &binding.kind {
                        krs_ir::ProtocolContextAliasBindingKind::Here => {
                            krs_ir::ProtocolContextAliasBindingKind::Here
                        }
                        krs_ir::ProtocolContextAliasBindingKind::Term { sort } => {
                            krs_ir::ProtocolContextAliasBindingKind::Term {
                                sort: resolve_sort_reference(sort, declarations, builtins)?,
                            }
                        }
                        krs_ir::ProtocolContextAliasBindingKind::KSequenceFrame => {
                            krs_ir::ProtocolContextAliasBindingKind::KSequenceFrame
                        }
                        krs_ir::ProtocolContextAliasBindingKind::MapFrame => {
                            krs_ir::ProtocolContextAliasBindingKind::MapFrame
                        }
                        krs_ir::ProtocolContextAliasBindingKind::ConfigurationFrame => {
                            krs_ir::ProtocolContextAliasBindingKind::ConfigurationFrame
                        }
                    },
                })
            })
            .collect::<Result<Vec<_>, CollectionError>>()?,
        pattern: resolve_rule_cells(&alias.pattern, declarations, cell_fields, builtins)?,
    })
}

fn resolve_cell_reference(
    reference: &krs_ir::HostCellReference,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
) -> Result<krs_ir::DescriptorCellReference, CollectionError> {
    let key = reference.cell.resolve();
    let cell = cell_fields.get(&key).cloned().ok_or_else(|| {
        CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "cell reference `{}#{}` has no selected owner/field-marker declaration",
                reference.key.role().as_str(),
                reference.key.ordinal()
            ),
        )
    })?;
    Ok(krs_ir::DescriptorCellReference {
        key: reference.key.clone(),
        cell,
    })
}

fn resolve_cell_declaration_reference(
    reference: &krs_ir::HostCellDeclarationReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<krs_ir::DescriptorCellDeclarationReference, CollectionError> {
    Ok(krs_ir::DescriptorCellDeclarationReference {
        key: reference.key.clone(),
        declaration: resolve_nominal_reference(
            &reference.declaration,
            ItemKind::Cell,
            declarations,
        )?,
    })
}

fn resolve_cell_declaration(
    declaration: &krs_ir::HostCellDeclaration,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorCellDeclaration, CollectionError> {
    Ok(krs_ir::ProtocolCellDeclaration {
        key: declaration.key.clone(),
        fields: declaration
            .fields
            .iter()
            .map(|field| {
                let content = match &field.content {
                    ProtocolCellContent::Leaf {
                        wrapper_key,
                        wrapper,
                        sort,
                        arguments,
                    } => ProtocolCellContent::Leaf {
                        wrapper_key: wrapper_key.clone(),
                        wrapper: *wrapper,
                        sort: resolve_sort_reference(sort, declarations, builtins)?,
                        arguments: arguments
                            .iter()
                            .map(|argument| {
                                resolve_sort_reference(argument, declarations, builtins)
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    },
                    ProtocolCellContent::Nested { declaration } => ProtocolCellContent::Nested {
                        declaration: resolve_cell_declaration_reference(declaration, declarations)?,
                    },
                };
                Ok(krs_ir::ProtocolCellField {
                    reference: resolve_cell_reference(&field.reference, cell_fields)?,
                    rust_field: field.rust_field.clone(),
                    emitted_name: field.emitted_name.clone(),
                    color: field.color.clone(),
                    multiplicity: field.multiplicity.clone(),
                    cell_type: field.cell_type.clone(),
                    content,
                })
            })
            .collect::<Result<Vec<_>, CollectionError>>()?,
    })
}

fn resolve_fixed_configuration(
    configuration: &krs_ir::HostFixedConfiguration,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorFixedConfiguration, CollectionError> {
    let declaration = resolve_cell_declaration(
        &configuration.declaration,
        declarations,
        cell_fields,
        builtins,
    )?;
    let owner = resolve_declared_identity(
        HostApplicationIdentity::Nominal(configuration.initializer.owner.resolve()),
        "Self",
        ItemKind::Configuration,
        declarations,
    )?;
    let variables = configuration
        .initializer
        .variables
        .iter()
        .map(|variable| {
            Ok(krs_ir::ProtocolConfigurationVariable {
                binding_key: variable.binding_key.clone(),
                binding: variable.binding.clone(),
                external_name_key: variable.external_name_key.clone(),
                external_name: variable.external_name.clone(),
                sort: resolve_sort_reference(&variable.sort, declarations, builtins)?,
                main_key: variable.main_key.clone(),
            })
        })
        .collect::<Result<Vec<_>, CollectionError>>()?;
    let cells = configuration
        .initializer
        .cells
        .iter()
        .map(|cell| resolve_initializer_cell(cell, declarations, cell_fields, builtins))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(krs_ir::DescriptorFixedConfiguration {
        root: configuration.root.clone(),
        declaration,
        initializer: krs_ir::ProtocolConfigurationInitializer {
            key: configuration.initializer.key.clone(),
            owner_key: configuration.initializer.owner_key.clone(),
            owner,
            variables,
            body_key: configuration.initializer.body_key.clone(),
            cells,
        },
    })
}

fn resolve_initializer_cell(
    cell: &krs_ir::HostInitializerCell,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorInitializerCell, CollectionError> {
    let content = match &cell.content {
        ProtocolInitializerCellContent::Leaf {
            constructor_key,
            wrapper,
            value,
        } => ProtocolInitializerCellContent::Leaf {
            constructor_key: constructor_key.clone(),
            wrapper: *wrapper,
            value: resolve_initializer_state(value, declarations, builtins)?,
        },
        ProtocolInitializerCellContent::Nested {
            declaration,
            children,
        } => ProtocolInitializerCellContent::Nested {
            declaration: resolve_cell_declaration_reference(declaration, declarations)?,
            children: children
                .iter()
                .map(|child| resolve_initializer_cell(child, declarations, cell_fields, builtins))
                .collect::<Result<Vec<_>, _>>()?,
        },
    };
    Ok(krs_ir::ProtocolInitializerCell {
        key: cell.key.clone(),
        field: resolve_cell_reference(&cell.field, cell_fields)?,
        content,
    })
}

fn resolve_initializer_term(
    term: &krs_ir::ProtocolInitializerTerm<HostTerm>,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::ProtocolInitializerTerm<DescriptorTerm>, CollectionError> {
    Ok(krs_ir::ProtocolInitializerTerm {
        key: term.key.clone(),
        term: resolve_term(&term.term, declarations, builtins)?,
    })
}

fn resolve_initializer_state(
    state: &krs_ir::HostInitializerStateTerm,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorInitializerStateTerm, CollectionError> {
    Ok(match state {
        ProtocolInitializerStateTerm::Term(term) => ProtocolInitializerStateTerm::Term(
            resolve_initializer_term(term, declarations, builtins)?,
        ),
        ProtocolInitializerStateTerm::KSequence(sequence) => {
            ProtocolInitializerStateTerm::KSequence(krs_ir::ProtocolKSequence {
                payload_key: sequence.payload_key.clone(),
                dot_k_key: sequence.dot_k_key.clone(),
                notation: sequence.notation,
                items: sequence
                    .items
                    .iter()
                    .map(|item| {
                        Ok(krs_ir::ProtocolKSequenceItem {
                            key: item.key.clone(),
                            value: resolve_initializer_term(&item.value, declarations, builtins)?,
                        })
                    })
                    .collect::<Result<Vec<_>, CollectionError>>()?,
            })
        }
        ProtocolInitializerStateTerm::Map(map) => {
            ProtocolInitializerStateTerm::Map(krs_ir::ProtocolMap {
                payload_key: map.payload_key.clone(),
                body: resolve_initializer_map_body(&map.body, declarations, builtins)?,
            })
        }
    })
}

fn resolve_initializer_map_body(
    body: &krs_ir::ProtocolMapBody<HostTerm>,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::ProtocolMapBody<DescriptorTerm>, CollectionError> {
    Ok(match body {
        ProtocolMapBody::Empty { explicit_dot } => ProtocolMapBody::Empty {
            explicit_dot: *explicit_dot,
        },
        ProtocolMapBody::Items { items } => ProtocolMapBody::Items {
            items: items
                .iter()
                .map(|item| {
                    Ok(krs_ir::ProtocolMapItem {
                        key_key: item.key_key.clone(),
                        key: resolve_initializer_term(&item.key, declarations, builtins)?,
                        value_key: item.value_key.clone(),
                        value: resolve_initializer_term(&item.value, declarations, builtins)?,
                    })
                })
                .collect::<Result<Vec<_>, CollectionError>>()?,
        },
        ProtocolMapBody::Update {
            base_key,
            base,
            key_key,
            key,
            value_key,
            value,
        } => ProtocolMapBody::Update {
            base_key: base_key.clone(),
            base: resolve_initializer_term(base, declarations, builtins)?,
            key_key: key_key.clone(),
            key: resolve_initializer_term(key, declarations, builtins)?,
            value_key: value_key.clone(),
            value: resolve_initializer_term(value, declarations, builtins)?,
        },
    })
}

fn resolve_configuration_reference(
    reference: &krs_ir::HostConfigurationReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<krs_ir::DescriptorConfigurationReference, CollectionError> {
    Ok(krs_ir::DescriptorConfigurationReference {
        key: reference.key.clone(),
        configuration: resolve_nominal_reference(
            &reference.configuration,
            ItemKind::Configuration,
            declarations,
        )?,
    })
}

fn resolve_rule_frame(frame: &ProtocolRuleFrame) -> ProtocolRuleFrame {
    frame.clone()
}

fn resolve_rule_state(
    state: &krs_ir::ProtocolRuleStateTerm<HostTerm>,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::ProtocolRuleStateTerm<DescriptorTerm>, CollectionError> {
    Ok(match state {
        ProtocolRuleStateTerm::Term(term) => {
            ProtocolRuleStateTerm::Term(resolve_term(term, declarations, builtins)?)
        }
        ProtocolRuleStateTerm::KSequence(sequence) => {
            ProtocolRuleStateTerm::KSequence(krs_ir::ProtocolRuleKSequence {
                payload_key: sequence.payload_key.clone(),
                dot_k_key: sequence.dot_k_key.clone(),
                notation: sequence.notation,
                items: sequence
                    .items
                    .iter()
                    .map(|item| {
                        Ok(krs_ir::ProtocolRuleKSequenceItem {
                            key: item.key.clone(),
                            value: resolve_term(&item.value, declarations, builtins)?,
                        })
                    })
                    .collect::<Result<Vec<_>, CollectionError>>()?,
                tail: resolve_rule_frame(&sequence.tail),
            })
        }
        ProtocolRuleStateTerm::Map(map) => ProtocolRuleStateTerm::Map(krs_ir::ProtocolRuleMap {
            payload_key: map.payload_key.clone(),
            body: resolve_rule_map_body(&map.body, declarations, builtins)?,
        }),
    })
}

fn resolve_rule_map_body(
    body: &krs_ir::ProtocolRuleMapBody<HostTerm>,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::ProtocolRuleMapBody<DescriptorTerm>, CollectionError> {
    Ok(match body {
        ProtocolRuleMapBody::Empty { explicit_dot } => ProtocolRuleMapBody::Empty {
            explicit_dot: *explicit_dot,
        },
        ProtocolRuleMapBody::Items { items, remainder } => ProtocolRuleMapBody::Items {
            items: items
                .iter()
                .map(|item| {
                    Ok(krs_ir::ProtocolRuleMapItem {
                        key_key: item.key_key.clone(),
                        key: resolve_term(&item.key, declarations, builtins)?,
                        value_key: item.value_key.clone(),
                        value: resolve_term(&item.value, declarations, builtins)?,
                    })
                })
                .collect::<Result<Vec<_>, CollectionError>>()?,
            remainder: resolve_rule_frame(remainder),
        },
        ProtocolRuleMapBody::Update {
            base_key,
            base,
            key_key,
            key,
            value_key,
            value,
        } => ProtocolRuleMapBody::Update {
            base_key: base_key.clone(),
            base: resolve_term(base, declarations, builtins)?,
            key_key: key_key.clone(),
            key: resolve_term(key, declarations, builtins)?,
            value_key: value_key.clone(),
            value: resolve_term(value, declarations, builtins)?,
        },
    })
}

fn resolve_rule_cells(
    cells: &krs_ir::HostRuleCells,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorRuleCells, CollectionError> {
    Ok(krs_ir::ProtocolRuleCells {
        key: cells.key.clone(),
        cells: cells
            .cells
            .iter()
            .map(|cell| {
                Ok(krs_ir::ProtocolRuleCell {
                    field: resolve_cell_reference(&cell.field, cell_fields)?,
                    wrapper_key: cell.wrapper_key.clone(),
                    wrapper: cell.wrapper,
                    value: resolve_rule_state(&cell.value, declarations, builtins)?,
                })
            })
            .collect::<Result<Vec<_>, CollectionError>>()?,
        remainder: resolve_rule_frame(&cells.remainder),
    })
}

fn resolve_configuration_rule(
    rule: &krs_ir::HostConfigurationRule,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<krs_ir::DescriptorConfigurationRule, CollectionError> {
    Ok(krs_ir::DescriptorConfigurationRule {
        sentence_kind: rule.sentence_kind,
        label: rule.label.clone(),
        priority: rule.priority.clone(),
        requires: rule
            .requires
            .as_ref()
            .map(|condition| {
                Ok(krs_ir::DescriptorRuleCondition {
                    key: condition.key.clone(),
                    term: resolve_term(&condition.term, declarations, builtins)?,
                })
            })
            .transpose()?,
        claim: rule
            .claim
            .as_ref()
            .map(|claim| {
                Ok(krs_ir::DescriptorClaim {
                    declaration_key: claim.declaration_key.clone(),
                    modality_key: claim.modality_key.clone(),
                    modality: claim.modality,
                    circularity_key: claim.circularity_key.clone(),
                    universals: resolve_claim_binders(&claim.universals, declarations, builtins)?,
                    existentials: resolve_claim_binders(
                        &claim.existentials,
                        declarations,
                        builtins,
                    )?,
                    ensures: claim
                        .ensures
                        .as_ref()
                        .map(|condition| {
                            Ok(krs_ir::DescriptorRuleCondition {
                                key: condition.key.clone(),
                                term: resolve_term(&condition.term, declarations, builtins)?,
                            })
                        })
                        .transpose()?,
                    or_bool_keys: claim.or_bool_keys.clone(),
                })
            })
            .transpose()?,
        pattern_key: rule.pattern_key.clone(),
        subject_configuration: resolve_configuration_reference(
            &rule.subject_configuration,
            declarations,
        )?,
        result_key: rule.result_key.clone(),
        result_configuration: resolve_configuration_reference(
            &rule.result_configuration,
            declarations,
        )?,
        bindings: rule
            .bindings
            .iter()
            .map(|binding| {
                Ok(krs_ir::ProtocolRuleBinding {
                    name: binding.name.clone(),
                    kind: match &binding.kind {
                        krs_ir::ProtocolRuleBindingKind::Term { sort } => {
                            krs_ir::ProtocolRuleBindingKind::Term {
                                sort: resolve_sort_reference(sort, declarations, builtins)?,
                            }
                        }
                        krs_ir::ProtocolRuleBindingKind::KSequenceFrame => {
                            krs_ir::ProtocolRuleBindingKind::KSequenceFrame
                        }
                        krs_ir::ProtocolRuleBindingKind::MapFrame => {
                            krs_ir::ProtocolRuleBindingKind::MapFrame
                        }
                        krs_ir::ProtocolRuleBindingKind::ConfigurationFrame => {
                            krs_ir::ProtocolRuleBindingKind::ConfigurationFrame
                        }
                    },
                })
            })
            .collect::<Result<Vec<_>, CollectionError>>()?,
        subject: resolve_rule_cells(&rule.subject, declarations, cell_fields, builtins)?,
        result: resolve_rule_cells(&rule.result, declarations, cell_fields, builtins)?,
    })
}

fn resolve_claim_binders(
    binders: &[krs_ir::HostClaimBinder],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<Vec<krs_ir::DescriptorClaimBinder>, CollectionError> {
    binders
        .iter()
        .map(|binder| {
            Ok(krs_ir::DescriptorClaimBinder {
                declaration_key: binder.declaration_key.clone(),
                name_key: binder.name_key.clone(),
                name: binder.name.clone(),
                sort: resolve_sort_reference(&binder.sort, declarations, builtins)?,
            })
        })
        .collect()
}

fn resolve_nominal_reference(
    reference: &HostTypeReference,
    expected: ItemKind,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<StableItemId, CollectionError> {
    resolve_declared_identity(
        HostApplicationIdentity::Nominal(reference.key.resolve()),
        &reference.authored_path,
        expected,
        declarations,
    )
}

fn resolve_constructor_field_sort(
    reference: &HostTypeReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<DescriptorSortRef, CollectionError> {
    let type_id = reference.key.resolve();
    if let Some((id, kind)) = declarations.get(&HostApplicationIdentity::Nominal(type_id)) {
        if *kind != ItemKind::Sort {
            return Err(CollectionError::new(
                CollectionErrorKind::ReferenceKindMismatch,
                format!(
                    "Rust path `{}` resolves to `{}`, but a sort is required",
                    reference.authored_path, id
                ),
            ));
        }
        Ok(DescriptorSortRef::Declared(id.clone()))
    } else if let Some(sort) = builtins.and_then(|registry| registry.resolve_sort(type_id)) {
        Ok(DescriptorSortRef::Builtin(sort))
    } else {
        Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{}` resolves to neither a selected sort nor a registered builtin sort",
                reference.authored_path
            ),
        ))
    }
}

fn resolve_declared_identity(
    identity: HostApplicationIdentity,
    authored_path: &str,
    expected: ItemKind,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<StableItemId, CollectionError> {
    let Some((id, kind)) = declarations.get(&identity) else {
        return Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{authored_path}` does not resolve to a selected KRS type declaration"
            ),
        ));
    };
    if *kind != expected {
        return Err(CollectionError::new(
            CollectionErrorKind::ReferenceKindMismatch,
            format!("Rust path `{authored_path}` resolves to `{id}`, but a {expected} is required"),
        ));
    }
    Ok(id.clone())
}

fn resolve_sort_reference(
    reference: &HostSortReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<DescriptorSortReference, CollectionError> {
    let type_id = reference.target.key.resolve();
    let sort = if let Some((id, kind)) =
        declarations.get(&HostApplicationIdentity::Nominal(type_id))
    {
        if *kind != ItemKind::Sort {
            return Err(CollectionError::new(
                CollectionErrorKind::ReferenceKindMismatch,
                format!(
                    "Rust path `{}` resolves to `{}`, but a sort is required",
                    reference.target.authored_path, id
                ),
            ));
        }
        DescriptorSortRef::Declared(id.clone())
    } else if let Some(sort) = builtins.and_then(|registry| registry.resolve_sort(type_id)) {
        DescriptorSortRef::Builtin(sort)
    } else {
        return Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{}` resolves to neither a selected sort nor a registered builtin sort",
                reference.target.authored_path
            ),
        ));
    };
    Ok(DescriptorSortReference {
        key: reference.key.clone(),
        sort,
    })
}

fn resolve_application_reference(
    reference: &krs_ir::HostApplicationReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
    allow_builtin: bool,
) -> Result<DescriptorApplicationReference, CollectionError> {
    let identity = reference.target.resolve();
    let application = if let Some((id, kind)) = declarations.get(&identity) {
        if *kind != ItemKind::Constructor {
            return Err(CollectionError::new(
                CollectionErrorKind::ReferenceKindMismatch,
                format!(
                    "Rust path `{}` resolves to `{}`, but a constructor is required",
                    reference.target.authored_path(),
                    id
                ),
            ));
        }
        DescriptorApplicationRef::Declared(id.clone())
    } else if allow_builtin {
        let HostApplicationIdentity::Nominal(type_id) = identity else {
            return Err(CollectionError::new(
                CollectionErrorKind::UnresolvedTypeReference,
                format!(
                    "enum-variant path `{}` has no selected constructor declaration",
                    reference.target.authored_path()
                ),
            ));
        };
        if let Some(operation) = builtins.and_then(|registry| registry.resolve_operation(type_id)) {
            DescriptorApplicationRef::Builtin(operation)
        } else if let Some(operation) =
            builtins.and_then(|registry| registry.resolve_map_operation(type_id))
        {
            DescriptorApplicationRef::Map(operation)
        } else if let Some(operation) =
            builtins.and_then(|registry| registry.resolve_list_operation(type_id))
        {
            DescriptorApplicationRef::List(operation)
        } else if let Some(operation) =
            builtins.and_then(|registry| registry.resolve_set_operation(type_id))
        {
            DescriptorApplicationRef::Set(operation)
        } else {
            return Err(CollectionError::new(
                CollectionErrorKind::UnresolvedTypeReference,
                format!(
                    "Rust path `{}` resolves to neither a selected constructor nor a registered term operation",
                    reference.target.authored_path()
                ),
            ));
        }
    } else {
        return Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{}` does not resolve to a selected constructor declaration",
                reference.target.authored_path()
            ),
        ));
    };
    Ok(DescriptorApplicationReference {
        key: reference.key.clone(),
        application,
    })
}

fn resolve_grammar_owner(
    owner: &HostProductionOwner,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<DescriptorProductionOwner, CollectionError> {
    Ok(match owner {
        HostProductionOwner::Constructor { constructor } => {
            DescriptorProductionOwner::Constructor {
                constructor: resolve_application_reference(
                    constructor,
                    declarations,
                    builtins,
                    false,
                )?,
            }
        }
        HostProductionOwner::TokenSort { sort } => DescriptorProductionOwner::TokenSort {
            sort: resolve_sort_reference(sort, declarations, builtins)?,
        },
        HostProductionOwner::BracketSort { sort } => DescriptorProductionOwner::BracketSort {
            sort: resolve_sort_reference(sort, declarations, builtins)?,
        },
    })
}

fn resolve_grammar_items(
    items: &[HostProductionItem],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<Vec<DescriptorProductionItem>, CollectionError> {
    items
        .iter()
        .map(|item| {
            Ok(match item {
                HostProductionItem::Terminal { key, text } => DescriptorProductionItem::Terminal {
                    key: key.clone(),
                    text: text.clone(),
                },
                HostProductionItem::NonTerminal {
                    key,
                    field_key,
                    declaration_key,
                    field,
                    sort,
                } => DescriptorProductionItem::NonTerminal {
                    key: key.clone(),
                    field_key: field_key.clone(),
                    declaration_key: declaration_key.clone(),
                    field: field.clone(),
                    sort: Box::new(resolve_sort_reference(sort, declarations, builtins)?),
                },
                HostProductionItem::RegexTerminal {
                    key,
                    precede_regex,
                    regex,
                    follow_regex,
                } => DescriptorProductionItem::RegexTerminal {
                    key: key.clone(),
                    precede_regex: precede_regex.clone(),
                    regex: regex.clone(),
                    follow_regex: follow_regex.clone(),
                },
            })
        })
        .collect::<Result<Vec<_>, CollectionError>>()
}

fn resolve_grammar_attributes(
    attributes: &[HostProductionAttribute],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    context_aliases: &HashMap<HostItemId, StableItemId>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<Vec<DescriptorProductionAttribute>, CollectionError> {
    attributes
        .iter()
        .map(|attribute| {
            resolve_grammar_attribute(attribute, declarations, context_aliases, builtins)
        })
        .collect::<Result<Vec<_>, CollectionError>>()
}

fn resolve_grammar_attribute(
    attribute: &HostProductionAttribute,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    context_aliases: &HashMap<HostItemId, StableItemId>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<DescriptorProductionAttribute, CollectionError> {
    Ok(match attribute {
        HostProductionAttribute::Documentation { key, text } => {
            DescriptorProductionAttribute::Documentation {
                key: key.clone(),
                text: text.clone(),
            }
        }
        HostProductionAttribute::Function { key } => {
            DescriptorProductionAttribute::Function { key: key.clone() }
        }
        HostProductionAttribute::Total { key } => {
            DescriptorProductionAttribute::Total { key: key.clone() }
        }
        HostProductionAttribute::Hook { key, operation } => DescriptorProductionAttribute::Hook {
            key: key.clone(),
            operation: *operation,
        },
        HostProductionAttribute::Alias { key } => {
            DescriptorProductionAttribute::Alias { key: key.clone() }
        }
        HostProductionAttribute::Token {
            key,
            lexical_precedence,
        } => DescriptorProductionAttribute::Token {
            key: key.clone(),
            lexical_precedence: lexical_precedence.clone(),
        },
        HostProductionAttribute::Group { reference } => DescriptorProductionAttribute::Group {
            reference: reference.clone(),
        },
        HostProductionAttribute::Bracket { key } => {
            DescriptorProductionAttribute::Bracket { key: key.clone() }
        }
        HostProductionAttribute::Avoid { key } => {
            DescriptorProductionAttribute::Avoid { key: key.clone() }
        }
        HostProductionAttribute::Format { key, fragments } => {
            DescriptorProductionAttribute::Format {
                key: key.clone(),
                fragments: fragments.clone(),
            }
        }
        HostProductionAttribute::Strictness {
            key,
            kind,
            using,
            fields,
            result_sort,
        } => DescriptorProductionAttribute::Strictness {
            key: key.clone(),
            kind: *kind,
            using: using
                .as_ref()
                .map(|using| {
                    let alias = context_aliases.get(&using.alias).cloned().ok_or_else(|| {
                        CollectionError::new(
                            CollectionErrorKind::UnresolvedTypeReference,
                            format!("unknown context alias `{}`", using.alias.item_name()),
                        )
                    })?;
                    Ok(krs_ir::DescriptorContextAliasReference {
                        key: using.key.clone(),
                        alias,
                    })
                })
                .transpose()?,
            fields: fields.clone(),
            result_sort: Box::new(resolve_sort_reference(result_sort, declarations, builtins)?),
        },
    })
}

fn resolve_grammar(
    grammar: &HostGrammarDescriptor,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    context_aliases: &HashMap<HostItemId, StableItemId>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<GrammarDescriptor, CollectionError> {
    Ok(match grammar {
        HostGrammarDescriptor::Production(production) => {
            let owner = resolve_grammar_owner(&production.owner, declarations, builtins)?;
            let items = resolve_grammar_items(&production.items, declarations, builtins)?;
            let attributes = resolve_grammar_attributes(
                &production.attributes,
                declarations,
                context_aliases,
                builtins,
            )?;
            GrammarDescriptor::Production(DescriptorProduction {
                key: production.key.clone(),
                template_key: production.template_key.clone(),
                owner,
                result_sort: resolve_sort_reference(
                    &production.result_sort,
                    declarations,
                    builtins,
                )?,
                items,
                attributes,
            })
        }
        HostGrammarDescriptor::Subsort {
            key,
            subsort,
            supersort,
        } => GrammarDescriptor::Subsort {
            key: key.clone(),
            subsort: resolve_sort_reference(subsort, declarations, builtins)?,
            supersort: resolve_sort_reference(supersort, declarations, builtins)?,
        },
        HostGrammarDescriptor::Precedence { key, chains } => GrammarDescriptor::Precedence {
            key: key.clone(),
            chains: chains.clone(),
        },
        HostGrammarDescriptor::Associativity { key, sentences } => {
            GrammarDescriptor::Associativity {
                key: key.clone(),
                sentences: sentences.clone(),
            }
        }
    })
}

fn resolve_structured_rule(
    rule: &HostStructuredRuleDescriptor,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<StructuredRuleDescriptor, CollectionError> {
    Ok(StructuredRuleDescriptor {
        sentence_kind: rule.sentence_kind,
        label: rule.label.clone(),
        requires: rule
            .requires
            .as_ref()
            .map(|condition| {
                Ok(krs_ir::DescriptorRuleCondition {
                    key: condition.key.clone(),
                    term: resolve_term(&condition.term, declarations, builtins)?,
                })
            })
            .transpose()?,
        priority: rule.priority.clone(),
        simplification: rule.simplification.clone(),
        pattern_key: rule.pattern_key.clone(),
        result_key: rule.result_key.clone(),
        subject_sort: resolve_sort_reference(&rule.subject_sort, declarations, builtins)?,
        result_sort: resolve_sort_reference(&rule.result_sort, declarations, builtins)?,
        bindings: rule.bindings.clone(),
        subject: resolve_term(&rule.subject, declarations, builtins)?,
        result: resolve_term(&rule.result, declarations, builtins)?,
    })
}

fn resolve_term(
    term: &HostTerm,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<DescriptorTerm, CollectionError> {
    Ok(match term {
        HostTerm::Variable {
            key,
            path_key,
            name,
        } => DescriptorTerm::Variable {
            key: key.clone(),
            path_key: path_key.clone(),
            name: name.clone(),
        },
        HostTerm::Application {
            head_class,
            reference,
            path_key,
            arguments,
        } => DescriptorTerm::Application {
            head_class: *head_class,
            reference: resolve_application_reference(reference, declarations, builtins, true)?,
            path_key: path_key.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    Ok(match argument {
                        HostTermArgument::Positional { value } => {
                            DescriptorTermArgument::Positional {
                                value: Box::new(resolve_term(value, declarations, builtins)?),
                            }
                        }
                        HostTermArgument::Named { key, field, value } => {
                            DescriptorTermArgument::Named {
                                key: key.clone(),
                                field: field.clone(),
                                value: Box::new(resolve_term(value, declarations, builtins)?),
                            }
                        }
                    })
                })
                .collect::<Result<Vec<_>, CollectionError>>()?,
        },
        HostTerm::Literal { key, literal } => DescriptorTerm::Literal {
            key: key.clone(),
            literal: literal.clone(),
        },
        HostTerm::Wildcard { key } => DescriptorTerm::Wildcard { key: key.clone() },
        HostTerm::BuiltinToken { key, sort, value } => DescriptorTerm::BuiltinToken {
            key: key.clone(),
            sort: *sort,
            value: value.clone(),
        },
        HostTerm::Anonymous {
            key,
            sort,
            spelling,
        } => DescriptorTerm::Anonymous {
            key: key.clone(),
            sort: resolve_sort_reference(sort, declarations, builtins)?,
            spelling: spelling.clone(),
        },
        HostTerm::OrBool { key, arguments } => DescriptorTerm::OrBool {
            key: key.clone(),
            arguments: arguments
                .iter()
                .map(|argument| resolve_term(argument, declarations, builtins))
                .collect::<Result<Vec<_>, _>>()?,
        },
        HostTerm::Cell {
            key,
            declaration,
            fields,
        } => DescriptorTerm::Cell {
            key: key.clone(),
            declaration: resolve_declared_identity(
                HostApplicationIdentity::Nominal(declaration.key.resolve()),
                &declaration.authored_path,
                ItemKind::Cell,
                declarations,
            )?,
            fields: fields
                .iter()
                .map(|field| {
                    Ok(krs_ir::DescriptorCellTermField {
                        key: field.key.clone(),
                        field: field.field.clone(),
                        value: Box::new(resolve_term(&field.value, declarations, builtins)?),
                    })
                })
                .collect::<Result<Vec<_>, CollectionError>>()?,
        },
    })
}

#[cfg(test)]
mod tests {
    use std::any::TypeId;

    use super::*;
    use krs_ir::{
        BuiltinSort, HostApplicationReference, HostApplicationTarget,
        HostBuiltinOperationRegistration, HostBuiltinSortRegistration, HostEnumVariantReference,
        HostListOperationRegistration, HostMapOperationRegistration, HostSetOperationRegistration,
        HostTypeKey, ListOperation, MapOperation, PackageId, ProvenanceKey, SetOperation,
    };

    struct Boolean;
    struct OtherBoolean;
    struct FalseMarker;
    struct SortK;
    struct SortInt;
    struct SortBool;
    struct SortMap;
    struct SortId;
    struct SortBytes;
    struct SortString;
    struct SortList;
    struct SortSet;
    struct Op0;
    struct Op1;
    struct Op2;
    struct Op3;
    struct Op4;
    struct Op5;
    struct Op6;
    struct Op7;
    struct Op8;
    struct Op9;
    struct Op10;
    struct Op11;
    struct Op12;
    struct Op13;
    struct Op14;
    struct Op15;
    struct Op16;
    struct Op17;
    struct Op18;
    struct Op19;
    struct Op20;
    struct Op21;
    struct Op22;
    struct Op23;
    struct Op24;
    struct Op25;
    struct Op26;
    struct Op27;
    struct Op28;
    struct MapUpdateOp;
    struct MapGetOp;
    struct MapInKeysOp;
    struct ListOp0;
    struct ListOp1;
    struct ListOp2;
    struct ListOp3;
    struct ListOp4;
    struct ListOp5;
    struct ListOp6;
    struct ListOp7;
    struct ListOp8;
    struct SetOp0;
    struct SetOp1;
    struct SetOp2;
    struct SetOp3;
    struct SetOp4;

    fn marker_key<T: 'static>() -> TypeId {
        TypeId::of::<T>()
    }

    fn registry() -> HostBuiltinRegistry {
        let sort_keys = [
            HostTypeKey(marker_key::<SortK>),
            HostTypeKey(marker_key::<SortInt>),
            HostTypeKey(marker_key::<SortBool>),
            HostTypeKey(marker_key::<SortMap>),
            HostTypeKey(marker_key::<SortId>),
            HostTypeKey(marker_key::<SortBytes>),
            HostTypeKey(marker_key::<SortString>),
            HostTypeKey(marker_key::<SortList>),
            HostTypeKey(marker_key::<SortSet>),
        ];
        let operation_keys = [
            HostTypeKey(marker_key::<Op0>),
            HostTypeKey(marker_key::<Op1>),
            HostTypeKey(marker_key::<Op2>),
            HostTypeKey(marker_key::<Op3>),
            HostTypeKey(marker_key::<Op4>),
            HostTypeKey(marker_key::<Op5>),
            HostTypeKey(marker_key::<Op6>),
            HostTypeKey(marker_key::<Op7>),
            HostTypeKey(marker_key::<Op8>),
            HostTypeKey(marker_key::<Op9>),
            HostTypeKey(marker_key::<Op10>),
            HostTypeKey(marker_key::<Op11>),
            HostTypeKey(marker_key::<Op12>),
            HostTypeKey(marker_key::<Op13>),
            HostTypeKey(marker_key::<Op14>),
            HostTypeKey(marker_key::<Op15>),
            HostTypeKey(marker_key::<Op16>),
            HostTypeKey(marker_key::<Op17>),
            HostTypeKey(marker_key::<Op18>),
            HostTypeKey(marker_key::<Op19>),
            HostTypeKey(marker_key::<Op20>),
            HostTypeKey(marker_key::<Op21>),
            HostTypeKey(marker_key::<Op22>),
            HostTypeKey(marker_key::<Op23>),
            HostTypeKey(marker_key::<Op24>),
            HostTypeKey(marker_key::<Op25>),
            HostTypeKey(marker_key::<Op26>),
            HostTypeKey(marker_key::<Op27>),
            HostTypeKey(marker_key::<Op28>),
        ];
        HostBuiltinRegistry {
            sorts: BuiltinSort::ALL
                .into_iter()
                .zip(sort_keys)
                .map(|(sort, target)| HostBuiltinSortRegistration { sort, target })
                .collect(),
            operations: krs_ir::BuiltinOperation::ALL
                .into_iter()
                .zip(operation_keys)
                .map(|(operation, target)| HostBuiltinOperationRegistration { operation, target })
                .collect(),
            map_operations: MapOperation::TERM_APPLICATIONS
                .into_iter()
                .zip([
                    HostTypeKey(marker_key::<MapUpdateOp>),
                    HostTypeKey(marker_key::<MapGetOp>),
                    HostTypeKey(marker_key::<MapInKeysOp>),
                ])
                .map(|(operation, target)| HostMapOperationRegistration { operation, target })
                .collect(),
            list_operations: ListOperation::TERM_APPLICATIONS
                .into_iter()
                .zip([
                    HostTypeKey(marker_key::<ListOp0>),
                    HostTypeKey(marker_key::<ListOp1>),
                    HostTypeKey(marker_key::<ListOp2>),
                    HostTypeKey(marker_key::<ListOp3>),
                    HostTypeKey(marker_key::<ListOp4>),
                    HostTypeKey(marker_key::<ListOp5>),
                    HostTypeKey(marker_key::<ListOp6>),
                    HostTypeKey(marker_key::<ListOp7>),
                    HostTypeKey(marker_key::<ListOp8>),
                ])
                .map(|(operation, target)| HostListOperationRegistration { operation, target })
                .collect(),
            set_operations: SetOperation::TERM_APPLICATIONS
                .into_iter()
                .zip([
                    HostTypeKey(marker_key::<SetOp0>),
                    HostTypeKey(marker_key::<SetOp1>),
                    HostTypeKey(marker_key::<SetOp2>),
                    HostTypeKey(marker_key::<SetOp3>),
                    HostTypeKey(marker_key::<SetOp4>),
                ])
                .map(|(operation, target)| HostSetOperationRegistration { operation, target })
                .collect(),
        }
    }

    fn boolean_key() -> TypeId {
        TypeId::of::<Boolean>()
    }

    fn other_boolean_key() -> TypeId {
        TypeId::of::<OtherBoolean>()
    }

    fn false_key() -> TypeId {
        TypeId::of::<FalseMarker>()
    }

    fn test_id(name: &str) -> StableItemId {
        StableItemId::new(
            PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap(),
            ["model"],
            name,
            ItemKind::Constructor,
            "enum:Boolean",
        )
        .unwrap()
    }

    #[test]
    fn enum_variant_join_uses_owner_and_marker_identity_not_alias_spelling() {
        let false_id = test_id("False");
        let identity = HostApplicationIdentity::EnumVariant {
            enum_type: boolean_key(),
            variant: false_key(),
        };
        let declarations = HashMap::from([(identity, (false_id.clone(), ItemKind::Constructor))]);
        let target = HostEnumVariantReference::new(
            HostTypeReference {
                key: HostTypeKey(boolean_key),
                authored_path: "Alias".into(),
            },
            HostTypeKey(false_key),
            "Alias::RenamedFalse",
        )
        .unwrap();
        let resolved = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightReference, 0),
                target: HostApplicationTarget::EnumVariant(target),
            },
            &declarations,
            None,
            false,
        )
        .unwrap();
        assert_eq!(
            resolved.application,
            DescriptorApplicationRef::Declared(false_id)
        );

        let wrong_owner = HostEnumVariantReference::new(
            HostTypeReference {
                key: HostTypeKey(other_boolean_key),
                authored_path: "OtherAlias".into(),
            },
            HostTypeKey(false_key),
            "OtherAlias::RenamedFalse",
        )
        .unwrap();
        let error = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightReference, 0),
                target: HostApplicationTarget::EnumVariant(wrong_owner),
            },
            &declarations,
            None,
            false,
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::UnresolvedTypeReference);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Exhaustively verifies sort and operation alias identity.
    fn complete_builtin_registry_joins_aliases_by_exact_type_identity() {
        let registry = registry();
        registry.validate().unwrap();
        let sort = resolve_sort_reference(
            &HostSortReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 0),
                target: HostTypeReference {
                    key: HostTypeKey(marker_key::<SortInt>),
                    authored_path: "RenamedInt".into(),
                },
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap();
        assert_eq!(sort.sort, DescriptorSortRef::Builtin(BuiltinSort::Int));

        let bytes_sort = resolve_sort_reference(
            &HostSortReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 1),
                target: HostTypeReference {
                    key: HostTypeKey(marker_key::<SortBytes>),
                    authored_path: "RenamedBytes".into(),
                },
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap();
        assert_eq!(
            bytes_sort.sort,
            DescriptorSortRef::Builtin(BuiltinSort::Bytes)
        );

        let application = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightApplicationHead, 0),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: HostTypeKey(marker_key::<Op0>),
                    authored_path: "RenamedAdd".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap();
        assert_eq!(
            application.application,
            DescriptorApplicationRef::Builtin(krs_ir::BuiltinOperation::IntAdd)
        );

        let integer_modulus = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightApplicationHead, 1),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: HostTypeKey(marker_key::<Op4>),
                    authored_path: "RenamedModulus".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap();
        assert_eq!(
            integer_modulus.application,
            DescriptorApplicationRef::Builtin(krs_ir::BuiltinOperation::IntMod)
        );

        let map_update = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightApplicationHead, 0),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: HostTypeKey(marker_key::<MapUpdateOp>),
                    authored_path: "persistent_update".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap();
        assert_eq!(
            map_update.application,
            DescriptorApplicationRef::Map(MapOperation::Update)
        );

        let list_get = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightApplicationHead, 1),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: HostTypeKey(marker_key::<ListOp3>),
                    authored_path: "indexed_lookup".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap();
        assert_eq!(
            list_get.application,
            DescriptorApplicationRef::List(ListOperation::Get)
        );

        let lookalike = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightApplicationHead, 0),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: HostTypeKey(marker_key::<OtherBoolean>),
                    authored_path: "map::update".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap_err();
        assert_eq!(
            lookalike.kind(),
            CollectionErrorKind::UnresolvedTypeReference
        );
    }

    #[test]
    fn constructor_field_sort_preserves_builtin_identity_and_rejects_lookalikes() {
        let registry = registry();
        let builtin = resolve_constructor_field_sort(
            &HostTypeReference {
                key: HostTypeKey(marker_key::<SortId>),
                authored_path: "RenamedId".into(),
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap();
        assert_eq!(builtin, DescriptorSortRef::Builtin(BuiltinSort::Id));

        let error = resolve_constructor_field_sort(
            &HostTypeReference {
                key: HostTypeKey(marker_key::<OtherBoolean>),
                authored_path: "BuiltinLookingButUnregistered".into(),
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::UnresolvedTypeReference);
        assert!(
            error
                .to_string()
                .contains("neither a selected sort nor a registered builtin sort")
        );
    }
}
