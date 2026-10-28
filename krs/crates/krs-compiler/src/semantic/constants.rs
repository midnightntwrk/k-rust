//! Named constants (`#[k::constant]`): substitution at every use, and the
//! check of each constant's value.
//!
//! A constant is a name for a ground constructor term, so replacing each use
//! by the term preserves the meaning of every sentence. The substitution runs
//! before any other analysis: sort inference, the overlap and coverage
//! checks, and emission see the value as if it were written at the use, and
//! no constant reaches the semantic IR. Each substituted node is keyed
//! [`ProvenanceRole::InlinedConstant`] and has the use's origin, so a
//! diagnostic about it points at the name the author wrote.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    Descriptor, DescriptorApplicationHeadClass, DescriptorApplicationRef, DescriptorIndex,
    DescriptorNodeOrigin, DescriptorPayload, DescriptorStage, DescriptorTerm, ItemKind,
    OriginFrame, OriginStack, ProvenanceKey, ProvenanceRole, RefMap, StableItemId,
    TransformationOriginKind,
};

use krs_ir_levels::SemanticSortRef;

use super::catalog::{ProductionSignature, semantic_sort_ref};
use super::error::DescriptorLoweringError;
use super::infer::StructuredTermBuilder;

/// The bundle's descriptors with every use of a constant substituted, and
/// the constants themselves, with the constants they use substituted.
pub(super) struct Inlined<'a> {
    /// Every descriptor that is not a constant, in the input order.
    pub(super) descriptors: Vec<Cow<'a, Descriptor>>,
    /// Every constant.
    pub(super) constants: Vec<Descriptor>,
}

/// Substitutes every constant's value at its uses.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::InvalidConstant`] for a cycle of
/// constants or a use that passes a constant arguments.
pub(super) fn inline_constants<'a>(
    descriptors: &[&'a Descriptor],
) -> Result<Inlined<'a>, DescriptorLoweringError> {
    let constants = descriptors
        .iter()
        .filter(|descriptor| matches!(descriptor.payload(), DescriptorPayload::Constant(_)))
        .map(|descriptor| (descriptor.id().clone(), *descriptor))
        .collect::<BTreeMap<_, _>>();
    if constants.is_empty() {
        return Ok(Inlined {
            descriptors: descriptors
                .iter()
                .map(|descriptor| Cow::Borrowed(*descriptor))
                .collect(),
            constants: Vec::new(),
        });
    }
    let mut expanded = BTreeMap::new();
    for id in constants.keys() {
        expand_constant(id, &constants, &mut expanded, &mut Vec::new())?;
    }
    let values = expanded
        .iter()
        .map(|(id, descriptor): (&StableItemId, &Descriptor)| {
            let DescriptorPayload::Constant(constant) = descriptor.payload() else {
                unreachable!("only constants are expanded");
            };
            (id.clone(), constant.value.clone())
        })
        .collect::<BTreeMap<_, _>>();
    let mut inlined = Vec::with_capacity(descriptors.len());
    for descriptor in descriptors {
        if constants.contains_key(descriptor.id()) {
            continue;
        }
        inlined.push(match substitute(descriptor, &values)? {
            Some(descriptor) => Cow::Owned(descriptor),
            None => Cow::Borrowed(*descriptor),
        });
    }
    Ok(Inlined {
        descriptors: inlined,
        constants: expanded.into_values().collect(),
    })
}

/// Expands the constants `id` uses, then `id` itself, depth first; `path`
/// holds the constants being expanded, to report a cycle.
fn expand_constant(
    id: &StableItemId,
    constants: &BTreeMap<StableItemId, &Descriptor>,
    expanded: &mut BTreeMap<StableItemId, Descriptor>,
    path: &mut Vec<StableItemId>,
) -> Result<(), DescriptorLoweringError> {
    if expanded.contains_key(id) {
        return Ok(());
    }
    let descriptor =
        constants
            .get(id)
            .ok_or_else(|| DescriptorLoweringError::DanglingReference {
                id: Box::new(id.clone()),
                range: None,
            })?;
    if let Some(start) = path.iter().position(|entry| entry == id) {
        let cycle = path[start..]
            .iter()
            .chain([id])
            .map(|entry| format!("`{}`", entry.item_name()))
            .collect::<Vec<_>>()
            .join(" -> ");
        return Err(DescriptorLoweringError::InvalidConstant {
            reason: format!(
                "constants refer to each other in a cycle ({cycle}), so none of them names a term"
            ),
            range: primary_range(descriptor),
            item: Some(Box::new(descriptor.id().clone())),
        });
    }
    let DescriptorPayload::Constant(constant) = descriptor.payload() else {
        unreachable!("only constants are expanded");
    };
    let mut used = BTreeSet::new();
    constant_uses(&constant.value, &mut used);
    path.push(id.clone());
    for dependency in &used {
        expand_constant(dependency, constants, expanded, path)?;
    }
    path.pop();
    let values = used
        .iter()
        .map(|dependency| {
            let DescriptorPayload::Constant(constant) = expanded[dependency].payload() else {
                unreachable!("only constants are expanded");
            };
            (dependency.clone(), constant.value.clone())
        })
        .collect::<BTreeMap<_, _>>();
    let descriptor = substitute(descriptor, &values)?.unwrap_or_else(|| (*descriptor).clone());
    expanded.insert(id.clone(), descriptor);
    Ok(())
}

/// The constants a constant's value uses directly.
fn constant_uses(term: &DescriptorTerm, output: &mut BTreeSet<StableItemId>) {
    if let DescriptorTerm::Application {
        reference,
        arguments,
        ..
    } = term
    {
        if let DescriptorApplicationRef::Declared(id) = &reference.application
            && id.item_kind() == ItemKind::Constant
        {
            output.insert(id.clone());
        }
        for argument in arguments {
            let (krs_ir::TermArgumentRef::Positional { value }
            | krs_ir::TermArgumentRef::Named { value, .. }) = argument;
            constant_uses(value, output);
        }
    }
}

/// `descriptor` with `values` substituted at every use, or `None` when it
/// uses no constant; a failure is about `descriptor`.
fn substitute(
    descriptor: &Descriptor,
    values: &BTreeMap<StableItemId, DescriptorTerm>,
) -> Result<Option<Descriptor>, DescriptorLoweringError> {
    substitute_uses(descriptor, values).map_err(|error| error.within(descriptor.id(), None))
}

fn substitute_uses(
    descriptor: &Descriptor,
    values: &BTreeMap<StableItemId, DescriptorTerm>,
) -> Result<Option<Descriptor>, DescriptorLoweringError> {
    let mut substitution = Substitution {
        descriptor,
        values,
        origins: Vec::new(),
    };
    let payload = descriptor
        .payload()
        .clone()
        .try_map_refs(&mut substitution, &mut |head, map| head.try_map_refs(map))?;
    if substitution.origins.is_empty() {
        return Ok(None);
    }
    descriptor
        .with_inlined_constants(payload, substitution.origins)
        .map(Some)
        .map_err(|error| {
            DescriptorLoweringError::unsupported_shape("inlined constant", error.to_string())
        })
}

/// Replaces each use of a constant by its value, keyed afresh.
struct Substitution<'a> {
    descriptor: &'a Descriptor,
    values: &'a BTreeMap<StableItemId, DescriptorTerm>,
    origins: Vec<DescriptorNodeOrigin>,
}

impl Substitution<'_> {
    /// A fresh key for one substituted node, whose origin is `origin`.
    fn key(&mut self, origin: &OriginStack) -> Result<ProvenanceKey, DescriptorLoweringError> {
        let ordinal = u32::try_from(self.origins.len()).map_err(|_| {
            DescriptorLoweringError::unsupported_shape(
                "inlined constant",
                format!("too many substituted nodes in {}", self.descriptor.id()),
            )
        })?;
        let key = ProvenanceRole::InlinedConstant.key(ordinal);
        self.origins
            .push(DescriptorNodeOrigin::new(key.clone(), origin.clone()));
        Ok(key)
    }

    /// `value`, keyed afresh, every node with `origin`.
    fn rekey(
        &mut self,
        value: &DescriptorTerm,
        origin: &OriginStack,
    ) -> Result<DescriptorTerm, DescriptorLoweringError> {
        Ok(match value {
            DescriptorTerm::Literal { literal, .. } => DescriptorTerm::Literal {
                key: self.key(origin)?,
                literal: literal.clone(),
            },
            // `k::id!`, `k::bytes!` and `k::lexeme!` each denote one token of
            // their sort, a ground term as a literal is.
            DescriptorTerm::BuiltinToken { sort, value, .. } => DescriptorTerm::BuiltinToken {
                key: self.key(origin)?,
                sort: *sort,
                value: value.clone(),
            },
            DescriptorTerm::Lexeme { sort, text, .. } => DescriptorTerm::Lexeme {
                key: self.key(origin)?,
                sort: krs_ir::DescriptorSortReference {
                    key: self.key(origin)?,
                    sort: sort.sort.clone(),
                },
                text: text.clone(),
            },
            DescriptorTerm::Application {
                head_class,
                reference,
                arguments,
                instance,
                update,
                ..
            } => {
                // A record update copies fields from a matched alias, and a
                // constant's value is ground: it matches nothing.
                if update.is_some() {
                    return Err(DescriptorLoweringError::unsupported_shape(
                        "constant value",
                        "a constant's value is a literal, a token, or a constructor application",
                    ));
                }
                let reference = krs_ir::DescriptorApplicationReference {
                    key: self.key(origin)?,
                    application: reference.application.clone(),
                };
                let path_key = self.key(origin)?;
                let arguments = match arguments {
                    krs_ir::Arguments::Positional(values) => krs_ir::Arguments::Positional(
                        values
                            .iter()
                            .map(|value| self.rekey(value, origin).map(Box::new))
                            .collect::<Result<_, _>>()?,
                    ),
                    krs_ir::Arguments::Named(values) => krs_ir::Arguments::named(
                        values
                            .iter()
                            .map(|argument| {
                                Ok(krs_ir::NamedTermArgument {
                                    key: self.key(origin)?,
                                    field: argument.field.clone(),
                                    value: Box::new(self.rekey(&argument.value, origin)?),
                                })
                            })
                            .collect::<Result<Vec<_>, DescriptorLoweringError>>()?,
                    ),
                };
                DescriptorTerm::Application {
                    head_class: *head_class,
                    reference,
                    path_key,
                    arguments,
                    instance: instance.clone(),
                    update: None,
                    open: false,
                }
            }
            _ => {
                return Err(DescriptorLoweringError::unsupported_shape(
                    "constant value",
                    "a constant's value is a literal, a token, or a constructor application",
                ));
            }
        })
    }
}

impl RefMap<DescriptorStage, DescriptorStage> for Substitution<'_> {
    type Error = DescriptorLoweringError;

    fn term(&mut self, term: DescriptorTerm) -> Result<DescriptorTerm, Self::Error> {
        let DescriptorTerm::Application {
            head_class,
            reference,
            arguments,
            instance,
            ..
        } = &term
        else {
            return Ok(term);
        };
        let DescriptorApplicationRef::Declared(id) = &reference.application else {
            return Ok(term);
        };
        if id.item_kind() != ItemKind::Constant {
            return Ok(term);
        }
        let use_origin = self.descriptor.provenance().origin_for(&reference.key);
        if *head_class != DescriptorApplicationHeadClass::BareReference
            || !arguments.is_empty()
            || !instance.is_empty()
        {
            return Err(DescriptorLoweringError::InvalidConstant {
                reason: format!(
                    "`{name}` is a constant, a value rather than a function: write `{name}` without arguments",
                    name = id.item_name()
                ),
                range: use_origin
                    .and_then(OriginStack::exact_authored_range)
                    .map(Box::new),
                item: Some(Box::new(self.descriptor.id().clone())),
            });
        }
        let value =
            self.values
                .get(id)
                .ok_or_else(|| DescriptorLoweringError::DanglingReference {
                    id: Box::new(id.clone()),
                    range: None,
                })?;
        let mut origin = use_origin.cloned().ok_or_else(|| {
            DescriptorLoweringError::ParserReferenceDisagreement {
                id: Box::new(self.descriptor.id().clone()),
                detail: format!(
                    "missing parser origin `{}#{}` for a use of constant {id}",
                    reference.key.role().as_str(),
                    reference.key.ordinal()
                ),
                range: None,
            }
        })?;
        origin.push(OriginFrame::Transformation {
            kind: TransformationOriginKind::SemanticIr,
            item: Some(id.clone()),
            label: Some("constant".to_owned()),
        });
        self.rekey(value, &origin)
    }

    fn sort(
        &mut self,
        reference: krs_ir::DescriptorSortReference,
    ) -> Result<krs_ir::DescriptorSortReference, Self::Error> {
        Ok(reference)
    }
    fn application(
        &mut self,
        reference: krs_ir::DescriptorApplicationReference,
    ) -> Result<krs_ir::DescriptorApplicationReference, Self::Error> {
        Ok(reference)
    }
    fn nominal(&mut self, reference: StableItemId) -> Result<StableItemId, Self::Error> {
        Ok(reference)
    }
    fn context_alias(
        &mut self,
        reference: krs_ir::DescriptorContextAliasReference,
    ) -> Result<krs_ir::DescriptorContextAliasReference, Self::Error> {
        Ok(reference)
    }
    fn configuration(
        &mut self,
        reference: krs_ir::DescriptorConfigurationReference,
    ) -> Result<krs_ir::DescriptorConfigurationReference, Self::Error> {
        Ok(reference)
    }
    fn cell(
        &mut self,
        reference: krs_ir::DescriptorCellReference,
    ) -> Result<krs_ir::DescriptorCellReference, Self::Error> {
        Ok(reference)
    }
    fn head_rule_cell(
        &mut self,
        reference: krs_ir::DescriptorCellReference,
    ) -> Result<krs_ir::DescriptorCellReference, Self::Error> {
        Ok(reference)
    }
    fn item(&mut self, reference: StableItemId) -> Result<StableItemId, Self::Error> {
        Ok(reference)
    }
    fn cell_declaration(
        &mut self,
        reference: krs_ir::DescriptorCellDeclarationReference,
    ) -> Result<krs_ir::DescriptorCellDeclarationReference, Self::Error> {
        Ok(reference)
    }
    fn initializer_owner(&mut self, reference: StableItemId) -> Result<StableItemId, Self::Error> {
        Ok(reference)
    }
    fn parent(
        &mut self,
        reference: krs_ir::DescriptorSortParent,
    ) -> Result<krs_ir::DescriptorSortParent, Self::Error> {
        Ok(reference)
    }
    fn constructor_sort(
        &mut self,
        reference: krs_ir::DescriptorSortRef,
    ) -> Result<krs_ir::DescriptorSortRef, Self::Error> {
        Ok(reference)
    }
    fn constructor_field_sort(
        &mut self,
        reference: krs_ir::DescriptorSortReference,
    ) -> Result<krs_ir::DescriptorSortReference, Self::Error> {
        Ok(reference)
    }
}

/// Checks each constant: its value applies constructors only, never a
/// function or a builtin operation, so it is a value that every use can
/// match, and its sort is the declared sort or one below it, so every use
/// is well sorted wherever the declared sort is.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::InvalidConstant`] for an application
/// that is not a constructor's, and the ordinary invalid-term error for a
/// value outside its declared sort.
pub(super) fn check_constants(
    constants: &[Descriptor],
    declarations: &DescriptorIndex<'_>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<(), DescriptorLoweringError> {
    for descriptor in constants {
        check_constant(descriptor, declarations, catalog, sort_parents)
            .map_err(|error| error.within(descriptor.id(), None))?;
    }
    Ok(())
}

/// Checks one constant, as [`check_constants`] does each.
fn check_constant(
    descriptor: &Descriptor,
    declarations: &DescriptorIndex<'_>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<(), DescriptorLoweringError> {
    let DescriptorPayload::Constant(constant) = descriptor.payload() else {
        unreachable!("only constants are checked");
    };
    check_constructors(descriptor, &constant.value, catalog)?;
    let binding_names = BTreeSet::new();
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations,
        k_item_sort: super::rules::framework_k_item_sort(declarations)?,
        sort_parents,
        binding_names: &binding_names,
        pattern_key: None,
        binding_sorts: BTreeMap::new(),
        binding_constraints: BTreeMap::new(),
        constraint_sites: BTreeMap::new(),
        wildcard_offset: 0,
        wildcards: Vec::new(),
        result_wildcards: false,
        locals: super::infer::LocalBinders::default(),
        head_pending: false,
        declared_binders: BTreeMap::new(),
        configuration_variables: BTreeMap::new(),
        subject_keys: BTreeMap::new(),
        operators: super::operators::OperatorInference::default(),
        record_updates: super::record_updates::RecordUpdateState::default(),
        collections: super::infer::CollectionUse::none(),
    };
    builder.infer(
        &constant.value,
        Some(&semantic_sort_ref(&constant.sort.sort)),
        false,
    )?;
    Ok(())
}

fn check_constructors(
    descriptor: &Descriptor,
    term: &DescriptorTerm,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<(), DescriptorLoweringError> {
    let DescriptorTerm::Application {
        reference,
        arguments,
        ..
    } = term
    else {
        return Ok(());
    };
    let applied = match &reference.application {
        DescriptorApplicationRef::Declared(id)
            if catalog
                .get(id)
                .is_some_and(|production| !production.function) =>
        {
            None
        }
        DescriptorApplicationRef::Declared(id) => {
            Some(format!("the function `{}`", id.item_name()))
        }
        _ => Some("a builtin operation".to_owned()),
    };
    if let Some(applied) = applied {
        return Err(DescriptorLoweringError::InvalidConstant {
            reason: format!(
                "the value of constant `{}` applies {applied}; a constant names a ground constructor term, which every use can match, and a function application is evaluated, not matched",
                descriptor.id().item_name()
            ),
            range: descriptor
                .provenance()
                .origin_for(&reference.key)
                .and_then(OriginStack::exact_authored_range)
                .map(Box::new),
            item: Some(Box::new(descriptor.id().clone())),
        });
    }
    for argument in arguments {
        let (krs_ir::TermArgumentRef::Positional { value }
        | krs_ir::TermArgumentRef::Named { value, .. }) = argument;
        check_constructors(descriptor, value, catalog)?;
    }
    Ok(())
}

fn primary_range(descriptor: &Descriptor) -> Option<Box<krs_ir::SourceRange>> {
    descriptor
        .provenance()
        .primary_origin()
        .exact_authored_range()
        .map(Box::new)
}
