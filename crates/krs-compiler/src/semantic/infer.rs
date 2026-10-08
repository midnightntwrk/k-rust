use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, CollectionApplication, CollectionOperandSort,
    CollectionResultSort, Descriptor, DescriptorApplicationRef, DescriptorApplicationReference,
    DescriptorIndex, DescriptorPayload, DescriptorTerm, GeneratedOperation, ListOperation,
    OperationSort, ProductionFieldId, ProtocolCellContent, ProvenanceKey, SemanticId, SortTestKind,
    StableItemId,
};
use krs_ir_levels::{
    ListOperands, MapOperands, SemanticSortRef, SemanticTerm, SemanticVariable, SetOperands,
};

use super::catalog::{
    ProductionSignature, semantic_is_subsort, semantic_sort_closure, semantic_sort_ref,
};
use super::error::DescriptorLoweringError;
use super::origin::{semantic_cell_id, semantic_origin};

pub(super) struct StructuredTermBuilder<'a> {
    pub(super) descriptor: &'a Descriptor,
    pub(super) catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    pub(super) declarations: Option<&'a DescriptorIndex<'a>>,
    pub(super) k_item_sort: Option<SemanticSortRef>,
    pub(super) sort_parents: &'a BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    pub(super) binding_names: &'a BTreeSet<String>,
    pub(super) pattern_key: Option<&'a ProvenanceKey>,
    /// Finalized inferred sorts.
    pub(super) binding_sorts: BTreeMap<String, SemanticSortRef>,
    /// Author-declared and occurrence-derived upper-bound constraints.
    pub(super) binding_constraints: BTreeMap<String, BTreeSet<SemanticSortRef>>,
    pub(super) wildcard_offset: usize,
    pub(super) wildcards: Vec<SemanticVariable>,
}

impl StructuredTermBuilder<'_> {
    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive inference over the closed descriptor term sum."
    )]
    pub(super) fn infer(
        &mut self,
        term: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        match term {
            DescriptorTerm::Variable { name, .. } => {
                if !self.binding_names.contains(name) {
                    return Err(self.invalid_term(format!("unbound variable {name:?}")));
                }
                if let Some(expected) = expected_sort {
                    self.binding_constraints
                        .entry(name.clone())
                        .or_default()
                        .insert(expected.clone());
                }
            }
            DescriptorTerm::Wildcard { .. } => {
                if !subject {
                    return Err(self.invalid_term("wildcard occurs outside the rule subject"));
                }
                if expected_sort.is_none() {
                    return Err(self.invalid_term("wildcard has no expected production-field sort"));
                }
            }
            DescriptorTerm::Literal { literal, .. } => {
                let sort = match literal {
                    krs_ir::DescriptorLiteral::Int(_) => SemanticSortRef::Builtin(BuiltinSort::Int),
                    krs_ir::DescriptorLiteral::Bool(_) => {
                        SemanticSortRef::Builtin(BuiltinSort::Bool)
                    }
                    krs_ir::DescriptorLiteral::String(_) => {
                        SemanticSortRef::Builtin(BuiltinSort::String)
                    }
                    krs_ir::DescriptorLiteral::Float(_) => {
                        SemanticSortRef::Builtin(BuiltinSort::Float)
                    }
                };
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(format!(
                        "literal of sort {sort} is not admissible at sort {expected}"
                    )));
                }
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                ..
            } => self.infer_application(reference, arguments, expected_sort, subject)?,
            DescriptorTerm::BuiltinToken { sort, .. } => {
                let sort = SemanticSortRef::Builtin(*sort);
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term("builtin token has an incompatible sort"));
                }
            }
            DescriptorTerm::Anonymous { sort, .. } => {
                if !subject {
                    return Err(self.invalid_term("anonymous occurrence outside claim subject"));
                }
                let sort = semantic_sort_ref(&sort.sort);
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term("anonymous occurrence has an incompatible sort"));
                }
            }
            DescriptorTerm::Lexeme { key, sort, text } => {
                let sort = self.lexeme_sort(key, sort, text)?;
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(format!(
                        "`k::lexeme!` token {text:?} has sort {sort}, which is not admissible at sort {expected}"
                    )));
                }
            }
            DescriptorTerm::OrBool { arguments, .. } => {
                if arguments.len() < 2 {
                    return Err(self.invalid_term("or_bool requires at least two operands"));
                }
                let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&bool_sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term("or_bool is not admissible at the expected sort"));
                }
                for argument in arguments {
                    self.infer(argument, Some(&bool_sort), subject)?;
                }
            }
            DescriptorTerm::Cell {
                declaration,
                fields,
                ..
            } => {
                let k_item = self.cell_k_item_sort()?;
                let whole_group = expected_sort.is_some_and(|expected| {
                    *expected == SemanticSortRef::Cell(declaration.clone())
                });
                if let Some(expected) = expected_sort
                    && !whole_group
                    && !semantic_is_subsort(&k_item, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(
                        "complete cell term is not admissible at the expected sort",
                    ));
                }
                self.infer_cell_fields(declaration, fields, subject)?;
            }
            DescriptorTerm::SortTest {
                key,
                kind,
                sort,
                operand,
            } => {
                let result = self.sort_test_result(key, *kind, sort, subject)?;
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&result, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(format!(
                        "{} has sort {result}, which is not admissible at sort {expected}",
                        sort_test_macro(*kind)
                    )));
                }
                let operand_sort = self.sort_test_operand_sort(operand);
                self.infer(operand, operand_sort.as_ref(), subject)?;
            }
        }
        Ok(())
    }

    fn infer_application(
        &mut self,
        reference: &DescriptorApplicationReference,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let signature = match &reference.application {
            DescriptorApplicationRef::Declared(id) => {
                self.catalog.get(id).cloned().ok_or_else(|| {
                    self.invalid_term(format!(
                        "declared application {id} has no grammar production"
                    ))
                })?
            }
            DescriptorApplicationRef::Builtin(operation) if operation.is_sort_generic() => {
                return self.infer_generic_builtin(*operation, arguments, expected_sort, subject);
            }
            DescriptorApplicationRef::Builtin(operation) => {
                builtin_production_signature(*operation)
                    .ok_or_else(|| self.sort_generic_builtin(*operation))?
            }
            DescriptorApplicationRef::Map(operation) => {
                self.infer_collection_operation(*operation, arguments, expected_sort, subject)?;
                return Ok(());
            }
            DescriptorApplicationRef::List(operation) => {
                self.infer_collection_operation(*operation, arguments, expected_sort, subject)?;
                return Ok(());
            }
            DescriptorApplicationRef::Set(operation) => {
                self.infer_collection_operation(*operation, arguments, expected_sort, subject)?;
                return Ok(());
            }
        };
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&signature.result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "application result sort {} is not admissible at sort {expected}",
                signature.result_sort
            )));
        }
        let ordered = order_structured_arguments(arguments, &signature.fields, subject)
            .map_err(|detail| self.invalid_term(detail))?;
        for (argument, (_, sort)) in ordered.into_iter().zip(&signature.fields) {
            if let Some(argument) = argument {
                self.infer(argument, Some(sort), subject)?;
            }
        }
        Ok(())
    }

    /// The sort each argument of a sort-generic builtin is inferred and lowered
    /// at: its builtin sort, nothing for `K`, and for `Parameter` the sort
    /// expected of a `Parameter` result, an upper bound of the instance.
    fn generic_argument_sorts(
        &self,
        operation: BuiltinOperation,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Result<Vec<Option<SemanticSortRef>>, DescriptorLoweringError> {
        let spec = operation.spec();
        if arguments.len() != spec.argument_sorts.len() || arguments.is_named() {
            return Err(self.invalid_term(format!(
                "the {operation} operation expects {} positional arguments",
                spec.argument_sorts.len()
            )));
        }
        let parameter_bound = match spec.result_sort {
            OperationSort::Parameter => expected_sort.cloned(),
            OperationSort::Builtin(_) | OperationSort::K => None,
        };
        Ok(spec
            .argument_sorts
            .iter()
            .map(|sort| match sort {
                OperationSort::Builtin(sort) => Some(SemanticSortRef::Builtin(*sort)),
                OperationSort::K => None,
                OperationSort::Parameter => parameter_bound.clone(),
            })
            .collect())
    }

    fn infer_generic_builtin(
        &mut self,
        operation: BuiltinOperation,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        if let OperationSort::Builtin(result) = operation.result_sort()
            && let Some(expected) = expected_sort
            && !semantic_is_subsort(
                &SemanticSortRef::Builtin(result),
                expected,
                self.sort_parents,
            )
        {
            return Err(self.invalid_term(format!(
                "application result sort {} is not admissible at sort {expected}",
                SemanticSortRef::Builtin(result)
            )));
        }
        let sorts = self.generic_argument_sorts(operation, arguments, expected_sort)?;
        for (argument, sort) in arguments.iter().zip(&sorts) {
            if let krs_ir::TermArgumentRef::Positional { value } = argument {
                self.infer(value, sort.as_ref(), subject)?;
            }
        }
        Ok(())
    }

    fn lower_generic_builtin(
        &mut self,
        reference: &DescriptorApplicationReference,
        operation: BuiltinOperation,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let sorts = self.generic_argument_sorts(operation, arguments, expected_sort)?;
        let mut lowered = Vec::with_capacity(sorts.len());
        for (argument, sort) in arguments.iter().zip(&sorts) {
            if let krs_ir::TermArgumentRef::Positional { value } = argument {
                lowered.push(self.lower(value, sort.as_ref(), subject)?);
            }
        }
        let result_sort = match operation.result_sort() {
            OperationSort::Builtin(sort) => SemanticSortRef::Builtin(sort),
            OperationSort::Parameter => {
                let branches = lowered
                    .iter()
                    .zip(operation.argument_sorts())
                    .filter(|(_, sort)| **sort == OperationSort::Parameter)
                    .map(|(argument, _)| argument.sort().clone())
                    .collect::<Vec<_>>();
                least_instance(&branches, expected_sort, self.sort_parents)
                    .map_err(|error| self.invalid_term(error.message(operation, &branches)))?
            }
            OperationSort::K => {
                return Err(
                    self.invalid_term(format!("builtin operation {operation} has no result sort"))
                );
            }
        };
        Ok(SemanticTerm::application(
            semantic_origin(self.descriptor, reference.key.clone(), "term-application")?,
            result_sort,
            ApplicationRef::Builtin(operation),
            lowered,
        ))
    }

    fn infer_collection_operation<O: CollectionApplication>(
        &mut self,
        operation: O,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let operands = collection_positional_operands(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let result_sort = self.collection_result_sort(operation, expected_sort)?;
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "{} operation result sort {result_sort} is not admissible at sort {expected}",
                O::SORT.k_name()
            )));
        }
        for (operand, sort) in operands.into_iter().zip(operation.spec().operand_sorts) {
            self.infer(operand, collection_operand_sort(*sort).as_ref(), subject)?;
        }
        Ok(())
    }

    /// Lowers a collection application's operands, in wire order, with its result sort.
    fn lower_collection_operands<O: CollectionApplication>(
        &mut self,
        operation: O,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(SemanticSortRef, Vec<SemanticTerm>), DescriptorLoweringError> {
        let operands = collection_positional_operands(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let result_sort = self.collection_result_sort(operation, expected_sort)?;
        let lowered = operands
            .into_iter()
            .zip(operation.spec().operand_sorts)
            .map(|(operand, sort)| {
                self.lower(operand, collection_operand_sort(*sort).as_ref(), subject)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok((result_sort, lowered))
    }

    fn collection_result_sort<O: CollectionApplication>(
        &self,
        operation: O,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Result<SemanticSortRef, DescriptorLoweringError> {
        match operation.spec().result_sort {
            CollectionResultSort::Builtin(sort) => Ok(SemanticSortRef::Builtin(sort)),
            CollectionResultSort::Projected => expected_sort.cloned().ok_or_else(|| {
                let marker = operation.facade_marker();
                self.invalid_term(format!(
                    "{}::{} requires an expected result sort",
                    marker.module, marker.name
                ))
            }),
        }
    }

    pub(super) fn infer_collection_update(
        &mut self,
        update: &DescriptorTerm,
        base_binding: &str,
        cell_sort: &SemanticSortRef,
        map_sorts: Option<&(SemanticSortRef, SemanticSortRef)>,
    ) -> Result<(), DescriptorLoweringError> {
        let DescriptorTerm::Application {
            head_class,
            reference,
            arguments,
            ..
        } = update
        else {
            return Err(self.invalid_term("updated-cell replacement is not an application"));
        };
        if *head_class != krs_ir::DescriptorApplicationHeadClass::Applied {
            return Err(self.invalid_term("updated-cell replacement head is not applied"));
        }
        let ordered = match (&reference.application, cell_sort) {
            (
                DescriptorApplicationRef::Map(krs_ir::TermMapOperation::Update),
                SemanticSortRef::Builtin(BuiltinSort::Map),
            ) => UpdateArguments::new(krs_ir::TermMapOperation::Update, arguments)
                .map_err(|detail| self.invalid_term(detail))?,
            (
                DescriptorApplicationRef::List(ListOperation::Update),
                SemanticSortRef::Builtin(BuiltinSort::List),
            ) => UpdateArguments::new(ListOperation::Update, arguments)
                .map_err(|detail| self.invalid_term(detail))?,
            _ => {
                return Err(self.invalid_term(
                    "updated-cell replacement does not resolve to the registered update operation for its collection sort",
                ));
            }
        };
        let UpdateArguments { base, key, value } = ordered;
        let DescriptorTerm::Variable { name, .. } = base else {
            return Err(
                self.invalid_term("updated-cell base is not the matched whole-collection binding")
            );
        };
        if name != base_binding {
            return Err(self.invalid_term(format!(
                "updated-cell base {name:?} does not match {base_binding:?}"
            )));
        }
        self.infer(base, Some(cell_sort), false)?;
        let int_sort = SemanticSortRef::Builtin(BuiltinSort::Int);
        match cell_sort {
            SemanticSortRef::Builtin(BuiltinSort::Map) => {
                self.infer(key, map_sorts.map(|(key_sort, _)| key_sort), false)?;
                self.infer(value, map_sorts.map(|(_, value_sort)| value_sort), false)
            }
            SemanticSortRef::Builtin(BuiltinSort::List) => {
                self.infer(key, Some(&int_sort), false)?;
                self.infer(value, None, false)
            }
            _ => Err(self.invalid_term("only Map and List cells support readable updates")),
        }
    }

    pub(super) fn resolve_binding_sorts(&mut self) -> Result<(), DescriptorLoweringError> {
        for name in self.binding_names {
            if self.binding_sorts.contains_key(name) {
                continue;
            }
            let constraints = self.binding_constraints.get(name).ok_or_else(|| {
                self.invalid_term(format!("variable {name:?} has no expected sort"))
            })?;
            let candidates = most_specific_common_descendants(constraints, self.sort_parents);
            let occurrence_sorts = constraints
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            let inferred = match candidates.as_slice() {
                [sort] => sort.clone(),
                [] => {
                    return Err(self.invalid_term(format!(
                        "variable {name:?} has no declared common descendant for occurrence sorts [{occurrence_sorts}]"
                    )));
                }
                _ => {
                    return Err(self.invalid_term(format!(
                        "variable {name:?} has ambiguous most-specific common descendants [{}] for occurrence sorts [{occurrence_sorts}]",
                        candidates.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")
                    )));
                }
            };
            self.binding_sorts.insert(name.clone(), inferred);
        }
        Ok(())
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive lowering over the closed descriptor term sum."
    )]
    pub(super) fn lower(
        &mut self,
        term: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        match term {
            DescriptorTerm::Variable { key, name, .. } => {
                if !self.binding_names.contains(name) {
                    return Err(self.invalid_term(format!("unbound variable {name:?}")));
                }
                let sort = self.binding_sorts.get(name).cloned().ok_or_else(|| {
                    self.invalid_term(format!("variable {name:?} has no inferred sort"))
                })?;
                debug_assert!(expected_sort.is_none_or(|expected| semantic_is_subsort(
                    &sort,
                    expected,
                    self.sort_parents
                )));
                Ok(SemanticTerm::variable(
                    semantic_origin(self.descriptor, key.clone(), "term-variable")?,
                    sort,
                    SemanticId::new(name.clone())?,
                ))
            }
            DescriptorTerm::Wildcard { key } => {
                if !subject {
                    return Err(self.invalid_term("wildcard occurs outside the rule subject"));
                }
                let sort = expected_sort.cloned().ok_or_else(|| {
                    self.invalid_term("wildcard has no expected production-field sort")
                })?;
                let ordinal = self.wildcard_offset + self.wildcards.len();
                let id = SemanticId::wildcard(ordinal);
                self.wildcards
                    .push(SemanticVariable::new(id.clone(), sort.clone()));
                Ok(SemanticTerm::variable(
                    semantic_origin(self.descriptor, key.clone(), "term-wildcard")?,
                    sort,
                    id,
                ))
            }
            DescriptorTerm::Literal { key, literal } => {
                let (sort, value) = match literal {
                    krs_ir::DescriptorLiteral::Int(value) => {
                        (SemanticSortRef::Builtin(BuiltinSort::Int), value.clone())
                    }
                    krs_ir::DescriptorLiteral::Bool(value) => (
                        SemanticSortRef::Builtin(BuiltinSort::Bool),
                        value.to_string(),
                    ),
                    krs_ir::DescriptorLiteral::String(value) => (
                        SemanticSortRef::Builtin(BuiltinSort::String),
                        krs_ir::string_token::encode(value).map_err(|error| {
                            self.invalid_term(format!("string literal: {error}"))
                        })?,
                    ),
                    krs_ir::DescriptorLiteral::Float(token) => {
                        krs_ir::float_token::validate(token).map_err(|error| {
                            self.invalid_term(format!("float literal `{token}`: {error}"))
                        })?;
                        (SemanticSortRef::Builtin(BuiltinSort::Float), token.clone())
                    }
                };
                Ok(SemanticTerm::token(
                    semantic_origin(self.descriptor, key.clone(), "term-literal")?,
                    sort,
                    value,
                )?)
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                ..
            } => self.lower_application(reference, arguments, expected_sort, subject),
            DescriptorTerm::BuiltinToken { key, sort, value } => SemanticTerm::token(
                semantic_origin(self.descriptor, key.clone(), "claim-builtin-token")?,
                SemanticSortRef::Builtin(*sort),
                value.clone(),
            )
            .map_err(Into::into),
            DescriptorTerm::Lexeme { key, sort, text } => {
                let sort = self.lexeme_sort(key, sort, text)?;
                SemanticTerm::token(
                    semantic_origin(self.descriptor, key.clone(), "term-lexeme")?,
                    sort,
                    text.clone(),
                )
                .map_err(Into::into)
            }
            DescriptorTerm::Anonymous {
                key,
                sort,
                spelling,
            } => {
                if !subject {
                    return Err(self.invalid_term("anonymous occurrence outside claim subject"));
                }
                let sort = semantic_sort_ref(&sort.sort);
                let ordinal = self.wildcard_offset + self.wildcards.len();
                let id = SemanticId::anonymous(spelling, ordinal)?;
                self.wildcards
                    .push(SemanticVariable::new(id.clone(), sort.clone()));
                Ok(SemanticTerm::variable(
                    semantic_origin(self.descriptor, key.clone(), "claim-anonymous")?,
                    sort,
                    id,
                ))
            }
            DescriptorTerm::OrBool { key, arguments } => {
                self.lower_or_bool(key, arguments, subject)
            }
            DescriptorTerm::Cell {
                key,
                declaration,
                fields,
            } => self.lower_cell_term(key, declaration, fields, expected_sort, subject),
            DescriptorTerm::SortTest {
                key,
                kind,
                sort,
                operand,
            } => {
                let result = self.sort_test_result(key, *kind, sort, subject)?;
                let target = semantic_sort_ref(&sort.sort);
                let operand_sort = self.sort_test_operand_sort(operand);
                let operand = self.lower(operand, operand_sort.as_ref(), subject)?;
                let operation = match kind {
                    SortTestKind::Predicate => GeneratedOperation::SortPredicate(target),
                    SortTestKind::Projection => GeneratedOperation::SortProjection(target),
                };
                Ok(SemanticTerm::application(
                    semantic_origin(self.descriptor, key.clone(), "term-sort-test")?,
                    result,
                    ApplicationRef::Generated(operation),
                    vec![operand],
                ))
            }
        }
    }

    /// The result sort of `k::is!` (Bool) or `k::project!` (its target).
    /// Either is a function call, so it cannot be matched, and K has no
    /// projection into `K`.
    fn sort_test_result(
        &self,
        key: &ProvenanceKey,
        kind: SortTestKind,
        sort: &krs_ir::DescriptorSortReference,
        subject: bool,
    ) -> Result<SemanticSortRef, DescriptorLoweringError> {
        let target = semantic_sort_ref(&sort.sort);
        let name = super::overload::sort_name(&target);
        let reason = if subject {
            Some(match kind {
                SortTestKind::Projection => format!(
                    "`k::project!({name}, ..)` is a projection, which is a function call and cannot be matched; restrict the binder with a typed parameter or `where x: {name}`"
                ),
                SortTestKind::Predicate => format!(
                    "`k::is!({name}, ..)` is a sort predicate, which is a function call and cannot be matched; restrict the binder with a typed parameter or `where x: {name}`"
                ),
            })
        } else if kind == SortTestKind::Projection
            && target == SemanticSortRef::Builtin(BuiltinSort::KSequence)
        {
            Some(
                "`k::project!(K, ..)` projects into `K`, for which K generates no projection; every term already has sort `K`"
                    .to_owned(),
            )
        } else {
            None
        };
        if let Some(reason) = reason {
            return Err(DescriptorLoweringError::InvalidSortTest {
                item: Box::new(self.descriptor.id().clone()),
                reason,
                range: self
                    .descriptor
                    .provenance()
                    .origin_for(key)
                    .and_then(krs_ir::OriginStack::exact_authored_range)
                    .map(Box::new),
            });
        }
        Ok(match kind {
            SortTestKind::Predicate => SemanticSortRef::Builtin(BuiltinSort::Bool),
            SortTestKind::Projection => target,
        })
    }

    /// The sort at which the operand of `k::is!` or `k::project!` is
    /// inferred. Both take an argument of sort `K`, so the operand is
    /// unconstrained, except that a projected collection lookup (`map::get`,
    /// `list::get`) keeps its declared result sort `KItem`: the sort test then
    /// supplies the term's one cast.
    fn sort_test_operand_sort(&self, operand: &DescriptorTerm) -> Option<SemanticSortRef> {
        let DescriptorTerm::Application { reference, .. } = operand else {
            return None;
        };
        let projected = match &reference.application {
            DescriptorApplicationRef::Map(operation) => operation.spec().is_projected(),
            DescriptorApplicationRef::List(operation) => operation.spec().is_projected(),
            DescriptorApplicationRef::Set(operation) => operation.spec().is_projected(),
            DescriptorApplicationRef::Declared(_) | DescriptorApplicationRef::Builtin(_) => false,
        };
        projected.then(|| {
            self.k_item_sort
                .clone()
                .unwrap_or(SemanticSortRef::Builtin(BuiltinSort::KSequence))
        })
    }

    fn lower_application(
        &mut self,
        reference: &DescriptorApplicationReference,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let (application, signature) = match &reference.application {
            DescriptorApplicationRef::Declared(id) => {
                let signature = self.catalog.get(id).cloned().ok_or_else(|| {
                    self.invalid_term(format!(
                        "declared application {id} has no grammar production"
                    ))
                })?;
                (ApplicationRef::Declared(id.clone()), signature)
            }
            DescriptorApplicationRef::Builtin(operation) if operation.is_sort_generic() => {
                return self.lower_generic_builtin(
                    reference,
                    *operation,
                    arguments,
                    expected_sort,
                    subject,
                );
            }
            DescriptorApplicationRef::Builtin(operation) => (
                ApplicationRef::Builtin(*operation),
                builtin_production_signature(*operation)
                    .ok_or_else(|| self.sort_generic_builtin(*operation))?,
            ),
            DescriptorApplicationRef::Map(operation) => {
                let (result_sort, operands) =
                    self.lower_collection_operands(*operation, arguments, expected_sort, subject)?;
                let operands = MapOperands::from_operands((*operation).into(), operands)
                    .map_err(|error| self.invalid_term(error.to_string()))?;
                return Ok(SemanticTerm::typed_map(
                    semantic_origin(self.descriptor, reference.key.clone(), "term-map-operation")?,
                    result_sort,
                    operands,
                ));
            }
            DescriptorApplicationRef::List(operation) => {
                let (result_sort, operands) =
                    self.lower_collection_operands(*operation, arguments, expected_sort, subject)?;
                let operands = ListOperands::from_operands(*operation, operands)
                    .map_err(|error| self.invalid_term(error.to_string()))?;
                return Ok(SemanticTerm::list(
                    semantic_origin(
                        self.descriptor,
                        reference.key.clone(),
                        "term-list-operation",
                    )?,
                    result_sort,
                    operands,
                ));
            }
            DescriptorApplicationRef::Set(operation) => {
                let (result_sort, operands) =
                    self.lower_collection_operands(*operation, arguments, expected_sort, subject)?;
                let operands = SetOperands::from_operands(*operation, operands)
                    .map_err(|error| self.invalid_term(error.to_string()))?;
                return Ok(SemanticTerm::set(
                    semantic_origin(self.descriptor, reference.key.clone(), "term-set-operation")?,
                    result_sort,
                    operands,
                ));
            }
        };
        let ordered = order_structured_arguments(arguments, &signature.fields, subject)
            .map_err(|detail| self.invalid_term(detail))?;
        let lowered = ordered
            .into_iter()
            .zip(&signature.fields)
            .map(|(argument, (_, sort))| match argument {
                Some(argument) => self.lower(argument, Some(sort), subject),
                None => self.lower_record_rest_wildcard(sort),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(SemanticTerm::application(
            semantic_origin(self.descriptor, reference.key.clone(), "term-application")?,
            signature.result_sort,
            application,
            lowered,
        ))
    }

    fn lower_or_bool(
        &mut self,
        key: &ProvenanceKey,
        arguments: &krs_ir::AtLeastTwo<DescriptorTerm>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let lowered =
            arguments.try_map_ref(|argument| self.lower(argument, Some(&bool_sort), subject))?;
        let (mut value, tail) = lowered.into_head_tail();
        for right in tail {
            value = SemanticTerm::application(
                semantic_origin(self.descriptor, key.clone(), "claim-or-bool")?,
                bool_sort.clone(),
                ApplicationRef::Builtin(BuiltinOperation::BoolOr),
                vec![value, right],
            );
        }
        Ok(value)
    }

    fn cell_k_item_sort(&self) -> Result<SemanticSortRef, DescriptorLoweringError> {
        self.k_item_sort.clone().ok_or_else(|| {
            self.invalid_term("fragment! requires one selected framework KItem sort")
        })
    }

    fn cell_declaration(
        &self,
        owner: &StableItemId,
    ) -> Result<&krs_ir::DescriptorCellDeclaration, DescriptorLoweringError> {
        let declarations = self.declarations.ok_or_else(|| {
            self.invalid_term("fragment! is supported only where cell declarations are available")
        })?;
        let declaration = declarations.cell(owner)?;
        Ok(declaration)
    }

    fn infer_cell_fields(
        &mut self,
        owner: &StableItemId,
        fields: &[krs_ir::DescriptorCellTermField],
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let declaration = self.cell_declaration(owner)?.clone();
        let supplied = fields
            .iter()
            .map(|field| (field.field.clone(), field))
            .collect::<BTreeMap<_, _>>();
        if supplied.len() != fields.len() || supplied.len() != declaration.fields.len() {
            return Err(self.invalid_term(format!(
                "fragment! for {:?} must provide every child field exactly once",
                owner.item_name()
            )));
        }
        for declared in &declaration.fields {
            let field = supplied
                .get(&ProductionFieldId::new(&declared.rust_field)?)
                .ok_or_else(|| {
                    self.invalid_term(format!(
                        "fragment! for {:?} is missing child field {:?}",
                        owner.item_name(),
                        declared.rust_field
                    ))
                })?;
            match &declared.content {
                ProtocolCellContent::Leaf { sort, .. } => {
                    self.infer(&field.value, Some(&semantic_sort_ref(&sort.sort)), subject)?;
                }
                ProtocolCellContent::Nested {
                    declaration: nested,
                } => {
                    let DescriptorTerm::Cell { declaration, .. } = field.value.as_ref() else {
                        return Err(self.invalid_term(format!(
                            "nested child {:?} must be authored with fragment!",
                            declared.rust_field
                        )));
                    };
                    if declaration != &nested.declaration {
                        return Err(self.invalid_term(format!(
                            "nested child {:?} uses the wrong cell declaration",
                            declared.rust_field
                        )));
                    }
                    self.infer(&field.value, Some(&self.cell_k_item_sort()?), subject)?;
                }
            }
        }
        Ok(())
    }

    fn lower_cell_term(
        &mut self,
        key: &ProvenanceKey,
        owner: &StableItemId,
        fields: &[krs_ir::DescriptorCellTermField],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        // A fragment that is a whole group-cell clause has the group's
        // generated cell sort (KF-016); elsewhere it keeps the KItem sort it
        // always had, so existing emitted and native terms are unchanged.
        let whole = SemanticSortRef::Cell(owner.clone());
        let sort = if expected_sort == Some(&whole) {
            whole
        } else {
            self.cell_k_item_sort()?
        };
        let declaration = self.cell_declaration(owner)?.clone();
        let supplied = fields
            .iter()
            .map(|field| (field.field.clone(), field))
            .collect::<BTreeMap<_, _>>();
        let mut children = Vec::with_capacity(declaration.fields.len());
        for declared in &declaration.fields {
            let field_id = ProductionFieldId::new(&declared.rust_field)?;
            let field = supplied.get(&field_id).ok_or_else(|| {
                self.invalid_term(format!(
                    "fragment! is missing child field {:?}",
                    declared.rust_field
                ))
            })?;
            let child = match &declared.content {
                ProtocolCellContent::Leaf { sort, .. } => {
                    let content_sort = semantic_sort_ref(&sort.sort);
                    let content = self.lower(&field.value, Some(&content_sort), subject)?;
                    SemanticTerm::cell(
                        semantic_origin(self.descriptor, field.key.clone(), "cell-term-child")?,
                        self.cell_k_item_sort()?,
                        semantic_cell_id(&declared.reference.cell)?,
                        vec![content],
                    )
                }
                ProtocolCellContent::Nested { .. } => {
                    self.lower(&field.value, Some(&self.cell_k_item_sort()?), subject)?
                }
            };
            children.push(child);
        }
        let identity = self.cell_identity_for_declaration(owner)?;
        Ok(SemanticTerm::cell(
            semantic_origin(self.descriptor, key.clone(), "cell-term")?,
            sort,
            semantic_cell_id(identity)?,
            children,
        ))
    }

    fn cell_identity_for_declaration(
        &self,
        owner: &StableItemId,
    ) -> Result<&krs_ir::DescriptorCellIdentity, DescriptorLoweringError> {
        let declarations = self
            .declarations
            .ok_or_else(|| self.invalid_term("fragment! has no cell-declaration catalog"))?;
        let mut matches = declarations
            .values()
            .flat_map(|descriptor| {
                let declaration = match descriptor.payload() {
                    DescriptorPayload::Cell(value) => Some(value.as_ref()),
                    DescriptorPayload::FixedConfiguration(value) => Some(&value.declaration),
                    _ => None,
                };
                declaration
                    .into_iter()
                    .flat_map(|declaration| declaration.fields.iter())
            })
            .filter(|field| {
                matches!(
                    &field.content,
                    ProtocolCellContent::Nested { declaration } if &declaration.declaration == owner
                )
            });
        let first = matches.next().ok_or_else(|| {
            self.invalid_term(format!(
                "cell declaration {:?} is not attached to the fixed configuration",
                owner.item_name()
            ))
        })?;
        if matches.next().is_some() {
            return Err(self.invalid_term(format!(
                "cell declaration {:?} is attached more than once",
                owner.item_name()
            )));
        }
        Ok(&first.reference.cell)
    }

    fn lower_record_rest_wildcard(
        &mut self,
        sort: &SemanticSortRef,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let pattern_key = self.pattern_key.ok_or_else(|| {
            self.invalid_term("partial named patterns are valid only in structured rule subjects")
        })?;
        let ordinal = self.wildcard_offset + self.wildcards.len();
        let id = SemanticId::wildcard(ordinal);
        let role = format!("record-rest-{ordinal}");
        self.wildcards
            .push(SemanticVariable::new(id.clone(), sort.clone()));
        Ok(SemanticTerm::variable(
            semantic_origin(self.descriptor, pattern_key.clone(), &role)?,
            sort.clone(),
            id,
        ))
    }

    fn sort_generic_builtin(&self, operation: BuiltinOperation) -> DescriptorLoweringError {
        self.invalid_term(format!(
            "builtin operation {operation} has a sort-generic signature"
        ))
    }

    /// The sort of a `k::lexeme!` term, which must be a user sort with token
    /// productions; builtin tokens are written as literals or with their own
    /// islands.
    fn lexeme_sort(
        &self,
        key: &ProvenanceKey,
        sort: &krs_ir::DescriptorSortReference,
        text: &str,
    ) -> Result<SemanticSortRef, DescriptorLoweringError> {
        let semantic = semantic_sort_ref(&sort.sort);
        let reason = match &semantic {
            SemanticSortRef::Builtin(builtin) => Some(format!(
                "`k::lexeme!` names the builtin sort `{}`; write a builtin token as a literal, `k::id!(\"$name\")`, or `k::bytes!(b\"..\")`",
                builtin.k_name()
            )),
            SemanticSortRef::Declared(_)
                if !self
                    .catalog
                    .values()
                    .any(|signature| signature.token && signature.result_sort == semantic) =>
            {
                Some(format!(
                    "`k::lexeme!({}, {text:?})` names `{}`, which is not a token sort; declare its tokens with `#[k::token(..)]` on a `struct {}(String);`",
                    super::overload::sort_name(&semantic),
                    super::overload::sort_name(&semantic),
                    super::overload::sort_name(&semantic),
                ))
            }
            SemanticSortRef::Cell(_) => Some(format!(
                "`k::lexeme!({}, {text:?})` names a generated cell sort, which is not a token sort",
                super::overload::sort_name(&semantic),
            )),
            SemanticSortRef::Declared(_) => None,
        };
        match reason {
            Some(reason) => Err(DescriptorLoweringError::InvalidTokenSort {
                item: Box::new(self.descriptor.id().clone()),
                reason,
                range: self
                    .descriptor
                    .provenance()
                    .origin_for(key)
                    .and_then(krs_ir::OriginStack::exact_authored_range)
                    .map(Box::new),
            }),
            None => Ok(semantic),
        }
    }

    fn invalid_term(&self, detail: impl Into<String>) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidTerm {
            id: Box::new(self.descriptor.id().clone()),
            detail: detail.into(),
        }
    }
}

/// The authored macro of a sort test, for messages.
const fn sort_test_macro(kind: SortTestKind) -> &'static str {
    match kind {
        SortTestKind::Predicate => "`k::is!`",
        SortTestKind::Projection => "`k::project!`",
    }
}

/// Why a sort-parametric application has no instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum InstanceError {
    /// The argument sorts have no common supersort within the bound.
    NoCommonSort { bound: Option<Box<SemanticSortRef>> },
    /// Several common supersorts are minimal, so none is least.
    Ambiguous(Vec<SemanticSortRef>),
}

impl InstanceError {
    fn message(&self, operation: BuiltinOperation, arguments: &[SemanticSortRef]) -> String {
        let spec = operation.spec();
        let sorts = arguments
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(" and ");
        let name = format!("{}::{}", spec.rust_module, spec.rust_name);
        match self {
            Self::NoCommonSort { bound: None } => format!(
                "branches of {name} have sorts {sorts} with no common sort; narrow one with a typed binder or `where`"
            ),
            Self::NoCommonSort { bound: Some(bound) } => format!(
                "branches of {name} have sorts {sorts} with no common sort admissible at sort {bound}; narrow one with a typed binder or `where`"
            ),
            Self::Ambiguous(candidates) => format!(
                "branches of {name} have sorts {sorts} with no least common sort (candidates {}); narrow one with a typed binder or `where`",
                candidates
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

/// The instance of a sort-parametric application, by k-rust's rule (X9.1):
/// the least sort that every argument sort is a subsort of, with the sort
/// expected at the position, when there is one, as an upper bound. A result
/// that is not unique is an error rather than a guess.
pub(super) fn least_instance(
    arguments: &[SemanticSortRef],
    bound: Option<&SemanticSortRef>,
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<SemanticSortRef, InstanceError> {
    let mut common: Option<BTreeSet<SemanticSortRef>> = None;
    for sort in arguments {
        let closure = semantic_sort_closure(sort, parents);
        common = Some(match common {
            None => closure,
            Some(common) => common.intersection(&closure).cloned().collect(),
        });
    }
    let mut common = common.unwrap_or_default();
    if let Some(bound) = bound {
        common.retain(|candidate| semantic_is_subsort(candidate, bound, parents));
    }
    let least = common
        .iter()
        .filter(|candidate| {
            !common
                .iter()
                .any(|other| other != *candidate && semantic_is_subsort(other, candidate, parents))
        })
        .cloned()
        .collect::<Vec<_>>();
    match least.as_slice() {
        [instance] => Ok(instance.clone()),
        [] => Err(InstanceError::NoCommonSort {
            bound: bound.cloned().map(Box::new),
        }),
        _ => Err(InstanceError::Ambiguous(least)),
    }
}

pub(super) fn initial_binding_constraints(
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> BTreeMap<String, BTreeSet<SemanticSortRef>> {
    binding_sorts
        .iter()
        .map(|(name, sort)| (name.clone(), BTreeSet::from([sort.clone()])))
        .collect()
}

/// Returns the nearest declared sorts below every occurrence constraint.
///
/// Descendants strictly below another common descendant are redundant: the
/// higher candidate is the greatest lower bound that preserves every value
/// admitted by the occurrence constraints. The stable sort ordering makes an
/// ambiguous result deterministic for diagnostics.
fn most_specific_common_descendants(
    constraints: &BTreeSet<SemanticSortRef>,
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Vec<SemanticSortRef> {
    let universe = parents
        .keys()
        .chain(parents.values().flatten())
        .chain(constraints)
        .cloned()
        .collect::<BTreeSet<_>>();
    let closures = universe
        .into_iter()
        .map(|candidate| {
            let closure = semantic_sort_closure(&candidate, parents);
            (candidate, closure)
        })
        .collect::<BTreeMap<_, _>>();
    let common = closures
        .iter()
        .filter(|(_, closure)| constraints.is_subset(closure))
        .map(|(candidate, _)| candidate.clone())
        .collect::<BTreeSet<_>>();
    common
        .iter()
        .filter(|candidate| {
            !closures[*candidate]
                .iter()
                .any(|ancestor| ancestor != *candidate && common.contains(ancestor))
        })
        .cloned()
        .collect()
}

/// The fixed signature of a builtin operation whose catalog sorts are all builtin sorts.
fn builtin_production_signature(operation: BuiltinOperation) -> Option<ProductionSignature> {
    Some(ProductionSignature {
        result_sort: SemanticSortRef::Builtin(operation.result_sort().builtin()?),
        fields: operation
            .argument_sorts()
            .iter()
            .enumerate()
            .map(|(index, sort)| {
                Some((
                    ProductionFieldId::new(format!("argument_{index}"))
                        .expect("builtin field identity is valid"),
                    SemanticSortRef::Builtin(sort.builtin()?),
                ))
            })
            .collect::<Option<_>>()?,
        token: false,
    })
}

struct UpdateArguments<'a> {
    base: &'a DescriptorTerm,
    key: &'a DescriptorTerm,
    value: &'a DescriptorTerm,
}

impl<'a> UpdateArguments<'a> {
    fn new(
        operation: impl CollectionApplication,
        arguments: &'a krs_ir::Arguments<krs_ir::DescriptorStage>,
    ) -> Result<Self, String> {
        let operands = collection_positional_operands(operation, arguments)?;
        let [base, key, value] =
            <[&DescriptorTerm; 3]>::try_from(operands).map_err(|operands| {
                format!(
                    "the {operation} operation expects 3 positional arguments but received {}",
                    operands.len()
                )
            })?;
        Ok(Self { base, key, value })
    }
}

/// Checks a collection application's arity against its catalog row and returns
/// its operands in wire order.
fn collection_positional_operands<O: CollectionApplication>(
    operation: O,
    arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
) -> Result<Vec<&DescriptorTerm>, String> {
    let expected = operation.spec().arity();
    if arguments.len() != expected {
        return Err(format!(
            "the {operation} operation expects {expected} positional arguments but received {}",
            arguments.len()
        ));
    }
    arguments
        .iter()
        .map(|argument| match argument {
            krs_ir::TermArgumentRef::Positional { value } => Ok(value),
            krs_ir::TermArgumentRef::Named { .. } => {
                Err("builtin collection operations accept positional arguments only".to_owned())
            }
        })
        .collect()
}

/// The sort an operand is inferred and lowered at, if its row fixes one.
fn collection_operand_sort(sort: CollectionOperandSort) -> Option<SemanticSortRef> {
    match sort {
        CollectionOperandSort::Builtin(sort) => Some(SemanticSortRef::Builtin(sort)),
        CollectionOperandSort::Element => None,
    }
}

fn order_structured_arguments<'a>(
    arguments: &'a krs_ir::Arguments<krs_ir::DescriptorStage>,
    fields: &[(ProductionFieldId, SemanticSortRef)],
    allow_missing_named: bool,
) -> Result<Vec<Option<&'a DescriptorTerm>>, String> {
    if arguments.len() != fields.len() && (!allow_missing_named || !arguments.is_named()) {
        return Err(format!(
            "application expects {} arguments but received {}",
            fields.len(),
            arguments.len()
        ));
    }
    let arguments = match arguments {
        krs_ir::Arguments::Positional(arguments) => {
            return Ok(arguments.iter().map(|value| Some(value.as_ref())).collect());
        }
        krs_ir::Arguments::Named(arguments) => arguments,
    };
    let mut by_name = arguments
        .iter()
        .map(|argument| (argument.field.clone(), argument.value.as_ref()))
        .collect::<BTreeMap<_, _>>();
    let ordered = fields
        .iter()
        .map(|(field, _)| {
            let value = by_name.remove(field);
            if value.is_none() && !allow_missing_named {
                return Err(format!(
                    "named application lacks field {:?}",
                    field.as_str()
                ));
            }
            Ok(value)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if let Some((field, _)) = by_name.into_iter().next() {
        return Err(format!(
            "named application has unknown field {:?}",
            field.as_str()
        ));
    }
    Ok(ordered)
}

#[cfg(test)]
mod instance_tests {
    use std::collections::{BTreeMap, BTreeSet};

    use krs_ir::{BuiltinSort, ItemKind};
    use krs_ir_levels::SemanticSortRef;

    use super::{InstanceError, least_instance};

    fn declared(name: &str) -> SemanticSortRef {
        SemanticSortRef::Declared(krs_ir::testing::item("sorts", name, ItemKind::Sort))
    }

    /// `Int, Bool < Value < Exp < KItem`, and `Left, Right < Both1, Both2`.
    fn graph() -> BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>> {
        let int = SemanticSortRef::Builtin(BuiltinSort::Int);
        let boolean = SemanticSortRef::Builtin(BuiltinSort::Bool);
        BTreeMap::from([
            (int, BTreeSet::from([declared("Value")])),
            (boolean, BTreeSet::from([declared("Value")])),
            (declared("Value"), BTreeSet::from([declared("Exp")])),
            (declared("Exp"), BTreeSet::from([declared("KItem")])),
            (
                declared("Left"),
                BTreeSet::from([declared("Both1"), declared("Both2")]),
            ),
            (
                declared("Right"),
                BTreeSet::from([declared("Both1"), declared("Both2")]),
            ),
        ])
    }

    #[test]
    fn the_instance_is_the_least_sort_of_the_branches_below_the_position() {
        let parents = graph();
        let int = SemanticSortRef::Builtin(BuiltinSort::Int);
        let boolean = SemanticSortRef::Builtin(BuiltinSort::Bool);
        // Two Int branches at an Exp position: the instance is Int, then injected.
        assert_eq!(
            least_instance(
                &[int.clone(), int.clone()],
                Some(&declared("Exp")),
                &parents
            ),
            Ok(int.clone())
        );
        assert_eq!(
            least_instance(
                &[declared("Exp"), declared("Exp")],
                Some(&declared("Exp")),
                &parents
            ),
            Ok(declared("Exp"))
        );
        assert_eq!(
            least_instance(&[int.clone(), boolean.clone()], None, &parents),
            Ok(declared("Value"))
        );
        assert_eq!(
            least_instance(
                &[int.clone(), declared("Exp")],
                Some(&declared("KItem")),
                &parents
            ),
            Ok(declared("Exp"))
        );
    }

    #[test]
    fn branches_without_a_unique_least_sort_are_rejected() {
        let parents = graph();
        let int = SemanticSortRef::Builtin(BuiltinSort::Int);
        let map = SemanticSortRef::Builtin(BuiltinSort::Map);
        assert_eq!(
            least_instance(&[int.clone(), map], None, &parents),
            Err(InstanceError::NoCommonSort { bound: None })
        );
        // The least common sort Value is above the Int position.
        assert_eq!(
            least_instance(
                &[int.clone(), SemanticSortRef::Builtin(BuiltinSort::Bool)],
                Some(&int),
                &parents
            ),
            Err(InstanceError::NoCommonSort {
                bound: Some(Box::new(int.clone()))
            })
        );
        assert_eq!(
            least_instance(&[declared("Left"), declared("Right")], None, &parents),
            Err(InstanceError::Ambiguous(vec![
                declared("Both1"),
                declared("Both2")
            ]))
        );
    }
}
