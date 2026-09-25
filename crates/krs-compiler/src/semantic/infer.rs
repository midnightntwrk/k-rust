use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, Descriptor, DescriptorApplicationRef,
    DescriptorApplicationReference, DescriptorPayload, DescriptorTerm, DescriptorTermArgument,
    ItemKind, ListOperation, MapOperation, ProductionFieldId, ProtocolCellContent, ProvenanceKey,
    SemanticId, SemanticSortRef, SemanticTerm, SemanticVariable, SetOperation, StableItemId,
};

use super::catalog::{
    ProductionSignature, semantic_is_subsort, semantic_sort_closure, semantic_sort_ref,
};
use super::error::DescriptorLoweringError;
use super::origin::{semantic_cell_id, semantic_origin};
use super::references::require_descriptor;

pub(super) struct StructuredTermBuilder<'a> {
    pub(super) descriptor: &'a Descriptor,
    pub(super) catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    pub(super) declarations: Option<&'a BTreeMap<StableItemId, &'a Descriptor>>,
    pub(super) k_item_sort: Option<SemanticSortRef>,
    pub(super) sort_parents: &'a BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
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
                };
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(format!(
                        "literal of sort {sort:?} is not admissible at sort {expected:?}"
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
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&k_item, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(
                        "complete cell term is not admissible at the expected sort",
                    ));
                }
                self.infer_cell_fields(declaration, fields, subject)?;
            }
        }
        Ok(())
    }

    fn infer_application(
        &mut self,
        reference: &DescriptorApplicationReference,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let signature = match &reference.application {
            DescriptorApplicationRef::Declared(id) => {
                self.catalog.get(id).cloned().ok_or_else(|| {
                    self.invalid_term(format!(
                        "declared application {id:?} has no grammar production"
                    ))
                })?
            }
            DescriptorApplicationRef::Builtin(operation) => {
                builtin_production_signature(*operation)
            }
            DescriptorApplicationRef::Map(operation) => {
                self.infer_map_operation(*operation, arguments, expected_sort, subject)?;
                return Ok(());
            }
            DescriptorApplicationRef::List(operation) => {
                self.infer_list_operation(*operation, arguments, expected_sort, subject)?;
                return Ok(());
            }
            DescriptorApplicationRef::Set(operation) => {
                self.infer_set_operation(*operation, arguments, expected_sort, subject)?;
                return Ok(());
            }
        };
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&signature.result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "application result sort {:?} is not admissible at sort {expected:?}",
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

    fn infer_map_operation(
        &mut self,
        operation: MapOperation,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let arguments = ordinary_map_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let map_sort = SemanticSortRef::Builtin(BuiltinSort::Map);
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let result_sort = match operation {
            MapOperation::Get => expected_sort
                .cloned()
                .ok_or_else(|| self.invalid_term("map::get requires an expected result sort"))?,
            MapOperation::InKeys => bool_sort.clone(),
            MapOperation::Update => map_sort.clone(),
            MapOperation::Empty | MapOperation::Item => {
                return Err(self.invalid_term("structural Map operation used as an application"));
            }
        };
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "Map operation result sort {result_sort:?} is not admissible at sort {expected:?}"
            )));
        }
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            MapOperation::Update => vec![Some(&map_sort), None, None],
            MapOperation::Get => vec![Some(&map_sort), None],
            MapOperation::InKeys => vec![None, Some(&map_sort)],
            MapOperation::Empty | MapOperation::Item => unreachable!("checked above"),
        };
        for (argument, expected) in arguments.into_iter().zip(operand_sorts) {
            self.infer(argument, expected, subject)?;
        }
        Ok(())
    }

    fn lower_map_operation(
        &mut self,
        reference: &krs_ir::DescriptorApplicationReference,
        operation: MapOperation,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let arguments = ordinary_map_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let map_sort = SemanticSortRef::Builtin(BuiltinSort::Map);
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let result_sort = match operation {
            MapOperation::Get => expected_sort
                .cloned()
                .ok_or_else(|| self.invalid_term("map::get requires an expected result sort"))?,
            MapOperation::InKeys => bool_sort,
            MapOperation::Update => map_sort.clone(),
            MapOperation::Empty | MapOperation::Item => {
                return Err(self.invalid_term("structural Map operation used as an application"));
            }
        };
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            MapOperation::Update => vec![Some(&map_sort), None, None],
            MapOperation::Get => vec![Some(&map_sort), None],
            MapOperation::InKeys => vec![None, Some(&map_sort)],
            MapOperation::Empty | MapOperation::Item => unreachable!("checked above"),
        };
        let lowered = arguments
            .into_iter()
            .zip(operand_sorts)
            .map(|(argument, expected)| self.lower(argument, expected, subject))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(SemanticTerm::typed_map(
            semantic_origin(self.descriptor, reference.key.clone(), "term-map-operation")?,
            result_sort,
            operation,
            lowered,
        ))
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
                DescriptorApplicationRef::Map(MapOperation::Update),
                SemanticSortRef::Builtin(BuiltinSort::Map),
            ) => ordinary_map_arguments(MapOperation::Update, arguments)
                .map_err(|detail| self.invalid_term(detail))?,
            (
                DescriptorApplicationRef::List(ListOperation::Update),
                SemanticSortRef::Builtin(BuiltinSort::List),
            ) => ordinary_list_arguments(ListOperation::Update, arguments)
                .map_err(|detail| self.invalid_term(detail))?,
            _ => {
                return Err(self.invalid_term(
                    "updated-cell replacement does not resolve to the registered update operation for its collection sort",
                ));
            }
        };
        let [base, key, value] = ordered.as_slice() else {
            unreachable!("collection update arity is checked")
        };
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

    fn infer_list_operation(
        &mut self,
        operation: ListOperation,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let arguments = ordinary_list_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let list_sort = SemanticSortRef::Builtin(BuiltinSort::List);
        let int_sort = SemanticSortRef::Builtin(BuiltinSort::Int);
        let result_sort = match operation {
            ListOperation::Get => expected_sort
                .cloned()
                .ok_or_else(|| self.invalid_term("list::get requires an expected result sort"))?,
            ListOperation::Size => int_sort.clone(),
            ListOperation::Empty
            | ListOperation::Item
            | ListOperation::Concat
            | ListOperation::Update
            | ListOperation::Make
            | ListOperation::Range
            | ListOperation::UpdateAll => list_sort.clone(),
        };
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "List operation result sort {result_sort:?} is not admissible at sort {expected:?}"
            )));
        }
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            ListOperation::Empty => vec![],
            ListOperation::Item => vec![None],
            ListOperation::Concat => vec![Some(&list_sort), Some(&list_sort)],
            ListOperation::Get => vec![Some(&list_sort), Some(&int_sort)],
            ListOperation::Update => vec![Some(&list_sort), Some(&int_sort), None],
            ListOperation::Size => vec![Some(&list_sort)],
            ListOperation::Make => vec![Some(&int_sort), None],
            ListOperation::Range => vec![Some(&list_sort), Some(&int_sort), Some(&int_sort)],
            ListOperation::UpdateAll => {
                vec![Some(&list_sort), Some(&int_sort), Some(&list_sort)]
            }
        };
        for (argument, expected) in arguments.into_iter().zip(operand_sorts) {
            self.infer(argument, expected, subject)?;
        }
        Ok(())
    }

    fn lower_list_operation(
        &mut self,
        reference: &krs_ir::DescriptorApplicationReference,
        operation: ListOperation,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let arguments = ordinary_list_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let list_sort = SemanticSortRef::Builtin(BuiltinSort::List);
        let int_sort = SemanticSortRef::Builtin(BuiltinSort::Int);
        let result_sort = match operation {
            ListOperation::Get => expected_sort
                .cloned()
                .ok_or_else(|| self.invalid_term("list::get requires an expected result sort"))?,
            ListOperation::Size => int_sort.clone(),
            ListOperation::Empty
            | ListOperation::Item
            | ListOperation::Concat
            | ListOperation::Update
            | ListOperation::Make
            | ListOperation::Range
            | ListOperation::UpdateAll => list_sort.clone(),
        };
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            ListOperation::Empty => vec![],
            ListOperation::Item => vec![None],
            ListOperation::Concat => vec![Some(&list_sort), Some(&list_sort)],
            ListOperation::Get => vec![Some(&list_sort), Some(&int_sort)],
            ListOperation::Update => vec![Some(&list_sort), Some(&int_sort), None],
            ListOperation::Size => vec![Some(&list_sort)],
            ListOperation::Make => vec![Some(&int_sort), None],
            ListOperation::Range => vec![Some(&list_sort), Some(&int_sort), Some(&int_sort)],
            ListOperation::UpdateAll => {
                vec![Some(&list_sort), Some(&int_sort), Some(&list_sort)]
            }
        };
        let lowered = arguments
            .into_iter()
            .zip(operand_sorts)
            .map(|(argument, expected)| self.lower(argument, expected, subject))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(SemanticTerm::list(
            semantic_origin(
                self.descriptor,
                reference.key.clone(),
                "term-list-operation",
            )?,
            result_sort,
            operation,
            lowered,
        ))
    }

    fn infer_set_operation(
        &mut self,
        operation: SetOperation,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let arguments = ordinary_set_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let set_sort = SemanticSortRef::Builtin(BuiltinSort::Set);
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let result_sort = match operation {
            SetOperation::Contains => bool_sort.clone(),
            SetOperation::Empty
            | SetOperation::Item
            | SetOperation::Concat
            | SetOperation::Union => set_sort.clone(),
        };
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "Set operation result sort {result_sort:?} is not admissible at sort {expected:?}"
            )));
        }
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            SetOperation::Empty => vec![],
            SetOperation::Item => vec![None],
            SetOperation::Concat | SetOperation::Union => vec![Some(&set_sort), Some(&set_sort)],
            SetOperation::Contains => vec![None, Some(&set_sort)],
        };
        for (argument, expected) in arguments.into_iter().zip(operand_sorts) {
            self.infer(argument, expected, subject)?;
        }
        Ok(())
    }

    fn lower_set_operation(
        &mut self,
        reference: &krs_ir::DescriptorApplicationReference,
        operation: SetOperation,
        arguments: &[DescriptorTermArgument],
        _expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let arguments = ordinary_set_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let set_sort = SemanticSortRef::Builtin(BuiltinSort::Set);
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let result_sort = match operation {
            SetOperation::Contains => bool_sort,
            SetOperation::Empty
            | SetOperation::Item
            | SetOperation::Concat
            | SetOperation::Union => set_sort.clone(),
        };
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            SetOperation::Empty => vec![],
            SetOperation::Item => vec![None],
            SetOperation::Concat | SetOperation::Union => vec![Some(&set_sort), Some(&set_sort)],
            SetOperation::Contains => vec![None, Some(&set_sort)],
        };
        let lowered = arguments
            .into_iter()
            .zip(operand_sorts)
            .map(|(argument, expected)| self.lower(argument, expected, subject))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(SemanticTerm::set(
            semantic_origin(self.descriptor, reference.key.clone(), "term-set-operation")?,
            result_sort,
            operation,
            lowered,
        ))
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
            let inferred = match candidates.as_slice() {
                [sort] => sort.clone(),
                [] => {
                    return Err(self.invalid_term(format!(
                        "variable {name:?} has no declared common descendant for occurrence sorts {constraints:?}"
                    )));
                }
                _ => {
                    return Err(self.invalid_term(format!(
                        "variable {name:?} has ambiguous most-specific common descendants {candidates:?} for occurrence sorts {constraints:?}"
                    )));
                }
            };
            self.binding_sorts.insert(name.clone(), inferred);
        }
        Ok(())
    }

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
                let id = SemanticId::new(format!("__krs_wildcard_{ordinal}"))?;
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
                let id = SemanticId::new(format!("{spelling}__krs_{ordinal}"))?;
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
            } => self.lower_cell_term(key, declaration, fields, subject),
        }
    }

    fn lower_application(
        &mut self,
        reference: &DescriptorApplicationReference,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let (application, signature) = match &reference.application {
            DescriptorApplicationRef::Declared(id) => {
                let signature = self.catalog.get(id).cloned().ok_or_else(|| {
                    self.invalid_term(format!(
                        "declared application {id:?} has no grammar production"
                    ))
                })?;
                (ApplicationRef::Declared(id.clone()), signature)
            }
            DescriptorApplicationRef::Builtin(operation) => (
                ApplicationRef::Builtin(*operation),
                builtin_production_signature(*operation),
            ),
            DescriptorApplicationRef::Map(operation) => {
                return self.lower_map_operation(
                    reference,
                    *operation,
                    arguments,
                    expected_sort,
                    subject,
                );
            }
            DescriptorApplicationRef::List(operation) => {
                return self.lower_list_operation(
                    reference,
                    *operation,
                    arguments,
                    expected_sort,
                    subject,
                );
            }
            DescriptorApplicationRef::Set(operation) => {
                return self.lower_set_operation(
                    reference,
                    *operation,
                    arguments,
                    expected_sort,
                    subject,
                );
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
        arguments: &[DescriptorTerm],
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let lowered = arguments
            .iter()
            .map(|argument| self.lower(argument, Some(&bool_sort), subject))
            .collect::<Result<Vec<_>, _>>()?;
        let mut iter = lowered.into_iter();
        let mut value = iter.next().expect("validated nonempty");
        for right in iter {
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
        let descriptor = require_descriptor(owner, ItemKind::Cell, declarations)?;
        let DescriptorPayload::Cell(declaration) = &descriptor.payload else {
            unreachable!("kind-checked cell descriptor has cell payload")
        };
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
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
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
            self.cell_k_item_sort()?,
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
                let declaration = match &descriptor.payload {
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
        let id = SemanticId::new(format!("__krs_wildcard_{ordinal}"))?;
        let role = format!("record-rest-{ordinal}");
        self.wildcards
            .push(SemanticVariable::new(id.clone(), sort.clone()));
        Ok(SemanticTerm::variable(
            semantic_origin(self.descriptor, pattern_key.clone(), &role)?,
            sort.clone(),
            id,
        ))
    }

    fn invalid_term(&self, detail: impl Into<String>) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidTerm {
            id: Box::new(self.descriptor.id.clone()),
            detail: detail.into(),
        }
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
    parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
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

fn builtin_production_signature(operation: BuiltinOperation) -> ProductionSignature {
    ProductionSignature {
        result_sort: SemanticSortRef::Builtin(operation.result_sort()),
        fields: operation
            .argument_sorts()
            .iter()
            .enumerate()
            .map(|(index, sort)| {
                (
                    ProductionFieldId::new(format!("argument_{index}"))
                        .expect("builtin field identity is valid"),
                    SemanticSortRef::Builtin(*sort),
                )
            })
            .collect(),
        grammar_owned: false,
    }
}

fn ordinary_map_arguments(
    operation: MapOperation,
    arguments: &[DescriptorTermArgument],
) -> Result<Vec<&DescriptorTerm>, String> {
    let expected = match operation {
        MapOperation::Update => 3,
        MapOperation::Get | MapOperation::InKeys => 2,
        MapOperation::Empty | MapOperation::Item => {
            return Err(format!(
                "Map operation {operation:?} is not available as an ordinary term application"
            ));
        }
    };
    if arguments.len() != expected {
        return Err(format!(
            "Map operation {operation:?} expects {expected} positional arguments but received {}",
            arguments.len()
        ));
    }
    arguments
        .iter()
        .map(ordinary_map_positional_argument)
        .collect()
}

fn ordinary_map_positional_argument(
    argument: &DescriptorTermArgument,
) -> Result<&DescriptorTerm, String> {
    match argument {
        DescriptorTermArgument::Positional { value } => Ok(value),
        DescriptorTermArgument::Named { .. } => {
            Err("builtin collection operations accept positional arguments only".to_owned())
        }
    }
}

fn ordinary_set_arguments(
    operation: SetOperation,
    arguments: &[DescriptorTermArgument],
) -> Result<Vec<&DescriptorTerm>, String> {
    let expected = match operation {
        SetOperation::Empty => 0,
        SetOperation::Item => 1,
        SetOperation::Concat | SetOperation::Union | SetOperation::Contains => 2,
    };
    if arguments.len() != expected {
        return Err(format!(
            "Set operation {operation:?} expects {expected} positional arguments but received {}",
            arguments.len()
        ));
    }
    arguments
        .iter()
        .map(ordinary_map_positional_argument)
        .collect()
}

fn ordinary_list_arguments(
    operation: ListOperation,
    arguments: &[DescriptorTermArgument],
) -> Result<Vec<&DescriptorTerm>, String> {
    let expected = match operation {
        ListOperation::Empty => 0,
        ListOperation::Item | ListOperation::Size => 1,
        ListOperation::Concat | ListOperation::Get | ListOperation::Make => 2,
        ListOperation::Update | ListOperation::Range | ListOperation::UpdateAll => 3,
    };
    if arguments.len() != expected {
        return Err(format!(
            "List operation {operation:?} expects {expected} positional arguments but received {}",
            arguments.len()
        ));
    }
    arguments
        .iter()
        .map(ordinary_map_positional_argument)
        .collect()
}

fn order_structured_arguments<'a>(
    arguments: &'a [DescriptorTermArgument],
    fields: &[(ProductionFieldId, SemanticSortRef)],
    allow_missing_named: bool,
) -> Result<Vec<Option<&'a DescriptorTerm>>, String> {
    if arguments.len() != fields.len()
        && (!allow_missing_named
            || arguments.first().is_none_or(|argument| {
                matches!(argument, DescriptorTermArgument::Positional { .. })
            }))
    {
        return Err(format!(
            "application expects {} arguments but received {}",
            fields.len(),
            arguments.len()
        ));
    }
    if arguments
        .first()
        .is_none_or(|argument| matches!(argument, DescriptorTermArgument::Positional { .. }))
    {
        return Ok(arguments
            .iter()
            .map(|argument| match argument {
                DescriptorTermArgument::Positional { value } => Some(value.as_ref()),
                DescriptorTermArgument::Named { .. } => {
                    unreachable!("protocol validation rejects mixed arguments")
                }
            })
            .collect());
    }
    let mut by_name = arguments
        .iter()
        .map(|argument| match argument {
            DescriptorTermArgument::Named { field, value, .. } => (field.clone(), value.as_ref()),
            DescriptorTermArgument::Positional { .. } => {
                unreachable!("protocol validation rejects mixed arguments")
            }
        })
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
