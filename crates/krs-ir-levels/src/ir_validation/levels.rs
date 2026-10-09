use std::collections::BTreeSet;

use super::{
    DeclarationRole, Declarations, RuleView, Signature, Signatures, Validation, ValidationError,
    expect_kind, insert_node, require_kind,
};
use crate::{
    DefinitionLevel, DefinitionModule, DefinitionSentence, DefinitionSortRef,
    DefinitionValidationError, LabelId, RuleSentence, SemanticLevel, SemanticModule, SemanticRule,
    SemanticSortRef, SemanticValidationError, SymbolKind,
};
use krs_ir::{FixedCell, ItemKind, PrecedenceRelation, SemanticId, SourceMapKey, StableItemId};

macro_rules! validation_error {
    ($error:expr, $public:ident, $identity:path) => {
        match $error {
            ValidationError::AliasCondition => $public::AliasCondition,
            ValidationError::ApplicationSignature(id) => {
                $public::ApplicationSignature($identity(id))
            }
            ValidationError::BuiltinApplicationSignature(operation) => {
                $public::BuiltinApplicationSignature(operation)
            }
            ValidationError::GeneratedApplicationSignature => {
                $public::GeneratedApplicationSignature
            }
            ValidationError::ParameterSortInTerm => $public::ParameterSortInTerm,
            ValidationError::CellFrameBindingMismatch(id) => $public::CellFrameBindingMismatch(id),
            ValidationError::CellFrameSortMismatch => $public::CellFrameSortMismatch,
            ValidationError::ContextAliasFrameSortMismatch => {
                $public::ContextAliasFrameSortMismatch
            }
            ValidationError::ContextAliasFrameBindingMismatch(id) => {
                $public::ContextAliasFrameBindingMismatch(id)
            }
            ValidationError::ContextAliasVariableClosure => $public::ContextAliasVariableClosure,
            ValidationError::ClaimBodyNotConfiguration(id) => {
                $public::ClaimBodyNotConfiguration($identity(id))
            }
            ValidationError::ConfigurationRuleTargetMismatch(id) => {
                $public::ConfigurationRuleTargetMismatch($identity(id))
            }
            ValidationError::ConfigurationRuleWithoutFixedConfiguration(id) => {
                $public::ConfigurationRuleWithoutFixedConfiguration($identity(id))
            }
            ValidationError::DanglingVariable(id) => $public::DanglingVariable(id),
            ValidationError::DuplicateProductionAttribute(name) => {
                $public::DuplicateProductionAttribute(name)
            }
            ValidationError::DuplicateSourceMapKey(key) => $public::DuplicateSourceMapKey(key),
            ValidationError::DuplicateVariable(id) => $public::DuplicateVariable(id),
            ValidationError::EmptyProduction(id) => $public::EmptyProduction($identity(id)),
            ValidationError::EmptyText(field) => $public::EmptyText(field),
            ValidationError::ExistentialScopeViolation(id) => {
                $public::ExistentialScopeViolation(id)
            }
            ValidationError::InitializerLeafSortMismatch => $public::InitializerLeafSortMismatch,
            ValidationError::InitializerTreeMismatch => $public::InitializerTreeMismatch,
            ValidationError::InvalidAliasProduction => $public::InvalidAliasProduction,
            ValidationError::InvalidAliasRoot(id) => $public::InvalidAliasRoot($identity(id)),
            ValidationError::InvalidBracketProduction => $public::InvalidBracketProduction,
            ValidationError::InvalidCellFraming => $public::InvalidCellFraming,
            ValidationError::InvalidClaimBinder(id) => $public::InvalidClaimBinder(id),
            ValidationError::InvalidClaimMetadata(id) => {
                $public::InvalidClaimMetadata($identity(id))
            }
            ValidationError::InvalidEquationRoot(id) => $public::InvalidEquationRoot($identity(id)),
            ValidationError::InvalidFormat => $public::InvalidFormat,
            ValidationError::InvalidSmtMetadata => $public::InvalidSmtMetadata,
            ValidationError::InvalidColors => $public::InvalidColors,
            ValidationError::InternalWithProgram => $public::InternalWithProgram,
            ValidationError::PreferAndAvoid => $public::PreferAndAvoid,
            ValidationError::AliasWithDesugar => $public::AliasWithDesugar,
            ValidationError::PreferOnParseOnlyProduction => $public::PreferOnParseOnlyProduction,
            ValidationError::InvalidOverloadProduction => $public::InvalidOverloadProduction,
            ValidationError::InvalidListProduction => $public::InvalidListProduction,
            ValidationError::InvalidFunctionProduction => $public::InvalidFunctionProduction,
            ValidationError::InvalidBn128PointConstructor {
                hook,
                sort,
                expected_signature,
                matching_constructors,
            } => $public::InvalidBn128PointConstructor {
                hook,
                sort,
                expected_signature,
                matching_constructors,
            },
            ValidationError::InvalidHookSignature(operation) => {
                $public::InvalidHookSignature(operation)
            }
            ValidationError::InvalidRulePriority(id) => $public::InvalidRulePriority($identity(id)),
            ValidationError::InvalidSimplificationMetadata(id) => {
                $public::InvalidSimplificationMetadata($identity(id))
            }
            ValidationError::InvalidSimplificationRoot(id) => {
                $public::InvalidSimplificationRoot($identity(id))
            }
            ValidationError::InvalidStrictnessField => $public::InvalidStrictnessField,
            ValidationError::InvalidTokenProduction => $public::InvalidTokenProduction,
            ValidationError::ListOperationSignature(operation) => {
                $public::ListOperationSignature(operation)
            }
            ValidationError::MapOperationSignature(operation) => {
                $public::MapOperationSignature(operation)
            }
            ValidationError::PrecedenceCycle(group) => $public::PrecedenceCycle(group),
            ValidationError::RegexWithoutToken => $public::RegexWithoutToken,
            ValidationError::RewriteSortMismatch => $public::RewriteSortMismatch,
            ValidationError::InvalidPatternAs => $public::InvalidPatternAs,
            ValidationError::InvalidPatternOr => $public::InvalidPatternOr,
            ValidationError::InvalidMatches => $public::InvalidMatches,
            ValidationError::InvalidLet => $public::InvalidLet,
            ValidationError::RuleConditionSortMismatch => $public::RuleConditionSortMismatch,
            ValidationError::SequenceItemSortMismatch => $public::SequenceItemSortMismatch,
            ValidationError::SequenceSortMismatch => $public::SequenceSortMismatch,
            ValidationError::SetOperationSignature(operation) => {
                $public::SetOperationSignature(operation)
            }
            ValidationError::SubsortCycle(sort) => $public::SubsortCycle($identity(sort)),
            ValidationError::UnusedExistential(id) => $public::UnusedExistential(id),
            ValidationError::InvalidRuleExistentials(id) => {
                $public::InvalidRuleExistentials($identity(id))
            }
            ValidationError::InvalidRuleFresh(id) => $public::InvalidRuleFresh($identity(id)),
            ValidationError::InvalidMatchRestriction(id) => {
                $public::InvalidMatchRestriction($identity(id))
            }
            ValidationError::InvalidUnboundVariables(id) => {
                $public::InvalidUnboundVariables($identity(id))
            }
            ValidationError::InvalidFunctionContext(id) => {
                $public::InvalidFunctionContext($identity(id))
            }
            ValidationError::FreshScopeViolation(id) => $public::FreshScopeViolation(id),
            ValidationError::VariableClosure => $public::VariableClosure,
            ValidationError::VariableSortMismatch(id) => $public::VariableSortMismatch(id),
        }
    };
}

impl Validation for SemanticLevel {
    const CHECK_CELL_REFERENCES_DURING_TERM_VALIDATION: bool = false;
    type Kind = ItemKind;
    type Rule = SemanticRule;
    type RuleId = StableItemId;
    type Module = SemanticModule;

    fn precedences(module: &Self::Module) -> impl Iterator<Item = &PrecedenceRelation> {
        module.precedences().iter()
    }
    type Registration<'a> = (&'a mut BTreeSet<SemanticId>, &'a mut BTreeSet<SemanticId>);

    fn rule_view(rule: &Self::Rule) -> RuleView<'_, Self> {
        RuleView {
            kind: rule.kind(),
            id: rule.id().clone(),
            variables: rule.variables(),
            body: rule.relational_body(),
            requires: rule.requires(),
            priority: rule.priority(),
            simplification: rule.simplification(),
            claim: rule.claim(),
            existentials: rule.existentials(),
            ensures: rule.ensures(),
            fresh: rule.fresh(),
            restriction: rule.restriction(),
            unbound_variables: rule.unbound_variables(),
            function_context: rule.function_context(),
            anywhere: rule.anywhere().is_some(),
        }
    }

    fn claim_label(rule: &Self::Rule) -> Result<(), Self::Error> {
        if rule.label().is_none() {
            return Err(SemanticValidationError::ClaimLabelRequired(Box::new(
                rule.id().clone(),
            )));
        }
        Ok(())
    }

    fn rule_label_origin(
        rule: &Self::Rule,
        nodes: &mut BTreeSet<SourceMapKey>,
    ) -> Result<(), Self::Error> {
        if let Some(label) = rule.label() {
            insert_node::<Self>(nodes, label.origin().key())?;
        }
        Ok(())
    }

    fn declared_sort(sort: &Self::Sort) -> Option<&Self::Declaration> {
        match sort {
            SemanticSortRef::Declared(id) => Some(id),
            SemanticSortRef::Builtin(_)
            | SemanticSortRef::Cell(_)
            | SemanticSortRef::Parameter(_) => None,
        }
    }

    fn parameter_name(sort: &Self::Sort) -> Option<&crate::SortParameterId> {
        match sort {
            SemanticSortRef::Parameter(name) => Some(name),
            _ => None,
        }
    }

    fn group_sort(cell: &FixedCell<Self::Sort, Self::Cell>) -> Option<Self::Sort> {
        cell.declaration().cloned().map(SemanticSortRef::Cell)
    }

    fn cell_sort(sort: &Self::Sort) -> Option<&Self::Declaration> {
        match sort {
            SemanticSortRef::Cell(id) => Some(id),
            SemanticSortRef::Declared(_)
            | SemanticSortRef::Builtin(_)
            | SemanticSortRef::Parameter(_) => None,
        }
    }

    fn require_cell_sort(
        _: &Declarations<Self>,
        id: &Self::Declaration,
    ) -> Result<(), Self::Error> {
        expect_kind::<Self>(id, id.item_kind(), ItemKind::Cell)
    }

    fn required_kind(role: DeclarationRole) -> Self::Kind {
        match role {
            DeclarationRole::Sort => ItemKind::Sort,
            DeclarationRole::Production => ItemKind::Constructor,
        }
    }

    fn missing_declaration(id: &Self::Declaration) -> Self::Error {
        SemanticValidationError::DanglingItem(Box::new(id.clone()))
    }

    fn wrong_kind(id: &Self::Declaration, expected: Self::Kind, actual: Self::Kind) -> Self::Error {
        SemanticValidationError::WrongItemKind {
            id: Box::new(id.clone()),
            expected,
            actual,
        }
    }

    fn application_signature(
        declarations: &Declarations<Self>,
        signatures: &Signatures<Self>,
        id: &Self::Declaration,
    ) -> Result<Signature<Self>, Self::Error> {
        let Some(kind) = declarations.get(id) else {
            return Err(SemanticValidationError::DanglingProduction(Box::new(
                id.clone(),
            )));
        };
        expect_kind::<Self>(id, *kind, Self::required_kind(DeclarationRole::Production))?;
        signatures
            .get(id)
            .cloned()
            .ok_or_else(|| SemanticValidationError::DanglingProduction(Box::new(id.clone())))
    }

    fn require_cell(
        _: &Declarations<Self>,
        cell_ids: &BTreeSet<Self::Cell>,
        cell: &Self::Cell,
    ) -> Result<(), Self::Error> {
        if cell_ids.contains(cell) {
            Ok(())
        } else {
            Err(SemanticValidationError::DanglingCell(cell.clone()))
        }
    }

    fn register_cell(
        registration: &mut Self::Registration<'_>,
        cell: &FixedCell<Self::Sort, Self::Cell>,
    ) -> Result<(), Self::Error> {
        if registration.0.insert(cell.id().clone()) {
            registration.1.insert(cell.id().clone());
            Ok(())
        } else {
            Err(SemanticValidationError::DuplicateId {
                kind: krs_ir::SemanticIdentityKind::Cell,
                id: cell.id().as_str().into(),
            })
        }
    }

    fn error(error: ValidationError<Self>) -> Self::Error {
        validation_error!(error, SemanticValidationError, Box::new)
    }
}

impl Validation for DefinitionLevel {
    const CHECK_CELL_REFERENCES_DURING_TERM_VALIDATION: bool = true;
    type Kind = SymbolKind;
    type Rule = RuleSentence;
    type RuleId = LabelId;
    type Module = DefinitionModule;

    fn precedences(module: &Self::Module) -> impl Iterator<Item = &PrecedenceRelation> {
        module
            .sentences()
            .iter()
            .filter_map(|sentence| match sentence {
                DefinitionSentence::Precedence(relation) => Some(relation),
                _ => None,
            })
    }
    type Registration<'a> = (&'a mut Declarations<Self>, &'a mut BTreeSet<String>);

    fn rule_view(rule: &Self::Rule) -> RuleView<'_, Self> {
        RuleView {
            kind: rule.kind(),
            id: rule.label().id().clone(),
            variables: rule.variables(),
            body: rule.relational_body(),
            requires: rule.requires(),
            priority: rule.priority(),
            simplification: rule.simplification(),
            claim: rule.claim(),
            existentials: rule.existentials(),
            ensures: rule.ensures(),
            fresh: rule.fresh(),
            restriction: rule.restriction(),
            unbound_variables: rule.unbound_variables(),
            function_context: rule.function_context(),
            anywhere: rule.anywhere().is_some(),
        }
    }

    fn claim_label(_: &Self::Rule) -> Result<(), Self::Error> {
        Ok(())
    }

    fn rule_label_origin(
        _: &Self::Rule,
        _: &mut BTreeSet<SourceMapKey>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn declared_sort(sort: &Self::Sort) -> Option<&Self::Declaration> {
        match sort {
            DefinitionSortRef::Declared(id) => Some(id),
            DefinitionSortRef::Builtin(_)
            | DefinitionSortRef::Cell(_)
            | DefinitionSortRef::Parameter(_) => None,
        }
    }

    fn parameter_name(sort: &Self::Sort) -> Option<&crate::SortParameterId> {
        match sort {
            DefinitionSortRef::Parameter(name) => Some(name),
            _ => None,
        }
    }

    fn group_sort(cell: &FixedCell<Self::Sort, Self::Cell>) -> Option<Self::Sort> {
        Some(DefinitionSortRef::Cell(cell.id().clone()))
    }

    fn cell_sort(sort: &Self::Sort) -> Option<&Self::Declaration> {
        match sort {
            DefinitionSortRef::Cell(id) => Some(id),
            DefinitionSortRef::Declared(_)
            | DefinitionSortRef::Builtin(_)
            | DefinitionSortRef::Parameter(_) => None,
        }
    }

    fn require_cell_sort(
        declarations: &Declarations<Self>,
        id: &Self::Declaration,
    ) -> Result<(), Self::Error> {
        require_kind::<Self>(declarations, id, SymbolKind::Cell)
    }

    fn required_kind(role: DeclarationRole) -> Self::Kind {
        match role {
            DeclarationRole::Sort => SymbolKind::Sort,
            DeclarationRole::Production => SymbolKind::Production,
        }
    }

    fn missing_declaration(id: &Self::Declaration) -> Self::Error {
        DefinitionValidationError::DanglingSymbol(id.clone())
    }

    fn wrong_kind(id: &Self::Declaration, expected: Self::Kind, actual: Self::Kind) -> Self::Error {
        DefinitionValidationError::WrongSymbolKind {
            id: id.clone(),
            expected,
            actual,
        }
    }

    fn application_signature(
        declarations: &Declarations<Self>,
        signatures: &Signatures<Self>,
        id: &Self::Declaration,
    ) -> Result<Signature<Self>, Self::Error> {
        require_kind::<Self>(
            declarations,
            id,
            Self::required_kind(DeclarationRole::Production),
        )?;
        signatures
            .get(id)
            .cloned()
            .ok_or_else(|| DefinitionValidationError::DanglingSymbol(id.clone()))
    }

    fn require_cell(
        declarations: &Declarations<Self>,
        _: &BTreeSet<Self::Cell>,
        cell: &Self::Cell,
    ) -> Result<(), Self::Error> {
        require_kind::<Self>(declarations, cell, SymbolKind::Cell)
    }

    fn register_cell(
        registration: &mut Self::Registration<'_>,
        cell: &FixedCell<Self::Sort, Self::Cell>,
    ) -> Result<(), Self::Error> {
        if registration
            .0
            .insert(cell.id().clone(), SymbolKind::Cell)
            .is_some()
        {
            return Err(DefinitionValidationError::DuplicateSymbol(
                cell.id().clone(),
            ));
        }
        if !registration.1.insert(cell.name().to_owned()) {
            return Err(DefinitionValidationError::DuplicateEmittedName(
                cell.name().to_owned(),
            ));
        }
        Ok(())
    }

    fn error(error: ValidationError<Self>) -> Self::Error {
        validation_error!(error, DefinitionValidationError, std::convert::identity)
    }
}
