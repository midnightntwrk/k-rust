//! Shared shape validation with level-specific identity and context checks.

use crate::ir_level::{
    IrClaim, IrLevel, IrRuleCondition, IrRulePriority, IrSimplification, IrTerm, IrTermKind,
    IrVariable, RuleBodyRef,
};
use crate::{
    ApplicationRef, BuiltinOperation, BuiltinSort, CellContentFrame, CellPost, FixedCell,
    FixedCellClause, FixedCellContent, FixedConfiguration, FixedConfigurationRewrite,
    FixedInitializerCell, FixedInitializerContent, FormatFragment, GrammarProductionItem,
    GrammarProductionItemKind, HookOperation, HookSignature, HookSortConstraint, ListOperation,
    MapOperation, PrecedenceRelation, ProductionAttribute, ProductionFieldId, ProductionGroupId,
    SemanticId, SentenceKind, SetOperation, SourceMapKey,
};
use std::collections::{BTreeMap, BTreeSet};

mod levels;
#[cfg(test)]
mod tests;

pub(crate) type Declarations<L> = BTreeMap<<L as IrLevel>::Declaration, <L as Validation>::Kind>;
pub(crate) type Signature<L> = (<L as IrLevel>::Sort, Vec<<L as IrLevel>::Sort>);
pub(crate) type Signatures<L> = BTreeMap<<L as IrLevel>::Declaration, Signature<L>>;
pub(crate) type SortParents<L> = BTreeMap<<L as IrLevel>::Sort, Vec<<L as IrLevel>::Sort>>;
pub(crate) type Configuration<L> =
    FixedConfiguration<<L as IrLevel>::Sort, <L as IrLevel>::Cell, IrTerm<L>>;

pub(crate) struct RuleView<'a, L: Validation> {
    pub kind: SentenceKind,
    pub id: L::RuleId,
    pub variables: &'a [IrVariable<L>],
    pub body: RuleBodyRef<'a, L>,
    pub requires: Option<&'a IrRuleCondition<L>>,
    pub priority: Option<&'a IrRulePriority>,
    pub simplification: Option<&'a IrSimplification>,
    pub claim: Option<&'a IrClaim<L>>,
}

#[derive(Clone, Copy)]
pub(crate) enum DeclarationRole {
    Sort,
    Production,
}

/// Level-specific identities, errors, and checks whose presence differs between levels.
pub(crate) trait Validation: IrLevel {
    type Kind: Copy + Eq;
    type Rule;
    type RuleId: Clone;
    type Module;
    /// Semantic modules carry a precedence collection; Definition modules select precedence sentences in sentence order.
    fn precedences(module: &Self::Module) -> impl Iterator<Item = &PrecedenceRelation>;
    /// Semantic cells share semantic IDs; Definition cells share symbol and emitted-name namespaces.
    type Registration<'a>;
    /// Registers a cell before its provenance, preserving identity-before-name error ordering.
    fn register_cell(
        registration: &mut Self::Registration<'_>,
        cell: &FixedCell<Self::Sort, Self::Cell>,
    ) -> Result<(), Self::Error>;
    /// Projects the different rule containers without changing either serialized shape.
    fn rule_view(rule: &Self::Rule) -> RuleView<'_, Self>;
    /// Semantic claims require an optional authored label; Definition labels are mandatory in the shape.
    fn claim_label(rule: &Self::Rule) -> Result<(), Self::Error>;
    /// Semantic labels carry a source node checked before scope; Definition labels carry no node.
    fn rule_label_origin(
        rule: &Self::Rule,
        nodes: &mut BTreeSet<SourceMapKey>,
    ) -> Result<(), Self::Error>;
    /// Extracts an authored item or generated symbol from a sort reference.
    fn declared_sort(sort: &Self::Sort) -> Option<&Self::Declaration>;
    /// Selects the semantic item kind or emitted symbol kind for the same role.
    fn required_kind(role: DeclarationRole) -> Self::Kind;
    /// Missing references report dangling items in Semantic IR and dangling symbols in Definition IR.
    fn missing_declaration(id: &Self::Declaration) -> Self::Error;
    /// Wrong roles retain the level's public error and identity representation.
    fn wrong_kind(id: &Self::Declaration, expected: Self::Kind, actual: Self::Kind) -> Self::Error;
    /// Semantic applications report dangling productions; Definition applications report dangling symbols.
    fn application_signature(
        declarations: &Declarations<Self>,
        signatures: &Signatures<Self>,
        id: &Self::Declaration,
    ) -> Result<Signature<Self>, Self::Error>;
    /// Definition cell terms require declared cell symbols; Semantic cell identities are unchecked here.
    fn require_cell(
        declarations: &Declarations<Self>,
        cell: &Self::Cell,
    ) -> Result<(), Self::Error>;
    /// Maps shared failures to the existing public variants, including Semantic boxed identities.
    fn error(error: ValidationError<Self>) -> Self::Error;
}

pub(crate) enum ValidationError<L: Validation> {
    AliasCondition,
    ApplicationSignature(L::Declaration),
    BuiltinApplicationSignature(BuiltinOperation),
    CellFrameBindingMismatch(SemanticId),
    CellFrameSortMismatch,
    ClaimBodyNotConfiguration(L::RuleId),
    ConfigurationRuleTargetMismatch(L::RuleId),
    ConfigurationRuleWithoutFixedConfiguration(L::RuleId),
    DanglingVariable(SemanticId),
    DuplicateProductionAttribute(crate::ProductionAttributeFamily),
    DuplicateSourceMapKey(SourceMapKey),
    DuplicateVariable(SemanticId),
    EmptyProduction(L::Declaration),
    EmptyText(crate::IrField),
    ExistentialScopeViolation(SemanticId),
    InitializerLeafSortMismatch,
    InitializerTreeMismatch,
    InvalidAliasProduction,
    InvalidAliasRoot(L::RuleId),
    InvalidBracketProduction,
    InvalidCellFraming,
    InvalidClaimBinder(SemanticId),
    InvalidClaimMetadata(L::RuleId),
    InvalidEquationRoot(L::RuleId),
    InvalidFormat,
    InvalidFunctionProduction,
    InvalidHookSignature(HookOperation),
    InvalidRulePriority(L::RuleId),
    InvalidSimplificationMetadata(L::RuleId),
    InvalidSimplificationRoot(L::RuleId),
    InvalidStrictnessField,
    InvalidTokenProduction,
    ListOperationSignature(ListOperation),
    MapOperationSignature(MapOperation),
    PrecedenceCycle(ProductionGroupId),
    RegexWithoutToken,
    RewriteSortMismatch,
    RuleConditionSortMismatch,
    SequenceItemSortMismatch,
    SequenceSortMismatch,
    SetOperationSignature(SetOperation),
    SubsortCycle(L::Sort),
    UnusedExistential(SemanticId),
    VariableClosure,
    VariableSortMismatch(SemanticId),
}

pub(crate) fn require_sort<L: Validation>(
    declarations: &Declarations<L>,
    sort: &L::Sort,
) -> Result<(), L::Error> {
    if let Some(id) = L::declared_sort(sort) {
        require_kind::<L>(declarations, id, L::required_kind(DeclarationRole::Sort))?;
    }
    Ok(())
}

pub(crate) fn insert_node<L: Validation>(
    set: &mut BTreeSet<SourceMapKey>,
    key: &SourceMapKey,
) -> Result<(), L::Error> {
    if set.insert(key.clone()) {
        Ok(())
    } else {
        Err(L::error(ValidationError::DuplicateSourceMapKey(
            key.clone(),
        )))
    }
}

pub(crate) fn variable_scope<L: Validation>(
    variables: &[IrVariable<L>],
    declarations: &Declarations<L>,
) -> Result<BTreeMap<SemanticId, L::Sort>, L::Error> {
    let mut scope = BTreeMap::new();
    for variable in variables {
        require_sort::<L>(declarations, variable.sort())?;
        if scope
            .insert(variable.id().clone(), variable.sort().clone())
            .is_some()
        {
            return Err(L::error(ValidationError::DuplicateVariable(
                variable.id().clone(),
            )));
        }
    }
    Ok(scope)
}

pub(crate) fn validate_fixed_configuration<L: Validation>(
    configuration: &FixedConfiguration<L::Sort, L::Cell, IrTerm<L>>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    let mut scope = BTreeMap::new();
    let mut external_names = BTreeSet::new();
    let mut main_count = 0_usize;
    for variable in configuration.variables() {
        require_sort::<L>(declarations, variable.sort())?;
        if scope
            .insert(variable.id().clone(), variable.sort().clone())
            .is_some()
        {
            return Err(L::error(ValidationError::DuplicateVariable(
                variable.id().clone(),
            )));
        }
        if !external_names.insert(variable.external_name()) {
            return Err(L::error(ValidationError::EmptyText(
                crate::IrField::DuplicateExternalConfigurationVariable,
            )));
        }
        main_count += usize::from(variable.is_main());
    }
    if main_count > 1 {
        return Err(L::error(ValidationError::EmptyText(
            crate::IrField::MultipleMainConfigurationVariables,
        )));
    }
    validate_initializer_forest::<L>(
        configuration.cells(),
        configuration.initializer(),
        &scope,
        declarations,
        signatures,
        sort_parents,
        nodes,
    )?;
    let mut used = BTreeSet::new();
    collect_initializer_variables::<L>(configuration.initializer(), &mut used);
    if used != scope.keys().cloned().collect() {
        return Err(L::error(ValidationError::VariableClosure));
    }
    Ok(())
}

pub(crate) fn collect_initializer_variables<L: Validation>(
    initializer: &[FixedInitializerCell<L::Cell, IrTerm<L>>],
    used: &mut BTreeSet<SemanticId>,
) {
    for cell in initializer {
        match cell.content() {
            FixedInitializerContent::Term { term } => collect_term_variables::<L>(term, used),
            FixedInitializerContent::Children { children } => {
                collect_initializer_variables::<L>(children, used);
            }
        }
    }
}

pub(crate) fn validate_initializer_forest<L: Validation>(
    cells: &[FixedCell<L::Sort, L::Cell>],
    initializer: &[FixedInitializerCell<L::Cell, IrTerm<L>>],
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    if cells.len() != initializer.len() {
        return Err(L::error(ValidationError::InitializerTreeMismatch));
    }
    for (cell, initialized) in cells.iter().zip(initializer) {
        if cell.id() != initialized.cell() {
            return Err(L::error(ValidationError::InitializerTreeMismatch));
        }
        match (cell.content(), initialized.content()) {
            (FixedCellContent::Term { sort }, FixedInitializerContent::Term { term }) => {
                require_sort::<L>(declarations, sort)?;
                validate_term::<L>(term, scope, declarations, signatures, sort_parents, nodes)?;
                if term.sort() != sort {
                    return Err(L::error(ValidationError::InitializerLeafSortMismatch));
                }
            }
            (
                FixedCellContent::Children { children },
                FixedInitializerContent::Children {
                    children: initialized_children,
                },
            ) => validate_initializer_forest::<L>(
                children,
                initialized_children,
                scope,
                declarations,
                signatures,
                sort_parents,
                nodes,
            )?,
            _ => return Err(L::error(ValidationError::InitializerTreeMismatch)),
        }
    }
    Ok(())
}

pub(crate) fn validate_configuration_rewrite<L: Validation>(
    rewrite: &FixedConfigurationRewrite<L::Cell, IrTerm<L>>,
    configuration: &FixedConfiguration<L::Sort, L::Cell, IrTerm<L>>,
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    fn leaves<L: Validation>(
        cells: &[FixedCell<L::Sort, L::Cell>],
        output: &mut BTreeMap<L::Cell, L::Sort>,
    ) -> Result<(), L::Error> {
        for cell in cells {
            match cell.content() {
                FixedCellContent::Term { sort } => {
                    if output.insert(cell.id().clone(), sort.clone()).is_some() {
                        return Err(L::error(ValidationError::InvalidCellFraming));
                    }
                }
                FixedCellContent::Children { children } => leaves::<L>(children, output)?,
            }
        }
        Ok(())
    }
    let mut leaf_sorts = BTreeMap::new();
    leaves::<L>(configuration.cells(), &mut leaf_sorts)?;
    let mentioned = rewrite
        .clauses()
        .iter()
        .map(|clause| clause.cell().clone())
        .collect::<BTreeSet<_>>();
    let omitted = rewrite
        .omitted_siblings()
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    if mentioned.len() != rewrite.clauses().len()
        || omitted.len() != rewrite.omitted_siblings().len()
        || !mentioned.is_disjoint(&omitted)
        || mentioned.union(&omitted).cloned().collect::<BTreeSet<_>>()
            != leaf_sorts.keys().cloned().collect()
    {
        return Err(L::error(ValidationError::InvalidCellFraming));
    }
    insert_node::<L>(nodes, rewrite.origin().key())?;
    for clause in rewrite.clauses() {
        let sort = leaf_sorts
            .get(clause.cell())
            .ok_or(L::error(ValidationError::InvalidCellFraming))?;
        insert_node::<L>(nodes, clause.origin().key())?;
        validate_term::<L>(
            clause.before(),
            scope,
            declarations,
            signatures,
            sort_parents,
            nodes,
        )?;
        if clause.before().sort() != sort {
            return Err(L::error(ValidationError::CellFrameSortMismatch));
        }
        if let CellPost::Replace { term } = clause.after() {
            validate_term::<L>(term, scope, declarations, signatures, sort_parents, nodes)?;
            if term.sort() != sort {
                return Err(L::error(ValidationError::CellFrameSortMismatch));
            }
        }
        validate_cell_frame::<L>(clause, sort, scope, nodes)?;
    }
    Ok(())
}

pub(crate) fn validate_cell_frame<L: Validation>(
    clause: &FixedCellClause<L::Cell, IrTerm<L>>,
    sort: &L::Sort,
    scope: &BTreeMap<SemanticId, L::Sort>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    let (origin, binding, required_sort) = match clause.frame() {
        CellContentFrame::Exact => return Ok(()),
        CellContentFrame::KSequenceTail { origin, binding } => {
            (origin, binding, L::builtin_sort(BuiltinSort::KSequence))
        }
        CellContentFrame::MapRemainder { origin, binding } => {
            (origin, binding, L::builtin_sort(BuiltinSort::Map))
        }
    };
    insert_node::<L>(nodes, origin.key())?;
    if sort != &required_sort {
        return Err(L::error(ValidationError::CellFrameSortMismatch));
    }
    if let Some(binding) = binding
        && scope.get(binding) != Some(&required_sort)
    {
        return Err(L::error(ValidationError::CellFrameBindingMismatch(
            binding.clone(),
        )));
    }
    Ok(())
}

#[expect(
    clippy::too_many_arguments,
    clippy::too_many_lines,
    reason = "The ordered rule checks must preserve the first reported failure."
)]
pub(crate) fn validate_rule<L: Validation>(
    sentence: &L::Rule,
    configuration: Option<&FixedConfiguration<L::Sort, L::Cell, IrTerm<L>>>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    functional_productions: &BTreeSet<L::Declaration>,
    alias_productions: &BTreeSet<L::Declaration>,
    sort_parents: &SortParents<L>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    let rule = L::rule_view(sentence);
    let claim = match (rule.kind, rule.claim) {
        (SentenceKind::Claim, Some(claim)) => Some(claim),
        (SentenceKind::Claim, None) | (_, Some(_)) => {
            return Err(L::error(ValidationError::InvalidClaimMetadata(
                rule.id.clone(),
            )));
        }
        (_, None) => None,
    };
    if rule.kind == SentenceKind::Claim {
        if rule.priority.is_some() || rule.simplification.is_some() {
            return Err(L::error(ValidationError::InvalidClaimMetadata(
                rule.id.clone(),
            )));
        }
        L::claim_label(sentence)?;
        if !matches!(rule.body, RuleBodyRef::Configuration { .. }) {
            return Err(L::error(ValidationError::ClaimBodyNotConfiguration(
                rule.id.clone(),
            )));
        }
    }
    L::rule_label_origin(sentence, nodes)?;
    let scope = variable_scope::<L>(rule.variables, declarations)?;
    match rule.body {
        RuleBodyRef::Term(body) => {
            insert_node::<L>(nodes, body.origin().key())?;
            require_sort::<L>(declarations, body.sort())?;
            validate_term::<L>(
                body.from(),
                &scope,
                declarations,
                signatures,
                sort_parents,
                nodes,
            )?;
            validate_term::<L>(
                body.to(),
                &scope,
                declarations,
                signatures,
                sort_parents,
                nodes,
            )?;
            if !is_subsort::<L>(body.from().sort(), body.sort(), sort_parents)
                || !is_subsort::<L>(body.to().sort(), body.sort(), sort_parents)
            {
                return Err(L::error(ValidationError::RewriteSortMismatch));
            }
            let from = body.from();
            if rule.kind == SentenceKind::Equation {
                let IrTermKind::Application {
                    application: ApplicationRef::Declared(production),
                    ..
                } = from.kind()
                else {
                    return Err(L::error(ValidationError::InvalidEquationRoot(
                        rule.id.clone(),
                    )));
                };
                if !functional_productions.contains(production) {
                    return Err(L::error(ValidationError::InvalidEquationRoot(
                        rule.id.clone(),
                    )));
                }
            }
            if rule.kind == SentenceKind::Alias {
                let IrTermKind::Application {
                    application: ApplicationRef::Declared(production),
                    ..
                } = from.kind()
                else {
                    return Err(L::error(ValidationError::InvalidAliasRoot(rule.id.clone())));
                };
                if !alias_productions.contains(production) {
                    return Err(L::error(ValidationError::InvalidAliasRoot(rule.id.clone())));
                }
            }
            if rule.kind == SentenceKind::Simplification {
                match from.kind() {
                    IrTermKind::Application {
                        application: ApplicationRef::Declared(production),
                        ..
                    } if functional_productions.contains(production) => {}
                    IrTermKind::Application {
                        application: ApplicationRef::Builtin(operation),
                        ..
                    } if operation.is_functional() => {}
                    _ => {
                        return Err(L::error(ValidationError::InvalidSimplificationRoot(
                            rule.id.clone(),
                        )));
                    }
                }
            }
        }
        RuleBodyRef::Configuration { body, .. } => {
            let configuration = configuration.ok_or_else(|| {
                L::error(ValidationError::ConfigurationRuleWithoutFixedConfiguration(
                    rule.id.clone(),
                ))
            })?;
            if body.configuration() != configuration.id() {
                return Err(L::error(ValidationError::ConfigurationRuleTargetMismatch(
                    rule.id.clone(),
                )));
            }
            validate_configuration_rewrite::<L>(
                body,
                configuration,
                &scope,
                declarations,
                signatures,
                sort_parents,
                nodes,
            )?;
        }
    }
    if rule.kind == SentenceKind::Simplification {
        let Some(simplification) = rule.simplification else {
            return Err(L::error(ValidationError::InvalidSimplificationMetadata(
                rule.id.clone(),
            )));
        };
        insert_node::<L>(nodes, simplification.origin().key())?;
        if let Some(priority) = simplification.priority() {
            insert_node::<L>(nodes, priority.origin().key())?;
        }
    } else if rule.simplification.is_some() {
        return Err(L::error(ValidationError::InvalidSimplificationMetadata(
            rule.id.clone(),
        )));
    }
    if let Some(priority) = rule.priority {
        if !matches!(rule.kind, SentenceKind::Equation | SentenceKind::Transition) {
            return Err(L::error(ValidationError::InvalidRulePriority(
                rule.id.clone(),
            )));
        }
        insert_node::<L>(nodes, priority.origin().key())?;
    }
    if let Some(condition) = rule.requires {
        if rule.kind == SentenceKind::Alias {
            return Err(L::error(ValidationError::AliasCondition));
        }
        insert_node::<L>(nodes, condition.origin().key())?;
        validate_term::<L>(
            condition.term(),
            &scope,
            declarations,
            signatures,
            sort_parents,
            nodes,
        )?;
        if condition.term().sort() != &L::builtin_sort(BuiltinSort::Bool) {
            return Err(L::error(ValidationError::RuleConditionSortMismatch));
        }
    }
    if let Some(claim) = claim {
        validate_claim::<L>(
            sentence,
            claim,
            &scope,
            declarations,
            signatures,
            sort_parents,
            nodes,
        )?;
    }
    let mut used = BTreeSet::new();
    match rule.body {
        RuleBodyRef::Term(body) => {
            collect_term_variables::<L>(body.from(), &mut used);
            collect_term_variables::<L>(body.to(), &mut used);
        }
        RuleBodyRef::Configuration { body, .. } => {
            for clause in body.clauses() {
                collect_term_variables::<L>(clause.before(), &mut used);
                if let CellPost::Replace { term } = clause.after() {
                    collect_term_variables::<L>(term, &mut used);
                }
                match clause.frame() {
                    CellContentFrame::Exact => {}
                    CellContentFrame::KSequenceTail { binding, .. }
                    | CellContentFrame::MapRemainder { binding, .. } => {
                        if let Some(binding) = binding {
                            used.insert(binding.clone());
                        }
                    }
                }
            }
        }
    }
    if let Some(condition) = rule.requires {
        collect_term_variables::<L>(condition.term(), &mut used);
    }
    if let Some(ensures) = claim.and_then(IrClaim::ensures) {
        collect_term_variables::<L>(ensures.term(), &mut used);
    }
    if used != scope.keys().cloned().collect() {
        return Err(L::error(ValidationError::VariableClosure));
    }
    Ok(())
}

pub(crate) fn validate_claim<L: Validation>(
    sentence: &L::Rule,
    claim: &IrClaim<L>,
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    let rule = L::rule_view(sentence);
    insert_node::<L>(nodes, claim.modality_origin().key())?;
    if let Some(origin) = claim.circularity_origin() {
        insert_node::<L>(nodes, origin.key())?;
    }

    let mut binder_ids = BTreeSet::new();
    for binder in claim.universals().iter().chain(claim.existentials()) {
        if !binder_ids.insert(binder.id().clone()) || scope.get(binder.id()) != Some(binder.sort())
        {
            return Err(L::error(ValidationError::InvalidClaimBinder(
                binder.id().clone(),
            )));
        }
        require_sort::<L>(declarations, binder.sort())?;
        insert_node::<L>(nodes, binder.origin().key())?;
        insert_node::<L>(nodes, binder.name_origin().key())?;
        insert_node::<L>(nodes, binder.sort_origin().key())?;
    }

    let mut left_uses = BTreeSet::new();
    let mut right_uses = BTreeSet::new();
    let RuleBodyRef::Configuration { body, .. } = rule.body else {
        return Err(L::error(ValidationError::ClaimBodyNotConfiguration(
            rule.id.clone(),
        )));
    };
    for clause in body.clauses() {
        collect_term_variables::<L>(clause.before(), &mut left_uses);
        if let CellPost::Replace { term } = clause.after() {
            collect_term_variables::<L>(term, &mut right_uses);
        }
        match clause.frame() {
            CellContentFrame::Exact => {}
            CellContentFrame::KSequenceTail { binding, .. }
            | CellContentFrame::MapRemainder { binding, .. } => {
                if let Some(binding) = binding {
                    left_uses.insert(binding.clone());
                }
            }
        }
    }
    if let Some(requires) = rule.requires {
        collect_term_variables::<L>(requires.term(), &mut left_uses);
    }
    if let Some(ensures) = claim.ensures() {
        insert_node::<L>(nodes, ensures.origin().key())?;
        validate_term::<L>(
            ensures.term(),
            scope,
            declarations,
            signatures,
            sort_parents,
            nodes,
        )?;
        if ensures.term().sort() != &L::builtin_sort(BuiltinSort::Bool) {
            return Err(L::error(ValidationError::RuleConditionSortMismatch));
        }
        collect_term_variables::<L>(ensures.term(), &mut right_uses);
    }
    for binder in claim.existentials() {
        if left_uses.contains(binder.id()) {
            return Err(L::error(ValidationError::ExistentialScopeViolation(
                binder.id().clone(),
            )));
        }
        if !right_uses.contains(binder.id()) {
            return Err(L::error(ValidationError::UnusedExistential(
                binder.id().clone(),
            )));
        }
    }
    Ok(())
}

pub(crate) fn collect_term_variables<L: Validation>(
    term: &IrTerm<L>,
    used: &mut BTreeSet<SemanticId>,
) {
    match term.kind() {
        IrTermKind::Variable { variable } => {
            used.insert(variable.clone());
        }
        IrTermKind::Application { arguments, .. }
        | IrTermKind::Map { arguments, .. }
        | IrTermKind::List { arguments, .. }
        | IrTermKind::Set { arguments, .. } => {
            for argument in arguments {
                collect_term_variables::<L>(argument, used);
            }
        }
        IrTermKind::KSequence { items, .. } => {
            for item in items {
                collect_term_variables::<L>(item, used);
            }
        }
        IrTermKind::Rewrite { from, to } => {
            collect_term_variables::<L>(from, used);
            collect_term_variables::<L>(to, used);
        }
        IrTermKind::Cell { children, .. } => {
            for child in children {
                collect_term_variables::<L>(child, used);
            }
        }
        IrTermKind::Token { .. } => {}
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "The closed shape checks must preserve the first reported failure."
)]
pub(crate) fn validate_term<L: Validation>(
    term: &IrTerm<L>,
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    insert_node::<L>(nodes, term.origin().key())?;
    require_sort::<L>(declarations, term.sort())?;
    match term.kind() {
        IrTermKind::Variable { variable } => match scope.get(variable) {
            None => {
                return Err(L::error(ValidationError::DanglingVariable(
                    variable.clone(),
                )));
            }
            Some(sort) if sort != term.sort() => {
                return Err(L::error(ValidationError::VariableSortMismatch(
                    variable.clone(),
                )));
            }
            Some(_) => {}
        },
        IrTermKind::Application {
            application,
            arguments,
        } => {
            let signature = match application {
                ApplicationRef::Declared(production) => {
                    L::application_signature(declarations, signatures, production)?
                }
                ApplicationRef::Builtin(operation) => builtin_signature::<L>(*operation),
            };
            let (result_sort, argument_sorts) = signature;
            if *term.sort() != result_sort
                || arguments.len() != argument_sorts.len()
                || arguments
                    .iter()
                    .zip(&argument_sorts)
                    .any(|(argument, sort)| !is_subsort::<L>(argument.sort(), sort, sort_parents))
            {
                return match application {
                    ApplicationRef::Declared(production) => Err(L::error(
                        ValidationError::ApplicationSignature(production.clone()),
                    )),
                    ApplicationRef::Builtin(operation) => Err(L::error(
                        ValidationError::BuiltinApplicationSignature(*operation),
                    )),
                };
            }
            for argument in arguments {
                validate_term::<L>(
                    argument,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    nodes,
                )?;
            }
        }
        IrTermKind::Token { value } => {
            if value.is_empty() {
                return Err(L::error(ValidationError::EmptyText(
                    crate::IrField::TokenValue,
                )));
            }
        }
        IrTermKind::KSequence { item_sort, items } => {
            require_sort::<L>(declarations, item_sort)?;
            if *term.sort() != L::builtin_sort(BuiltinSort::KSequence) {
                return Err(L::error(ValidationError::SequenceSortMismatch));
            }
            for item in items {
                validate_term::<L>(item, scope, declarations, signatures, sort_parents, nodes)?;
                if !is_subsort::<L>(item.sort(), item_sort, sort_parents) {
                    return Err(L::error(ValidationError::SequenceItemSortMismatch));
                }
            }
        }
        IrTermKind::Map {
            operation,
            arguments,
        } => {
            let map_sort = L::builtin_sort(BuiltinSort::Map);
            let bool_sort = L::builtin_sort(BuiltinSort::Bool);
            let valid_arity = match operation {
                MapOperation::Empty => *term.sort() == map_sort && arguments.is_empty(),
                MapOperation::Item => {
                    *term.sort() == map_sort
                        && !arguments.is_empty()
                        && arguments.len().is_multiple_of(2)
                }
                MapOperation::Update => {
                    *term.sort() == map_sort
                        && arguments.len() == 3
                        && arguments[0].sort == map_sort
                }
                MapOperation::Get => arguments.len() == 2 && arguments[0].sort == map_sort,
                MapOperation::InKeys => {
                    *term.sort() == bool_sort
                        && arguments.len() == 2
                        && arguments[1].sort == map_sort
                }
            };
            if !valid_arity {
                return Err(L::error(ValidationError::MapOperationSignature(*operation)));
            }
            for argument in arguments {
                validate_term::<L>(
                    argument,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    nodes,
                )?;
            }
        }
        IrTermKind::List {
            operation,
            arguments,
        } => {
            let list_sort = L::builtin_sort(BuiltinSort::List);
            let int_sort = L::builtin_sort(BuiltinSort::Int);
            let valid = match operation {
                ListOperation::Empty => *term.sort() == list_sort && arguments.is_empty(),
                ListOperation::Item => *term.sort() == list_sort && arguments.len() == 1,
                ListOperation::Concat => {
                    *term.sort() == list_sort
                        && arguments.len() == 2
                        && arguments
                            .iter()
                            .all(|argument| *argument.sort() == list_sort)
                }
                ListOperation::Get => {
                    arguments.len() == 2
                        && arguments[0].sort == list_sort
                        && arguments[1].sort == int_sort
                }
                ListOperation::Update => {
                    *term.sort() == list_sort
                        && arguments.len() == 3
                        && arguments[0].sort == list_sort
                        && arguments[1].sort == int_sort
                }
                ListOperation::Size => {
                    *term.sort() == int_sort
                        && arguments.len() == 1
                        && arguments[0].sort == list_sort
                }
                ListOperation::Make => {
                    *term.sort() == list_sort
                        && arguments.len() == 2
                        && arguments[0].sort == int_sort
                }
                ListOperation::Range => {
                    *term.sort() == list_sort
                        && arguments.len() == 3
                        && arguments[0].sort == list_sort
                        && arguments[1].sort == int_sort
                        && arguments[2].sort == int_sort
                }
                ListOperation::UpdateAll => {
                    *term.sort() == list_sort
                        && arguments.len() == 3
                        && arguments[0].sort == list_sort
                        && arguments[1].sort == int_sort
                        && arguments[2].sort == list_sort
                }
            };
            if !valid {
                return Err(L::error(ValidationError::ListOperationSignature(
                    *operation,
                )));
            }
            for argument in arguments {
                validate_term::<L>(
                    argument,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    nodes,
                )?;
            }
        }
        IrTermKind::Set {
            operation,
            arguments,
        } => {
            let set_sort = L::builtin_sort(BuiltinSort::Set);
            let bool_sort = L::builtin_sort(BuiltinSort::Bool);
            let valid = match operation {
                SetOperation::Empty => *term.sort() == set_sort && arguments.is_empty(),
                SetOperation::Item => *term.sort() == set_sort && arguments.len() == 1,
                SetOperation::Concat | SetOperation::Union => {
                    *term.sort() == set_sort
                        && arguments.len() == 2
                        && arguments
                            .iter()
                            .all(|argument| *argument.sort() == set_sort)
                }
                SetOperation::Contains => {
                    *term.sort() == bool_sort
                        && arguments.len() == 2
                        && arguments[1].sort == set_sort
                }
            };
            if !valid {
                return Err(L::error(ValidationError::SetOperationSignature(*operation)));
            }
            for argument in arguments {
                validate_term::<L>(
                    argument,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    nodes,
                )?;
            }
        }
        IrTermKind::Cell { cell, children } => {
            L::require_cell(declarations, cell)?;
            if children.is_empty() {
                return Err(L::error(ValidationError::InvalidCellFraming));
            }
            for child in children {
                validate_term::<L>(child, scope, declarations, signatures, sort_parents, nodes)?;
            }
        }
        IrTermKind::Rewrite { from, to } => {
            validate_term::<L>(from, scope, declarations, signatures, sort_parents, nodes)?;
            validate_term::<L>(to, scope, declarations, signatures, sort_parents, nodes)?;
            if !is_subsort::<L>(from.sort(), term.sort(), sort_parents)
                || !is_subsort::<L>(to.sort(), term.sort(), sort_parents)
            {
                return Err(L::error(ValidationError::RewriteSortMismatch));
            }
        }
    }
    Ok(())
}

#[expect(
    clippy::too_many_lines,
    reason = "The closed shape checks must preserve the first reported failure."
)]
pub(crate) fn validate_production_shape<L: Validation>(
    id: &L::Declaration,
    result_sort: &L::Sort,
    items: &[GrammarProductionItem<L::Sort>],
    attributes: &[ProductionAttribute<L::Sort>],
) -> Result<(), L::Error> {
    if items.is_empty() {
        return Err(L::error(ValidationError::EmptyProduction(id.clone())));
    }
    let fields = items
        .iter()
        .filter_map(|item| match item.kind() {
            GrammarProductionItemKind::NonTerminal { field, .. } => Some(field.clone()),
            GrammarProductionItemKind::Terminal { .. }
            | GrammarProductionItemKind::RegexTerminal { .. } => None,
        })
        .collect::<Vec<_>>();
    if has_duplicate_fields(&fields) {
        return Err(L::error(ValidationError::InvalidStrictnessField));
    }
    let regexes = items
        .iter()
        .filter(|item| matches!(item.kind(), GrammarProductionItemKind::RegexTerminal { .. }))
        .count();
    let mut token = false;
    let mut function = false;
    let mut total = false;
    let mut hook = None;
    let mut alias = false;
    let mut group = false;
    let mut bracket = false;
    let mut avoid = false;
    let mut format = false;
    let mut strictness = false;
    for attribute in attributes {
        let already = match attribute {
            ProductionAttribute::Documentation { .. } => continue,
            ProductionAttribute::Function { .. } => std::mem::replace(&mut function, true),
            ProductionAttribute::Total { .. } => std::mem::replace(&mut total, true),
            ProductionAttribute::Hook { operation, .. } => hook.replace(*operation).is_some(),
            ProductionAttribute::Alias { .. } => std::mem::replace(&mut alias, true),
            ProductionAttribute::Token { .. } => std::mem::replace(&mut token, true),
            ProductionAttribute::Group { .. } => std::mem::replace(&mut group, true),
            ProductionAttribute::Bracket { .. } => std::mem::replace(&mut bracket, true),
            ProductionAttribute::Avoid { .. } => std::mem::replace(&mut avoid, true),
            ProductionAttribute::Format { .. } => std::mem::replace(&mut format, true),
            ProductionAttribute::Strictness { .. } => std::mem::replace(&mut strictness, true),
        };
        if already {
            let name = attribute
                .unique_family()
                .expect("repeatable documentation was skipped above");
            return Err(L::error(ValidationError::DuplicateProductionAttribute(
                name,
            )));
        }
        match attribute {
            ProductionAttribute::Strictness {
                fields: selected, ..
            } => {
                if selected.is_empty()
                    || has_duplicate_fields(&selected.iter().map(|field| field.field().clone()).collect::<Vec<_>>())
                    || selected.iter().any(|field| !fields.contains(field.field()))
                {
                    return Err(L::error(ValidationError::InvalidStrictnessField));
                }
            }
            ProductionAttribute::Format { fragments, .. } => {
                if fragments.is_empty()
                    || fragments.iter().any(|fragment| {
                        matches!(fragment, FormatFragment::Item(position) if *position == 0 || usize::from(*position) > items.len())
                    })
                {
                    return Err(L::error(ValidationError::InvalidFormat));
                }
            }
            ProductionAttribute::Documentation { .. }
            | ProductionAttribute::Function { .. }
            | ProductionAttribute::Total { .. }
            | ProductionAttribute::Hook { .. }
            | ProductionAttribute::Alias { .. }
            | ProductionAttribute::Token { .. }
            | ProductionAttribute::Group { .. }
            | ProductionAttribute::Bracket { .. }
            | ProductionAttribute::Avoid { .. } => {}
        }
    }
    if total && !function {
        return Err(L::error(ValidationError::InvalidFunctionProduction));
    }
    if hook.is_some() && !(function && total) {
        return Err(L::error(ValidationError::InvalidFunctionProduction));
    }
    if let Some(operation) = hook {
        let argument_sorts = items
            .iter()
            .filter_map(|item| match item.kind() {
                GrammarProductionItemKind::NonTerminal { sort, .. } => Some(sort),
                GrammarProductionItemKind::Terminal { .. }
                | GrammarProductionItemKind::RegexTerminal { .. } => None,
            })
            .collect::<Vec<_>>();
        let valid_signature = match operation.spec().signature {
            HookSignature::Builtin {
                result_sort: expected_result,
                argument_sorts: expected_arguments,
                ..
            } => {
                result_sort == &L::builtin_sort(expected_result)
                    && argument_sorts.len() == expected_arguments.len()
                    && argument_sorts
                        .iter()
                        .zip(expected_arguments)
                        .all(|(actual, expected)| *actual == &L::builtin_sort(*expected))
            }
            HookSignature::DeclaredPoint {
                result_sort: expected_result,
                argument_sorts: expected_arguments,
                ..
            } => {
                let matches = |actual: &L::Sort, expected: HookSortConstraint| match expected {
                    HookSortConstraint::Builtin(sort) => actual == &L::builtin_sort(sort),
                    HookSortConstraint::Declared => L::declared_sort(actual).is_some(),
                    HookSortConstraint::Result => actual == result_sort,
                };
                matches(result_sort, expected_result)
                    && argument_sorts.len() == expected_arguments.len()
                    && argument_sorts
                        .iter()
                        .zip(expected_arguments)
                        .all(|(actual, expected)| matches(actual, *expected))
            }
        };
        if !valid_signature {
            return Err(L::error(ValidationError::InvalidHookSignature(operation)));
        }
    }
    if alias && function {
        return Err(L::error(ValidationError::InvalidAliasProduction));
    }
    if token && (items.len() != 1 || regexes != 1) {
        return Err(L::error(ValidationError::InvalidTokenProduction));
    }
    if regexes != 0 && !token {
        return Err(L::error(ValidationError::RegexWithoutToken));
    }
    if bracket && fields.len() != 1 {
        return Err(L::error(ValidationError::InvalidBracketProduction));
    }
    Ok(())
}

fn has_duplicate_fields(fields: &[ProductionFieldId]) -> bool {
    let mut unique = BTreeSet::new();
    fields.iter().any(|field| !unique.insert(field))
}

pub(crate) fn builtin_signature<L: Validation>(
    operation: BuiltinOperation,
) -> (L::Sort, Vec<L::Sort>) {
    (
        L::builtin_sort(operation.result_sort()),
        operation
            .argument_sorts()
            .iter()
            .copied()
            .map(L::builtin_sort)
            .collect(),
    )
}

pub(crate) fn validate_precedence_order<L: Validation>(
    modules: &[L::Module],
) -> Result<(), L::Error> {
    let mut edges: BTreeMap<ProductionGroupId, BTreeSet<ProductionGroupId>> = BTreeMap::new();
    for relation in modules.iter().flat_map(L::precedences) {
        for higher in relation.higher() {
            for lower in relation.lower() {
                edges
                    .entry(higher.clone())
                    .or_default()
                    .insert(lower.clone());
            }
        }
    }
    for start in edges.keys() {
        let mut pending = edges
            .get(start)
            .into_iter()
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        while let Some(group) = pending.pop() {
            if &group == start {
                return Err(L::error(ValidationError::PrecedenceCycle(start.clone())));
            }
            if visited.insert(group.clone()) {
                pending.extend(edges.get(&group).into_iter().flatten().cloned());
            }
        }
    }
    Ok(())
}

pub(crate) fn validate_subsort_order<L: Validation>(
    edges: &BTreeMap<L::Sort, Vec<L::Sort>>,
) -> Result<(), L::Error> {
    for start in edges.keys() {
        let mut pending = edges
            .get(start)
            .into_iter()
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        while let Some(sort) = pending.pop() {
            if &sort == start {
                return Err(L::error(ValidationError::SubsortCycle(start.clone())));
            }
            if visited.insert(sort.clone()) {
                pending.extend(edges.get(&sort).into_iter().flatten().cloned());
            }
        }
    }
    Ok(())
}

pub(crate) fn is_subsort<L: Validation>(
    candidate: &L::Sort,
    expected: &L::Sort,
    parents: &BTreeMap<L::Sort, Vec<L::Sort>>,
) -> bool {
    let mut pending = vec![candidate];
    let mut visited = BTreeSet::new();
    while let Some(sort) = pending.pop() {
        if sort == expected {
            return true;
        }
        if visited.insert(sort) {
            pending.extend(parents.get(sort).into_iter().flatten());
        }
    }
    false
}

/// Checks an intrinsic declaration role before it enters a level's graph.
pub(crate) fn expect_kind<L: Validation>(
    id: &L::Declaration,
    actual: L::Kind,
    expected: L::Kind,
) -> Result<(), L::Error> {
    if actual == expected {
        Ok(())
    } else {
        Err(L::wrong_kind(id, expected, actual))
    }
}

/// Checks a referenced role without changing either level's missing-reference error.
pub(crate) fn require_kind<L: Validation>(
    declarations: &Declarations<L>,
    id: &L::Declaration,
    expected: L::Kind,
) -> Result<(), L::Error> {
    match declarations.get(id) {
        None => Err(L::missing_declaration(id)),
        Some(actual) => expect_kind::<L>(id, *actual, expected),
    }
}

pub(crate) fn collect_configuration_nodes<L: Validation>(
    configuration: &Configuration<L>,
    registration: &mut L::Registration<'_>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    fn cells<L: Validation>(
        values: &[FixedCell<L::Sort, L::Cell>],
        registration: &mut L::Registration<'_>,
        nodes: &mut BTreeSet<SourceMapKey>,
    ) -> Result<(), L::Error> {
        for cell in values {
            L::register_cell(registration, cell)?;
            insert_node::<L>(nodes, cell.origin().key())?;
            for attribute in cell.attributes() {
                insert_node::<L>(nodes, attribute.origin().key())?;
            }
            if let FixedCellContent::Children { children } = cell.content() {
                cells::<L>(children, registration, nodes)?;
            }
        }
        Ok(())
    }
    fn initializer<L: Validation>(
        values: &[FixedInitializerCell<L::Cell, IrTerm<L>>],
        nodes: &mut BTreeSet<SourceMapKey>,
    ) -> Result<(), L::Error> {
        for cell in values {
            insert_node::<L>(nodes, cell.origin().key())?;
            if let FixedInitializerContent::Children { children } = cell.content() {
                initializer::<L>(children, nodes)?;
            }
        }
        Ok(())
    }
    if let Some(origin) = configuration.root().origin() {
        insert_node::<L>(nodes, origin.key())?;
    }
    for variable in configuration.variables() {
        insert_node::<L>(nodes, variable.origin().key())?;
    }
    cells::<L>(configuration.cells(), registration, nodes)?;
    initializer::<L>(configuration.initializer(), nodes)
}
