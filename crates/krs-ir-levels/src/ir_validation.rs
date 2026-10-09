//! Shared shape validation with level-specific identity and context checks.

use crate::ir_level::{
    IrClaim, IrLevel, IrRuleCondition, IrRulePriority, IrSimplification, IrTerm, IrTermKind,
    IrVariable, RuleBodyRef,
};
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, CellClauseKind, CellContentFrame, CellPost,
    CollectionOperandSort, CollectionOperationSpec, CollectionResultSort, FixedCell,
    FixedCellClause, FixedCellContent, FixedConfiguration, FixedConfigurationRewrite,
    FixedInitializerCell, FixedInitializerContent, FormatFragment, GeneratedOperation,
    GrammarProductionItem, GrammarProductionItemKind, HookOperation, HookPointSortSource,
    HookSignature, HookSortConstraint, ListOperation, MapOperation, OperationSort,
    PrecedenceRelation, ProductionAttribute, ProductionFieldId, ProductionGroupId, SemanticId,
    SentenceKind, SetOperation, SourceMapKey,
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
    pub existentials: &'a [crate::IrScopedBinder<L>],
    pub ensures: Option<&'a IrRuleCondition<L>>,
    pub fresh: &'a [crate::IrScopedBinder<L>],
    pub restriction: Option<&'a crate::IrMatchRestriction>,
    pub anywhere: bool,
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
    /// The generated sort of a nested cell: `Cell(declaration)` in Semantic
    /// IR (absent when the cell records no declaration), `Cell(symbol)` in
    /// Definition IR.
    fn group_sort(cell: &FixedCell<Self::Sort, Self::Cell>) -> Option<Self::Sort>;
    /// Extracts the cell named by a group-cell sort (`IrSortRef::Cell`).
    fn cell_sort(sort: &Self::Sort) -> Option<&Self::Declaration>;
    /// Checks the cell named by a group-cell sort (`IrSortRef::Cell`): a
    /// nominal `#[k::cell]` declaration in Semantic IR, a fixed-cell symbol in
    /// Definition IR.
    fn require_cell_sort(
        declarations: &Declarations<Self>,
        id: &Self::Declaration,
    ) -> Result<(), Self::Error>;
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
    /// Definition cell references must retain their check before content validation.
    /// Semantic references must be checked in the final reference pass after existing theory checks succeed.
    const CHECK_CELL_REFERENCES_DURING_TERM_VALIDATION: bool;
    /// Cell references must name a registered fixed cell at the current level.
    fn require_cell(
        declarations: &Declarations<Self>,
        cell_ids: &BTreeSet<Self::Cell>,
        cell: &Self::Cell,
    ) -> Result<(), Self::Error>;
    /// Maps shared failures to the level-specific public variants, including Semantic boxed identities.
    fn error(error: ValidationError<Self>) -> Self::Error;
}

pub(crate) enum ValidationError<L: Validation> {
    AliasCondition,
    ApplicationSignature(L::Declaration),
    BuiltinApplicationSignature(BuiltinOperation),
    GeneratedApplicationSignature,
    CellFrameBindingMismatch(SemanticId),
    CellFrameSortMismatch,
    ContextAliasFrameSortMismatch,
    ContextAliasFrameBindingMismatch(SemanticId),
    ContextAliasVariableClosure,
    ClaimBodyNotConfiguration(L::RuleId),
    ConfigurationRuleTargetMismatch(L::RuleId),
    ConfigurationRuleWithoutFixedConfiguration(L::RuleId),
    DanglingVariable(SemanticId),
    DuplicateProductionAttribute(krs_ir::ProductionAttributeFamily),
    DuplicateSourceMapKey(SourceMapKey),
    DuplicateVariable(SemanticId),
    EmptyProduction(L::Declaration),
    EmptyText(krs_ir::IrField),
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
    InvalidSmtMetadata,
    InvalidColors,
    InternalWithProgram,
    PreferAndAvoid,
    AliasWithDesugar,
    PreferOnParseOnlyProduction,
    InvalidOverloadProduction,
    InvalidListProduction,
    InvalidFunctionProduction,
    InvalidHookSignature(HookOperation),
    InvalidBn128PointConstructor {
        hook: HookOperation,
        sort: String,
        expected_signature: krs_ir::Bn128PointSignature,
        matching_constructors: usize,
    },
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
    InvalidRuleExistentials(L::RuleId),
    InvalidRuleFresh(L::RuleId),
    InvalidMatchRestriction(L::RuleId),
    FreshScopeViolation(SemanticId),
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
    if let Some(id) = L::cell_sort(sort) {
        L::require_cell_sort(declarations, id)?;
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
    cell_ids: &BTreeSet<L::Cell>,
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
                krs_ir::IrField::DuplicateExternalConfigurationVariable,
            )));
        }
        main_count += usize::from(variable.is_main());
    }
    if main_count > 1 {
        return Err(L::error(ValidationError::EmptyText(
            krs_ir::IrField::MultipleMainConfigurationVariables,
        )));
    }
    validate_initializer_forest::<L>(
        configuration.cells(),
        configuration.initializer(),
        &scope,
        declarations,
        signatures,
        sort_parents,
        cell_ids,
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

#[expect(
    clippy::too_many_arguments,
    reason = "Validation carries the cell registry alongside declaration, sort, scope, and provenance contexts."
)]
pub(crate) fn validate_initializer_forest<L: Validation>(
    cells: &[FixedCell<L::Sort, L::Cell>],
    initializer: &[FixedInitializerCell<L::Cell, IrTerm<L>>],
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    cell_ids: &BTreeSet<L::Cell>,
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
                validate_term::<L>(
                    term,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
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
                cell_ids,
                nodes,
            )?,
            _ => return Err(L::error(ValidationError::InitializerTreeMismatch)),
        }
    }
    Ok(())
}

fn configuration_leaf_sorts<L: Validation>(
    configuration: &Configuration<L>,
) -> Result<BTreeMap<L::Cell, L::Sort>, L::Error> {
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
    Ok(leaf_sorts)
}

/// Nested (group) cells with their generated cell sort, when the level can
/// name it, and every leaf below them.
type GroupCells<L> =
    BTreeMap<<L as IrLevel>::Cell, (Option<<L as IrLevel>::Sort>, BTreeSet<<L as IrLevel>::Cell>)>;

fn configuration_groups<L: Validation>(configuration: &Configuration<L>) -> GroupCells<L> {
    fn leaves<L: Validation>(cell: &FixedCell<L::Sort, L::Cell>, output: &mut BTreeSet<L::Cell>) {
        match cell.content() {
            FixedCellContent::Term { .. } => {
                output.insert(cell.id().clone());
            }
            FixedCellContent::Children { children } => {
                for child in children {
                    leaves::<L>(child, output);
                }
            }
        }
    }
    fn groups<L: Validation>(cells: &[FixedCell<L::Sort, L::Cell>], output: &mut GroupCells<L>) {
        for cell in cells {
            if let FixedCellContent::Children { children } = cell.content() {
                let mut below = BTreeSet::new();
                leaves::<L>(cell, &mut below);
                output.insert(cell.id().clone(), (L::group_sort(cell), below));
                groups::<L>(children, output);
            }
        }
    }
    let mut output = BTreeMap::new();
    groups::<L>(configuration.cells(), &mut output);
    output
}

#[expect(
    clippy::too_many_arguments,
    reason = "Validation carries the cell registry alongside declaration, sort, scope, and provenance contexts."
)]
pub(crate) fn validate_configuration_rewrite<L: Validation>(
    rewrite: &FixedConfigurationRewrite<L::Cell, IrTerm<L>>,
    configuration: &FixedConfiguration<L::Sort, L::Cell, IrTerm<L>>,
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    cell_ids: &BTreeSet<L::Cell>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    let leaf_sorts = configuration_leaf_sorts::<L>(configuration)?;
    let groups = configuration_groups::<L>(configuration);
    let omitted = rewrite
        .omitted_siblings()
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    // Each clause covers its leaf, or every leaf below its whole group cell
    // (KF-016); covered and omitted leaves partition the configuration.
    let mut covered = BTreeSet::new();
    let mut disjoint = omitted.len() == rewrite.omitted_siblings().len();
    for clause in rewrite.clauses() {
        let leaves = match clause.kind() {
            CellClauseKind::Content => leaf_sorts
                .contains_key(clause.cell())
                .then(|| vec![clause.cell().clone()]),
            CellClauseKind::Whole => groups
                .get(clause.cell())
                .map(|(_, leaves)| leaves.iter().cloned().collect()),
        }
        .ok_or(L::error(ValidationError::InvalidCellFraming))?;
        for leaf in leaves {
            disjoint &= !omitted.contains(&leaf) && covered.insert(leaf);
        }
    }
    if !disjoint
        || covered.union(&omitted).cloned().collect::<BTreeSet<_>>()
            != leaf_sorts.keys().cloned().collect()
    {
        return Err(L::error(ValidationError::InvalidCellFraming));
    }
    insert_node::<L>(nodes, rewrite.origin().key())?;
    for clause in rewrite.clauses() {
        let sort = match clause.kind() {
            CellClauseKind::Content => leaf_sorts.get(clause.cell()),
            CellClauseKind::Whole => groups
                .get(clause.cell())
                .and_then(|(sort, _)| sort.as_ref())
                .filter(|_| clause.frame() == &CellContentFrame::Exact),
        }
        .ok_or(L::error(ValidationError::InvalidCellFraming))?;
        insert_node::<L>(nodes, clause.origin().key())?;
        validate_term::<L>(
            clause.before(),
            scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        )?;
        if clause.before().sort() != sort {
            return Err(L::error(ValidationError::CellFrameSortMismatch));
        }
        if let CellPost::Replace { term } = clause.after() {
            validate_term::<L>(
                term,
                scope,
                declarations,
                signatures,
                sort_parents,
                cell_ids,
                nodes,
            )?;
            if term.sort() != sort {
                return Err(L::error(ValidationError::CellFrameSortMismatch));
            }
        }
        validate_cell_frame::<L>(clause, sort, scope, nodes)?;
    }
    Ok(())
}

/// Both levels must validate alias names, scopes, cell references, terms, and provenance with the same contracts.
pub(crate) fn validate_context_alias<L: Validation>(
    alias: &crate::IrContextAlias<L>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    cell_ids: &BTreeSet<L::Cell>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    if alias.name().trim().is_empty()
        || !alias
            .variables()
            .iter()
            .any(|variable| variable.id() == alias.here())
    {
        return Err(L::error(ValidationError::EmptyText(
            krs_ir::IrField::ContextAliasNameHere,
        )));
    }
    let scope = variable_scope::<L>(alias.variables(), declarations)?;
    for cell in alias.body().cells() {
        L::require_cell(declarations, cell_ids, cell.cell())?;
        insert_node::<L>(nodes, cell.origin().key())?;
        validate_term::<L>(
            cell.pattern(),
            &scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        )?;
        if let CellContentFrame::KSequenceTail { origin, .. }
        | CellContentFrame::MapRemainder { origin, .. }
        | CellContentFrame::ListRemainder { origin } = cell.frame()
        {
            insert_node::<L>(nodes, origin.key())?;
        }
    }
    Ok(())
}

/// Frame and closure checks must run after existing theory checks so existing errors retain precedence.
/// HERE must retain its authored term sort; named K/Map frame bindings must count as uses.
/// Lowering erases configuration-remainder bindings from the alias scope.
pub(crate) fn validate_context_alias_frames<L: Validation>(
    alias: &crate::IrContextAlias<L>,
    configuration: Option<&Configuration<L>>,
    declarations: &Declarations<L>,
) -> Result<(), L::Error> {
    let scope = variable_scope::<L>(alias.variables(), declarations)?;
    let leaf_sorts = configuration
        .map(configuration_leaf_sorts::<L>)
        .transpose()?
        .unwrap_or_default();
    let mut used = BTreeSet::new();
    for cell in alias.body().cells() {
        collect_term_variables::<L>(cell.pattern(), &mut used);
        let (binding, required_sort) = match cell.frame() {
            CellContentFrame::Exact => continue,
            CellContentFrame::KSequenceTail { binding, .. } => {
                (binding.as_ref(), L::builtin_sort(BuiltinSort::KSequence))
            }
            CellContentFrame::MapRemainder { binding, .. } => {
                (binding.as_ref(), L::builtin_sort(BuiltinSort::Map))
            }
            CellContentFrame::ListRemainder { .. } => (None, L::builtin_sort(BuiltinSort::List)),
        };
        if leaf_sorts.get(cell.cell()) != Some(&required_sort) {
            return Err(L::error(ValidationError::ContextAliasFrameSortMismatch));
        }
        if let Some(binding) = binding {
            if scope.get(binding) != Some(&required_sort) {
                return Err(L::error(ValidationError::ContextAliasFrameBindingMismatch(
                    binding.clone(),
                )));
            }
            used.insert(binding.clone());
        }
    }
    if used != scope.keys().cloned().collect() {
        return Err(L::error(ValidationError::ContextAliasVariableClosure));
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
        CellContentFrame::KSequenceTail { origin, binding } => (
            origin,
            binding.as_ref(),
            L::builtin_sort(BuiltinSort::KSequence),
        ),
        CellContentFrame::MapRemainder { origin, binding } => {
            (origin, binding.as_ref(), L::builtin_sort(BuiltinSort::Map))
        }
        CellContentFrame::ListRemainder { origin } => {
            (origin, None, L::builtin_sort(BuiltinSort::List))
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
    desugar_productions: &BTreeSet<L::Declaration>,
    sort_parents: &SortParents<L>,
    cell_ids: &BTreeSet<L::Cell>,
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
                cell_ids,
                nodes,
            )?;
            validate_term::<L>(
                body.to(),
                &scope,
                declarations,
                signatures,
                sort_parents,
                cell_ids,
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
            if matches!(rule.kind, SentenceKind::Alias | SentenceKind::Desugar) {
                let IrTermKind::Application {
                    application: ApplicationRef::Declared(production),
                    ..
                } = from.kind()
                else {
                    return Err(L::error(ValidationError::InvalidAliasRoot(rule.id.clone())));
                };
                let heads = if rule.kind == SentenceKind::Alias {
                    alias_productions
                } else {
                    desugar_productions
                };
                if !heads.contains(production) {
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
                cell_ids,
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
    if let Some(restriction) = rule.restriction {
        validate_restriction::<L>(&rule, restriction, nodes)?;
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
        if matches!(rule.kind, SentenceKind::Alias | SentenceKind::Desugar) {
            return Err(L::error(ValidationError::AliasCondition));
        }
        insert_node::<L>(nodes, condition.origin().key())?;
        validate_term::<L>(
            condition.term(),
            &scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        )?;
        if condition.term().sort() != &L::builtin_sort(BuiltinSort::Bool) {
            return Err(L::error(ValidationError::RuleConditionSortMismatch));
        }
    }
    if let Some(claim) = claim {
        validate_claim::<L>(sentence, claim, &scope, declarations, nodes)?;
    }
    validate_existentials::<L>(
        sentence,
        &scope,
        declarations,
        signatures,
        sort_parents,
        cell_ids,
        nodes,
    )?;
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
                    CellContentFrame::Exact | CellContentFrame::ListRemainder { .. } => {}
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
    if let Some(ensures) = rule.ensures {
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
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    let rule = L::rule_view(sentence);
    insert_node::<L>(nodes, claim.modality_origin().key())?;
    if let Some(origin) = claim.circularity_origin() {
        insert_node::<L>(nodes, origin.key())?;
    }
    if let Some(origin) = claim.trusted_origin() {
        insert_node::<L>(nodes, origin.key())?;
    }
    if !matches!(rule.body, RuleBodyRef::Configuration { .. }) {
        return Err(L::error(ValidationError::ClaimBodyNotConfiguration(
            rule.id.clone(),
        )));
    }
    let mut binder_ids = BTreeSet::new();
    for binder in claim.universals().iter().chain(rule.existentials) {
        if !binder_ids.insert(binder.id().clone()) || scope.get(binder.id()) != Some(binder.sort())
        {
            return Err(L::error(ValidationError::InvalidClaimBinder(
                binder.id().clone(),
            )));
        }
    }
    for binder in claim.universals() {
        require_sort::<L>(declarations, binder.sort())?;
        insert_node::<L>(nodes, binder.origin().key())?;
        insert_node::<L>(nodes, binder.name_origin().key())?;
        insert_node::<L>(nodes, binder.sort_origin().key())?;
    }
    Ok(())
}

/// Checks the `concrete`, `symbolic`, and `smt_lemma` keys (KF-043): only on a
/// term-shaped equation or simplification, with at least one key, each listed
/// binder a variable of the left-hand side, listed once per key.
fn validate_restriction<L: Validation>(
    rule: &RuleView<'_, L>,
    restriction: &crate::IrMatchRestriction,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    let invalid = || L::error(ValidationError::InvalidMatchRestriction(rule.id.clone()));
    let RuleBodyRef::Term(body) = rule.body else {
        return Err(invalid());
    };
    if !matches!(
        rule.kind,
        SentenceKind::Equation | SentenceKind::Simplification
    ) || restriction.is_empty()
    {
        return Err(invalid());
    }
    let mut left = BTreeSet::new();
    collect_term_variables::<L>(body.from(), &mut left);
    for key in restriction
        .concrete()
        .into_iter()
        .chain(restriction.symbolic())
    {
        let mut listed = BTreeSet::new();
        for variable in key.variables() {
            if !left.contains(variable.id()) || !listed.insert(variable.id()) {
                return Err(invalid());
            }
        }
    }
    for origin in restriction.origins() {
        insert_node::<L>(nodes, origin.key())?;
    }
    Ok(())
}

/// Checks the result-scoped existential and fresh binders and the `ensures`
/// condition of a transition or claim (fresh binders: transitions only): each binder is declared once with its scope sort, never
/// occurs in the left-hand side or `requires`, and occurs in the right-hand side
/// or `ensures`.
pub(crate) fn validate_existentials<L: Validation>(
    sentence: &L::Rule,
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    cell_ids: &BTreeSet<L::Cell>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    let rule = L::rule_view(sentence);
    if rule.existentials.is_empty() && rule.ensures.is_none() && rule.fresh.is_empty() {
        return Ok(());
    }
    if (!rule.existentials.is_empty() || rule.ensures.is_some())
        && !matches!(rule.kind, SentenceKind::Transition | SentenceKind::Claim)
    {
        return Err(L::error(ValidationError::InvalidRuleExistentials(
            rule.id.clone(),
        )));
    }
    if !rule.fresh.is_empty() && (rule.kind != SentenceKind::Transition || rule.anywhere) {
        return Err(L::error(ValidationError::InvalidRuleFresh(rule.id.clone())));
    }
    let mut binder_ids = BTreeSet::new();
    for binder in rule.existentials.iter().chain(rule.fresh) {
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
    match rule.body {
        RuleBodyRef::Term(body) => {
            collect_term_variables::<L>(body.from(), &mut left_uses);
            collect_term_variables::<L>(body.to(), &mut right_uses);
        }
        RuleBodyRef::Configuration { body, .. } => {
            for clause in body.clauses() {
                collect_term_variables::<L>(clause.before(), &mut left_uses);
                if let CellPost::Replace { term } = clause.after() {
                    collect_term_variables::<L>(term, &mut right_uses);
                }
                match clause.frame() {
                    CellContentFrame::Exact | CellContentFrame::ListRemainder { .. } => {}
                    CellContentFrame::KSequenceTail { binding, .. }
                    | CellContentFrame::MapRemainder { binding, .. } => {
                        if let Some(binding) = binding {
                            left_uses.insert(binding.clone());
                        }
                    }
                }
            }
        }
    }
    if let Some(requires) = rule.requires {
        collect_term_variables::<L>(requires.term(), &mut left_uses);
    }
    if let Some(ensures) = rule.ensures {
        insert_node::<L>(nodes, ensures.origin().key())?;
        validate_term::<L>(
            ensures.term(),
            scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        )?;
        if ensures.term().sort() != &L::builtin_sort(BuiltinSort::Bool) {
            return Err(L::error(ValidationError::RuleConditionSortMismatch));
        }
        collect_term_variables::<L>(ensures.term(), &mut right_uses);
    }
    for binder in rule.existentials {
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
    for binder in rule.fresh {
        if left_uses.contains(binder.id()) || !right_uses.contains(binder.id()) {
            return Err(L::error(ValidationError::FreshScopeViolation(
                binder.id().clone(),
            )));
        }
    }
    Ok(())
}

/// Semantic cell membership must be checked after existing term and sentence checks succeed.
pub(crate) fn validate_term_cell_references<L: Validation>(
    term: &IrTerm<L>,
    declarations: &Declarations<L>,
    cell_ids: &BTreeSet<L::Cell>,
) -> Result<(), L::Error> {
    let children = match term.kind() {
        IrTermKind::Cell { cell, children } => {
            L::require_cell(declarations, cell_ids, cell)?;
            children
        }
        IrTermKind::Application { arguments, .. } => arguments,
        IrTermKind::KSequence { items, .. } => items,
        IrTermKind::Map(operands) => {
            for operand in operands.operands() {
                validate_term_cell_references::<L>(operand, declarations, cell_ids)?;
            }
            return Ok(());
        }
        IrTermKind::List(operands) => {
            for operand in operands.operands() {
                validate_term_cell_references::<L>(operand, declarations, cell_ids)?;
            }
            return Ok(());
        }
        IrTermKind::Set(operands) => {
            for operand in operands.operands() {
                validate_term_cell_references::<L>(operand, declarations, cell_ids)?;
            }
            return Ok(());
        }
        IrTermKind::Rewrite { from, to } => {
            validate_term_cell_references::<L>(from, declarations, cell_ids)?;
            return validate_term_cell_references::<L>(to, declarations, cell_ids);
        }
        IrTermKind::Variable { .. } | IrTermKind::Token { .. } => return Ok(()),
    };
    for child in children {
        validate_term_cell_references::<L>(child, declarations, cell_ids)?;
    }
    Ok(())
}

pub(crate) fn validate_initializer_cell_references<L: Validation>(
    initializer: &[FixedInitializerCell<L::Cell, IrTerm<L>>],
    declarations: &Declarations<L>,
    cell_ids: &BTreeSet<L::Cell>,
) -> Result<(), L::Error> {
    for cell in initializer {
        match cell.content() {
            FixedInitializerContent::Term { term } => {
                validate_term_cell_references::<L>(term, declarations, cell_ids)?;
            }
            FixedInitializerContent::Children { children } => {
                validate_initializer_cell_references::<L>(children, declarations, cell_ids)?;
            }
        }
    }
    Ok(())
}

pub(crate) fn validate_rule_cell_references<L: Validation>(
    sentence: &L::Rule,
    declarations: &Declarations<L>,
    cell_ids: &BTreeSet<L::Cell>,
) -> Result<(), L::Error> {
    let rule = L::rule_view(sentence);
    match rule.body {
        RuleBodyRef::Term(body) => {
            validate_term_cell_references::<L>(body.from(), declarations, cell_ids)?;
            validate_term_cell_references::<L>(body.to(), declarations, cell_ids)?;
        }
        RuleBodyRef::Configuration { body, .. } => {
            for clause in body.clauses() {
                validate_term_cell_references::<L>(clause.before(), declarations, cell_ids)?;
                if let CellPost::Replace { term } = clause.after() {
                    validate_term_cell_references::<L>(term, declarations, cell_ids)?;
                }
            }
        }
    }
    if let Some(condition) = rule.requires {
        validate_term_cell_references::<L>(condition.term(), declarations, cell_ids)?;
    }
    if let Some(ensures) = rule.ensures {
        validate_term_cell_references::<L>(ensures.term(), declarations, cell_ids)?;
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
        IrTermKind::Application { arguments, .. } => {
            for argument in arguments {
                collect_term_variables::<L>(argument, used);
            }
        }
        IrTermKind::Map(operands) => {
            for operand in operands.operands() {
                collect_term_variables::<L>(operand, used);
            }
        }
        IrTermKind::List(operands) => {
            for operand in operands.operands() {
                collect_term_variables::<L>(operand, used);
            }
        }
        IrTermKind::Set(operands) => {
            for operand in operands.operands() {
                collect_term_variables::<L>(operand, used);
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

/// Whether a collection term's result and operand sorts satisfy its catalog row.
/// Operand sorts repeat per entry, which only `MapOperation::Item` has more than one of.
fn collection_signature_holds<'a, L: Validation + 'a>(
    result: &L::Sort,
    spec: &CollectionOperationSpec,
    operands: impl Iterator<Item = &'a IrTerm<L>>,
) -> bool {
    let result_holds = match spec.result_sort {
        CollectionResultSort::Builtin(sort) => *result == L::builtin_sort(sort),
        CollectionResultSort::Projected => true,
    };
    result_holds
        && operands
            .zip(spec.operand_sorts.iter().cycle())
            .all(|(operand, sort)| match sort {
                CollectionOperandSort::Builtin(sort) => *operand.sort() == L::builtin_sort(*sort),
                CollectionOperandSort::Element => true,
            })
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
    cell_ids: &BTreeSet<L::Cell>,
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
            let holds = match application {
                ApplicationRef::Declared(production) => {
                    let (result_sort, argument_sorts) =
                        L::application_signature(declarations, signatures, production)?;
                    *term.sort() == result_sort
                        && arguments.len() == argument_sorts.len()
                        && arguments
                            .iter()
                            .zip(&argument_sorts)
                            .all(|(argument, sort)| {
                                is_subsort::<L>(argument.sort(), sort, sort_parents)
                            })
                }
                ApplicationRef::Builtin(operation) => {
                    builtin_application_holds::<L>(*operation, term.sort(), arguments, sort_parents)
                }
                ApplicationRef::Generated(operation) => {
                    require_sort::<L>(declarations, operation.sort())?;
                    arguments.len() == 1
                        && match operation {
                            GeneratedOperation::SortPredicate(_) => {
                                *term.sort() == L::builtin_sort(BuiltinSort::Bool)
                            }
                            GeneratedOperation::SortProjection(sort) => term.sort() == sort,
                        }
                }
            };
            if !holds {
                return match application {
                    ApplicationRef::Declared(production) => Err(L::error(
                        ValidationError::ApplicationSignature(production.clone()),
                    )),
                    ApplicationRef::Builtin(operation) => Err(L::error(
                        ValidationError::BuiltinApplicationSignature(*operation),
                    )),
                    ApplicationRef::Generated(_) => {
                        Err(L::error(ValidationError::GeneratedApplicationSignature))
                    }
                };
            }
            for argument in arguments {
                validate_term::<L>(
                    argument,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
            }
        }
        IrTermKind::Token { value } => {
            if value.is_empty() {
                return Err(L::error(ValidationError::EmptyText(
                    krs_ir::IrField::TokenValue,
                )));
            }
        }
        IrTermKind::KSequence { item_sort, items } => {
            require_sort::<L>(declarations, item_sort)?;
            if *term.sort() != L::builtin_sort(BuiltinSort::KSequence) {
                return Err(L::error(ValidationError::SequenceSortMismatch));
            }
            for item in items {
                validate_term::<L>(
                    item,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
                if !is_subsort::<L>(item.sort(), item_sort, sort_parents) {
                    return Err(L::error(ValidationError::SequenceItemSortMismatch));
                }
            }
        }
        IrTermKind::Map(operands) => {
            if !collection_signature_holds::<L>(
                term.sort(),
                operands.operation().spec(),
                operands.operands(),
            ) {
                return Err(L::error(ValidationError::MapOperationSignature(
                    operands.operation(),
                )));
            }
            for operand in operands.operands() {
                validate_term::<L>(
                    operand,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
            }
        }
        IrTermKind::List(operands) => {
            if !collection_signature_holds::<L>(
                term.sort(),
                operands.operation().spec(),
                operands.operands(),
            ) {
                return Err(L::error(ValidationError::ListOperationSignature(
                    operands.operation(),
                )));
            }
            for operand in operands.operands() {
                validate_term::<L>(
                    operand,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
            }
        }
        IrTermKind::Set(operands) => {
            if !collection_signature_holds::<L>(
                term.sort(),
                operands.operation().spec(),
                operands.operands(),
            ) {
                return Err(L::error(ValidationError::SetOperationSignature(
                    operands.operation(),
                )));
            }
            for operand in operands.operands() {
                validate_term::<L>(
                    operand,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
            }
        }
        IrTermKind::Cell { cell, children } => {
            if L::CHECK_CELL_REFERENCES_DURING_TERM_VALIDATION {
                L::require_cell(declarations, cell_ids, cell)?;
            }
            if children.is_empty() {
                return Err(L::error(ValidationError::InvalidCellFraming));
            }
            for child in children {
                validate_term::<L>(
                    child,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
            }
        }
        IrTermKind::Rewrite { from, to } => {
            validate_term::<L>(
                from,
                scope,
                declarations,
                signatures,
                sort_parents,
                cell_ids,
                nodes,
            )?;
            validate_term::<L>(
                to,
                scope,
                declarations,
                signatures,
                sort_parents,
                cell_ids,
                nodes,
            )?;
            if !is_subsort::<L>(from.sort(), term.sort(), sort_parents)
                || !is_subsort::<L>(to.sort(), term.sort(), sort_parents)
            {
                return Err(L::error(ValidationError::RewriteSortMismatch));
            }
        }
    }
    Ok(())
}

/// Checks a syntactic-list cons production: `[head, separator, tail]` with
/// the separator item present exactly when the separator is nonempty, and
/// the tail of the list's own sort (KF-020).
fn valid_list_cons<L: Validation>(
    result_sort: &L::Sort,
    items: &[GrammarProductionItem<L::Sort>],
    separator: &str,
) -> bool {
    let tail_is_list = |item: &GrammarProductionItem<L::Sort>| matches!(item.kind(), GrammarProductionItemKind::NonTerminal { sort, .. } if sort == result_sort);
    let is_head = |item: &GrammarProductionItem<L::Sort>| {
        matches!(item.kind(), GrammarProductionItemKind::NonTerminal { .. })
    };
    match items {
        [head, tail] => separator.is_empty() && is_head(head) && tail_is_list(tail),
        [head, terminal, tail] => {
            !separator.is_empty()
                && is_head(head)
                && matches!(terminal.kind(), GrammarProductionItemKind::Terminal { text } if text == separator)
                && tail_is_list(tail)
        }
        _ => false,
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "The closed shape checks must preserve the first reported failure."
)]
pub(crate) fn validate_production_shape<L: Validation>(
    id: &L::Declaration,
    result_sort: &L::Sort,
    items: &[GrammarProductionItem<L::Sort>],
    attributes: &[ProductionAttribute<L::Sort, L::Declaration>],
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
    let mut desugar = false;
    let mut group = false;
    let mut bracket = false;
    let mut avoid = false;
    let mut format = false;
    let mut strictness = false;
    let mut internal = false;
    let mut program = false;
    let mut colors = None;
    let mut prefer = false;
    let mut overload = false;
    let mut private = false;
    let mut memo = false;
    let mut fresh_generator = false;
    let mut smt = false;
    let mut list = false;
    let mut raw_hook = false;
    for attribute in attributes {
        let already = match attribute {
            ProductionAttribute::Documentation { .. } => continue,
            ProductionAttribute::Function { .. } => std::mem::replace(&mut function, true),
            ProductionAttribute::Total { .. } => std::mem::replace(&mut total, true),
            ProductionAttribute::Hook { operation, .. } => {
                hook.replace(*operation).is_some() || raw_hook
            }
            ProductionAttribute::RawHook { .. } => {
                std::mem::replace(&mut raw_hook, true) || hook.is_some()
            }
            ProductionAttribute::Alias { .. } => std::mem::replace(&mut alias, true),
            ProductionAttribute::Desugar { .. } => std::mem::replace(&mut desugar, true),
            ProductionAttribute::Token { .. } => std::mem::replace(&mut token, true),
            ProductionAttribute::Group { .. } => std::mem::replace(&mut group, true),
            ProductionAttribute::Bracket { .. } => std::mem::replace(&mut bracket, true),
            ProductionAttribute::Avoid { .. } => std::mem::replace(&mut avoid, true),
            ProductionAttribute::Format { .. } => std::mem::replace(&mut format, true),
            ProductionAttribute::Strictness { .. } => std::mem::replace(&mut strictness, true),
            ProductionAttribute::Internal { .. } => std::mem::replace(&mut internal, true),
            ProductionAttribute::Program { .. } => std::mem::replace(&mut program, true),
            ProductionAttribute::Color { value, .. } => {
                colors.replace(vec![value.as_str()]).is_some()
            }
            ProductionAttribute::Colors { values, .. } => colors
                .replace(values.iter().map(String::as_str).collect())
                .is_some(),
            ProductionAttribute::Prefer { .. } => std::mem::replace(&mut prefer, true),
            ProductionAttribute::Overload { .. } => std::mem::replace(&mut overload, true),
            ProductionAttribute::Private { .. } => std::mem::replace(&mut private, true),
            ProductionAttribute::Memo { .. } => std::mem::replace(&mut memo, true),
            ProductionAttribute::FreshGenerator { .. } => {
                std::mem::replace(&mut fresh_generator, true)
            }
            ProductionAttribute::Smtlib { .. } | ProductionAttribute::SmtHook { .. } => {
                std::mem::replace(&mut smt, true)
            }
            ProductionAttribute::ListCons { .. } | ProductionAttribute::ListTerminator { .. } => {
                std::mem::replace(&mut list, true)
            }
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
            | ProductionAttribute::Avoid { .. }
            | ProductionAttribute::Internal { .. }
            | ProductionAttribute::Program { .. }
            | ProductionAttribute::Color { .. }
            | ProductionAttribute::Colors { .. }
            | ProductionAttribute::Prefer { .. }
            | ProductionAttribute::Overload { .. }
            | ProductionAttribute::Private { .. }
            | ProductionAttribute::Memo { .. }
            | ProductionAttribute::FreshGenerator { .. }
            | ProductionAttribute::RawHook { .. }
            | ProductionAttribute::Desugar { .. } => {}
            ProductionAttribute::Smtlib { symbol, .. } => {
                if !krs_ir::is_smtlib_simple_symbol(symbol) {
                    return Err(L::error(ValidationError::InvalidSmtMetadata));
                }
            }
            ProductionAttribute::SmtHook { template, .. } => {
                let valid = !template.is_empty()
                    && template.iter().all(|fragment| match fragment {
                        krs_ir::SmtFragment::Text(text) => !text.is_empty(),
                        krs_ir::SmtFragment::Field(field) => fields.contains(field),
                    });
                if !valid {
                    return Err(L::error(ValidationError::InvalidSmtMetadata));
                }
            }
            ProductionAttribute::ListCons { separator, .. } => {
                if !valid_list_cons::<L>(result_sort, items, separator) {
                    return Err(L::error(ValidationError::InvalidListProduction));
                }
            }
            ProductionAttribute::ListTerminator { .. } => {
                let valid = matches!(
                    items,
                    [item] if matches!(
                        item.kind(),
                        GrammarProductionItemKind::Terminal { text } if text.starts_with('.') && text.len() > 1
                    )
                );
                if !valid {
                    return Err(L::error(ValidationError::InvalidListProduction));
                }
            }
        }
    }
    // A syntactic list is K constructor syntax: its two productions carry
    // no function, token, bracket, alias, or desugar metadata.
    if list && (function || token || bracket || alias || desugar || hook.is_some()) {
        return Err(L::error(ValidationError::InvalidListProduction));
    }
    if alias && desugar {
        return Err(L::error(ValidationError::AliasWithDesugar));
    }
    // A static rewrite expands a constructor before anything runs; a
    // function is evaluated by rules.
    if (alias || desugar) && function {
        return Err(L::error(ValidationError::InvalidFunctionProduction));
    }
    if internal && program {
        return Err(L::error(ValidationError::InternalWithProgram));
    }
    // K lets `prefer` win silently over `avoid`; a production takes one.
    if prefer && avoid {
        return Err(L::error(ValidationError::PreferAndAvoid));
    }
    // Token and bracket productions never compete in a parse forest as
    // constructors, so a preference on them has no meaning.
    if prefer && (token || bracket) {
        return Err(L::error(ValidationError::PreferOnParseOnlyProduction));
    }
    // An overload family relates constructors; functions, tokens, and
    // brackets are not members.
    if overload && (function || token || bracket) {
        return Err(L::error(ValidationError::InvalidOverloadProduction));
    }
    validate_production_colors::<L>(items, attributes, colors.as_deref())?;
    // K's freshGenerator is a function; analysis requires it to be total (KF-022).
    // K's smtlib and smt-hook give a function's SMT translation (KF-044).
    if (total || memo || fresh_generator || smt) && !function {
        return Err(L::error(ValidationError::InvalidFunctionProduction));
    }
    if (hook.is_some() || raw_hook) && !(function && total) {
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
    // A token production is one regex or one terminal (`syntax S ::= "main"
    // [token]`); `prec` orders regexes only, as a terminal already outranks
    // every regex.
    if token
        && !matches!(
            items,
            [item] if matches!(item.kind(), GrammarProductionItemKind::RegexTerminal { .. })
                || (matches!(item.kind(), GrammarProductionItemKind::Terminal { .. })
                    && !attributes.iter().any(|attribute| matches!(
                        attribute,
                        ProductionAttribute::Token { lexical_precedence: Some(_), .. }
                    )))
        )
    {
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

/// Checks K's colour metadata (`color`, `colors`, `%c`, `%r`).
///
/// A colour must be nonempty and must not contain `,` or `)`, which would end
/// the K attribute value. A `colors` list has one entry per printed terminal
/// plus one per `%c` (K's `CheckAtt` rule). `%c` and `%r` require a colour,
/// which is stricter than K: without one they have no effect.
fn validate_production_colors<L: Validation>(
    items: &[GrammarProductionItem<L::Sort>],
    attributes: &[ProductionAttribute<L::Sort, L::Declaration>],
    colors: Option<&[&str]>,
) -> Result<(), L::Error> {
    let color_controls = attributes
        .iter()
        .filter_map(|attribute| match attribute {
            ProductionAttribute::Format { fragments, .. } => Some(fragments),
            _ => None,
        })
        .flatten()
        .filter(|fragment| {
            matches!(
                fragment,
                FormatFragment::ColorNext | FormatFragment::ColorReset
            )
        })
        .collect::<Vec<_>>();
    let Some(colors) = colors else {
        return if color_controls.is_empty() {
            Ok(())
        } else {
            Err(L::error(ValidationError::InvalidColors))
        };
    };
    if colors
        .iter()
        .any(|color| color.is_empty() || color.contains([',', ')']))
    {
        return Err(L::error(ValidationError::InvalidColors));
    }
    let is_list = attributes
        .iter()
        .any(|attribute| matches!(attribute, ProductionAttribute::Colors { .. }));
    if is_list {
        let terminals = items
            .iter()
            .filter(|item| !matches!(item.kind(), GrammarProductionItemKind::NonTerminal { .. }))
            .count();
        let color_next = color_controls
            .iter()
            .filter(|fragment| matches!(fragment, FormatFragment::ColorNext))
            .count();
        if colors.len() != terminals + color_next {
            return Err(L::error(ValidationError::InvalidColors));
        }
    }
    Ok(())
}

fn has_duplicate_fields(fields: &[ProductionFieldId]) -> bool {
    let mut unique = BTreeSet::new();
    fields.iter().any(|field| !unique.insert(field))
}

/// Whether a builtin application's sorts fit its catalog signature.
///
/// A `K` argument admits any sort. Every `Parameter` position shares one
/// instance: the application's sort when the result is `Parameter`, so each
/// `Parameter` argument must be a subsort of it.
pub(crate) fn builtin_application_holds<L: Validation>(
    operation: BuiltinOperation,
    sort: &L::Sort,
    arguments: &[IrTerm<L>],
    sort_parents: &SortParents<L>,
) -> bool {
    let instance = match operation.result_sort() {
        OperationSort::Builtin(result) => {
            if *sort != L::builtin_sort(result) {
                return false;
            }
            None
        }
        OperationSort::Parameter => Some(sort),
        OperationSort::K => None,
    };
    arguments.len() == operation.argument_sorts().len()
        && arguments
            .iter()
            .zip(operation.argument_sorts())
            .all(|(argument, expected)| match expected {
                OperationSort::Builtin(expected) => {
                    is_subsort::<L>(argument.sort(), &L::builtin_sort(*expected), sort_parents)
                }
                OperationSort::K => true,
                OperationSort::Parameter => instance.is_none_or(|instance| {
                    is_subsort::<L>(argument.sort(), instance, sort_parents)
                }),
            })
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

pub(crate) struct ProductionView<'a, L: Validation> {
    pub result_sort: &'a L::Sort,
    pub items: &'a [GrammarProductionItem<L::Sort>],
    pub attributes: &'a [ProductionAttribute<L::Sort, L::Declaration>],
}

/// BN128 hooks must use the backend's named point sorts and unique integer-field constructors.
/// Semantic sort names must use the explicit symbol's final component, or the authored item name, as in Definition lowering.
pub(crate) fn validate_hook_point_constructors<'a, L: Validation>(
    sorts: &BTreeMap<&'a L::Declaration, &'a str>,
    productions: impl Iterator<Item = ProductionView<'a, L>>,
) -> Result<(), L::Error>
where
    L::Sort: 'a,
    L::Declaration: 'a,
{
    let productions = productions.collect::<Vec<_>>();
    let check =
        |hook, expected_signature: krs_ir::Bn128PointSignature, used_sort: Option<&L::Sort>| {
            let expected_sort = expected_signature.sort_name();
            let arity = expected_signature.arity();
            let sort = if let Some(used_sort) = used_sort {
                L::declared_sort(used_sort)
            } else {
                sorts
                    .iter()
                    .find(|(_, name)| **name == expected_sort)
                    .map(|(id, _)| *id)
            };
            let sort_name = sort
                .and_then(|id| sorts.get(id).copied())
                .unwrap_or(expected_sort);
            let matching_constructors = productions
                .iter()
                .filter(|production| {
                    L::declared_sort(production.result_sort).is_some_and(|id| Some(id) == sort)
                        && !production.attributes.iter().any(|attribute| {
                            matches!(
                                attribute,
                                ProductionAttribute::Function { .. }
                                    | ProductionAttribute::Alias { .. }
                                    | ProductionAttribute::Token { .. }
                                    | ProductionAttribute::Bracket { .. }
                            )
                        })
                        && production
                            .items
                            .iter()
                            .filter_map(|item| match item.kind() {
                                GrammarProductionItemKind::NonTerminal { sort, .. } => Some(sort),
                                _ => None,
                            })
                            .collect::<Vec<_>>()
                            == vec![&L::builtin_sort(BuiltinSort::Int); arity]
                })
                .count();
            if sort_name == expected_sort && matching_constructors == 1 {
                Ok(())
            } else {
                Err(L::error(ValidationError::InvalidBn128PointConstructor {
                    hook,
                    sort: sort_name.to_owned(),
                    expected_signature,
                    matching_constructors,
                }))
            }
        };
    for production in &productions {
        let Some(hook) = production
            .attributes
            .iter()
            .find_map(|attribute| match attribute {
                ProductionAttribute::Hook { operation, .. } => Some(*operation),
                _ => None,
            })
        else {
            continue;
        };
        let first_argument = production.items.iter().find_map(|item| match item.kind() {
            GrammarProductionItemKind::NonTerminal { sort, .. } => Some(sort),
            _ => None,
        });
        for constraint in hook.spec().signature.point_constructors() {
            let used_sort = match constraint.source {
                HookPointSortSource::FirstArgument => first_argument,
                HookPointSortSource::Result => Some(production.result_sort),
                HookPointSortSource::Named => None,
            };
            check(hook, constraint.signature, used_sort)?;
        }
    }
    Ok(())
}
