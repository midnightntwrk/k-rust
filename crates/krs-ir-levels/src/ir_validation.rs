//! Shared shape validation with level-specific identity and context checks.

use crate::ir_level::{
    IrClaim, IrCondition, IrLevel, IrMlKind, IrMlPredicate, IrPredicateRewrite, IrRulePriority,
    IrSimplification, IrTerm, IrTermKind, IrVariable, RuleBodyRef,
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
/// A production's result sort, sort parameters (KF-027), and argument sorts.
pub(crate) type Signature<L> = (
    <L as IrLevel>::Sort,
    Vec<crate::SortParameterId>,
    Vec<<L as IrLevel>::Sort>,
);
pub(crate) type Signatures<L> = BTreeMap<<L as IrLevel>::Declaration, Signature<L>>;
pub(crate) type SortParents<L> = BTreeMap<<L as IrLevel>::Sort, Vec<<L as IrLevel>::Sort>>;
pub(crate) type Configuration<L> =
    FixedConfiguration<<L as IrLevel>::Sort, <L as IrLevel>::Cell, IrTerm<L>>;

pub(crate) struct RuleView<'a, L: Validation> {
    pub kind: SentenceKind,
    pub id: L::RuleId,
    pub variables: &'a [IrVariable<L>],
    pub body: RuleBodyRef<'a, L>,
    pub requires: Option<&'a IrCondition<L>>,
    pub priority: Option<&'a IrRulePriority>,
    pub simplification: Option<&'a IrSimplification>,
    pub claim: Option<&'a IrClaim<L>>,
    pub existentials: &'a [crate::IrScopedBinder<L>],
    pub ensures: Option<&'a IrCondition<L>>,
    pub fresh: &'a [crate::IrScopedBinder<L>],
    pub restriction: Option<&'a crate::IrMatchRestriction>,
    pub unbound_variables: Option<&'a crate::IrUnboundVariables>,
    pub function_context: Option<&'a crate::IrFunctionContext<L>>,
    pub anywhere: bool,
    pub evaluation: Option<&'a crate::IrEvaluationStep<L>>,
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

    /// The parameter name of a sort-parameter reference, which may occur only
    /// in a parametric production's signature (KF-027).
    fn parameter_name(sort: &Self::Sort) -> Option<&crate::SortParameterId>;
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
    ParameterSortInTerm,
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
    /// `alias @ pattern` outside a pre-pattern, or at a sort its alias or
    /// pattern does not have.
    InvalidPatternAs,
    /// `A | B` outside a pre-pattern, at a sort an alternative does not
    /// inject into, or with alternatives binding different variables.
    InvalidPatternOr,
    /// `k::matches!` outside a post-term or condition, at a sort other than
    /// Bool, or with local binders that are not exactly its pattern's named
    /// variables or that occur outside it.
    InvalidMatches,
    /// `let` (#let) outside a post-term or condition, at a sort other than
    /// its body's, or with local binders that are not exactly its pattern's
    /// named variables or that occur outside its pattern and body.
    InvalidLet,
    /// A misplaced or malformed matching-logic predicate (KF-039).
    InvalidMlPredicate,
    /// A local rewrite (KF-011) outside a single-body clause's subject,
    /// nested in another rewrite, or a single-body clause without one.
    InvalidLocalRewrite,
    RuleConditionSortMismatch,
    SequenceItemSortMismatch,
    SequenceSortMismatch,
    SetOperationSignature(SetOperation),
    SubsortCycle(L::Sort),
    UnusedExistential(SemanticId),
    InvalidRuleExistentials(L::RuleId),
    InvalidRuleFresh(L::RuleId),
    InvalidMatchRestriction(L::RuleId),
    InvalidUnboundVariables(L::RuleId),
    InvalidFunctionContext(L::RuleId),
    InvalidEvaluationStep(L::RuleId),
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
        // A single-body clause (KF-011) rewrites below its root; every other
        // clause states its pre-pattern and post-state without local rewrites.
        let local_rewrites_hold = match clause.after() {
            CellPost::Local => {
                clause.before().contains_rewrite()
                    && !matches!(clause.before().kind(), IrTermKind::Rewrite { .. })
                    && local_rewrites_valid(clause.before(), false)
            }
            CellPost::Preserve => !clause.before().contains_rewrite(),
            CellPost::Replace { term } => {
                !clause.before().contains_rewrite() && !term.contains_rewrite()
            }
        };
        if !local_rewrites_hold {
            return Err(L::error(ValidationError::InvalidLocalRewrite));
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
    if let Some(result) = alias.result() {
        require_sort::<L>(declarations, result.sort())?;
        insert_node::<L>(nodes, result.origin().key())?;
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
    if rule.kind == SentenceKind::Context
        && (rule.evaluation.is_none()
            || matches!(rule.body, RuleBodyRef::Term(body) if body.local_term().is_none()))
    {
        return Err(L::error(ValidationError::InvalidEvaluationStep(
            rule.id.clone(),
        )));
    }
    let scope = variable_scope::<L>(rule.variables, declarations)?;
    match rule.body {
        RuleBodyRef::Term(body) => {
            require_sort::<L>(declarations, body.sort())?;
            if let Some(local) = body.local_term() {
                // A single-body rule (KF-011): one transition whose
                // rewrites sit below the root, validated once as authored.
                // A context (KF-021) is its pattern, with at most one
                // rewrite, of its hole.
                if !matches!(rule.kind, SentenceKind::Transition | SentenceKind::Context)
                    || matches!(local.kind(), IrTermKind::Rewrite { .. })
                    || !local_rewrites_valid(local, false)
                {
                    return Err(L::error(ValidationError::InvalidLocalRewrite));
                }
                validate_term::<L>(
                    local,
                    &scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
            } else {
                insert_node::<L>(nodes, body.origin().key())?;
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
            }
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
        RuleBodyRef::Predicate(body) => {
            validate_predicate_rewrite::<L>(
                &rule,
                body,
                &scope,
                declarations,
                signatures,
                sort_parents,
                cell_ids,
                nodes,
            )?;
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
    if let Some(unbound) = rule.unbound_variables {
        validate_unbound_variables::<L>(&rule, unbound, nodes)?;
    }
    if let Some(step) = rule.evaluation {
        validate_evaluation_step::<L>(&rule, step, &scope, declarations, nodes)?;
    }
    if let Some(context) = rule.function_context {
        validate_function_context::<L>(
            &rule,
            context,
            configuration,
            &scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        )?;
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
        // A predicate condition is a claim's or a simplification's (KF-039).
        if matches!(condition, IrCondition::Predicate(_))
            && !matches!(
                rule.kind,
                SentenceKind::Claim | SentenceKind::Simplification
            )
        {
            return Err(L::error(ValidationError::InvalidMlPredicate));
        }
        validate_condition::<L>(
            condition,
            &scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        )?;
    }
    if let Some(claim) = claim {
        validate_claim::<L>(sentence, claim, &scope, declarations, nodes)?;
    }
    reject_pattern_as_outside_patterns::<L>(&rule)?;
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
        RuleBodyRef::Predicate(body) => {
            collect_predicate_variables::<L>(body.lhs(), &mut used);
            collect_predicate_variables::<L>(body.rhs(), &mut used);
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
        collect_condition_variables::<L>(condition, &mut used);
    }
    if let Some(ensures) = rule.ensures {
        collect_condition_variables::<L>(ensures, &mut used);
    }
    if let Some(context) = rule.function_context {
        for cell in context.cells().cells() {
            collect_term_variables::<L>(cell.pattern(), &mut used);
            if let CellContentFrame::KSequenceTail {
                binding: Some(binding),
                ..
            }
            | CellContentFrame::MapRemainder {
                binding: Some(binding),
                ..
            } = cell.frame()
            {
                used.insert(binding.clone());
            }
        }
    }
    if used != scope.keys().cloned().collect() {
        return Err(L::error(ValidationError::VariableClosure));
    }
    Ok(())
}

/// Checks an equation's function context (KF-025): only on a term-shaped
/// equation, over the fixed configuration, its cells declared, its terms
/// valid pre-patterns, and its frames typed like a context alias's.
#[expect(
    clippy::too_many_arguments,
    reason = "The context is validated against the same tables as the rule body."
)]
fn validate_function_context<L: Validation>(
    rule: &RuleView<'_, L>,
    context: &crate::IrFunctionContext<L>,
    configuration: Option<&FixedConfiguration<L::Sort, L::Cell, IrTerm<L>>>,
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    cell_ids: &BTreeSet<L::Cell>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    let invalid = || L::error(ValidationError::InvalidFunctionContext(rule.id.clone()));
    if rule.kind != SentenceKind::Equation || !matches!(rule.body, RuleBodyRef::Term(_)) {
        return Err(invalid());
    }
    let configuration = configuration.ok_or_else(invalid)?;
    if context.cells().configuration() != configuration.id() {
        return Err(invalid());
    }
    let leaf_sorts = configuration_leaf_sorts::<L>(configuration)?;
    insert_node::<L>(nodes, context.origin().key())?;
    insert_node::<L>(nodes, context.cells().origin().key())?;
    for cell in context.cells().cells() {
        L::require_cell(declarations, cell_ids, cell.cell())?;
        insert_node::<L>(nodes, cell.origin().key())?;
        validate_term::<L>(
            cell.pattern(),
            scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        )?;
        let (origin, binding, required_sort) = match cell.frame() {
            CellContentFrame::Exact => continue,
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
        if leaf_sorts.get(cell.cell()) != Some(&required_sort) {
            return Err(L::error(ValidationError::CellFrameSortMismatch));
        }
        if let Some(binding) = binding
            && scope.get(binding) != Some(&required_sort)
        {
            return Err(L::error(ValidationError::CellFrameBindingMismatch(
                binding.clone(),
            )));
        }
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

/// Checks `unbound_variables` (KF-046): only on a term-shaped desugar clause,
/// with at least one entry, each named entry a distinct variable of the
/// right-hand side that the left-hand side does not bind, and `_` at most once.
fn validate_unbound_variables<L: Validation>(
    rule: &RuleView<'_, L>,
    unbound: &crate::IrUnboundVariables,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    let invalid = || L::error(ValidationError::InvalidUnboundVariables(rule.id.clone()));
    let RuleBodyRef::Term(body) = rule.body else {
        return Err(invalid());
    };
    if rule.kind != SentenceKind::Desugar || unbound.variables().is_empty() {
        return Err(invalid());
    }
    let mut left = BTreeSet::new();
    collect_term_variables::<L>(body.from(), &mut left);
    let mut right = BTreeSet::new();
    collect_term_variables::<L>(body.to(), &mut right);
    let mut listed = BTreeSet::new();
    let mut wildcard = false;
    for variable in unbound.variables() {
        match variable.id() {
            None if !wildcard => wildcard = true,
            Some(id) if !left.contains(id) && right.contains(id) && listed.insert(id) => {}
            _ => return Err(invalid()),
        }
    }
    for origin in unbound.origins() {
        insert_node::<L>(nodes, origin.key())?;
    }
    Ok(())
}

/// Checks the `heat` or `cool` key of a transition (KF-014): the rule has no
/// priority, anywhere marker, or fresh binders, and its hole is a declared
/// variable of the left-hand side.
fn validate_evaluation_step<L: Validation>(
    rule: &RuleView<'_, L>,
    step: &crate::IrEvaluationStep<L>,
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    let invalid = || L::error(ValidationError::InvalidEvaluationStep(rule.id.clone()));
    // A context's step (KF-021) belongs to a context, a heat or cool key to
    // a transition.
    let kind_matches = if step.kind() == krs_ir::EvaluationKind::Context {
        rule.kind == SentenceKind::Context
    } else {
        rule.kind == SentenceKind::Transition
    };
    if !kind_matches
        || rule.priority.is_some()
        || rule.anywhere
        || !rule.fresh.is_empty()
        || !scope.contains_key(step.hole())
    {
        return Err(invalid());
    }
    let mut left = BTreeSet::new();
    match rule.body {
        RuleBodyRef::Term(body) => collect_term_variables::<L>(body.from(), &mut left),
        RuleBodyRef::Configuration { body, .. } => {
            for clause in body.clauses() {
                collect_term_variables::<L>(clause.before(), &mut left);
            }
        }
        // A predicate simplification (KF-039) is never a transition.
        RuleBodyRef::Predicate(_) => return Err(invalid()),
    }
    if !left.contains(step.hole()) {
        return Err(invalid());
    }
    insert_node::<L>(nodes, step.origin().key())?;
    insert_node::<L>(nodes, step.hole_origin().key())?;
    if let Some(result) = step.result() {
        require_sort::<L>(declarations, result.sort())?;
        insert_node::<L>(nodes, result.origin().key())?;
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
        RuleBodyRef::Predicate(body) => {
            collect_predicate_variables::<L>(body.lhs(), &mut left_uses);
            collect_predicate_variables::<L>(body.rhs(), &mut right_uses);
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
        collect_condition_variables::<L>(requires, &mut left_uses);
    }
    if let Some(ensures) = rule.ensures {
        // A predicate postcondition is a claim's (KF-039).
        if matches!(ensures, IrCondition::Predicate(_)) && rule.kind != SentenceKind::Claim {
            return Err(L::error(ValidationError::InvalidMlPredicate));
        }
        validate_condition::<L>(
            ensures,
            scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        )?;
        collect_condition_variables::<L>(ensures, &mut right_uses);
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
        IrTermKind::As { pattern, .. } => {
            return validate_term_cell_references::<L>(pattern, declarations, cell_ids);
        }
        IrTermKind::Or { alternatives } => {
            for alternative in alternatives {
                validate_term_cell_references::<L>(alternative, declarations, cell_ids)?;
            }
            return Ok(());
        }
        IrTermKind::Matches {
            subject, pattern, ..
        } => {
            validate_term_cell_references::<L>(subject, declarations, cell_ids)?;
            return validate_term_cell_references::<L>(pattern, declarations, cell_ids);
        }
        IrTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => {
            validate_term_cell_references::<L>(pattern, declarations, cell_ids)?;
            validate_term_cell_references::<L>(value, declarations, cell_ids)?;
            return validate_term_cell_references::<L>(body, declarations, cell_ids);
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
        RuleBodyRef::Predicate(body) => {
            for term in body.lhs().terms().into_iter().chain(body.rhs().terms()) {
                validate_term_cell_references::<L>(term, declarations, cell_ids)?;
            }
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
    for condition in rule.requires.into_iter().chain(rule.ensures) {
        for term in condition.terms() {
            validate_term_cell_references::<L>(term, declarations, cell_ids)?;
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
        IrTermKind::As { alias, pattern } => {
            used.insert(alias.clone());
            collect_term_variables::<L>(pattern, used);
        }
        IrTermKind::Or { alternatives } => {
            for alternative in alternatives {
                collect_term_variables::<L>(alternative, used);
            }
        }
        IrTermKind::Matches {
            subject, pattern, ..
        } => {
            collect_term_variables::<L>(subject, used);
            collect_term_variables::<L>(pattern, used);
        }
        IrTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => {
            collect_term_variables::<L>(pattern, used);
            collect_term_variables::<L>(value, used);
            collect_term_variables::<L>(body, used);
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
    if L::parameter_name(term.sort()).is_some() {
        return Err(L::error(ValidationError::ParameterSortInTerm));
    }
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
            instance,
            head_instance_fixed,
        } => {
            let holds = match application {
                ApplicationRef::Declared(production) => {
                    let (result_sort, parameters, argument_sorts) =
                        L::application_signature(declarations, signatures, production)?;
                    // A parametric application carries one resolved sort per
                    // parameter, and its signature is read at that instance
                    // (KF-027); no other application has an instance.
                    let instantiate = |sort: &L::Sort| {
                        L::parameter_name(sort)
                            .and_then(|name| parameters.iter().position(|p| p == name))
                            .and_then(|index| instance.get(index))
                            .unwrap_or(sort)
                            .clone()
                    };
                    let result_sort = instantiate(&result_sort);
                    let argument_sorts = argument_sorts.iter().map(instantiate).collect::<Vec<_>>();
                    instance.len() == parameters.len()
                        && (!*head_instance_fixed || !parameters.is_empty())
                        && instance
                            .iter()
                            .all(|sort| L::parameter_name(sort).is_none())
                        && argument_sorts
                            .iter()
                            .all(|sort| L::parameter_name(sort).is_none())
                        && *term.sort() == result_sort
                        && arguments.len() == argument_sorts.len()
                        && arguments
                            .iter()
                            .zip(&argument_sorts)
                            .all(|(argument, sort)| {
                                is_subsort::<L>(argument.sort(), sort, sort_parents)
                            })
                }
                ApplicationRef::Builtin(operation) => {
                    instance.is_empty()
                        && !*head_instance_fixed
                        && builtin_application_holds::<L>(
                            *operation,
                            term.sort(),
                            arguments,
                            sort_parents,
                        )
                }
                ApplicationRef::Generated(operation) => {
                    require_sort::<L>(declarations, operation.sort())?;
                    instance.is_empty()
                        && !*head_instance_fixed
                        && arguments.len() == 1
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
            // A K-sequence item that rewrites to `.K` keeps its own sort
            // (KF-011); the item is removed.
            let removes_item = matches!(to.kind(), IrTermKind::KSequence { items, .. } if items.is_empty())
                && from.sort() == term.sort();
            if !is_subsort::<L>(from.sort(), term.sort(), sort_parents)
                || (!removes_item && !is_subsort::<L>(to.sort(), term.sort(), sort_parents))
            {
                return Err(L::error(ValidationError::RewriteSortMismatch));
            }
        }
        IrTermKind::As { alias, pattern } => {
            if scope.get(alias) != Some(term.sort())
                || !is_subsort::<L>(pattern.sort(), term.sort(), sort_parents)
            {
                return Err(L::error(ValidationError::InvalidPatternAs));
            }
            validate_term::<L>(
                pattern,
                scope,
                declarations,
                signatures,
                sort_parents,
                cell_ids,
                nodes,
            )?;
        }
        IrTermKind::Or { alternatives } => {
            let mut expected = None;
            for alternative in alternatives {
                if !is_subsort::<L>(alternative.sort(), term.sort(), sort_parents) {
                    return Err(L::error(ValidationError::InvalidPatternOr));
                }
                // Wildcards are distinct generated variables per occurrence;
                // only named binders must agree across alternatives.
                let mut bound = BTreeSet::new();
                collect_term_variables::<L>(alternative, &mut bound);
                bound.retain(|variable| {
                    matches!(
                        variable.kind(),
                        krs_ir::SemanticIdKind::Named | krs_ir::SemanticIdKind::Local { .. }
                    )
                });
                match &expected {
                    None => expected = Some(bound),
                    Some(expected) if *expected != bound => {
                        return Err(L::error(ValidationError::InvalidPatternOr));
                    }
                    Some(_) => {}
                }
                validate_term::<L>(
                    alternative,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
            }
        }
        IrTermKind::Matches {
            subject,
            pattern,
            binds,
        } => {
            // The pattern's named variables are exactly its local binders,
            // each listed once; wildcards are generated variables.
            let mut named = BTreeSet::new();
            collect_term_variables::<L>(pattern, &mut named);
            named.retain(|variable| variable.kind() != krs_ir::SemanticIdKind::Wildcard);
            let listed = binds.iter().cloned().collect::<BTreeSet<_>>();
            if *term.sort() != L::builtin_sort(BuiltinSort::Bool)
                || listed.len() != binds.len()
                || listed != named
                || contains_matches(pattern)
            {
                return Err(L::error(ValidationError::InvalidMatches));
            }
            for term in [subject, pattern] {
                validate_term::<L>(
                    term,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
            }
        }
        IrTermKind::Let {
            pattern,
            value,
            body,
            binds,
        } => {
            // The pattern's named variables are exactly its local binders,
            // each listed once; wildcards are generated variables. A `let`
            // pattern neither aliases nor has alternatives (K's #let).
            let mut named = BTreeSet::new();
            collect_term_variables::<L>(pattern, &mut named);
            named.retain(|variable| variable.kind() != krs_ir::SemanticIdKind::Wildcard);
            let listed = binds.iter().cloned().collect::<BTreeSet<_>>();
            if term.sort() != body.sort()
                || listed.len() != binds.len()
                || listed != named
                || contains_matches(pattern)
                || contains_let(pattern)
                || contains_pattern_as(pattern)
                || contains_pattern_or(pattern)
            {
                return Err(L::error(ValidationError::InvalidLet));
            }
            for term in [pattern, value, body] {
                validate_term::<L>(
                    term,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
            }
        }
    }
    Ok(())
}

/// Whether `term` contains a `let` block (KF-032), which is admitted only in
/// post-terms and conditions.
pub(crate) fn contains_let<L: IrLevel>(term: &IrTerm<L>) -> bool {
    match term.kind() {
        IrTermKind::Let { .. } => true,
        IrTermKind::Matches {
            subject, pattern, ..
        } => contains_let(subject) || contains_let(pattern),
        IrTermKind::As { pattern, .. } => contains_let(pattern),
        IrTermKind::Or { alternatives } => alternatives.iter().any(contains_let),
        IrTermKind::Variable { .. } | IrTermKind::Token { .. } => false,
        IrTermKind::Application { arguments, .. } => arguments.iter().any(contains_let),
        IrTermKind::KSequence { items, .. } => items.iter().any(contains_let),
        IrTermKind::Cell { children, .. } => children.iter().any(contains_let),
        IrTermKind::Map(operands) => operands.operands().any(contains_let),
        IrTermKind::List(operands) => operands.operands().any(contains_let),
        IrTermKind::Set(operands) => operands.operands().any(contains_let),
        IrTermKind::Rewrite { from, to } => contains_let(from) || contains_let(to),
    }
}

/// Whether `term` contains `k::matches!` (KF-031), which is admitted only in
/// post-terms and conditions.
pub(crate) fn contains_matches<L: IrLevel>(term: &IrTerm<L>) -> bool {
    match term.kind() {
        IrTermKind::Matches { .. } => true,
        IrTermKind::As { pattern, .. } => contains_matches(pattern),
        IrTermKind::Or { alternatives } => alternatives.iter().any(contains_matches),
        IrTermKind::Variable { .. } | IrTermKind::Token { .. } => false,
        IrTermKind::Application { arguments, .. } => arguments.iter().any(contains_matches),
        IrTermKind::KSequence { items, .. } => items.iter().any(contains_matches),
        IrTermKind::Cell { children, .. } => children.iter().any(contains_matches),
        IrTermKind::Map(operands) => operands.operands().any(contains_matches),
        IrTermKind::List(operands) => operands.operands().any(contains_matches),
        IrTermKind::Set(operands) => operands.operands().any(contains_matches),
        IrTermKind::Rewrite { from, to } => contains_matches(from) || contains_matches(to),
        IrTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => contains_matches(pattern) || contains_matches(value) || contains_matches(body),
    }
}

/// Collects the binder of every `#Exists` in `predicate` and the local
/// binders of its terms into `binds`, and every variable its terms use
/// outside an `#Exists` that binds it into `outside` (KF-039).
fn collect_exists_binders<L: IrLevel>(
    predicate: &IrMlPredicate<L>,
    binds: &mut Vec<SemanticId>,
    outside: &mut BTreeSet<SemanticId>,
) {
    match predicate.kind() {
        IrMlKind::Top | IrMlKind::Bottom => {}
        IrMlKind::Not { operand } => collect_exists_binders(operand, binds, outside),
        IrMlKind::And { left, right }
        | IrMlKind::Or { left, right }
        | IrMlKind::Implies { left, right } => {
            collect_exists_binders(left, binds, outside);
            collect_exists_binders(right, binds, outside);
        }
        IrMlKind::Equals { left, right, .. } => {
            collect_local_binders(left, binds, outside);
            collect_local_binders(right, binds, outside);
        }
        IrMlKind::Ceil { term, .. } => collect_local_binders(term, binds, outside),
        IrMlKind::Exists { binder, body } => {
            binds.push(binder.id().clone());
            let mut inside = BTreeSet::new();
            collect_exists_binders(body, binds, &mut inside);
            outside.extend(
                inside
                    .into_iter()
                    .filter(|variable| variable != binder.id()),
            );
        }
    }
}

/// The terms of a rule's predicates (KF-039): its predicate rewrite's and
/// its predicate conditions'.
fn predicate_terms<'a, L: Validation>(rule: &RuleView<'a, L>) -> Vec<&'a IrTerm<L>> {
    let mut terms = match rule.body {
        RuleBodyRef::Predicate(body) => {
            let mut terms = body.lhs().terms();
            terms.extend(body.rhs().terms());
            terms
        }
        RuleBodyRef::Term(_) | RuleBodyRef::Configuration { .. } => Vec::new(),
    };
    for predicate in rule
        .requires
        .into_iter()
        .chain(rule.ensures)
        .filter_map(IrCondition::as_predicate)
    {
        terms.extend(predicate.terms());
    }
    terms
}

/// Collects every variable of `condition`: its terms' variables and its
/// `#Exists` binders (KF-039).
pub(crate) fn collect_condition_variables<L: Validation>(
    condition: &IrCondition<L>,
    used: &mut BTreeSet<SemanticId>,
) {
    match condition {
        IrCondition::Bool(condition) => collect_term_variables::<L>(condition.term(), used),
        IrCondition::Predicate(predicate) => collect_predicate_variables::<L>(predicate, used),
    }
}

/// Collects every variable of `predicate`: its terms' variables and its
/// `#Exists` binders (KF-039).
pub(crate) fn collect_predicate_variables<L: Validation>(
    predicate: &IrMlPredicate<L>,
    used: &mut BTreeSet<SemanticId>,
) {
    for term in predicate.terms() {
        collect_term_variables::<L>(term, used);
    }
    for binder in predicate.binders() {
        used.insert(binder.id().clone());
    }
}

/// Validates one condition (KF-039): a Bool term of sort Bool, or a
/// matching-logic predicate.
fn validate_condition<L: Validation>(
    condition: &IrCondition<L>,
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    cell_ids: &BTreeSet<L::Cell>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    match condition {
        IrCondition::Bool(condition) => {
            insert_node::<L>(nodes, condition.origin().key())?;
            validate_term::<L>(
                condition.term(),
                scope,
                declarations,
                signatures,
                sort_parents,
                cell_ids,
                nodes,
            )?;
            if condition.term().sort() != &L::builtin_sort(BuiltinSort::Bool) {
                return Err(L::error(ValidationError::RuleConditionSortMismatch));
            }
            Ok(())
        }
        IrCondition::Predicate(predicate) => validate_predicate::<L>(
            predicate,
            scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        ),
    }
}

/// Validates a predicate simplification's body (KF-039): a simplification
/// whose left side is rooted at `#Equals` or `#Ceil`.
#[expect(
    clippy::too_many_arguments,
    reason = "The rewrite is validated against the same tables as any rule body."
)]
fn validate_predicate_rewrite<L: Validation>(
    rule: &RuleView<'_, L>,
    body: &IrPredicateRewrite<L>,
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    cell_ids: &BTreeSet<L::Cell>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    if rule.kind != SentenceKind::Simplification
        || !matches!(
            body.lhs().kind(),
            IrMlKind::Equals { .. } | IrMlKind::Ceil { .. }
        )
    {
        return Err(L::error(ValidationError::InvalidMlPredicate));
    }
    insert_node::<L>(nodes, body.origin().key())?;
    for predicate in [body.lhs(), body.rhs()] {
        validate_predicate::<L>(
            predicate,
            scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        )?;
    }
    Ok(())
}

/// Validates one matching-logic predicate (KF-039): every node's origin,
/// every operand at its node's operand sort, and every `#Exists` binder a
/// sentence variable of its declared sort.
fn validate_predicate<L: Validation>(
    predicate: &IrMlPredicate<L>,
    scope: &BTreeMap<SemanticId, L::Sort>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    cell_ids: &BTreeSet<L::Cell>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    insert_node::<L>(nodes, predicate.origin().key())?;
    let operand = |term: &IrTerm<L>,
                   operand_sort: &L::Sort,
                   nodes: &mut BTreeSet<SourceMapKey>|
     -> Result<(), L::Error> {
        validate_term::<L>(
            term,
            scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        )?;
        if !is_subsort::<L>(term.sort(), operand_sort, sort_parents) {
            return Err(L::error(ValidationError::InvalidMlPredicate));
        }
        Ok(())
    };
    match predicate.kind() {
        IrMlKind::Top | IrMlKind::Bottom => Ok(()),
        IrMlKind::Not { operand: inner } => validate_predicate::<L>(
            inner,
            scope,
            declarations,
            signatures,
            sort_parents,
            cell_ids,
            nodes,
        ),
        IrMlKind::And { left, right }
        | IrMlKind::Or { left, right }
        | IrMlKind::Implies { left, right } => {
            for inner in [left, right] {
                validate_predicate::<L>(
                    inner,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    cell_ids,
                    nodes,
                )?;
            }
            Ok(())
        }
        IrMlKind::Equals {
            operand_sort,
            left,
            right,
        } => {
            require_sort::<L>(declarations, operand_sort)?;
            operand(left, operand_sort, nodes)?;
            operand(right, operand_sort, nodes)
        }
        IrMlKind::Ceil { operand_sort, term } => {
            require_sort::<L>(declarations, operand_sort)?;
            operand(term, operand_sort, nodes)
        }
        IrMlKind::Exists { binder, body } => {
            if scope.get(binder.id()) != Some(binder.sort()) {
                return Err(L::error(ValidationError::InvalidClaimBinder(
                    binder.id().clone(),
                )));
            }
            require_sort::<L>(declarations, binder.sort())?;
            insert_node::<L>(nodes, binder.origin().key())?;
            insert_node::<L>(nodes, binder.name_origin().key())?;
            insert_node::<L>(nodes, binder.sort_origin().key())?;
            validate_predicate::<L>(
                body,
                scope,
                declarations,
                signatures,
                sort_parents,
                cell_ids,
                nodes,
            )
        }
    }
}

/// Collects the local binders of every `k::matches!` in `term` into `binds`
/// and every variable used outside a `k::matches!` pattern into `outside`.
fn collect_local_binders<L: IrLevel>(
    term: &IrTerm<L>,
    binds: &mut Vec<SemanticId>,
    outside: &mut BTreeSet<SemanticId>,
) {
    let mut each = |terms: &mut dyn Iterator<Item = &IrTerm<L>>| {
        for child in terms {
            collect_local_binders(child, binds, outside);
        }
    };
    match term.kind() {
        IrTermKind::Matches {
            subject,
            binds: local,
            ..
        } => {
            binds.extend(local.iter().cloned());
            collect_local_binders(subject, binds, outside);
        }
        IrTermKind::Variable { variable } => {
            outside.insert(variable.clone());
        }
        IrTermKind::Token { .. } => {}
        IrTermKind::As { alias, pattern } => {
            outside.insert(alias.clone());
            collect_local_binders(pattern, binds, outside);
        }
        IrTermKind::Or { alternatives } => each(&mut alternatives.iter()),
        IrTermKind::Application { arguments, .. } => each(&mut arguments.iter()),
        IrTermKind::KSequence { items, .. } => each(&mut items.iter()),
        IrTermKind::Cell { children, .. } => each(&mut children.iter()),
        IrTermKind::Map(operands) => each(&mut operands.operands()),
        IrTermKind::List(operands) => each(&mut operands.operands()),
        IrTermKind::Set(operands) => each(&mut operands.operands()),
        IrTermKind::Rewrite { from, to } => each(&mut [&**from, &**to].into_iter()),
        // The value is outside the pattern's scope; the let's own binders
        // occur only in its pattern and body.
        IrTermKind::Let {
            pattern,
            value,
            body,
            binds: local,
        } => {
            binds.extend(local.iter().cloned());
            collect_local_binders(value, binds, outside);
            let mut inside = BTreeSet::new();
            collect_local_binders(pattern, binds, &mut inside);
            collect_local_binders(body, binds, &mut inside);
            outside.extend(
                inside
                    .into_iter()
                    .filter(|variable| !local.contains(variable)),
            );
        }
    }
}

/// Whether `term` contains `alias @ pattern`, which is admitted only in
/// pre-patterns (KF-029).
pub(crate) fn contains_pattern_as<L: IrLevel>(term: &IrTerm<L>) -> bool {
    match term.kind() {
        IrTermKind::As { .. } => true,
        // A `k::matches!` pattern may alias (KF-031).
        IrTermKind::Matches { subject, .. } => contains_pattern_as(subject),
        IrTermKind::Or { alternatives } => alternatives.iter().any(contains_pattern_as),
        IrTermKind::Variable { .. } | IrTermKind::Token { .. } => false,
        IrTermKind::Application { arguments, .. } => arguments.iter().any(contains_pattern_as),
        IrTermKind::KSequence { items, .. } => items.iter().any(contains_pattern_as),
        IrTermKind::Cell { children, .. } => children.iter().any(contains_pattern_as),
        IrTermKind::Map(operands) => operands.operands().any(contains_pattern_as),
        IrTermKind::List(operands) => operands.operands().any(contains_pattern_as),
        IrTermKind::Set(operands) => operands.operands().any(contains_pattern_as),
        IrTermKind::Rewrite { from, to } => contains_pattern_as(from) || contains_pattern_as(to),
        IrTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => {
            contains_pattern_as(pattern) || contains_pattern_as(value) || contains_pattern_as(body)
        }
    }
}

/// Whether `term` contains `A | B`, which is admitted only in pre-patterns
/// (KF-030).
pub(crate) fn contains_pattern_or<L: IrLevel>(term: &IrTerm<L>) -> bool {
    match term.kind() {
        IrTermKind::Or { .. } => true,
        // A `k::matches!` pattern may have alternatives (KF-031).
        IrTermKind::Matches { subject, .. } => contains_pattern_or(subject),
        IrTermKind::As { pattern, .. } => contains_pattern_or(pattern),
        IrTermKind::Variable { .. } | IrTermKind::Token { .. } => false,
        IrTermKind::Application { arguments, .. } => arguments.iter().any(contains_pattern_or),
        IrTermKind::KSequence { items, .. } => items.iter().any(contains_pattern_or),
        IrTermKind::Cell { children, .. } => children.iter().any(contains_pattern_or),
        IrTermKind::Map(operands) => operands.operands().any(contains_pattern_or),
        IrTermKind::List(operands) => operands.operands().any(contains_pattern_or),
        IrTermKind::Set(operands) => operands.operands().any(contains_pattern_or),
        IrTermKind::Rewrite { from, to } => contains_pattern_or(from) || contains_pattern_or(to),
        IrTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => {
            contains_pattern_or(pattern) || contains_pattern_or(value) || contains_pattern_or(body)
        }
    }
}

/// Rejects `alias @ pattern` and `A | B` in a rule's post-terms and
/// conditions (outside `k::matches!` patterns), `k::matches!` in its
/// pre-patterns, and a `k::matches!` local binder that is listed twice or
/// occurs outside its pattern (BIND-1).
/// Whether the local rewrites of a single-body term are well placed
/// (KF-011): none inside another rewrite, and a right side `.K` (an empty K
/// sequence) only on a whole K-sequence item.
fn local_rewrites_valid<L: Validation>(term: &IrTerm<L>, item: bool) -> bool {
    match term.kind() {
        IrTermKind::Rewrite { from, to } => {
            let empty =
                matches!(to.kind(), IrTermKind::KSequence { items, .. } if items.is_empty());
            (!empty || item) && !from.contains_rewrite() && !to.contains_rewrite()
        }
        IrTermKind::KSequence { items, .. } => {
            items.iter().all(|child| local_rewrites_valid(child, true))
        }
        _ => term
            .children()
            .into_iter()
            .all(|child| local_rewrites_valid(child, false)),
    }
}

/// Whether a two-sided rule body holds a local rewrite (KF-011), which only
/// a single-body clause may: a term rewrite's sides, or a predicate
/// rewrite's object terms.
fn body_contains_rewrite<L: Validation>(body: RuleBodyRef<'_, L>) -> bool {
    match body {
        RuleBodyRef::Term(body) => body.from().contains_rewrite() || body.to().contains_rewrite(),
        RuleBodyRef::Predicate(body) => body
            .lhs()
            .terms()
            .into_iter()
            .chain(body.rhs().terms())
            .any(IrTerm::contains_rewrite),
        RuleBodyRef::Configuration { .. } => false,
    }
}

fn reject_pattern_as_outside_patterns<L: Validation>(
    rule: &RuleView<'_, L>,
) -> Result<(), L::Error> {
    let mut pre = Vec::new();
    let mut post = Vec::new();
    // A single-body clause (KF-011) is read through its images.
    let mut images = Vec::new();
    match rule.body {
        RuleBodyRef::Term(body) => {
            pre.push(body.from());
            post.push(body.to());
        }
        RuleBodyRef::Predicate(body) => {
            pre.extend(body.lhs().terms());
            post.extend(body.rhs().terms());
        }
        RuleBodyRef::Configuration { body, .. } => {
            for clause in body.clauses() {
                match clause.after() {
                    CellPost::Local => {
                        images.push((clause.before().pre_pattern(), clause.before().post_term()));
                    }
                    CellPost::Preserve => pre.push(clause.before()),
                    CellPost::Replace { term } => {
                        pre.push(clause.before());
                        post.push(term);
                    }
                }
            }
        }
    }
    for (left, right) in &images {
        pre.push(left);
        post.push(right);
    }
    let conditions = rule
        .requires
        .into_iter()
        .chain(rule.ensures)
        .flat_map(IrCondition::terms)
        .collect::<Vec<_>>();
    if body_contains_rewrite(rule.body) || conditions.iter().any(|term| term.contains_rewrite()) {
        return Err(L::error(ValidationError::InvalidLocalRewrite));
    }
    post.extend(conditions);
    if post.iter().copied().any(contains_pattern_as) {
        return Err(L::error(ValidationError::InvalidPatternAs));
    }
    if post.iter().copied().any(contains_pattern_or) {
        return Err(L::error(ValidationError::InvalidPatternOr));
    }
    if pre.iter().copied().any(contains_matches) {
        return Err(L::error(ValidationError::InvalidMatches));
    }
    if pre.iter().copied().any(contains_let) {
        return Err(L::error(ValidationError::InvalidLet));
    }
    let mut binds = Vec::new();
    let mut outside = BTreeSet::new();
    // A predicate's terms are collected with its `#Exists` binders below.
    let predicate_terms = predicate_terms(rule);
    for term in pre.into_iter().chain(post) {
        if !predicate_terms
            .iter()
            .any(|candidate| std::ptr::eq(*candidate, term))
        {
            collect_local_binders(term, &mut binds, &mut outside);
        }
    }
    // An `#Exists` binder (KF-039) is a local binder of its body.
    let predicates = match rule.body {
        RuleBodyRef::Predicate(body) => vec![body.lhs(), body.rhs()],
        RuleBodyRef::Term(_) | RuleBodyRef::Configuration { .. } => Vec::new(),
    };
    let conditions = rule
        .requires
        .into_iter()
        .chain(rule.ensures)
        .filter_map(IrCondition::as_predicate);
    for predicate in predicates.into_iter().chain(conditions) {
        collect_exists_binders(predicate, &mut binds, &mut outside);
    }
    if let RuleBodyRef::Configuration { body, .. } = rule.body {
        for clause in body.clauses() {
            if let CellContentFrame::KSequenceTail {
                binding: Some(binding),
                ..
            }
            | CellContentFrame::MapRemainder {
                binding: Some(binding),
                ..
            } = clause.frame()
            {
                outside.insert(binding.clone());
            }
        }
    }
    let distinct = binds.iter().collect::<BTreeSet<_>>();
    if distinct.len() != binds.len() || distinct.iter().any(|bind| outside.contains(*bind)) {
        return Err(L::error(ValidationError::InvalidMatches));
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

/// Validates a production's parameters and records its signature.
pub(crate) fn insert_production_signature<L: Validation>(
    signatures: &mut Signatures<L>,
    id: L::Declaration,
    signature: Signature<L>,
) -> Result<(), L::Error> {
    validate_production_parameters::<L>(&id, &signature)?;
    signatures.insert(id, signature);
    Ok(())
}

/// Checks a production's sort parameters (KF-027): distinct, each the sort
/// of some argument, and the only parameters its result and arguments name.
pub(crate) fn validate_production_parameters<L: Validation>(
    id: &L::Declaration,
    (result_sort, parameters, argument_sorts): &Signature<L>,
) -> Result<(), L::Error> {
    let declared =
        |sort: &L::Sort| L::parameter_name(sort).is_none_or(|name| parameters.contains(name));
    let distinct = parameters
        .iter()
        .enumerate()
        .all(|(index, name)| !parameters[..index].contains(name));
    let used = parameters.iter().all(|name| {
        argument_sorts
            .iter()
            .any(|sort| L::parameter_name(sort) == Some(name))
    });
    if distinct && used && declared(result_sort) && argument_sorts.iter().all(declared) {
        Ok(())
    } else {
        Err(L::error(ValidationError::ApplicationSignature(id.clone())))
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
