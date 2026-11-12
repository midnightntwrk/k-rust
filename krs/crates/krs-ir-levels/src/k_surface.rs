//! K-surface facts shared by the `.k` printer and the k-rust adapter.
//! Each backend must retain its own printing.

use std::collections::{BTreeMap, BTreeSet};

mod variable_names;

pub use variable_names::{
    SentenceVariables, VariableNaming, authored_variable_spelling, definition_terminals,
    generated_binder_names, generated_variable_name,
};

use crate::{
    DefinitionIr, DefinitionModule, DefinitionSentence, DefinitionSortRef, DefinitionTerm,
    DefinitionTermKind, IrLevel, IrSortRef, IrTerm, IrTermKind, ProductionSentence, RuleBodyRef,
    SymbolId, SymbolIdentity,
};
use krs_ir::{
    ApplicationRef, BuiltinSort, FixedCell, FixedCellContent, FixedConfiguration,
    FixedInitializerCell, FixedInitializerContent, GrammarProductionItemKind, OperationSort,
    ProductionAttribute, ProductionGroupId, StableItemId,
};

/// Borrowed declarations and names from one Definition IR.
#[derive(Default)]
pub struct DefinitionIndex<'a> {
    sorts: BTreeMap<SymbolId, &'a SymbolIdentity>,
    productions: BTreeMap<SymbolId, &'a ProductionSentence>,
    symbols: BTreeMap<SymbolId, &'a str>,
    groups: BTreeMap<ProductionGroupId, &'a str>,
    cells: BTreeMap<SymbolId, &'a str>,
    collections: BTreeMap<SymbolId, krs_ir::CellCollectionType>,
    cell_parents: BTreeMap<SymbolId, SymbolId>,
    instance_holders: BTreeMap<SymbolId, SymbolId>,
    context_aliases: BTreeMap<StableItemId, &'a str>,
}

impl<'a> DefinitionIndex<'a> {
    /// Indexes declarations in canonical module and sentence order.
    #[must_use]
    pub fn new(definition: &'a DefinitionIr) -> Self {
        let mut index = Self::default();
        for module in definition.modules() {
            for group in module.production_groups() {
                index
                    .groups
                    .insert(group.id().clone(), group.emitted_name());
            }
            for sentence in module.sentences() {
                match sentence {
                    DefinitionSentence::SyntaxSort(sort) => {
                        let symbol = sort.symbol();
                        index.sorts.insert(symbol.id().clone(), symbol);
                        index
                            .symbols
                            .insert(symbol.id().clone(), symbol.emitted_name());
                    }
                    DefinitionSentence::Production(production) => {
                        let symbol = production.symbol();
                        index.productions.insert(symbol.id().clone(), production);
                        index
                            .symbols
                            .insert(symbol.id().clone(), symbol.emitted_name());
                    }
                    DefinitionSentence::Configuration(configuration) => {
                        index.collect_cells(configuration.cells(), None);
                    }
                    DefinitionSentence::ContextAlias(alias) => {
                        index
                            .context_aliases
                            .insert(alias.id().clone(), alias.name());
                    }
                    DefinitionSentence::Subsort(_)
                    | DefinitionSentence::Precedence(_)
                    | DefinitionSentence::Associativity(_)
                    | DefinitionSentence::Rule(_)
                    | DefinitionSentence::Lexical(_)
                    | DefinitionSentence::Layout(_)
                    | DefinitionSentence::Raw(_) => {}
                }
            }
        }
        index
    }

    /// Returns a declared sort's symbol identity.
    #[must_use]
    pub fn sort(&self, id: &SymbolId) -> Option<&'a SymbolIdentity> {
        self.sorts.get(id).copied()
    }

    /// Returns a declared sort's emitted name.
    #[must_use]
    pub fn sort_name(&self, id: &SymbolId) -> Option<&'a str> {
        self.sort(id).map(SymbolIdentity::emitted_name)
    }

    /// Returns a declared production's sentence.
    #[must_use]
    pub fn production(&self, id: &SymbolId) -> Option<&'a ProductionSentence> {
        self.productions.get(id).copied()
    }

    /// Returns the emitted name of a sort or production symbol.
    #[must_use]
    pub fn symbol_name(&self, id: &SymbolId) -> Option<&'a str> {
        self.symbols.get(id).copied()
    }

    /// Returns a production group's emitted name.
    #[must_use]
    pub fn group_name(&self, id: &ProductionGroupId) -> Option<&'a str> {
        self.groups.get(id).copied()
    }

    /// Returns a fixed cell's authored name at any depth in the configuration.
    #[must_use]
    pub fn cell_name(&self, id: &SymbolId) -> Option<&'a str> {
        self.cells.get(id).copied()
    }

    /// Returns the parent cell of a nested cell; a top-level cell has none.
    #[must_use]
    pub fn cell_parent(&self, id: &SymbolId) -> Option<&SymbolId> {
        self.cell_parents.get(id)
    }

    /// Returns the instance a cell lies in: the innermost optional (`?`) or collection (`*`)
    /// cell strictly above it. A sentence's clause for the cell is written inside that cell,
    /// so that every clause of a sentence about one instance matches in the same instance; a
    /// cell outside every `?` and `*` cell has none.
    #[must_use]
    pub fn instance_holder(&self, id: &SymbolId) -> Option<&SymbolId> {
        self.instance_holders.get(id)
    }

    /// Returns the instances a sentence's cells lie in ([`Self::instance_holder`]), outermost
    /// first: the instance each cell lies in and the instances enclosing it, from the outermost
    /// one some cell lies in directly; empty when every cell lies outside every `?` and `*` cell.
    ///
    /// A sentence about one instance names cells of that instance, and, where it passes the
    /// keys of the instances enclosing it, the key cell of each of those; a sentence about the
    /// configuration names no cell inside an instance except through its instance record. So
    /// each clause is written inside the cell of the instance it lies in, nested in the cells
    /// of the enclosing instances the sentence names, or at the top.
    ///
    /// A cell outside every instance occurs once in the configuration, so its clause matches that
    /// occurrence wherever the instance clauses match: a rule that matches a core's computation
    /// and the memory beside the cores is a step of one core that reads or writes the one memory.
    /// The instances are those of the cells inside an instance alone; a cell outside every
    /// instance adds none, and its clause is written at the top ([`Self::clause_layout`]).
    ///
    /// # Errors
    ///
    /// Returns [`MixedInstances`] for two cells inside instances that lie in no one chain of
    /// nested instances: no nesting of instance cells holds both.
    pub fn sentence_instances<'c>(
        &self,
        cells: impl IntoIterator<Item = &'c SymbolId>,
    ) -> Result<Vec<&SymbolId>, MixedInstances> {
        let chains = cells
            .into_iter()
            .map(|cell| (cell, self.instance_chain(cell)))
            .collect::<Vec<_>>();
        let Some((deepest, chain)) = chains.iter().max_by_key(|(_, chain)| chain.len()) else {
            return Ok(Vec::new());
        };
        let mut outermost = chain.len();
        for (cell, other) in chains.iter().filter(|(_, other)| !other.is_empty()) {
            if !chain.starts_with(other) {
                return Err(MixedInstances {
                    first: (*deepest).clone(),
                    other: (*cell).clone(),
                });
            }
            outermost = outermost.min(other.len() - 1);
        }
        Ok(chain[outermost.min(chain.len())..].to_vec())
    }

    /// Returns where a sentence's clauses, whose cells are `cells` in clause order, are written:
    /// inside the cells of the instances they lie in ([`Self::sentence_instances`]), each
    /// instance's cell holding the clauses that lie in it directly, in clause order, then the
    /// cell of the next instance, open on the right for the instance's other cells; or at the
    /// top, every clause in order, where they lie in no instance. The clauses of cells outside
    /// every instance beside those inside one ([`ClauseLayout::top`]) are written at the top,
    /// beside the outermost instance's cell, after it.
    ///
    /// # Errors
    ///
    /// Returns [`MixedInstances`] as [`Self::sentence_instances`] does.
    pub fn clause_layout<'c>(
        &self,
        cells: impl IntoIterator<Item = &'c SymbolId>,
    ) -> Result<ClauseLayout<'_>, MixedInstances> {
        let cells = cells.into_iter().collect::<Vec<_>>();
        let chain = self.sentence_instances(cells.iter().copied())?;
        let (levels, top) = if chain.is_empty() {
            (vec![(0..cells.len()).collect()], Vec::new())
        } else {
            let levels = chain
                .iter()
                .map(|instance| {
                    cells
                        .iter()
                        .enumerate()
                        .filter(|(_, cell)| self.instance_holder(cell) == Some(*instance))
                        .map(|(index, _)| index)
                        .collect()
                })
                .collect();
            let top = cells
                .iter()
                .enumerate()
                .filter(|(_, cell)| self.instance_holder(cell).is_none())
                .map(|(index, _)| index)
                .collect();
            (levels, top)
        };
        Ok(ClauseLayout { chain, levels, top })
    }

    /// The instances `cell` lies in, outermost first ([`Self::instance_holder`], then the
    /// instance that holder lies in, and so on).
    fn instance_chain(&self, cell: &SymbolId) -> Vec<&SymbolId> {
        let mut chain = Vec::new();
        let mut current = self.instance_holder(cell);
        while let Some(holder) = current {
            chain.push(holder);
            current = self.instance_holder(holder);
        }
        chain.reverse();
        chain
    }

    /// Returns K's generated sort name of a fixed cell, such as `FrameCell`
    /// for `<frame>` (see [`cell_sort_name`]).
    #[must_use]
    pub fn cell_sort_name(&self, id: &SymbolId) -> Option<String> {
        self.cell_name(id).map(cell_sort_name)
    }

    /// Returns K's generated sort name of a collection cell's instances, such as `AcctCellMap`
    /// for `<acct multiplicity="*" type="Map">` (see [`collection_sort_name`]); `None` for a
    /// cell that is no typed collection.
    #[must_use]
    pub fn cell_collection_sort_name(&self, id: &SymbolId) -> Option<String> {
        Some(collection_sort_name(
            self.cell_name(id)?,
            *self.collections.get(id)?,
        ))
    }

    /// Returns a context alias's authored name without backend escaping.
    #[must_use]
    pub fn context_alias_name(&self, id: &StableItemId) -> Option<&'a str> {
        self.context_aliases.get(id).copied()
    }

    /// Indexes `cells` and their descendants; `holder` is the innermost `?` or `*` cell
    /// strictly above `cells`.
    fn collect_cells(
        &mut self,
        cells: &'a [FixedCell<DefinitionSortRef, SymbolId>],
        holder: Option<&SymbolId>,
    ) {
        for cell in cells {
            self.cells.insert(cell.id().clone(), cell.name());
            if let Some(collection) = cell.collection_type() {
                self.collections.insert(cell.id().clone(), collection);
            }
            if let Some(holder) = holder {
                self.instance_holders
                    .insert(cell.id().clone(), holder.clone());
            }
            if let FixedCellContent::Children { children } = cell.content() {
                for child in children {
                    self.cell_parents
                        .insert(child.id().clone(), cell.id().clone());
                }
                let holds_instances = cell.attributes().iter().any(|attribute| {
                    matches!(attribute, krs_ir::CellAttribute::Multiplicity { .. })
                });
                self.collect_cells(
                    children,
                    if holds_instances {
                        Some(cell.id())
                    } else {
                        holder
                    },
                );
            }
        }
    }
}

/// The field of the hidden argument in which a function evaluated in one instance of the Map
/// collection cell `holder` receives that instance's key, after its own arguments: a function has
/// one value for its arguments, so the instance its context reads is one of them.
#[must_use]
pub fn instance_key_field(holder: &str) -> String {
    format!("{}{INSTANCE_KEY}{holder}", krs_ir::ir::RESERVED_MARKER)
}

/// The Map collection cell whose instance key a production's field receives, where the field is
/// such a hidden argument ([`instance_key_field`]).
#[must_use]
pub fn instance_key_holder(field: &str) -> Option<&str> {
    field
        .strip_prefix(krs_ir::ir::RESERVED_MARKER)?
        .strip_prefix(INSTANCE_KEY)
}

const INSTANCE_KEY: &str = "key_";

/// Where a sentence's clauses are written ([`DefinitionIndex::clause_layout`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClauseLayout<'a> {
    /// The instances whose cells hold the clauses, outermost first; empty where the clauses are
    /// written at the top.
    pub chain: Vec<&'a SymbolId>,
    /// The clauses each level holds directly, by index, in clause order: one level, the top,
    /// where `chain` is empty, else one for each instance of `chain`, in its order.
    pub levels: Vec<Vec<usize>>,
    /// Where `chain` is not empty, the clauses outside every instance, by index, in clause order:
    /// a cell the configuration holds once, matched beside the one instance of each holder the
    /// other clauses match, and written at the top after the outermost instance's cell. Empty
    /// where `chain` is, whose one level is the top.
    pub top: Vec<usize>,
}

/// The number of items a clause is written as among the cells of its level
/// ([`DefinitionIndex::clause_layout`]): one cell, or one rewrite of an optional cell, for a
/// fixed or an optional cell's clause; for a collection's, its [`InstancesLayout::written`].
#[must_use]
pub fn written_items<C, T>(clause: &krs_ir::ConfigurationClause<C, T>) -> usize {
    match clause {
        krs_ir::ConfigurationClause::Fixed(_) | krs_ir::ConfigurationClause::Optional(_) => 1,
        krs_ir::ConfigurationClause::Instances(clause) => instances_layout(clause).written(),
    }
}

/// One item a collection (`*`) clause is written as ([`instances_layout`]).
#[derive(Debug)]
pub enum InstancesItem<'c, C, T> {
    /// An instance the clause matches, creates or removes.
    Instance(&'c krs_ir::InstanceClause<C, T>),
    /// `...`, the other instances, inside the collection's parent cell.
    Others,
    /// A variable naming the other instances, before the back instances.
    Rest,
    /// `.Bag`: an exact clause that names no instance, whose parent cell holds none.
    Empty,
}

/// How a collection (`*`) clause is written: an open Set or Map clause as its instances, beside
/// the other cells of its level, leaving the collection's parent cell to cell completion; an
/// exact clause and a List clause inside the parent cell, a List clause's back instances after
/// the other instances, which a variable names. A clause that names no instance is the
/// collection as a whole, so it is written inside the parent cell too, as the parent's content:
/// `.Bag` when exact, the other instances when open.
#[derive(Debug)]
pub struct InstancesLayout<'c, C, T> {
    /// Whether the items are written inside the collection's parent cell.
    pub in_parent: bool,
    /// The items, in order: the front instances, the other instances (`...` inside the parent
    /// cell, or a variable when back instances follow them), the back instances.
    pub items: Vec<InstancesItem<'c, C, T>>,
}

impl<C, T> InstancesLayout<'_, C, T> {
    /// The number of items the clause is written as among the cells of its level: the parent
    /// cell, or each of [`Self::items`].
    #[must_use]
    pub fn written(&self) -> usize {
        if self.in_parent { 1 } else { self.items.len() }
    }
}

/// How the collection clause `clause` is written ([`InstancesLayout`]).
#[must_use]
pub fn instances_layout<C, T>(clause: &krs_ir::InstancesClause<C, T>) -> InstancesLayout<'_, C, T> {
    let names_none = clause.front().is_empty() && clause.back().is_empty();
    let in_parent =
        clause.ordering() == krs_ir::InstanceOrdering::List || !clause.is_open() || names_none;
    let mut items = clause
        .front()
        .iter()
        .map(InstancesItem::Instance)
        .collect::<Vec<_>>();
    if clause.is_open() {
        if !clause.back().is_empty() {
            items.push(InstancesItem::Rest);
        } else if in_parent {
            items.push(InstancesItem::Others);
        }
    }
    items.extend(clause.back().iter().map(InstancesItem::Instance));
    if items.is_empty() {
        items.push(InstancesItem::Empty);
    }
    InstancesLayout { in_parent, items }
}

/// The one instance a collection (`*`) clause steps
/// ([`krs_ir::InstancesClause::stepped_instance`]), where it is written
/// ([`stepped_instance_layout`]).
#[derive(Debug)]
pub struct SteppedInstanceLayout<'c, C, T> {
    /// The instance's children, the cells of that instance the clause reads or rewrites in place,
    /// in the order the instance's cell holds them, each as one cell.
    pub children: &'c [krs_ir::FixedCellClause<C, T>],
    /// Whether the instance's cell is open on the right for the instance's other cells.
    pub open: bool,
    /// Whether the clause is written inside the collection's parent cell
    /// ([`InstancesLayout::in_parent`]).
    pub in_parent: bool,
    /// The instance's place among the items the clause is written as
    /// ([`InstancesLayout::items`]); an item before it is a variable of the parent cell's
    /// content, never its frame.
    pub position: usize,
}

/// Where the clause `clause` writes the one instance it steps, if it steps one
/// ([`krs_ir::InstancesClause::stepped_instance`]): that instance's cell is one item of
/// [`instances_layout`], and it holds the instance's children, one cell each, in order, then its
/// frame where the instance is open. The children are the clauses of a rule about that one
/// instance, as the cells of an instance a rule lies in are ([`DefinitionIndex::clause_layout`]),
/// and the rest of the collection is no part of the step. `None` for a clause about the
/// collection whole.
#[must_use]
pub fn stepped_instance_layout<C, T>(
    clause: &krs_ir::InstancesClause<C, T>,
) -> Option<SteppedInstanceLayout<'_, C, T>> {
    // `stepped_instance` names only a kept instance; the pattern destructures it.
    let krs_ir::InstanceClause::Kept { children, open, .. } = clause.stepped_instance()? else {
        return None;
    };
    let layout = instances_layout(clause);
    let position = layout
        .items
        .iter()
        .position(|item| matches!(item, InstancesItem::Instance(_)))?;
    Some(SteppedInstanceLayout {
        children,
        open: *open,
        in_parent: layout.in_parent,
        position,
    })
}

/// Two cells of one sentence that lie in instances on no one chain of nested instances
/// ([`DefinitionIndex::sentence_instances`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MixedInstances {
    /// A cell of the sentence that lies deepest.
    pub first: SymbolId,
    /// A cell that lies in an instance whose chain is no part of `first`'s.
    pub other: SymbolId,
}

impl std::fmt::Display for MixedInstances {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "the cells {} and {} of one sentence lie in different instances, so no one instance cell holds its clauses",
            self.first, self.other
        )
    }
}

/// Builtin import requirements for a K consumer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImportPolicy {
    /// Imports for the source-text printer.
    /// Each sort found in a declaration or term annotation must select its syntax module unless a visited builtin operation uses that sort, in which case it must select its full module.
    /// Every visited builtin or collection operation must add its catalog `k_module`; its other signature sorts must only upgrade already required sorts.
    /// Configurations must not imply a Map import, and claim `ensures` terms must not contribute requirements.
    SourceText,
    /// Imports for the native frontend.
    /// Sorts and operations select modules exactly as for [`Self::SourceText`], so the
    /// native definition holds the sentences Java K kompiles from the emitted K: a sort
    /// that only occurs imports its syntax module, never its full module.
    /// Every configuration must require Map because frontend expansion lowers external variables through `Map:lookup`,
    /// as Java K's configuration expansion does for the emitted K.
    /// Claim `ensures` terms must contribute requirements.
    NativeFrontend,
    /// Imports of a package's program-syntax module `<NS>-SYNTAX`, shared by
    /// both consumers.
    /// Each required sort must select its catalog `k_program_syntax_module`
    /// (Int under the module's `int-literals` setting), so builtin operations
    /// such as `+Int` and `andBool` are never program syntax.
    ProgramSyntax,
}

impl ImportPolicy {
    /// Selects this consumer policy for a semantics module and
    /// [`Self::ProgramSyntax`] for a program-syntax module.
    #[must_use]
    pub fn for_module(self, module: &DefinitionModule) -> Self {
        match module.role() {
            crate::ModuleRole::ProgramSyntax => Self::ProgramSyntax,
            crate::ModuleRole::Semantics | crate::ModuleRole::Spec => self,
        }
    }
}

/// Returns a module's builtin imports under the selected consumer policy.
/// Both policies must inspect subsorts, production signatures and strictness result sorts, configuration cell sorts, variables and initializers, context alias variables and cell patterns, and rule variables, bodies and `requires` terms.
/// Term traversal must include annotations, K-sequence item sorts, collection sorts and all children.
/// Claim binder declarations must not contribute requirements independently of rule variables and terms.
/// Sorts whose selected catalog module is absent must not produce imports.
#[must_use]
pub fn builtin_imports(module: &DefinitionModule, policy: ImportPolicy) -> BTreeSet<&'static str> {
    let requirements = module_requirements(module, policy);
    // `K` has no module of its own in the catalog: rule, configuration, and
    // program grammars always contain it, but a production over it needs
    // the sort declared where the production is (N16).
    let sort_k = requirements.declares_k.then_some(SORT_K_MODULE);
    if policy == ImportPolicy::ProgramSyntax {
        let int_literals = module.int_literals();
        return requirements
            .sorts
            .into_iter()
            .filter_map(|sort| int_literals.program_syntax_module(sort))
            .chain(sort_k)
            .collect();
    }
    let mut imports = requirements.term_imports();
    imports.extend(sort_k);
    imports
}

/// The builtin modules the K text of the `k::patterns!` parts `parts` names: what a module
/// holding exactly those parts as its rules would import ([`builtin_imports`] under
/// [`ImportPolicy::SourceText`]).
///
/// A part is a question about the definition's runs and no sentence of it, so its text is read
/// in the definition's main module together with these modules, never in the main module alone:
/// which builtin operations a part may name does not depend on which ones the definition's own
/// sentences happen to name. A part's variables, cell patterns and `requires` contribute, the
/// tests the definedness pass wrote into the `requires` among them.
#[must_use]
pub fn pattern_part_imports<'a>(
    parts: impl IntoIterator<Item = &'a crate::RuleSentence>,
) -> BTreeSet<&'static str> {
    let mut requirements = BuiltinRequirements::default();
    for part in parts {
        requirements.rule_reads(part);
    }
    requirements.term_imports()
}

/// Whether `sentence` is a rule or claim with a matching-logic predicate in
/// its body or conditions (KF-039).
#[must_use]
pub fn has_predicate(sentence: &crate::RuleSentence) -> bool {
    matches!(sentence.relational_body(), RuleBodyRef::Predicate(_))
        || sentence
            .requires()
            .into_iter()
            .chain(sentence.ensures())
            .any(|condition| condition.as_predicate().is_some())
}

/// K's module of the matching-logic connectives (`kast.md`), imported by a
/// module with predicates (KF-039).
pub const ML_SYNTAX_MODULE: &str = "ML-SYNTAX";

/// K's module that declares the sort `K` and nothing else (`kast.md`),
/// imported by a module whose declarations name `KSequence`.
pub const SORT_K_MODULE: &str = "SORT-K";

/// K's symbolic map lemmas (`domains.md`), imported by a module with
/// predicates that uses maps (KF-039).
pub const MAP_SYMBOLIC_MODULE: &str = "MAP-SYMBOLIC";

/// Every declared sort and production symbol `configuration` names: the
/// sorts of its cells and variables, and the sorts and productions of its
/// initializer terms. Its own cells are not included.
#[must_use]
pub fn configuration_symbols(configuration: &crate::ConfigurationSentence) -> BTreeSet<SymbolId> {
    let mut requirements = BuiltinRequirements::default();
    requirements.fixed_cells(configuration.cells());
    for variable in configuration.variables() {
        requirements.sort(variable.sort());
    }
    requirements.initializer(configuration.initializer());
    requirements.declared
}

/// Every builtin sort `module` mentions, whether or not it uses one of its
/// operations.
#[must_use]
pub fn builtin_sorts(module: &DefinitionModule) -> BTreeSet<BuiltinSort> {
    let requirements = module_requirements(module, ImportPolicy::SourceText);
    requirements
        .sorts
        .union(&requirements.operations)
        .copied()
        .collect()
}

fn module_requirements(module: &DefinitionModule, policy: ImportPolicy) -> BuiltinRequirements {
    let mut requirements = BuiltinRequirements::default();
    for sentence in module.sentences() {
        match sentence {
            // Raw K text is opaque: it may use any operation of the builtin
            // sorts its package mentions, so those import their full modules.
            DefinitionSentence::Raw(raw) => {
                requirements.sorts.extend(&raw.builtin_sorts);
                requirements.operations.extend(&raw.builtin_sorts);
            }
            DefinitionSentence::SyntaxSort(_)
            | DefinitionSentence::Precedence(_)
            | DefinitionSentence::Associativity(_)
            | DefinitionSentence::Lexical(_)
            | DefinitionSentence::Layout(_) => {}
            DefinitionSentence::Subsort(sentence) => {
                requirements.declared_sort(sentence.subsort());
                requirements.declared_sort(sentence.supersort());
            }
            DefinitionSentence::Production(sentence) => {
                requirements.declared_sort(sentence.result_sort());
                for item in sentence.items() {
                    if let GrammarProductionItemKind::NonTerminal { sort, .. } = item.kind() {
                        requirements.declared_sort(sort);
                    }
                }
                for attribute in sentence.attributes() {
                    if let ProductionAttribute::Strictness { result_sort, .. } = attribute {
                        requirements.sort(result_sort.sort());
                    }
                }
            }
            DefinitionSentence::Configuration(configuration) => {
                if policy == ImportPolicy::NativeFrontend {
                    requirements.sorts.insert(BuiltinSort::Map);
                }
                requirements.fixed_cells(configuration.cells());
                for variable in configuration.variables() {
                    requirements.sort(variable.sort());
                }
                requirements.initializer(configuration.initializer());
            }
            DefinitionSentence::ContextAlias(sentence) => {
                for variable in sentence.variables() {
                    requirements.sort(variable.sort());
                }
                for cell in sentence.body().cells() {
                    requirements.term(cell.pattern());
                }
            }
            DefinitionSentence::Rule(sentence) => {
                let ml_before = requirements.ml;
                requirements.rule_reads(sentence);
                // A fresh binder of a builtin sort draws from K's own generator
                // (`freshInt`, `freshId`), declared in the sort's full module.
                for binder in sentence.fresh() {
                    if let DefinitionSortRef::Builtin(sort) = binder.sort() {
                        requirements.operations.insert(*sort);
                    }
                }
                // A transition's ensures condition is part of the main module's
                // rule; a claim's is imported here only for the native frontend.
                if (sentence.kind() != krs_ir::SentenceKind::Claim
                    || policy == ImportPolicy::NativeFrontend)
                    && let Some(condition) = sentence.ensures()
                {
                    requirements.condition(condition);
                }
                // A claim's predicate postcondition still makes the module
                // one with predicates (KF-039).
                if sentence
                    .ensures()
                    .is_some_and(|condition| condition.as_predicate().is_some())
                {
                    requirements.ml = true;
                }
                // The source printer moves a definition module's claims to
                // the generated spec module, which imports what their
                // predicates need itself.
                if sentence.kind() == krs_ir::SentenceKind::Claim
                    && policy == ImportPolicy::SourceText
                    && !module.is_spec()
                {
                    requirements.ml = ml_before;
                }
            }
        }
    }
    requirements
}

#[derive(Default)]
struct BuiltinRequirements {
    sorts: BTreeSet<BuiltinSort>,
    /// Builtin sorts in the signature of a used operation: the source printer
    /// imports their full module rather than their syntax module.
    operations: BTreeSet<BuiltinSort>,
    /// The catalog `k_module` of every used operation.
    modules: BTreeSet<&'static str>,
    /// Whether the module has a matching-logic predicate (KF-039).
    ml: bool,
    /// Every declared sort and production symbol a term names.
    declared: BTreeSet<SymbolId>,
    /// Whether a production or subsort declaration names `K`.
    declares_k: bool,
}

impl BuiltinRequirements {
    /// The modules of the sorts and operations required: a sort's full module where an
    /// operation over it is used, else its syntax module, and every used operation's module.
    fn term_imports(self) -> BTreeSet<&'static str> {
        // A module with matching-logic predicates imports K's ML-SYNTAX and,
        // when it uses maps, MAP-SYMBOLIC: the Haskell prover reasons about a
        // symbolic map only with its lemmas (KF-039).
        let map_symbolic = self.ml && self.sorts.contains(&BuiltinSort::Map);
        let mut imports = self
            .sorts
            .into_iter()
            .filter_map(|sort| {
                if self.operations.contains(&sort) {
                    sort.spec().k_module
                } else {
                    sort.spec().k_syntax_module
                }
            })
            .collect::<BTreeSet<_>>();
        imports.extend(self.modules);
        if self.ml {
            imports.insert(ML_SYNTAX_MODULE);
        }
        if map_symbolic {
            imports.insert(MAP_SYMBOLIC_MODULE);
        }
        imports
    }

    /// What a rule's variables, body and `requires` name.
    fn rule_reads(&mut self, sentence: &crate::RuleSentence) {
        for variable in sentence.variables() {
            self.sort(variable.sort());
        }
        match sentence.relational_body() {
            RuleBodyRef::Term(term) => {
                self.sort(term.sort());
                self.term(term.from());
                self.term(term.to());
            }
            RuleBodyRef::Configuration { body: rewrite, .. } => {
                for part in rewrite.parts() {
                    for term in part.terms() {
                        self.term(term);
                    }
                }
            }
            RuleBodyRef::Predicate(rewrite) => {
                self.predicate(rewrite.lhs());
                self.predicate(rewrite.rhs());
            }
        }
        if let Some(condition) = sentence.requires() {
            self.condition(condition);
        }
    }

    fn condition(&mut self, condition: &crate::DefinitionCondition) {
        match condition {
            crate::IrCondition::Bool(condition) => self.term(condition.term()),
            crate::IrCondition::Predicate(predicate) => self.predicate(predicate),
        }
    }

    fn predicate(&mut self, predicate: &crate::DefinitionMlPredicate) {
        self.ml = true;
        for term in predicate.terms() {
            self.term(term);
        }
        predicate.visit(&mut |node| match node.kind() {
            crate::IrMlKind::Equals { operand_sort, .. }
            | crate::IrMlKind::Ceil { operand_sort, .. } => self.sort(operand_sort),
            crate::IrMlKind::Exists { binder, .. } => self.sort(binder.sort()),
            _ => {}
        });
    }

    /// A sort in a production or subsort declaration.
    fn declared_sort(&mut self, sort: &DefinitionSortRef) {
        self.declares_k |= matches!(sort, DefinitionSortRef::Builtin(BuiltinSort::KSequence));
        self.sort(sort);
    }

    fn sort(&mut self, sort: &DefinitionSortRef) {
        match sort {
            DefinitionSortRef::Builtin(sort) => {
                self.sorts.insert(*sort);
            }
            DefinitionSortRef::Declared(id) => {
                self.declared.insert(id.clone());
            }
            DefinitionSortRef::Cell(_)
            | DefinitionSortRef::LeafCell(_)
            | DefinitionSortRef::CellCollection(_)
            | DefinitionSortRef::Parameter(_) => {}
        }
    }

    fn term(&mut self, term: &DefinitionTerm) {
        self.sort(term.sort());
        match term.kind() {
            DefinitionTermKind::Variable { .. } | DefinitionTermKind::Token { .. } => {}
            DefinitionTermKind::Application {
                application,
                arguments,
                instance,
                ..
            } => {
                // A head's strict casts name its instance (KF-027).
                for sort in instance {
                    self.sort(sort);
                }
                if let ApplicationRef::Declared(symbol) = application {
                    self.declared.insert(symbol.clone());
                }
                if let ApplicationRef::Builtin(operation) = application {
                    self.modules.insert(operation.spec().k_module);
                    self.operations.extend(
                        std::iter::once(operation.result_sort())
                            .chain(operation.argument_sorts().iter().copied())
                            .filter_map(OperationSort::builtin),
                    );
                }
                // K generates `isS` and `project:S` with the sort itself, so
                // only the sort's declaration must be visible.
                if let ApplicationRef::Generated(operation) = application {
                    self.sort(operation.sort());
                }
                for argument in arguments {
                    self.term(argument);
                }
            }
            DefinitionTermKind::KSequence { item_sort, items } => {
                self.sort(item_sort);
                for item in items {
                    self.term(item);
                }
            }
            DefinitionTermKind::Map(operands) => {
                self.sorts.insert(BuiltinSort::Map);
                self.modules.insert(operands.operation().spec().k_module);
                for operand in operands.operands() {
                    self.term(operand);
                }
            }
            DefinitionTermKind::List(operands) => {
                self.sorts.insert(BuiltinSort::List);
                self.modules.insert(operands.operation().spec().k_module);
                for operand in operands.operands() {
                    self.term(operand);
                }
            }
            DefinitionTermKind::Set(operands) => {
                self.sorts.insert(BuiltinSort::Set);
                self.modules.insert(operands.operation().spec().k_module);
                for operand in operands.operands() {
                    self.term(operand);
                }
            }
            DefinitionTermKind::Rewrite { from, to } => {
                self.term(from);
                self.term(to);
            }
            DefinitionTermKind::Cell { children, .. } => {
                for child in children {
                    self.term(child);
                }
            }
            DefinitionTermKind::As { pattern, .. } => self.term(pattern),
            DefinitionTermKind::Or { alternatives } => {
                for alternative in alternatives {
                    self.term(alternative);
                }
            }
            DefinitionTermKind::Matches {
                subject, pattern, ..
            } => {
                self.term(subject);
                self.term(pattern);
            }
            DefinitionTermKind::Let {
                pattern,
                value,
                body,
                ..
            } => {
                self.term(pattern);
                self.term(value);
                self.term(body);
            }
        }
    }

    fn fixed_cells(&mut self, cells: &[FixedCell<DefinitionSortRef, SymbolId>]) {
        for cell in cells {
            match cell.content() {
                // Element types are erased in K.
                FixedCellContent::Term { sort, .. } => self.sort(sort),
                FixedCellContent::Children { children } => self.fixed_cells(children),
            }
        }
    }

    fn initializer(&mut self, cells: &[FixedInitializerCell<SymbolId, DefinitionTerm>]) {
        for cell in cells {
            match cell.content() {
                FixedInitializerContent::Term { term } => self.term(term),
                FixedInitializerContent::Children { children } => self.initializer(children),
            }
        }
    }
}

/// The main cell of `configuration`: the computation cell a cell-free sentence (a term rule, a
/// context, a strict production's heating) is placed in, and the cell a run's program starts in.
///
/// It is the `KSequence` leaf whose initial value reads the main configuration variable, at any
/// depth (a computation cell inside a group or a collection instance); where no `KSequence` leaf
/// reads it, the configuration's one `KSequence` leaf. `None` where neither rule picks exactly one
/// cell: no `KSequence` leaf, two that read the program, or several of which none does.
///
/// A cell of another sort that reads the program (a map keyed by it) is no main cell: it holds a
/// value of its declared sort, not a computation. Both backends mark this cell and no other, and
/// a cell named `k`, which K takes as the computation cell by its name, must be this cell (the
/// configuration's lowering refuses another).
#[must_use]
pub fn main_cell<D, C, L>(
    configuration: &FixedConfiguration<IrSortRef<D, C>, C, IrTerm<L>>,
) -> krs_ir::MainCell<&FixedCell<IrSortRef<D, C>, C>>
where
    C: Clone + Ord,
    L: IrLevel,
{
    type Found<'a, D, C, L> = Vec<(&'a FixedCell<IrSortRef<D, C>, C>, Option<&'a IrTerm<L>>)>;
    fn computation_cells<'a, D, C: PartialEq, L: IrLevel>(
        cells: &'a [FixedCell<IrSortRef<D, C>, C>],
        values: &'a [FixedInitializerCell<C, IrTerm<L>>],
        found: &mut Found<'a, D, C, L>,
    ) {
        for cell in cells {
            let value = values.iter().find(|value| value.cell() == cell.id());
            match cell.content() {
                FixedCellContent::Term {
                    sort: IrSortRef::Builtin(BuiltinSort::KSequence),
                    ..
                } => found.push((
                    cell,
                    value.and_then(|value| match value.content() {
                        FixedInitializerContent::Term { term } => Some(term),
                        FixedInitializerContent::Children { .. } => None,
                    }),
                )),
                FixedCellContent::Term { .. } => {}
                FixedCellContent::Children { children } => {
                    let values = value.map_or(&[][..], |value| match value.content() {
                        FixedInitializerContent::Children { children } => children.as_slice(),
                        FixedInitializerContent::Term { .. } => &[],
                    });
                    computation_cells(children, values, found);
                }
            }
        }
    }
    fn reads<L: IrLevel>(term: &IrTerm<L>, variable: &krs_ir::SemanticId) -> bool {
        matches!(term.kind(), IrTermKind::Variable { variable: read } if read == variable)
            || term
                .children()
                .into_iter()
                .any(|child| reads(child, variable))
    }
    let mut found = Vec::new();
    computation_cells(
        configuration.cells(),
        configuration.initializer(),
        &mut found,
    );
    let main = configuration
        .variables()
        .iter()
        .find(|variable| variable.is_main());
    krs_ir::select_main_cell(found.into_iter().map(|(cell, term)| {
        let reads = main
            .zip(term)
            .is_some_and(|(variable, term)| reads(term, variable.id()));
        (cell, reads)
    }))
}

/// Whether a leaf cell's whole initial value `term`, in a cell of declared sort `cell_sort`, is
/// written cast to that sort, `( term ):Sort`.
///
/// K reads a leaf cell's sort from its initial content as it reads the configuration: the sort
/// of the production the content's head names. That is the cell's declared sort only where the
/// content has exactly that sort and its head gives one. A term of a strict subsort (`1` in a
/// `Value` cell) would declare a narrower cell, and a `let` block (`#let`), a `k::matches!` test
/// (`:=K`), a sort predicate (`isS`, generated after the configuration is read) and a parametric
/// production's application (whose result sort is one of its parameters) head no production that
/// gives one sort. There the cell's sort is stated by a cast, a sort annotation: the value is the
/// term's, which has the cell's sort or a subsort of it, as every initial value does.
#[must_use]
pub fn initial_value_needs_cell_sort(term: &DefinitionTerm, cell_sort: &DefinitionSortRef) -> bool {
    term.sort() != cell_sort
        || match term.kind() {
            DefinitionTermKind::Let { .. } | DefinitionTermKind::Matches { .. } => true,
            DefinitionTermKind::Application {
                application,
                instance,
                ..
            } => {
                !instance.is_empty()
                    || matches!(
                        application,
                        ApplicationRef::Generated(krs_ir::GeneratedOperation::SortPredicate(_))
                    )
            }
            _ => false,
        }
}

/// K's generated sort name of a collection cell's instances: the cell's sort name followed by
/// its collection type (`<acct multiplicity="*" type="Map">` has sort `AcctCellMap`).
#[must_use]
pub fn collection_sort_name(cell_name: &str, collection: krs_ir::CellCollectionType) -> String {
    format!("{}{}", cell_sort_name(cell_name), collection.as_str())
}

/// K's generated sort name of a cell: each hyphen-separated word of the cell
/// name capitalised and joined, followed by `Cell` (`<call-stack>` has sort
/// `CallStackCell`). It matches k-rust's `cell_sort_name` function.
#[must_use]
pub fn cell_sort_name(cell_name: &str) -> String {
    let mut output = String::new();
    let mut uppercase = true;
    for character in cell_name.chars() {
        if character == '-' {
            uppercase = true;
        } else if uppercase {
            output.extend(character.to_uppercase());
            uppercase = false;
        } else {
            output.push(character);
        }
    }
    output.push_str("Cell");
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ConfigurationSentence, ContextAliasSentence, DefinitionClaim, DefinitionModule,
        DefinitionRuleCondition, DefinitionTerm, DefinitionVariable, LabelId, LabelIdentity,
        ProductionGroupIdentity, ProductionItem, RuleSentence, SymbolKind, SyntaxSortSentence,
    };
    use krs_ir::testing::{item, origin};
    use krs_ir::{
        BuiltinOperation, BuiltinSort, CellContentFrame, ClaimModality, ConfigurationRoot,
        FixedCellPattern, FixedConfigurationPattern, FixedConfigurationVariable,
        FixedInitializerCell, ItemKind, ModuleId, ProductionAttribute, SemanticId, SentenceKind,
    };

    fn symbol_id(name: &str) -> SymbolId {
        SymbolId::new(name).expect("valid symbol ID")
    }

    fn semantic_id(name: &str) -> SemanticId {
        SemanticId::new(name).expect("valid semantic ID")
    }

    fn group_id() -> ProductionGroupId {
        ProductionGroupId::new("expression-group").expect("valid group ID")
    }

    fn int_sort() -> DefinitionSortRef {
        DefinitionSortRef::Builtin(BuiltinSort::Int)
    }

    fn configuration() -> ConfigurationSentence {
        let leaf = FixedCell::leaf(
            origin("leaf-cell"),
            symbol_id("leaf"),
            "value",
            Vec::new(),
            int_sort(),
        )
        .expect("valid leaf");
        let parent = FixedCell::nested(
            origin("parent-cell"),
            symbol_id("parent"),
            "state",
            Vec::new(),
            vec![leaf],
        )
        .expect("valid parent");
        let leaf_initializer = FixedInitializerCell::term(
            origin("leaf-initializer"),
            symbol_id("leaf"),
            DefinitionTerm::token(origin("initial-value"), int_sort(), "0")
                .expect("valid integer token"),
        );
        let parent_initializer = FixedInitializerCell::children(
            origin("parent-initializer"),
            symbol_id("parent"),
            vec![leaf_initializer],
        )
        .expect("valid parent initializer");
        ConfigurationSentence::new(
            origin("configuration"),
            semantic_id("configuration"),
            ConfigurationRoot::GeneratedTop,
            vec![parent],
            origin("initializer"),
            semantic_id("initializer"),
            Vec::new(),
            vec![parent_initializer],
        )
        .expect("valid configuration")
    }

    fn context_alias() -> ContextAliasSentence {
        let here = semantic_id("here");
        let body = FixedConfigurationPattern::new(
            origin("alias-body"),
            semantic_id("configuration"),
            vec![FixedCellPattern::new(
                origin("alias-cell"),
                symbol_id("leaf"),
                DefinitionTerm::variable(origin("alias-term"), int_sort(), here.clone()),
                CellContentFrame::Exact,
            )],
            Vec::new(),
        )
        .expect("valid alias body");
        ContextAliasSentence::new(
            origin("alias"),
            item("surface", "template", ItemKind::ContextAlias),
            origin("alias-name"),
            "eval_context".to_owned(),
            origin("alias-here"),
            here.clone(),
            vec![DefinitionVariable::new(here, int_sort())],
            body,
        )
    }

    fn definition() -> DefinitionIr {
        let sort = SyntaxSortSentence::new(
            origin("sort"),
            SymbolIdentity::new(symbol_id("sort"), "Expression", SymbolKind::Sort)
                .expect("valid sort symbol"),
        )
        .expect("valid syntax sort");
        let production = ProductionSentence::new(
            origin("production"),
            SymbolIdentity::new(symbol_id("production"), "literal", SymbolKind::Production)
                .expect("valid production symbol"),
            DefinitionSortRef::Declared(symbol_id("sort")),
            vec![ProductionItem::terminal(origin("terminal"), "literal").expect("valid terminal")],
            vec![ProductionAttribute::Group {
                origin: origin("group-attribute"),
                group: group_id(),
            }],
        )
        .expect("valid production");
        let module_id = ModuleId::new("SURFACE").expect("valid module ID");
        let module = DefinitionModule::new(
            origin("module"),
            module_id.clone(),
            Vec::new(),
            vec![
                ProductionGroupIdentity::new(origin("group"), group_id(), "expressions")
                    .expect("valid production group"),
            ],
            vec![
                DefinitionSentence::SyntaxSort(sort),
                DefinitionSentence::Production(production),
                DefinitionSentence::Configuration(configuration()),
                DefinitionSentence::ContextAlias(context_alias()),
            ],
        );
        DefinitionIr::new(module_id, vec![module]).expect("valid definition")
    }

    fn import_module(sentences: Vec<DefinitionSentence>) -> DefinitionModule {
        DefinitionModule::new(
            origin("imports-module"),
            ModuleId::new("IMPORTS").expect("valid module ID"),
            Vec::new(),
            Vec::new(),
            sentences,
        )
    }

    fn term_rule(term: DefinitionTerm, kind: SentenceKind) -> RuleSentence {
        let body = DefinitionTerm::rewrite(
            origin("imports-rewrite"),
            term.sort().clone(),
            term.clone(),
            term,
        )
        .expect("valid rewrite");
        RuleSentence::new(
            origin("imports-rule"),
            LabelIdentity::new(
                LabelId::new("imports-rule").expect("valid label ID"),
                "imports",
            )
            .expect("valid label"),
            kind,
            Vec::new(),
            body,
        )
        .expect("valid rule")
    }

    fn bool_operation() -> DefinitionTerm {
        DefinitionTerm::application(
            origin("bool-operation"),
            DefinitionSortRef::Builtin(BuiltinSort::Bool),
            ApplicationRef::Builtin(BuiltinOperation::BoolNot),
            vec![
                DefinitionTerm::token(
                    origin("bool-argument"),
                    DefinitionSortRef::Builtin(BuiltinSort::Bool),
                    "false",
                )
                .expect("valid Boolean token"),
            ],
        )
    }

    fn claim_with_ensures(term: DefinitionTerm) -> RuleSentence {
        term_rule(bool_operation(), SentenceKind::Claim)
            .with_claim(Some(DefinitionClaim::new(
                origin("claim-modality"),
                ClaimModality::AllPaths,
                None,
                Vec::new(),
            )))
            .with_ensures(Some(
                DefinitionRuleCondition::new(origin("ensures"), term).into(),
            ))
    }

    #[test]
    fn sentence_variables_name_rule_claim_and_alias_binders() {
        let variable = |key: &str, name: &str| {
            DefinitionTerm::variable(origin(key), int_sort(), semantic_id(name))
        };
        let sum = DefinitionTerm::application(
            origin("sum"),
            int_sort(),
            ApplicationRef::Builtin(BuiltinOperation::IntAdd),
            vec![variable("left", "old_value"), variable("right", "_once")],
        );
        let result = variable("result", "literal");
        let body = DefinitionTerm::rewrite(origin("sum-rewrite"), int_sort(), sum, result)
            .expect("valid rewrite");
        let binder = |name: &str| {
            crate::DefinitionScopedBinder::new(
                origin(&format!("{name}-binder")),
                origin(&format!("{name}-name")),
                semantic_id(name),
                origin(&format!("{name}-sort")),
                int_sort(),
            )
        };
        let claim = RuleSentence::new(
            origin("naming-claim"),
            LabelIdentity::new(
                LabelId::new("naming-claim").expect("valid label ID"),
                "naming",
            )
            .expect("valid label"),
            SentenceKind::Claim,
            Vec::new(),
            body,
        )
        .expect("valid claim")
        .with_claim(Some(DefinitionClaim::new(
            origin("naming-modality"),
            ClaimModality::AllPaths,
            None,
            vec![binder("old_value"), binder("_once")],
        )))
        .with_existentials(vec![binder("literal")]);
        let definition = definition();
        assert!(definition_terminals(&definition).contains("literal"));
        let naming = VariableNaming::new(&definition);
        let names = naming.rule(&claim);
        assert_eq!(
            names.iter().collect::<Vec<_>>(),
            vec![
                (&semantic_id("_once"), "_Once"),
                (&semantic_id("literal"), "?Literal"),
                (&semantic_id("old_value"), "OldValue"),
            ],
        );
        assert_eq!(naming.rule(&claim), names);
        let alias = naming.context_alias(&context_alias());
        assert_eq!(alias.name(&semantic_id("here")), Some("HERE"));
        assert_eq!(
            naming.configuration(&configuration()),
            SentenceVariables::default()
        );
    }

    #[test]
    fn import_policies_preserve_consumer_differences() {
        let syntax_only = term_rule(
            DefinitionTerm::token(origin("syntax-int"), int_sort(), "0")
                .expect("valid integer token"),
            SentenceKind::Equation,
        );
        let operation = term_rule(bool_operation(), SentenceKind::Equation);
        let ensures = DefinitionTerm::application(
            origin("ensures-application"),
            DefinitionSortRef::Builtin(BuiltinSort::Bool),
            ApplicationRef::Declared(symbol_id("predicate")),
            vec![
                DefinitionTerm::token(
                    origin("ensures-bytes"),
                    DefinitionSortRef::Builtin(BuiltinSort::Bytes),
                    "0x00",
                )
                .expect("valid bytes token"),
            ],
        );
        let module = import_module(vec![
            DefinitionSentence::Rule(syntax_only),
            DefinitionSentence::Rule(operation),
            DefinitionSentence::Configuration(configuration()),
            DefinitionSentence::Rule(claim_with_ensures(ensures)),
        ]);
        assert_eq!(
            builtin_imports(&module, ImportPolicy::SourceText),
            BTreeSet::from(["BOOL", "INT-SYNTAX"]),
        );
        // The native frontend selects the same modules for sorts, so an Int
        // token alone imports INT-SYNTAX on both routes; it differs only by
        // the configuration's Map and the claim's ensures terms.
        assert_eq!(
            builtin_imports(&module, ImportPolicy::NativeFrontend),
            BTreeSet::from(["BOOL", "BYTES", "INT-SYNTAX", "MAP"]),
        );
    }

    #[test]
    fn operations_import_their_module_on_both_routes() {
        let term = DefinitionTerm::application(
            origin("signature-only-operation"),
            DefinitionSortRef::Builtin(BuiltinSort::Bool),
            ApplicationRef::Builtin(BuiltinOperation::IntGreaterEqual),
            vec![
                DefinitionTerm::variable(
                    origin("signature-left"),
                    DefinitionSortRef::Declared(symbol_id("integer-subsort")),
                    semantic_id("left"),
                ),
                DefinitionTerm::variable(
                    origin("signature-right"),
                    DefinitionSortRef::Declared(symbol_id("integer-subsort")),
                    semantic_id("right"),
                ),
            ],
        );
        let module = import_module(vec![DefinitionSentence::Rule(term_rule(
            term,
            SentenceKind::Equation,
        ))]);
        // `>=Int` imports its catalog module INT on both routes, although no
        // Int-sorted term occurs.
        assert_eq!(
            builtin_imports(&module, ImportPolicy::SourceText),
            BTreeSet::from(["BOOL", "INT"]),
        );
        assert_eq!(
            builtin_imports(&module, ImportPolicy::NativeFrontend),
            BTreeSet::from(["BOOL", "INT"]),
        );
    }

    #[test]
    fn program_syntax_policy_imports_only_syntax_modules() {
        let subsort = |name: &str, sort: BuiltinSort| {
            DefinitionSentence::Subsort(crate::SubsortSentence::new(
                origin(name),
                DefinitionSortRef::Builtin(sort),
                DefinitionSortRef::Declared(symbol_id("sort")),
            ))
        };
        let module = import_module(vec![
            subsort("syntax-int", BuiltinSort::Int),
            subsort("syntax-bool", BuiltinSort::Bool),
            subsort("syntax-bytes", BuiltinSort::Bytes),
            subsort("syntax-map", BuiltinSort::Map),
        ]);
        assert_eq!(
            ImportPolicy::SourceText.for_module(&module),
            ImportPolicy::SourceText
        );
        let signed = module
            .clone()
            .into_program_syntax(krs_ir::IntLiterals::Signed);
        assert_eq!(
            ImportPolicy::NativeFrontend.for_module(&signed),
            ImportPolicy::ProgramSyntax
        );
        assert_eq!(
            builtin_imports(&signed, ImportPolicy::ProgramSyntax),
            BTreeSet::from(["BOOL-SYNTAX", "BYTES-SYNTAX", "INT-SYNTAX"]),
        );
        let unsigned = module.into_program_syntax(krs_ir::IntLiterals::Unsigned);
        assert_eq!(
            builtin_imports(&unsigned, ImportPolicy::ProgramSyntax),
            BTreeSet::from(["BOOL-SYNTAX", "BYTES-SYNTAX", "UNSIGNED-INT-SYNTAX"]),
        );
    }

    #[test]
    fn sorts_without_catalog_modules_do_not_add_imports() {
        let module = import_module(vec![DefinitionSentence::Rule(term_rule(
            DefinitionTerm::variable(
                origin("computation-variable"),
                DefinitionSortRef::Builtin(BuiltinSort::KSequence),
                semantic_id("computation"),
            ),
            SentenceKind::Equation,
        ))]);
        for policy in [ImportPolicy::SourceText, ImportPolicy::NativeFrontend] {
            assert!(builtin_imports(&module, policy).is_empty());
        }
    }

    #[test]
    fn a_declaration_over_k_imports_sort_k_on_every_route() {
        let module = import_module(vec![DefinitionSentence::Subsort(
            crate::SubsortSentence::new(
                origin("k-subsort"),
                DefinitionSortRef::Builtin(BuiltinSort::KSequence),
                DefinitionSortRef::Declared(symbol_id("sort")),
            ),
        )]);
        for policy in [ImportPolicy::SourceText, ImportPolicy::NativeFrontend] {
            assert_eq!(
                builtin_imports(&module, policy),
                BTreeSet::from([SORT_K_MODULE])
            );
        }
        let syntax = module.into_program_syntax(krs_ir::IntLiterals::Signed);
        assert_eq!(
            builtin_imports(&syntax, ImportPolicy::ProgramSyntax),
            BTreeSet::from([SORT_K_MODULE])
        );
    }

    #[test]
    fn indexes_declarations_and_authored_names() {
        let definition = definition();
        let index = DefinitionIndex::new(&definition);
        let sort = index.sort(&symbol_id("sort")).expect("indexed sort");
        assert_eq!(sort.kind(), SymbolKind::Sort);
        assert_eq!(sort.emitted_name(), "Expression");
        assert_eq!(index.sort_name(&symbol_id("sort")), Some("Expression"));
        assert_eq!(index.symbol_name(&symbol_id("sort")), Some("Expression"));
        let production = index
            .production(&symbol_id("production"))
            .expect("indexed production");
        assert_eq!(production.symbol().emitted_name(), "literal");
        assert_eq!(
            production.result_sort(),
            &DefinitionSortRef::Declared(symbol_id("sort"))
        );
        assert_eq!(index.symbol_name(&symbol_id("production")), Some("literal"));
        assert_eq!(index.group_name(&group_id()), Some("expressions"));
        assert_eq!(index.cell_name(&symbol_id("parent")), Some("state"));
        assert_eq!(index.cell_name(&symbol_id("leaf")), Some("value"));
        assert_eq!(
            index.context_alias_name(&item("surface", "template", ItemKind::ContextAlias)),
            Some("eval_context")
        );
    }

    #[test]
    fn absent_and_wrong_role_lookups_return_none() {
        let definition = definition();
        let index = DefinitionIndex::new(&definition);
        let missing = symbol_id("missing");
        assert!(index.sort(&missing).is_none());
        assert!(index.sort_name(&missing).is_none());
        assert!(index.production(&missing).is_none());
        assert!(index.symbol_name(&missing).is_none());
        assert!(index.cell_name(&missing).is_none());
        assert!(
            index
                .group_name(&ProductionGroupId::new("missing").expect("valid group ID"))
                .is_none()
        );
        assert!(
            index
                .context_alias_name(&item("surface", "missing", ItemKind::ContextAlias))
                .is_none()
        );
        assert!(index.sort(&symbol_id("production")).is_none());
        assert!(index.production(&symbol_id("sort")).is_none());
        assert!(index.symbol_name(&symbol_id("leaf")).is_none());
    }

    /// One cell of a [`main_cell`] fixture and its initial value: a `KSequence` leaf holds the
    /// program or nothing, a leaf of another sort the program or 0, a group its children.
    enum Shape {
        Computation {
            reads: bool,
        },
        Leaf {
            sort: DefinitionSortRef,
            reads: bool,
        },
        Group(Vec<(&'static str, Shape)>),
    }

    fn shaped(
        name: &str,
        shape: Shape,
    ) -> (
        FixedCell<DefinitionSortRef, SymbolId>,
        FixedInitializerCell<SymbolId, DefinitionTerm>,
    ) {
        let id = symbol_id(&format!("cell.{name}"));
        let program = |sort: DefinitionSortRef| {
            DefinitionTerm::variable(origin(&format!("{name}.pgm")), sort, semantic_id("pgm"))
        };
        match shape {
            Shape::Computation { reads } => {
                let items = if reads {
                    vec![program(int_sort())]
                } else {
                    Vec::new()
                };
                (
                    FixedCell::leaf(
                        origin(name),
                        id.clone(),
                        name,
                        Vec::new(),
                        DefinitionSortRef::k_sequence(),
                    )
                    .unwrap(),
                    FixedInitializerCell::term(
                        origin(&format!("{name}.init")),
                        id,
                        DefinitionTerm::k_sequence(
                            origin(&format!("{name}.seq")),
                            int_sort(),
                            items,
                        ),
                    ),
                )
            }
            Shape::Leaf { sort, reads } => {
                let value = if reads {
                    program(sort.clone())
                } else {
                    DefinitionTerm::token(origin(&format!("{name}.zero")), int_sort(), "0").unwrap()
                };
                (
                    FixedCell::leaf(origin(name), id.clone(), name, Vec::new(), sort).unwrap(),
                    FixedInitializerCell::term(origin(&format!("{name}.init")), id, value),
                )
            }
            Shape::Group(children) => {
                let (cells, values): (Vec<_>, Vec<_>) = children
                    .into_iter()
                    .map(|(child, shape)| shaped(child, shape))
                    .unzip();
                (
                    FixedCell::nested(origin(name), id.clone(), name, Vec::new(), cells).unwrap(),
                    FixedInitializerCell::children(origin(&format!("{name}.init")), id, values)
                        .unwrap(),
                )
            }
        }
    }

    /// The name of the main cell of a configuration of `cells` whose main variable is `pgm`.
    fn main_cell_of(cells: Vec<(&'static str, Shape)>) -> Option<String> {
        let (cells, initializer): (Vec<_>, Vec<_>) = cells
            .into_iter()
            .map(|(name, shape)| shaped(name, shape))
            .unzip();
        let configuration = ConfigurationSentence::new(
            origin("configuration"),
            semantic_id("configuration"),
            ConfigurationRoot::GeneratedTop,
            cells,
            origin("initializer"),
            semantic_id("initializer"),
            vec![
                FixedConfigurationVariable::new(
                    origin("pgm"),
                    semantic_id("pgm"),
                    "PGM",
                    int_sort(),
                    true,
                )
                .unwrap(),
            ],
            initializer,
        )
        .unwrap();
        main_cell(&configuration)
            .cell()
            .map(|cell| cell.name().to_owned())
    }

    /// The main cell is the computation cell that reads the program, whatever its name and
    /// depth; failing that, the one computation cell; and no cell where neither is unique. A
    /// map that reads the program is no computation cell.
    #[test]
    fn the_main_cell_is_the_computation_cell_that_reads_the_program() {
        use Shape::{Computation, Group, Leaf};
        let map = || DefinitionSortRef::Builtin(BuiltinSort::Map);
        assert_eq!(
            main_cell_of(vec![
                ("prog", Computation { reads: true }),
                (
                    "n",
                    Leaf {
                        sort: int_sort(),
                        reads: false
                    }
                ),
            ])
            .as_deref(),
            Some("prog")
        );
        assert_eq!(
            main_cell_of(vec![
                ("k", Computation { reads: false }),
                ("prog", Computation { reads: true }),
            ])
            .as_deref(),
            Some("prog")
        );
        assert_eq!(
            main_cell_of(vec![
                ("prog", Computation { reads: false }),
                ("frame", Group(vec![("code", Computation { reads: true })])),
            ])
            .as_deref(),
            Some("code")
        );
        assert_eq!(
            main_cell_of(vec![
                ("k", Computation { reads: false }),
                (
                    "env",
                    Leaf {
                        sort: map(),
                        reads: true
                    }
                ),
            ])
            .as_deref(),
            Some("k")
        );
        assert_eq!(
            main_cell_of(vec![
                ("k", Computation { reads: false }),
                ("slot", Computation { reads: false }),
                (
                    "pgm",
                    Leaf {
                        sort: int_sort(),
                        reads: true
                    }
                ),
            ]),
            None
        );
        assert_eq!(
            main_cell_of(vec![
                ("a", Computation { reads: true }),
                ("b", Computation { reads: true }),
            ]),
            None
        );
        assert_eq!(
            main_cell_of(vec![(
                "n",
                Leaf {
                    sort: int_sort(),
                    reads: true
                }
            )]),
            None
        );
    }

    /// An entry steps one instance when it matches exactly one, keeps it and frames the others;
    /// the instance is then one item of its layout, beside the other cells of an open Map or Set
    /// entry and inside the parent cell, after the variable naming the other instances, as a List
    /// entry's back instance. An entry that creates or removes its instance, names two, or names
    /// every instance steps none.
    #[test]
    fn an_entry_that_steps_one_instance_writes_it_as_one_item() {
        let cell = || symbol_id("cell.core");
        let child = || {
            krs_ir::FixedCellClause::new(
                origin("core.k"),
                symbol_id("cell.k"),
                DefinitionTerm::token(origin("core.k.term"), int_sort(), "0").unwrap(),
                krs_ir::CellPost::Preserve,
                CellContentFrame::Exact,
            )
        };
        let kept = || krs_ir::InstanceClause::Kept {
            origin: origin("core"),
            label: Some("me".into()),
            children: vec![child()],
            open: true,
        };
        let entry = |ordering, front, back, open| {
            krs_ir::InstancesClause::new(origin("cores"), cell(), ordering, front, back, open)
        };
        let shape = |clause: &krs_ir::InstancesClause<SymbolId, DefinitionTerm>| {
            stepped_instance_layout(clause).map(|layout| {
                (
                    layout.children.len(),
                    layout.open,
                    layout.in_parent,
                    layout.position,
                )
            })
        };
        let unordered = krs_ir::InstanceOrdering::Unordered;
        let list = krs_ir::InstanceOrdering::List;
        assert_eq!(
            shape(&entry(unordered, vec![kept()], Vec::new(), true)),
            Some((1, true, false, 0))
        );
        assert_eq!(
            shape(&entry(list, Vec::new(), vec![kept()], true)),
            Some((1, true, true, 1))
        );
        assert_eq!(
            shape(&entry(unordered, vec![kept()], Vec::new(), false)),
            None
        );
        assert_eq!(
            shape(&entry(unordered, vec![kept(), kept()], Vec::new(), true)),
            None
        );
        let created = krs_ir::InstanceClause::Created {
            origin: origin("new"),
            children: Vec::new(),
            defaults: true,
        };
        assert_eq!(
            shape(&entry(unordered, vec![created], Vec::new(), true)),
            None
        );
    }
}
