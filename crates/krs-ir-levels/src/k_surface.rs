//! K-surface facts shared by the `.k` printer and the k-rust adapter.
//! Each backend must retain its own printing.

use std::collections::{BTreeMap, BTreeSet};

mod variable_names;

pub use variable_names::{
    SentenceVariables, VariableNaming, definition_terminals, generated_variable_name,
};

use crate::{
    DefinitionIr, DefinitionModule, DefinitionSentence, DefinitionSortRef, DefinitionTerm,
    DefinitionTermKind, ProductionSentence, RuleBodyRef, SymbolId, SymbolIdentity,
};
use krs_ir::{
    ApplicationRef, BuiltinSort, FixedCell, FixedCellContent, FixedInitializerCell,
    FixedInitializerContent, GrammarProductionItemKind, OperationSort, ProductionAttribute,
    ProductionGroupId, StableItemId,
};

/// Borrowed declarations and names from one Definition IR.
#[derive(Default)]
pub struct DefinitionIndex<'a> {
    sorts: BTreeMap<SymbolId, &'a SymbolIdentity>,
    productions: BTreeMap<SymbolId, &'a ProductionSentence>,
    symbols: BTreeMap<SymbolId, &'a str>,
    groups: BTreeMap<ProductionGroupId, &'a str>,
    cells: BTreeMap<SymbolId, &'a str>,
    cell_parents: BTreeMap<SymbolId, SymbolId>,
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
                        index.collect_cells(configuration.cells());
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

    /// Returns K's generated sort name of a fixed cell, such as `FrameCell`
    /// for `<frame>` (see [`cell_sort_name`]).
    #[must_use]
    pub fn cell_sort_name(&self, id: &SymbolId) -> Option<String> {
        self.cell_name(id).map(cell_sort_name)
    }

    /// Returns a context alias's authored name without backend escaping.
    #[must_use]
    pub fn context_alias_name(&self, id: &StableItemId) -> Option<&'a str> {
        self.context_aliases.get(id).copied()
    }

    fn collect_cells(&mut self, cells: &'a [FixedCell<DefinitionSortRef, SymbolId>]) {
        for cell in cells {
            self.cells.insert(cell.id().clone(), cell.name());
            if let FixedCellContent::Children { children } = cell.content() {
                for child in children {
                    self.cell_parents
                        .insert(child.id().clone(), cell.id().clone());
                }
                self.collect_cells(children);
            }
        }
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
    /// Each required sort must select its full module, including sorts required only by a builtin operation's signature.
    /// Every configuration must require Map because frontend expansion lowers external variables through `Map:lookup`.
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
    let mut requirements = module_requirements(module, policy);
    if policy == ImportPolicy::NativeFrontend {
        requirements.sorts.extend(&requirements.operations);
    }
    if policy == ImportPolicy::ProgramSyntax {
        let int_literals = module.int_literals();
        return requirements
            .sorts
            .into_iter()
            .filter_map(|sort| int_literals.program_syntax_module(sort))
            .collect();
    }
    // A module with matching-logic predicates imports K's ML-SYNTAX and,
    // when it uses maps, MAP-SYMBOLIC: the Haskell prover reasons about a
    // symbolic map only with its lemmas (KF-039).
    let map_symbolic = requirements.ml && requirements.sorts.contains(&BuiltinSort::Map);
    let mut imports = requirements
        .sorts
        .into_iter()
        .filter_map(|sort| {
            if policy == ImportPolicy::NativeFrontend || requirements.operations.contains(&sort) {
                sort.spec().k_module
            } else {
                sort.spec().k_syntax_module
            }
        })
        .collect::<BTreeSet<_>>();
    imports.extend(requirements.modules);
    if requirements.ml {
        imports.insert(ML_SYNTAX_MODULE);
    }
    if map_symbolic {
        imports.insert(MAP_SYMBOLIC_MODULE);
    }
    imports
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
                requirements.sort(sentence.subsort());
                requirements.sort(sentence.supersort());
            }
            DefinitionSentence::Production(sentence) => {
                requirements.sort(sentence.result_sort());
                for item in sentence.items() {
                    if let GrammarProductionItemKind::NonTerminal { sort, .. } = item.kind() {
                        requirements.sort(sort);
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
                for variable in sentence.variables() {
                    requirements.sort(variable.sort());
                }
                match sentence.relational_body() {
                    RuleBodyRef::Term(term) => {
                        requirements.sort(term.sort());
                        requirements.term(term.from());
                        requirements.term(term.to());
                    }
                    RuleBodyRef::Configuration { body: rewrite, .. } => {
                        for part in rewrite.parts() {
                            for term in part.terms() {
                                requirements.term(term);
                            }
                        }
                    }
                    RuleBodyRef::Predicate(rewrite) => {
                        requirements.predicate(rewrite.lhs());
                        requirements.predicate(rewrite.rhs());
                    }
                }
                if let Some(condition) = sentence.requires() {
                    requirements.condition(condition);
                }
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
}

impl BuiltinRequirements {
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

    fn sort(&mut self, sort: &DefinitionSortRef) {
        match sort {
            DefinitionSortRef::Builtin(sort) => {
                self.sorts.insert(*sort);
            }
            DefinitionSortRef::Declared(id) => {
                self.declared.insert(id.clone());
            }
            DefinitionSortRef::Cell(_) | DefinitionSortRef::Parameter(_) => {}
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
                FixedCellContent::Term { sort } => self.sort(sort),
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
        FixedCellPattern, FixedConfigurationPattern, FixedInitializerCell, ItemKind, ModuleId,
        ProductionAttribute, SemanticId, SentenceKind,
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
        assert_eq!(
            builtin_imports(&module, ImportPolicy::NativeFrontend),
            BTreeSet::from(["BOOL", "BYTES", "INT", "MAP"]),
        );
    }

    #[test]
    fn operations_import_their_module_and_signatures_upgrade_only_for_native_frontend() {
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
}
