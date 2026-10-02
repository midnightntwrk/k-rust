//! K-surface facts shared by the `.k` printer and the k-rust adapter.
//! Each backend must retain its own printing.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    ApplicationRef, BuiltinSort, CellPost, DefinitionIr, DefinitionModule, DefinitionRuleBody,
    DefinitionSentence, DefinitionSortRef, DefinitionTerm, DefinitionTermKind, FixedCell,
    FixedCellContent, FixedInitializerCell, FixedInitializerContent, GrammarProductionItemKind,
    ProductionAttribute, ProductionGroupId, ProductionSentence, SemanticId, StableItemId, SymbolId,
    SymbolIdentity,
};

/// Borrowed declarations and names from one Definition IR.
#[derive(Default)]
pub struct DefinitionIndex<'a> {
    sorts: BTreeMap<SymbolId, &'a SymbolIdentity>,
    productions: BTreeMap<SymbolId, &'a ProductionSentence>,
    symbols: BTreeMap<SymbolId, &'a str>,
    groups: BTreeMap<ProductionGroupId, &'a str>,
    cells: BTreeMap<SymbolId, &'a str>,
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
                    | DefinitionSentence::Rule(_) => {}
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

    /// Returns a context alias's authored name without backend escaping.
    #[must_use]
    pub fn context_alias_name(&self, id: &StableItemId) -> Option<&'a str> {
        self.context_aliases.get(id).copied()
    }

    fn collect_cells(&mut self, cells: &'a [FixedCell<DefinitionSortRef, SymbolId>]) {
        for cell in cells {
            self.cells.insert(cell.id().clone(), cell.name());
            if let FixedCellContent::Children { children } = cell.content() {
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
    /// Operation signature sorts must only upgrade already required sorts; they must not add imports by themselves.
    /// Configurations must not imply a Map import, and claim `ensures` terms must not contribute requirements.
    SourceText,
    /// Imports for the native frontend.
    /// Each required sort must select its full module, including sorts required only by a builtin operation's signature.
    /// Every configuration must require Map because frontend expansion lowers external variables through `Map:lookup`.
    /// Claim `ensures` terms must contribute requirements.
    NativeFrontend,
}

/// Returns a module's builtin imports under the selected consumer policy.
/// Both policies must inspect subsorts, production signatures and strictness result sorts, configuration cell sorts, variables and initializers, context alias variables and cell patterns, and rule variables, bodies and `requires` terms.
/// Term traversal must include annotations, K-sequence item sorts, collection sorts and all children.
/// Claim binder declarations must not contribute requirements independently of rule variables and terms.
/// Sorts whose selected catalog module is absent must not produce imports.
#[must_use]
pub fn builtin_imports(module: &DefinitionModule, policy: ImportPolicy) -> BTreeSet<&'static str> {
    let mut requirements = BuiltinRequirements::default();
    for sentence in module.sentences() {
        match sentence {
            DefinitionSentence::SyntaxSort(_)
            | DefinitionSentence::Precedence(_)
            | DefinitionSentence::Associativity(_) => {}
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
                for variable in sentence.variables() {
                    requirements.sort(variable.sort());
                }
                match sentence.relational_body() {
                    DefinitionRuleBody::Term(term) => requirements.term(term),
                    DefinitionRuleBody::Configuration(rewrite) => {
                        for clause in rewrite.clauses() {
                            requirements.term(clause.before());
                            if let CellPost::Replace { term } = clause.after() {
                                requirements.term(term);
                            }
                        }
                    }
                }
                if let Some(condition) = sentence.requires() {
                    requirements.term(condition.term());
                }
                if policy == ImportPolicy::NativeFrontend
                    && let Some(condition) = sentence.claim().and_then(|claim| claim.ensures())
                {
                    requirements.term(condition.term());
                }
            }
        }
    }
    if policy == ImportPolicy::NativeFrontend {
        requirements.sorts.extend(&requirements.operations);
    }
    requirements
        .sorts
        .into_iter()
        .filter_map(|sort| {
            if policy == ImportPolicy::NativeFrontend || requirements.operations.contains(&sort) {
                sort.spec().k_module
            } else {
                sort.spec().k_syntax_module
            }
        })
        .collect()
}

#[derive(Default)]
struct BuiltinRequirements {
    sorts: BTreeSet<BuiltinSort>,
    operations: BTreeSet<BuiltinSort>,
}

impl BuiltinRequirements {
    fn sort(&mut self, sort: &DefinitionSortRef) {
        if let DefinitionSortRef::Builtin(sort) = sort {
            self.sorts.insert(*sort);
        }
    }

    fn term(&mut self, term: &DefinitionTerm) {
        self.sort(term.sort());
        match term.kind() {
            DefinitionTermKind::Variable { .. } | DefinitionTermKind::Token { .. } => {}
            DefinitionTermKind::Application {
                application,
                arguments,
            } => {
                if let ApplicationRef::Builtin(operation) = application {
                    self.operations.insert(operation.result_sort());
                    for sort in operation.argument_sorts() {
                        self.operations.insert(*sort);
                    }
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
            DefinitionTermKind::Map { arguments, .. } => {
                self.sorts.insert(BuiltinSort::Map);
                for argument in arguments {
                    self.term(argument);
                }
            }
            DefinitionTermKind::List { arguments, .. } => {
                self.sorts.insert(BuiltinSort::List);
                for argument in arguments {
                    self.term(argument);
                }
            }
            DefinitionTermKind::Set { arguments, .. } => {
                self.sorts.insert(BuiltinSort::Set);
                for argument in arguments {
                    self.term(argument);
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

/// Returns `V` followed by the identity's UTF-8 bytes in uppercase hexadecimal.
///
/// # Panics
///
/// Panics if writing to a `String` fails.
#[must_use]
pub fn variable_name(variable: &SemanticId) -> String {
    use std::fmt::Write as _;

    let mut output = String::from("V");
    for byte in variable.as_str().as_bytes() {
        write!(output, "{byte:02X}").expect("writing to String cannot fail");
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testing::{item, origin};
    use crate::{
        BuiltinOperation, BuiltinSort, CellContentFrame, ClaimModality, ConfigurationRoot,
        ConfigurationSentence, ContextAliasSentence, DefinitionClaim, DefinitionModule,
        DefinitionRuleCondition, DefinitionTerm, DefinitionVariable, FixedCellPattern,
        FixedConfigurationPattern, FixedInitializerCell, ItemKind, LabelId, LabelIdentity,
        ModuleId, ProductionAttribute, ProductionGroupIdentity, ProductionItem, RuleSentence,
        SentenceKind, SymbolKind, SyntaxSortSentence,
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
        term_rule(bool_operation(), SentenceKind::Claim).with_claim(Some(DefinitionClaim::new(
            origin("claim-modality"),
            ClaimModality::AllPaths,
            None,
            Vec::new(),
            Vec::new(),
            Some(DefinitionRuleCondition::new(origin("ensures"), term)),
        )))
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
    fn operation_signatures_only_add_requirements_for_native_frontend() {
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
        assert_eq!(
            builtin_imports(&module, ImportPolicy::SourceText),
            BTreeSet::from(["BOOL"]),
        );
        assert_eq!(
            builtin_imports(&module, ImportPolicy::NativeFrontend),
            BTreeSet::from(["BOOL", "INT"]),
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

    #[test]
    fn variable_names_encode_every_utf8_byte() {
        for (identity, expected) in [
            ("X", "V58"),
            ("a_b9", "V615F6239"),
            ("éλ", "VC3A9CEBB"),
            ("__krs_wildcard_0", "V5F5F6B72735F77696C64636172645F30"),
            ("_X__krs_2", "V5F585F5F6B72735F32"),
        ] {
            assert_eq!(variable_name(&semantic_id(identity)), expected);
        }
    }
}
