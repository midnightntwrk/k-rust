//! K-surface naming shared by the `.k` printer and the k-rust adapter.
//! Each backend must retain its own printing.

use std::collections::BTreeMap;

use crate::{
    DefinitionIr, DefinitionSentence, DefinitionSortRef, FixedCell, FixedCellContent,
    ProductionGroupId, ProductionSentence, SemanticId, StableItemId, SymbolId, SymbolIdentity,
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
        BuiltinSort, CellContentFrame, ConfigurationRoot, ConfigurationSentence,
        ContextAliasSentence, DefinitionModule, DefinitionTerm, DefinitionVariable,
        FixedCellPattern, FixedConfigurationPattern, FixedInitializerCell, ItemKind, ModuleId,
        ProductionAttribute, ProductionGroupIdentity, ProductionItem, SymbolKind,
        SyntaxSortSentence,
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
