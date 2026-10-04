use krs_ir::{
    ApplicationRef, ConfigurationRoot, FixedCell, FixedConfiguration, FixedConfigurationVariable,
    FixedInitializerCell, ModuleId, NodeOrigin, SemanticId, SentenceKind,
};
use krs_ir_levels::{
    DefinitionIr, DefinitionModule, DefinitionSentence, DefinitionSortRef, DefinitionTerm, LabelId,
    LabelIdentity, ProductionItem as IrProductionItem, ProductionSentence, RuleSentence,
    SubsortSentence, SymbolId, SymbolIdentity, SymbolKind, SyntaxSortSentence,
};

pub(crate) const MODULE: &str = "KRS-ADAPTER-TEST";

pub(crate) fn smoke_definition() -> DefinitionIr {
    smoke_definition_with_cell(SentenceKind::Transition, "k")
}

#[allow(clippy::too_many_lines)]
pub(crate) fn smoke_definition_with_cell(rule_kind: SentenceKind, cell_name: &str) -> DefinitionIr {
    let k_item = SymbolId::new("sort.kitem").unwrap();
    let k_result = SymbolId::new("sort.kresult").unwrap();
    let value = SymbolId::new("sort.value").unwrap();
    let foo = SymbolId::new("production.foo").unwrap();
    let bar = SymbolId::new("production.bar").unwrap();
    let syntax_id = ModuleId::new("SMOKE-SYNTAX").unwrap();
    let main_id = ModuleId::new("SMOKE").unwrap();
    let syntax = DefinitionModule::new(
        node("def.module.syntax"),
        syntax_id.clone(),
        Vec::new(),
        Vec::new(),
        vec![
            DefinitionSentence::Production(
                ProductionSentence::new(
                    node("def.production.bar"),
                    symbol("production.bar", "Lblbar", SymbolKind::Production),
                    DefinitionSortRef::declared(value.clone()),
                    vec![
                        IrProductionItem::terminal(node("def.production.bar.item"), "bar").unwrap(),
                    ],
                    Vec::new(),
                )
                .unwrap(),
            ),
            DefinitionSentence::Production(
                ProductionSentence::new(
                    node("def.production.foo"),
                    symbol("production.foo", "Lblfoo", SymbolKind::Production),
                    DefinitionSortRef::declared(value.clone()),
                    vec![
                        IrProductionItem::terminal(node("def.production.foo.item"), "foo").unwrap(),
                    ],
                    Vec::new(),
                )
                .unwrap(),
            ),
            DefinitionSentence::SyntaxSort(
                SyntaxSortSentence::new(
                    node("def.sort.kitem"),
                    symbol("sort.kitem", "KItem", SymbolKind::Sort),
                )
                .unwrap(),
            ),
            DefinitionSentence::SyntaxSort(
                SyntaxSortSentence::new(
                    node("def.sort.kresult"),
                    symbol("sort.kresult", "KResult", SymbolKind::Sort),
                )
                .unwrap(),
            ),
            DefinitionSentence::SyntaxSort(
                SyntaxSortSentence::new(
                    node("def.sort.value"),
                    symbol("sort.value", "Value", SymbolKind::Sort),
                )
                .unwrap(),
            ),
            DefinitionSentence::Subsort(SubsortSentence::new(
                node("def.subsort.kresult-kitem"),
                DefinitionSortRef::declared(k_result.clone()),
                DefinitionSortRef::declared(k_item.clone()),
            )),
            DefinitionSentence::Subsort(SubsortSentence::new(
                node("def.subsort.value-kresult"),
                DefinitionSortRef::declared(value.clone()),
                DefinitionSortRef::declared(k_result),
            )),
        ],
    );
    let configuration = {
        let cell = SymbolId::new("cell.k").unwrap();
        let program = semantic_id("program");
        let initializer_body = DefinitionTerm::k_sequence(
            node("def.term.init.sequence"),
            DefinitionSortRef::declared(k_item.clone()),
            vec![DefinitionTerm::variable(
                node("def.term.init.program"),
                DefinitionSortRef::declared(value.clone()),
                program.clone(),
            )],
        );
        DefinitionSentence::Configuration(
            FixedConfiguration::new(
                node("def.configuration"),
                semantic_id("configuration.machine"),
                ConfigurationRoot::GeneratedTop,
                vec![
                    FixedCell::leaf(
                        node("def.cell.k"),
                        cell.clone(),
                        cell_name,
                        Vec::new(),
                        DefinitionSortRef::k_sequence(),
                    )
                    .unwrap(),
                ],
                node("def.initializer"),
                semantic_id("initializer.machine"),
                vec![
                    FixedConfigurationVariable::new(
                        node("def.initializer.program"),
                        program,
                        "PGM",
                        DefinitionSortRef::declared(value.clone()),
                        true,
                    )
                    .unwrap(),
                ],
                vec![FixedInitializerCell::term(
                    node("def.initializer.cell"),
                    cell,
                    initializer_body,
                )],
            )
            .unwrap(),
        )
    };
    let rewrite = DefinitionTerm::rewrite(
        node("def.term.rule.rewrite"),
        DefinitionSortRef::declared(value.clone()),
        DefinitionTerm::application(
            node("def.term.rule.foo"),
            DefinitionSortRef::declared(value.clone()),
            ApplicationRef::Declared(foo),
            Vec::new(),
        ),
        DefinitionTerm::application(
            node("def.term.rule.bar"),
            DefinitionSortRef::declared(value.clone()),
            ApplicationRef::Declared(bar),
            Vec::new(),
        ),
    )
    .unwrap();
    let rule = DefinitionSentence::Rule(
        RuleSentence::new(
            node("def.rule.foo-to-bar"),
            LabelIdentity::new(
                LabelId::new("rule.foo-to-bar").unwrap(),
                "ORG-EXAMPLE-SMOKE.rules.foo-to-bar",
            )
            .unwrap(),
            rule_kind,
            Vec::new(),
            rewrite,
        )
        .unwrap(),
    );
    let main = DefinitionModule::new(
        node("def.module.main"),
        main_id.clone(),
        vec![syntax_id],
        Vec::new(),
        vec![configuration, rule],
    );
    DefinitionIr::new(main_id, vec![main, syntax]).unwrap()
}

pub(crate) fn symbol(id: &str, emitted_name: &str, kind: SymbolKind) -> SymbolIdentity {
    SymbolIdentity::new(SymbolId::new(id).unwrap(), emitted_name, kind).unwrap()
}

pub(crate) fn node(key: &str) -> NodeOrigin {
    krs_ir::testing::origin(key)
}

pub(crate) fn semantic_id(value: &str) -> SemanticId {
    SemanticId::new(value).unwrap()
}
