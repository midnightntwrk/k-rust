//! Every sort but `K` is a `KItem` in both validators' sort graphs, whether or
//! not a subsort sentence says so: a `KItem` rewrite may have endpoints of an
//! undeclared sort, and a `KItem` field holds a term of one, while a `K`
//! sequence is still no `KItem`.

use krs_ir::testing::{self, item, origin as node};
use krs_ir::{
    ApplicationRef, ConfigurationRoot, FixedCell, FixedConfiguration, FixedInitializerCell,
    ItemKind, ModuleId, ProductionFieldId, SemanticId, SentenceKind, StableItemId,
};
use krs_ir_levels::{
    DefinitionIr, DefinitionModule, DefinitionSentence, DefinitionSortRef, DefinitionTerm,
    DefinitionValidationError, DefinitionVariable, LabelId, LabelIdentity, ProductionItem,
    ProductionSentence, RuleSentence, SemanticModule, SemanticProduction, SemanticProductionItem,
    SemanticRule, SemanticSort, SemanticSortRef, SemanticTerm, SemanticTheory,
    SemanticValidationError, SemanticVariable, SymbolId, SymbolIdentity, SymbolKind,
    SyntaxSortSentence,
};

fn framework_k_item() -> StableItemId {
    testing::item_in(
        testing::package_with("KRS-FRAMEWORK", "krs", "0.1.0", "framework"),
        "syntax",
        "KItem",
        ItemKind::Sort,
    )
}

/// `hold(KItem) : Frame`, `skip : Stmt`, and the `KItem` rule
/// `hold(S) => S` with `S` of `variable_sort`; neither `Stmt` nor `Frame` is
/// declared below `KItem`.
#[expect(
    clippy::too_many_lines,
    reason = "One hand-built theory: sorts, productions, configuration, and the rule."
)]
fn semantic_theory(
    variable_sort: &SemanticSortRef,
) -> Result<SemanticTheory, SemanticValidationError> {
    let k_item = SemanticSortRef::declared(framework_k_item());
    let stmt = item("syntax", "Stmt", ItemKind::Sort);
    let frame = item("syntax", "Frame", ItemKind::Sort);
    let hold = item("syntax", "Hold", ItemKind::Constructor);
    let skip = item("syntax", "Skip", ItemKind::Constructor);
    let productions = vec![
        SemanticProduction::new(
            node("sem.production.hold"),
            hold.clone(),
            SemanticSortRef::declared(frame.clone()),
            vec![
                SemanticProductionItem::terminal(node("sem.production.hold.terminal"), "hold")
                    .unwrap(),
                SemanticProductionItem::non_terminal(
                    node("sem.production.hold.saved"),
                    ProductionFieldId::new("saved").unwrap(),
                    k_item.clone(),
                ),
            ],
            vec![],
        )
        .unwrap(),
        SemanticProduction::new(
            node("sem.production.skip"),
            skip.clone(),
            SemanticSortRef::declared(stmt.clone()),
            vec![
                SemanticProductionItem::terminal(node("sem.production.skip.terminal"), "skip")
                    .unwrap(),
            ],
            vec![],
        )
        .unwrap(),
    ];
    let syntax_id = ModuleId::new("HOLD-SYNTAX").unwrap();
    let syntax = SemanticModule::new(
        node("sem.module.syntax"),
        syntax_id.clone(),
        vec![],
        vec![
            SemanticSort::new(node("sem.sort.kitem"), framework_k_item()),
            SemanticSort::new(node("sem.sort.stmt"), stmt.clone()),
            SemanticSort::new(node("sem.sort.frame"), frame.clone()),
        ],
        vec![],
        productions,
        vec![],
        vec![],
        None,
        vec![],
    );
    let k_cell = SemanticId::new("machine.k").unwrap();
    let configuration = FixedConfiguration::new(
        node("sem.configuration"),
        SemanticId::new("machine").unwrap(),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                node("sem.cell.k"),
                k_cell.clone(),
                "k",
                vec![],
                SemanticSortRef::declared(stmt.clone()),
            )
            .unwrap(),
        ],
        node("sem.initializer"),
        SemanticId::new("machine.init").unwrap(),
        vec![],
        vec![FixedInitializerCell::term(
            node("sem.initializer.k"),
            k_cell,
            SemanticTerm::application(
                node("sem.term.init.skip"),
                SemanticSortRef::declared(stmt),
                ApplicationRef::Declared(skip),
                vec![],
            ),
        )],
    )
    .unwrap();
    let s = SemanticId::new("S").unwrap();
    let rewrite = SemanticTerm::rewrite(
        node("sem.term.rule.rewrite"),
        k_item,
        SemanticTerm::application(
            node("sem.term.rule.hold"),
            SemanticSortRef::declared(frame),
            ApplicationRef::Declared(hold),
            vec![SemanticTerm::variable(
                node("sem.term.rule.saved"),
                variable_sort.clone(),
                s.clone(),
            )],
        ),
        SemanticTerm::variable(
            node("sem.term.rule.result"),
            variable_sort.clone(),
            s.clone(),
        ),
    )
    .unwrap();
    let rule = SemanticRule::new(
        node("sem.rule.unhold"),
        item("rules", "unhold", ItemKind::Rule),
        SentenceKind::Transition,
        vec![SemanticVariable::new(s, variable_sort.clone())],
        rewrite,
    )
    .unwrap();
    let main_id = ModuleId::new("HOLD").unwrap();
    let main = SemanticModule::new(
        node("sem.module.main"),
        main_id,
        vec![syntax_id],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        Some(configuration),
        vec![rule],
    );
    SemanticTheory::new(vec![syntax, main])
}

fn symbol(id: &str, name: &str, kind: SymbolKind) -> SymbolIdentity {
    SymbolIdentity::new(SymbolId::new(id).unwrap(), name, kind).unwrap()
}

/// The Definition IR of [`semantic_theory`].
#[expect(
    clippy::too_many_lines,
    reason = "Mirrors the semantic fixture sentence by sentence."
)]
fn definition_ir(
    variable_sort: &DefinitionSortRef,
) -> Result<DefinitionIr, DefinitionValidationError> {
    let k_item = DefinitionSortRef::declared(SymbolId::new("sort.kitem").unwrap());
    let stmt = DefinitionSortRef::declared(SymbolId::new("sort.stmt").unwrap());
    let frame = DefinitionSortRef::declared(SymbolId::new("sort.frame").unwrap());
    let hold = SymbolId::new("production.hold").unwrap();
    let skip = SymbolId::new("production.skip").unwrap();
    let sort = |key: &str, id: &str, name: &str| {
        DefinitionSentence::SyntaxSort(
            SyntaxSortSentence::new(node(key), symbol(id, name, SymbolKind::Sort)).unwrap(),
        )
    };
    let syntax_sentences = vec![
        sort("def.sort.kitem", "sort.kitem", "KItem"),
        sort("def.sort.stmt", "sort.stmt", "Stmt"),
        sort("def.sort.frame", "sort.frame", "Frame"),
        DefinitionSentence::Production(
            ProductionSentence::new(
                node("def.production.hold"),
                symbol("production.hold", "Lblhold", SymbolKind::Production),
                frame.clone(),
                vec![
                    ProductionItem::terminal(node("def.production.hold.terminal"), "hold").unwrap(),
                    ProductionItem::non_terminal(
                        node("def.production.hold.saved"),
                        ProductionFieldId::new("saved").unwrap(),
                        k_item.clone(),
                    ),
                ],
                vec![],
            )
            .unwrap(),
        ),
        DefinitionSentence::Production(
            ProductionSentence::new(
                node("def.production.skip"),
                symbol("production.skip", "Lblskip", SymbolKind::Production),
                stmt.clone(),
                vec![
                    ProductionItem::terminal(node("def.production.skip.terminal"), "skip").unwrap(),
                ],
                vec![],
            )
            .unwrap(),
        ),
    ];
    let syntax_id = ModuleId::new("HOLD-SYNTAX").unwrap();
    let main_id = ModuleId::new("HOLD").unwrap();
    let syntax = DefinitionModule::new(
        node("def.module.syntax"),
        syntax_id.clone(),
        vec![],
        vec![],
        syntax_sentences,
    );
    let k_cell = SymbolId::new("cell.k").unwrap();
    let configuration = DefinitionSentence::Configuration(
        FixedConfiguration::new(
            node("def.configuration"),
            SemanticId::new("machine").unwrap(),
            ConfigurationRoot::GeneratedTop,
            vec![
                FixedCell::leaf(
                    node("def.cell.k"),
                    k_cell.clone(),
                    "k",
                    vec![],
                    stmt.clone(),
                )
                .unwrap(),
            ],
            node("def.initializer"),
            SemanticId::new("machine.init").unwrap(),
            vec![],
            vec![FixedInitializerCell::term(
                node("def.initializer.k"),
                k_cell,
                DefinitionTerm::application(
                    node("def.term.init.skip"),
                    stmt,
                    ApplicationRef::Declared(skip),
                    vec![],
                ),
            )],
        )
        .unwrap(),
    );
    let s = SemanticId::new("S").unwrap();
    let rewrite = DefinitionTerm::rewrite(
        node("def.term.rule.rewrite"),
        k_item,
        DefinitionTerm::application(
            node("def.term.rule.hold"),
            frame,
            ApplicationRef::Declared(hold),
            vec![DefinitionTerm::variable(
                node("def.term.rule.saved"),
                variable_sort.clone(),
                s.clone(),
            )],
        ),
        DefinitionTerm::variable(
            node("def.term.rule.result"),
            variable_sort.clone(),
            s.clone(),
        ),
    )
    .unwrap();
    let rule = DefinitionSentence::Rule(
        RuleSentence::new(
            node("def.rule.unhold"),
            LabelIdentity::new(
                LabelId::new("rule.unhold").unwrap(),
                "ORG-EXAMPLE-HOLD.rules.unhold",
            )
            .unwrap(),
            SentenceKind::Transition,
            vec![DefinitionVariable::new(s, variable_sort.clone())],
            rewrite,
        )
        .unwrap(),
    );
    let main = DefinitionModule::new(
        node("def.module.main"),
        main_id.clone(),
        vec![syntax_id],
        vec![],
        vec![configuration, rule],
    );
    DefinitionIr::new(main_id, vec![syntax, main])
}

#[test]
fn every_sort_but_k_is_a_k_item_in_the_semantic_theory() {
    let stmt = SemanticSortRef::declared(item("syntax", "Stmt", ItemKind::Sort));
    semantic_theory(&stmt).unwrap();
    semantic_theory(&SemanticSortRef::int()).unwrap();
    semantic_theory(&SemanticSortRef::k_sequence()).unwrap_err();
}

#[test]
fn every_sort_but_k_is_a_k_item_in_the_definition() {
    let stmt = DefinitionSortRef::declared(SymbolId::new("sort.stmt").unwrap());
    definition_ir(&stmt).unwrap();
    definition_ir(&DefinitionSortRef::int()).unwrap();
    definition_ir(&DefinitionSortRef::k_sequence()).unwrap_err();
}
