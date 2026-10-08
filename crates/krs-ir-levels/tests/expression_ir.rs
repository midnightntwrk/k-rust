//! Hand-built expression-grammar Definition IR contract.

use krs_ir::testing;
use krs_ir::{
    ApplicationRef, BuiltinOperation, ConfigurationRoot, FixedCell, FixedConfiguration,
    FixedConfigurationVariable, FixedInitializerCell, FormatFragment, GroupAssociativity,
    GroupAssociativitySentence, ModuleId, NodeOrigin, PrecedenceRelation, ProductionAttribute,
    ProductionFieldId, ProductionFieldReference, ProductionGroupId, ProductionResultSort,
    SemanticId, SentenceKind, SourceMapKey, StableItemId, StrictnessKind,
};
use krs_ir_levels::{
    DefinitionIr, DefinitionModule, DefinitionSentence, DefinitionSortRef, DefinitionTerm,
    DefinitionValidationError, DefinitionVariable, LabelId, LabelIdentity, ProductionGroupIdentity,
    ProductionItem, ProductionSentence, SemanticModule, SemanticProduction, SemanticProductionItem,
    SemanticRule, SemanticSort, SemanticSortRef, SemanticSubsort, SemanticTerm, SemanticTheory,
    SubsortSentence, SymbolId, SymbolIdentity, SymbolKind, SyntaxSortSentence,
};
use krs_test_support::assert_rejects_with_message;

fn node(key: &str) -> NodeOrigin {
    testing::origin_in(
        key,
        testing::package("ORG-EXAMPLE-EXPR", "expr-semantics"),
        "src/expr.rs",
        testing::digest_with("abcdef0123456789".repeat(4)),
        0,
        7,
    )
}

fn symbol(id: &str, name: &str, kind: SymbolKind) -> SymbolIdentity {
    SymbolIdentity::new(SymbolId::new(id).unwrap(), name, kind).unwrap()
}

fn declared(id: &str) -> DefinitionSortRef {
    DefinitionSortRef::declared(SymbolId::new(id).unwrap())
}

fn field(name: &str) -> ProductionFieldId {
    ProductionFieldId::new(name).unwrap()
}

fn field_reference(key: &str, name: &str) -> ProductionFieldReference {
    ProductionFieldReference::new(node(key), field(name))
}

fn result_sort<S>(key: &str, sort: S) -> ProductionResultSort<S> {
    ProductionResultSort::new(node(key), sort)
}

fn group(name: &str) -> ProductionGroupId {
    ProductionGroupId::new(name).unwrap()
}

fn stable_item(module: &str, name: &str, kind: krs_ir::ItemKind) -> StableItemId {
    testing::item_in(
        testing::package("ORG-EXAMPLE-EXPR", "expr-semantics"),
        module,
        name,
        kind,
    )
}

fn terminal(key: &str, text: &str) -> ProductionItem {
    ProductionItem::terminal(node(key), text).unwrap()
}

fn non_terminal(key: &str, name: &str, sort: DefinitionSortRef) -> ProductionItem {
    ProductionItem::non_terminal(node(key), field(name), sort)
}

fn production(
    key: &str,
    id: &str,
    emitted: &str,
    result_sort: DefinitionSortRef,
    items: Vec<ProductionItem>,
    attributes: Vec<ProductionAttribute<DefinitionSortRef, SymbolId>>,
) -> DefinitionSentence {
    DefinitionSentence::Production(
        ProductionSentence::new(
            node(key),
            symbol(id, emitted, SymbolKind::Production),
            result_sort,
            items,
            attributes,
        )
        .unwrap(),
    )
}

fn variable(key: &str, id: &str, sort: DefinitionSortRef) -> DefinitionTerm {
    DefinitionTerm::variable(node(key), sort, SemanticId::new(id).unwrap())
}

fn application(
    key: &str,
    sort: DefinitionSortRef,
    application: ApplicationRef<SymbolId, DefinitionSortRef>,
    arguments: Vec<DefinitionTerm>,
) -> DefinitionTerm {
    DefinitionTerm::application(node(key), sort, application, arguments)
}

#[expect(
    clippy::too_many_lines,
    reason = "One fixture assembles the complete expression Definition IR contract."
)]
fn expression_definition() -> Result<DefinitionIr, DefinitionValidationError> {
    let expr = declared("sort.expr");
    let value = declared("sort.value");
    let k_item = declared("sort.kitem");
    let k_result = declared("sort.kresult");

    let groups = vec![
        ProductionGroupIdentity::new(node("group.prefix"), group("prefix"), "exprPrefix")?,
        ProductionGroupIdentity::new(node("group.additive"), group("additive"), "exprAdditive")?,
        ProductionGroupIdentity::new(
            node("group.conjunction"),
            group("conjunction"),
            "exprConjunction",
        )?,
    ];

    let syntax = vec![
        DefinitionSentence::SyntaxSort(SyntaxSortSentence::new(
            node("sort.kitem"),
            symbol("sort.kitem", "KItem", SymbolKind::Sort),
        )?),
        DefinitionSentence::SyntaxSort(SyntaxSortSentence::new(
            node("sort.kresult"),
            symbol("sort.kresult", "KResult", SymbolKind::Sort),
        )?),
        DefinitionSentence::SyntaxSort(SyntaxSortSentence::new(
            node("sort.expr"),
            symbol("sort.expr", "Expr", SymbolKind::Sort),
        )?),
        DefinitionSentence::SyntaxSort(SyntaxSortSentence::new(
            node("sort.value"),
            symbol("sort.value", "Value", SymbolKind::Sort),
        )?),
        DefinitionSentence::SyntaxSort(SyntaxSortSentence::new(
            node("sort.id"),
            symbol("sort.id", "Id", SymbolKind::Sort),
        )?),
        DefinitionSentence::Subsort(SubsortSentence::new(
            node("subsort.int-value"),
            DefinitionSortRef::int(),
            value.clone(),
        )),
        DefinitionSentence::Subsort(SubsortSentence::new(
            node("subsort.bool-value"),
            DefinitionSortRef::bool(),
            value.clone(),
        )),
        DefinitionSentence::Subsort(SubsortSentence::new(
            node("subsort.value-expr"),
            value.clone(),
            expr.clone(),
        )),
        DefinitionSentence::Subsort(SubsortSentence::new(
            node("subsort.value-kresult"),
            value.clone(),
            k_result.clone(),
        )),
        DefinitionSentence::Subsort(SubsortSentence::new(
            node("subsort.expr-kitem"),
            expr.clone(),
            k_item.clone(),
        )),
        DefinitionSentence::Subsort(SubsortSentence::new(
            node("subsort.kresult-kitem"),
            k_result.clone(),
            k_item.clone(),
        )),
        DefinitionSentence::Subsort(SubsortSentence::new(
            node("subsort.id-expr"),
            declared("sort.id"),
            expr.clone(),
        )),
        production(
            "production.id",
            "production.id",
            "LblId",
            declared("sort.id"),
            vec![
                ProductionItem::regex_terminal(
                    node("production.id.regex"),
                    Some("[A-Za-z0-9_]".into()),
                    "[A-Za-z][A-Za-z0-9_]*",
                    Some("[A-Za-z0-9_]".into()),
                )
                .unwrap(),
            ],
            vec![
                ProductionAttribute::Token {
                    origin: node("production.id.token"),
                    lexical_precedence: Some(2),
                },
                ProductionAttribute::Avoid {
                    origin: node("production.id.avoid"),
                },
            ],
        ),
        production(
            "production.paren",
            "production.paren",
            "LblParens",
            expr.clone(),
            vec![
                terminal("production.paren.open", "("),
                non_terminal("production.paren.value", "value", expr.clone()),
                terminal("production.paren.close", ")"),
            ],
            vec![
                ProductionAttribute::Bracket {
                    origin: node("production.paren.bracket"),
                },
                ProductionAttribute::Format {
                    origin: node("production.paren.format"),
                    fragments: vec![
                        FormatFragment::Item(1),
                        FormatFragment::Item(2),
                        FormatFragment::Item(3),
                    ],
                },
            ],
        ),
        production(
            "production.neg",
            "production.neg",
            "LblNeg",
            expr.clone(),
            vec![
                terminal("production.neg.minus", "-"),
                non_terminal("production.neg.operand", "operand", expr.clone()),
            ],
            vec![
                ProductionAttribute::Group {
                    origin: node("production.neg.group"),
                    group: group("prefix"),
                },
                ProductionAttribute::Format {
                    origin: node("production.neg.format"),
                    fragments: vec![FormatFragment::Item(1), FormatFragment::Item(2)],
                },
                ProductionAttribute::Strictness {
                    origin: node("production.neg.strict"),
                    kind: StrictnessKind::Strict,
                    using: None,
                    fields: vec![field_reference("production.neg.strict.operand", "operand")],
                    result_sort: result_sort("production.neg.strict.result-sort", k_result.clone()),
                },
            ],
        ),
        production(
            "production.add",
            "production.add",
            "LblAdd",
            expr.clone(),
            vec![
                non_terminal("production.add.lhs", "lhs", expr.clone()),
                terminal("production.add.plus", "+"),
                non_terminal("production.add.rhs", "rhs", expr.clone()),
            ],
            vec![
                ProductionAttribute::Group {
                    origin: node("production.add.group"),
                    group: group("additive"),
                },
                ProductionAttribute::Format {
                    origin: node("production.add.format"),
                    fragments: vec![
                        FormatFragment::Item(1),
                        FormatFragment::Literal(" ".into()),
                        FormatFragment::Item(2),
                        FormatFragment::Literal(" ".into()),
                        FormatFragment::Item(3),
                    ],
                },
                ProductionAttribute::Strictness {
                    origin: node("production.add.seqstrict"),
                    kind: StrictnessKind::SeqStrict,
                    using: None,
                    fields: vec![
                        field_reference("production.add.seqstrict.lhs", "lhs"),
                        field_reference("production.add.seqstrict.rhs", "rhs"),
                    ],
                    result_sort: result_sort(
                        "production.add.seqstrict.result-sort",
                        k_result.clone(),
                    ),
                },
            ],
        ),
        production(
            "production.and",
            "production.and",
            "LblAnd",
            expr.clone(),
            vec![
                non_terminal("production.and.lhs", "lhs", expr.clone()),
                terminal("production.and.operator", "&&"),
                non_terminal("production.and.rhs", "rhs", expr.clone()),
            ],
            vec![
                ProductionAttribute::Group {
                    origin: node("production.and.group"),
                    group: group("conjunction"),
                },
                ProductionAttribute::Format {
                    origin: node("production.and.format"),
                    fragments: vec![
                        FormatFragment::Item(1),
                        FormatFragment::Literal(" ".into()),
                        FormatFragment::Item(2),
                        FormatFragment::Literal(" ".into()),
                        FormatFragment::Item(3),
                    ],
                },
                ProductionAttribute::Strictness {
                    origin: node("production.and.strict"),
                    kind: StrictnessKind::Strict,
                    using: None,
                    fields: vec![field_reference("production.and.strict.lhs", "lhs")],
                    result_sort: result_sort("production.and.strict.result-sort", k_result.clone()),
                },
            ],
        ),
        DefinitionSentence::Precedence(
            PrecedenceRelation::new(
                node("precedence.prefix-additive"),
                vec![group("prefix")],
                vec![group("additive")],
            )
            .unwrap(),
        ),
        DefinitionSentence::Precedence(
            PrecedenceRelation::new(
                node("precedence.additive-conjunction"),
                vec![group("additive")],
                vec![group("conjunction")],
            )
            .unwrap(),
        ),
        DefinitionSentence::Associativity(
            GroupAssociativitySentence::new(
                node("associativity.left"),
                GroupAssociativity::Left,
                vec![group("additive"), group("conjunction")],
            )
            .unwrap(),
        ),
    ];

    let int_x = DefinitionVariable::new(SemanticId::new("x").unwrap(), DefinitionSortRef::int());
    let int_y = DefinitionVariable::new(SemanticId::new("y").unwrap(), DefinitionSortRef::int());
    let bool_b = DefinitionVariable::new(SemanticId::new("b").unwrap(), DefinitionSortRef::bool());

    let neg_lhs = application(
        "term.neg.lhs",
        expr.clone(),
        ApplicationRef::Declared(SymbolId::new("production.neg").unwrap()),
        vec![variable("term.neg.x.lhs", "x", DefinitionSortRef::int())],
    );
    let neg_rhs = application(
        "term.neg.rhs",
        DefinitionSortRef::int(),
        ApplicationRef::Builtin(BuiltinOperation::IntSub),
        vec![
            DefinitionTerm::token(node("term.neg.zero"), DefinitionSortRef::int(), "0")?,
            variable("term.neg.x.rhs", "x", DefinitionSortRef::int()),
        ],
    );
    let neg_rule = DefinitionSentence::Rule(krs_ir_levels::RuleSentence::new(
        node("rule.neg"),
        LabelIdentity::new(LabelId::new("rule.neg").unwrap(), "expr.neg")?,
        SentenceKind::Transition,
        vec![int_x],
        DefinitionTerm::rewrite(node("term.neg.rewrite"), expr.clone(), neg_lhs, neg_rhs)?,
    )?);

    let add_lhs = application(
        "term.add.lhs",
        expr.clone(),
        ApplicationRef::Declared(SymbolId::new("production.add").unwrap()),
        vec![
            variable("term.add.x.lhs", "x", DefinitionSortRef::int()),
            variable("term.add.y.lhs", "y", DefinitionSortRef::int()),
        ],
    );
    let add_rhs = application(
        "term.add.rhs",
        DefinitionSortRef::int(),
        ApplicationRef::Builtin(BuiltinOperation::IntAdd),
        vec![
            variable("term.add.x.rhs", "x", DefinitionSortRef::int()),
            variable("term.add.y.rhs", "y", DefinitionSortRef::int()),
        ],
    );
    let addition_rule = DefinitionSentence::Rule(krs_ir_levels::RuleSentence::new(
        node("rule.add"),
        LabelIdentity::new(LabelId::new("rule.add").unwrap(), "expr.add")?,
        SentenceKind::Transition,
        vec![
            int_y,
            DefinitionVariable::new(SemanticId::new("x").unwrap(), DefinitionSortRef::int()),
        ],
        DefinitionTerm::rewrite(node("term.add.rewrite"), expr.clone(), add_lhs, add_rhs)?,
    )?);

    let and_lhs = application(
        "term.and.lhs",
        expr.clone(),
        ApplicationRef::Declared(SymbolId::new("production.and").unwrap()),
        vec![
            DefinitionTerm::token(node("term.and.true"), DefinitionSortRef::bool(), "true")?,
            variable("term.and.b.lhs", "b", DefinitionSortRef::bool()),
        ],
    );
    let and_rhs = variable("term.and.b.rhs", "b", DefinitionSortRef::bool());
    let conjunction_rule = DefinitionSentence::Rule(krs_ir_levels::RuleSentence::new(
        node("rule.and-true"),
        LabelIdentity::new(LabelId::new("rule.and-true").unwrap(), "expr.and-true")?,
        SentenceKind::Transition,
        vec![bool_b],
        DefinitionTerm::rewrite(node("term.and.rewrite"), expr.clone(), and_lhs, and_rhs)?,
    )?);

    let syntax_id = ModuleId::new("EXPR-SYNTAX").unwrap();
    let syntax_module = DefinitionModule::new(
        node("module.syntax"),
        syntax_id.clone(),
        vec![],
        groups,
        syntax,
    );

    let k_cell = SymbolId::new("cell.k").unwrap();
    let configuration = DefinitionSentence::Configuration(
        FixedConfiguration::new(
            node("configuration.expr"),
            SemanticId::new("machine").unwrap(),
            ConfigurationRoot::GeneratedTop,
            vec![
                FixedCell::leaf(
                    node("cell.k"),
                    k_cell.clone(),
                    "k",
                    vec![],
                    DefinitionSortRef::k_sequence(),
                )
                .unwrap(),
            ],
            node("initializer.expr"),
            SemanticId::new("machine.init").unwrap(),
            vec![
                FixedConfigurationVariable::new(
                    node("configuration.variable.pgm"),
                    SemanticId::new("pgm").unwrap(),
                    "PGM",
                    expr.clone(),
                    true,
                )
                .unwrap(),
            ],
            vec![FixedInitializerCell::term(
                node("initializer.k"),
                k_cell,
                DefinitionTerm::k_sequence(
                    node("term.init.sequence"),
                    k_item,
                    vec![variable("term.init.pgm", "pgm", expr)],
                ),
            )],
        )
        .unwrap(),
    );
    let rules = vec![configuration, neg_rule, addition_rule, conjunction_rule];
    let main_id = ModuleId::new("EXPR").unwrap();
    let main_module = DefinitionModule::new(
        node("module.main"),
        main_id.clone(),
        vec![syntax_id],
        vec![],
        rules,
    );
    DefinitionIr::new(main_id, vec![syntax_module, main_module])
}

#[test]
fn representative_expression_definition_has_canonical_bytes() {
    let definition = expression_definition().unwrap();
    testing::assert_canonical_contract(&definition);
    let normal = definition.to_canonical_json().unwrap();
    expect_test::expect_file!["golden/definition_expr.json"].assert_eq(&normal);
    assert!(normal.contains("\"sort\": \"int\""));
    assert!(normal.contains("\"sort\": \"bool\""));
    assert!(normal.contains("\"application\": \"int_add\""));
    assert!(!normal.contains("INT.add"));
    assert!(!normal.contains("resolved_production_id"));
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One fixture checks semantic expression sort and application resolution together."
)]
fn semantic_expression_contract_resolves_builtin_sorts_and_applications() {
    let k_item = stable_item("syntax", "KItem", krs_ir::ItemKind::Sort);
    let k_result = stable_item("syntax", "KResult", krs_ir::ItemKind::Sort);
    let expr = stable_item("syntax", "Expr", krs_ir::ItemKind::Sort);
    let value = stable_item("syntax", "Value", krs_ir::ItemKind::Sort);
    let id_sort = stable_item("syntax", "Id", krs_ir::ItemKind::Sort);
    let neg = stable_item("syntax", "Neg", krs_ir::ItemKind::Constructor);
    let add = stable_item("syntax", "Add", krs_ir::ItemKind::Constructor);
    let id_token = stable_item("syntax", "IdToken", krs_ir::ItemKind::Constructor);
    let rule_id = stable_item("rules", "add_int", krs_ir::ItemKind::Rule);

    let sorts = vec![
        SemanticSort::new(node("sem.sort.kitem"), k_item.clone()),
        SemanticSort::new(node("sem.sort.kresult"), k_result.clone()),
        SemanticSort::new(node("sem.sort.expr"), expr.clone()),
        SemanticSort::new(node("sem.sort.value"), value.clone()),
        SemanticSort::new(node("sem.sort.id"), id_sort.clone()),
    ];
    let subsorts = vec![
        SemanticSubsort::new(
            node("sem.subsort.int-value"),
            SemanticSortRef::int(),
            SemanticSortRef::declared(value.clone()),
        ),
        SemanticSubsort::new(
            node("sem.subsort.bool-value"),
            SemanticSortRef::bool(),
            SemanticSortRef::declared(value.clone()),
        ),
        SemanticSubsort::new(
            node("sem.subsort.value-expr"),
            SemanticSortRef::declared(value.clone()),
            SemanticSortRef::declared(expr.clone()),
        ),
        SemanticSubsort::new(
            node("sem.subsort.value-kresult"),
            SemanticSortRef::declared(value),
            SemanticSortRef::declared(k_result.clone()),
        ),
        SemanticSubsort::new(
            node("sem.subsort.expr-kitem"),
            SemanticSortRef::declared(expr.clone()),
            SemanticSortRef::declared(k_item.clone()),
        ),
        SemanticSubsort::new(
            node("sem.subsort.kresult-kitem"),
            SemanticSortRef::declared(k_result.clone()),
            SemanticSortRef::declared(k_item.clone()),
        ),
    ];
    let productions = vec![
        SemanticProduction::new(
            node("sem.production.id"),
            id_token,
            SemanticSortRef::declared(id_sort),
            vec![
                SemanticProductionItem::regex_terminal(
                    node("sem.production.id.regex"),
                    None,
                    "[A-Za-z][A-Za-z0-9_]*",
                    None,
                )
                .unwrap(),
            ],
            vec![ProductionAttribute::Token {
                origin: node("sem.production.id.token"),
                lexical_precedence: Some(2),
            }],
        )
        .unwrap(),
        SemanticProduction::new(
            node("sem.production.neg"),
            neg,
            SemanticSortRef::declared(expr.clone()),
            vec![
                SemanticProductionItem::terminal(node("sem.production.neg.minus"), "-").unwrap(),
                SemanticProductionItem::non_terminal(
                    node("sem.production.neg.operand"),
                    field("operand"),
                    SemanticSortRef::declared(expr.clone()),
                ),
            ],
            vec![ProductionAttribute::Group {
                origin: node("sem.production.neg.group"),
                group: group("prefix"),
            }],
        )
        .unwrap(),
        SemanticProduction::new(
            node("sem.production.add"),
            add.clone(),
            SemanticSortRef::declared(expr.clone()),
            vec![
                SemanticProductionItem::non_terminal(
                    node("sem.production.add.lhs"),
                    field("lhs"),
                    SemanticSortRef::declared(expr.clone()),
                ),
                SemanticProductionItem::terminal(node("sem.production.add.plus"), "+").unwrap(),
                SemanticProductionItem::non_terminal(
                    node("sem.production.add.rhs"),
                    field("rhs"),
                    SemanticSortRef::declared(expr.clone()),
                ),
            ],
            vec![
                ProductionAttribute::Group {
                    origin: node("sem.production.add.group"),
                    group: group("additive"),
                },
                ProductionAttribute::Strictness {
                    origin: node("sem.production.add.strict"),
                    kind: StrictnessKind::SeqStrict,
                    using: None,
                    fields: vec![
                        field_reference("sem.production.add.strict.lhs", "lhs"),
                        field_reference("sem.production.add.strict.rhs", "rhs"),
                    ],
                    result_sort: result_sort(
                        "sem.production.add.strict.result-sort",
                        SemanticSortRef::declared(k_result),
                    ),
                },
            ],
        )
        .unwrap(),
    ];
    let syntax_id = ModuleId::new("SEM-EXPR-SYNTAX").unwrap();
    let syntax = SemanticModule::new(
        node("sem.module.syntax"),
        syntax_id.clone(),
        vec![],
        sorts,
        subsorts,
        productions,
        vec![
            PrecedenceRelation::new(
                node("sem.precedence.prefix-additive"),
                vec![group("prefix")],
                vec![group("additive")],
            )
            .unwrap(),
        ],
        vec![],
        None,
        vec![],
    );

    let x_id = SemanticId::new("x").unwrap();
    let y_id = SemanticId::new("y").unwrap();
    let lhs = SemanticTerm::application(
        node("sem.term.add.lhs"),
        SemanticSortRef::declared(expr.clone()),
        ApplicationRef::Declared(add),
        vec![
            SemanticTerm::variable(
                node("sem.term.add.x.lhs"),
                SemanticSortRef::int(),
                x_id.clone(),
            ),
            SemanticTerm::variable(
                node("sem.term.add.y.lhs"),
                SemanticSortRef::int(),
                y_id.clone(),
            ),
        ],
    );
    let rhs = SemanticTerm::application(
        node("sem.term.add.rhs"),
        SemanticSortRef::int(),
        ApplicationRef::Builtin(BuiltinOperation::IntAdd),
        vec![
            SemanticTerm::variable(
                node("sem.term.add.x.rhs"),
                SemanticSortRef::int(),
                x_id.clone(),
            ),
            SemanticTerm::variable(
                node("sem.term.add.y.rhs"),
                SemanticSortRef::int(),
                y_id.clone(),
            ),
        ],
    );
    let rule = SemanticRule::new(
        node("sem.rule.add"),
        rule_id,
        SentenceKind::Transition,
        vec![
            krs_ir_levels::SemanticVariable::new(x_id, SemanticSortRef::int()),
            krs_ir_levels::SemanticVariable::new(y_id, SemanticSortRef::int()),
        ],
        SemanticTerm::rewrite(
            node("sem.term.add.rewrite"),
            SemanticSortRef::declared(expr.clone()),
            lhs,
            rhs,
        )
        .unwrap(),
    )
    .unwrap();
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
                SemanticSortRef::k_sequence(),
            )
            .unwrap(),
        ],
        node("sem.initializer"),
        SemanticId::new("machine.init").unwrap(),
        vec![
            FixedConfigurationVariable::new(
                node("sem.configuration.variable.pgm"),
                SemanticId::new("pgm").unwrap(),
                "PGM",
                SemanticSortRef::declared(expr.clone()),
                true,
            )
            .unwrap(),
        ],
        vec![FixedInitializerCell::term(
            node("sem.initializer.k"),
            k_cell,
            SemanticTerm::k_sequence(
                node("sem.term.init.sequence"),
                SemanticSortRef::declared(k_item),
                vec![SemanticTerm::variable(
                    node("sem.term.init.pgm"),
                    SemanticSortRef::declared(expr),
                    SemanticId::new("pgm").unwrap(),
                )],
            ),
        )],
    )
    .unwrap();
    let main = SemanticModule::new(
        node("sem.module.main"),
        ModuleId::new("SEM-EXPR").unwrap(),
        vec![syntax_id],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        Some(configuration),
        vec![rule],
    );
    let theory = SemanticTheory::new(vec![main, syntax]).unwrap();
    testing::assert_canonical_contract(&theory);
    let json = theory.to_canonical_json().unwrap();
    assert!(json.contains("\"application\": \"int_add\""));
    assert!(json.contains("\"sort\": \"int\""));
    assert!(!json.contains("INT.add"));
}

fn expression_json() -> serde_json::Value {
    serde_json::to_value(expression_definition().unwrap()).unwrap()
}

fn syntax_module_mut(json: &mut serde_json::Value) -> &mut serde_json::Value {
    json["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|module| module["id"] == "EXPR-SYNTAX")
        .unwrap()
}

fn production_mut<'a>(json: &'a mut serde_json::Value, id: &str) -> &'a mut serde_json::Value {
    syntax_module_mut(json)["sentences"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|sentence| {
            sentence["sentence_kind"] == "production" && sentence["sentence"]["symbol"]["id"] == id
        })
        .unwrap()
}

#[test]
fn rejects_regex_without_classified_token_metadata() {
    let mut json = expression_json();
    production_mut(&mut json, "production.id")["sentence"]["attributes"] = serde_json::json!([]);
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(json),
        DefinitionValidationError::RegexWithoutToken,
    );
}

#[test]
fn rejects_prefer_with_avoid_and_on_parse_only_productions() {
    let prefer = |key: &str| {
        serde_json::json!({
            "attribute_kind": "prefer",
            "origin": serde_json::to_value(node(key)).unwrap(),
        })
    };
    let mut with_avoid = expression_json();
    production_mut(&mut with_avoid, "production.neg")["sentence"]["attributes"]
        .as_array_mut()
        .unwrap()
        .push(serde_json::json!({
            "attribute_kind": "avoid",
            "origin": serde_json::to_value(node("production.neg.avoid")).unwrap(),
        }));
    let mut accepted = with_avoid.clone();
    production_mut(&mut with_avoid, "production.neg")["sentence"]["attributes"]
        .as_array_mut()
        .unwrap()
        .push(prefer("production.neg.prefer"));
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(with_avoid),
        DefinitionValidationError::PreferAndAvoid,
    );
    let attributes = production_mut(&mut accepted, "production.neg")["sentence"]["attributes"]
        .as_array_mut()
        .unwrap();
    attributes.pop();
    attributes.push(prefer("production.neg.prefer"));
    serde_json::from_value::<DefinitionIr>(accepted).unwrap();

    for (production, key) in [
        ("production.paren", "production.paren.prefer"),
        ("production.id", "production.id.prefer"),
    ] {
        let mut json = expression_json();
        let attributes = production_mut(&mut json, production)["sentence"]["attributes"]
            .as_array_mut()
            .unwrap();
        attributes.retain(|attribute| attribute["attribute_kind"] != "avoid");
        attributes.push(prefer(key));
        assert_rejects_with_message(
            serde_json::from_value::<DefinitionIr>(json),
            DefinitionValidationError::PreferOnParseOnlyProduction,
        );
    }
}

#[test]
fn overload_names_a_production_symbol_on_a_constructor() {
    let overload = |key: &str, target: &str| {
        serde_json::json!({
            "attribute_kind": "overload",
            "origin": serde_json::to_value(node(key)).unwrap(),
            "target": target,
        })
    };
    let mut accepted = expression_json();
    production_mut(&mut accepted, "production.neg")["sentence"]["attributes"]
        .as_array_mut()
        .unwrap()
        .push(overload("production.neg.overload", "production.add"));
    serde_json::from_value::<DefinitionIr>(accepted).unwrap();

    let mut dangling = expression_json();
    production_mut(&mut dangling, "production.neg")["sentence"]["attributes"]
        .as_array_mut()
        .unwrap()
        .push(overload("production.neg.overload", "production.missing"));
    assert!(serde_json::from_value::<DefinitionIr>(dangling).is_err());

    let mut token = expression_json();
    production_mut(&mut token, "production.id")["sentence"]["attributes"]
        .as_array_mut()
        .unwrap()
        .push(overload("production.id.overload", "production.add"));
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(token),
        DefinitionValidationError::InvalidOverloadProduction,
    );
}

#[test]
fn rejects_strictness_for_an_unknown_field() {
    let mut json = expression_json();
    let attributes = production_mut(&mut json, "production.add")["sentence"]["attributes"]
        .as_array_mut()
        .unwrap();
    let strictness = attributes
        .iter_mut()
        .find(|attribute| attribute["attribute_kind"] == "strictness")
        .unwrap();
    strictness["fields"] = serde_json::json!([{
        "origin": serde_json::to_value(node("production.add.seqstrict.missing")).unwrap(),
        "field": "missing"
    }]);
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(json),
        DefinitionValidationError::InvalidStrictnessField,
    );
}

#[test]
fn rejects_precedence_cycles_and_dangling_groups() {
    let mut cycle = expression_json();
    syntax_module_mut(&mut cycle)["sentences"]
        .as_array_mut()
        .unwrap()
        .push(serde_json::json!({
            "sentence_kind": "precedence",
            "sentence": {
                "origin": serde_json::to_value(node("precedence.cycle")).unwrap(),
                "higher": ["conjunction"],
                "lower": ["prefix"]
            }
        }));
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(cycle),
        DefinitionValidationError::PrecedenceCycle(group("additive")),
    );

    let mut dangling = expression_json();
    let precedence = syntax_module_mut(&mut dangling)["sentences"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|sentence| sentence["sentence_kind"] == "precedence")
        .unwrap();
    precedence["sentence"]["higher"] = serde_json::json!(["unknown"]);
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(dangling),
        DefinitionValidationError::DanglingProductionGroup(group("unknown")),
    );
}

#[test]
fn rejects_subsort_cycles() {
    let mut json = expression_json();
    syntax_module_mut(&mut json)["sentences"]
        .as_array_mut()
        .unwrap()
        .push(serde_json::json!({
            "sentence_kind": "subsort",
            "sentence": {
                "origin": serde_json::to_value(node("subsort.cycle")).unwrap(),
                "subsort": {"sort_source": "declared", "sort": "sort.expr"},
                "supersort": {"sort_source": "builtin", "sort": "int"}
            }
        }));
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(json),
        DefinitionValidationError::SubsortCycle(declared("sort.expr")),
    );
}

#[test]
fn rejects_wrong_builtin_signature_and_raw_or_adapter_attributes() {
    let mut signature = expression_json();
    let main = signature["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|module| module["id"] == "EXPR")
        .unwrap();
    let neg = main["sentences"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|sentence| {
            sentence["sentence_kind"] == "rule" && sentence["sentence"]["label"]["id"] == "rule.neg"
        })
        .unwrap();
    neg["sentence"]["body"]["to"]["arguments"][0]["sort"] =
        serde_json::json!({"sort_source": "builtin", "sort": "bool"});
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(signature),
        DefinitionValidationError::BuiltinApplicationSignature(BuiltinOperation::IntSub),
    );

    let mut raw = expression_json();
    production_mut(&mut raw, "production.add")["sentence"]["attributes"][0]["raw_hook"] =
        serde_json::json!("INT.add");
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(raw),
        "unknown field `raw_hook`",
    );

    let mut adapter = expression_json();
    production_mut(&mut adapter, "production.add")["sentence"]["k_rust_production_id"] =
        serde_json::json!(17);
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(adapter),
        "unknown field `k_rust_production_id`",
    );
}

#[test]
fn rejects_missing_or_reused_nested_provenance() {
    let mut missing = expression_json();
    production_mut(&mut missing, "production.add")["sentence"]["items"][0]
        .as_object_mut()
        .unwrap()
        .remove("origin");
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(missing),
        "missing field `origin`",
    );

    let mut duplicate = expression_json();
    let production = production_mut(&mut duplicate, "production.add");
    production["sentence"]["items"][1]["origin"] =
        production["sentence"]["items"][0]["origin"].clone();
    assert_rejects_with_message(
        serde_json::from_value::<DefinitionIr>(duplicate),
        DefinitionValidationError::DuplicateSourceMapKey(
            SourceMapKey::new("production.add.lhs").unwrap(),
        ),
    );
}
