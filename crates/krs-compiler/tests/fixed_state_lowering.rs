//! IMP calculation fixed-state lowering, canonical source, and sidecars.

use std::collections::BTreeMap;

use krs_compiler::testing::assert_lowering_contract;
use krs_compiler::{EmittedK, LoweringError, SourceMapNodeKind, lower_semantic_theory};
use krs_ir::testing;
use krs_ir::{
    ApplicationRef, CellAttribute, CellContentFrame, CellPost, ConfigurationRoot, FixedCell,
    FixedCellClause, FixedConfiguration, FixedConfigurationRewrite, FixedConfigurationVariable,
    FixedInitializerCell, FormatFragment, GroupAssociativity, GroupAssociativitySentence, ItemKind,
    MapOperation, ModuleId, NodeOrigin, PackageId, PrecedenceRelation, ProductionAttribute,
    ProductionFieldId, ProductionFieldReference, ProductionGroupId, ProductionResultSort,
    RuleBodyRef, SemanticId, SemanticModule, SemanticProduction, SemanticProductionItem,
    SemanticRule, SemanticSort, SemanticSortRef, SemanticSubsort, SemanticTerm, SemanticTheory,
    SemanticVariable, SentenceKind, StableItemId, StrictnessKind,
};
use krs_test_support::kompile_reference;

fn package() -> PackageId {
    testing::package("KRS-CALC", "calc")
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), "calc", name, kind)
}

fn origin(key: &str) -> NodeOrigin {
    testing::origin_in(
        key,
        package(),
        "src/calc.rs",
        testing::digest_with("abcdef0123456789".repeat(4)),
        0,
        1,
    )
}

fn sid(value: &str) -> SemanticId {
    SemanticId::new(value).unwrap()
}

fn declared(value: &str) -> SemanticSortRef {
    SemanticSortRef::Declared(item(value, ItemKind::Sort))
}

fn field(value: &str) -> ProductionFieldId {
    ProductionFieldId::new(value).unwrap()
}

fn group(value: &str) -> ProductionGroupId {
    ProductionGroupId::new(value).unwrap()
}

fn variable(key: &str, id: &str, sort: SemanticSortRef) -> SemanticTerm {
    SemanticTerm::variable(origin(key), sort, sid(id))
}

#[derive(Clone, Copy, Default)]
struct CalcOptions {
    nested_configuration: bool,
    named_frames: bool,
    colliding_rule_label: bool,
}

#[allow(clippy::too_many_lines)]
fn calc_theory(options: CalcOptions) -> SemanticTheory {
    let expr = declared("Expr");
    let stmt = declared("Stmt");
    let value = declared("Value");
    let kresult = declared("KResult");
    let assign_id = item("Assign", ItemKind::Constructor);
    let sequence_id = item("Sequence", ItemKind::Constructor);
    let k = sid("cell.k");
    let env = sid("cell.env");
    let configuration_id = sid("configuration.calc");

    let assign = SemanticProduction::new(
        origin("production.assign"),
        assign_id.clone(),
        stmt.clone(),
        vec![
            SemanticProductionItem::non_terminal(
                origin("production.assign.name"),
                field("name"),
                SemanticSortRef::id(),
            ),
            SemanticProductionItem::terminal(origin("production.assign.equals"), "=").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("production.assign.expression"),
                field("expression"),
                expr.clone(),
            ),
            SemanticProductionItem::terminal(origin("production.assign.semicolon"), ";").unwrap(),
        ],
        vec![
            ProductionAttribute::Group {
                origin: origin("production.assign.group"),
                group: group("stmt"),
            },
            ProductionAttribute::Strictness {
                origin: origin("production.assign.strict"),
                kind: StrictnessKind::Strict,
                using: None,
                fields: vec![ProductionFieldReference::new(
                    origin("production.assign.strict.expression"),
                    field("expression"),
                )],
                result_sort: ProductionResultSort::new(
                    origin("production.assign.strict.result"),
                    kresult.clone(),
                ),
            },
            ProductionAttribute::Format {
                origin: origin("production.assign.format"),
                fragments: vec![
                    FormatFragment::Item(1),
                    FormatFragment::Literal(" ".into()),
                    FormatFragment::Item(2),
                    FormatFragment::Literal(" ".into()),
                    FormatFragment::Item(3),
                    FormatFragment::Item(4),
                ],
            },
        ],
    )
    .unwrap();
    let sequence = SemanticProduction::new(
        origin("production.sequence"),
        sequence_id.clone(),
        stmt.clone(),
        vec![
            SemanticProductionItem::non_terminal(
                origin("production.sequence.first"),
                field("first"),
                stmt.clone(),
            ),
            SemanticProductionItem::non_terminal(
                origin("production.sequence.second"),
                field("second"),
                stmt.clone(),
            ),
        ],
        vec![
            ProductionAttribute::Group {
                origin: origin("production.sequence.group"),
                group: group("seq-stmt"),
            },
            ProductionAttribute::Format {
                origin: origin("production.sequence.format"),
                fragments: vec![
                    FormatFragment::Item(1),
                    FormatFragment::Newline,
                    FormatFragment::Item(2),
                ],
            },
        ],
    )
    .unwrap();

    let k_cell = FixedCell::leaf(
        origin("configuration.cell.k"),
        k.clone(),
        "k",
        vec![CellAttribute::color(origin("configuration.cell.k.color"), "green").unwrap()],
        SemanticSortRef::k_sequence(),
    )
    .unwrap();
    let env_cell = FixedCell::leaf(
        origin("configuration.cell.env"),
        env.clone(),
        "env",
        vec![CellAttribute::color(origin("configuration.cell.env.color"), "yellow").unwrap()],
        SemanticSortRef::map(),
    )
    .unwrap();
    let mut initializer = vec![
        FixedInitializerCell::term(
            origin("configuration.initializer.k"),
            k.clone(),
            SemanticTerm::k_sequence(
                origin("configuration.initializer.k.sequence"),
                stmt.clone(),
                vec![variable(
                    "configuration.initializer.pgm",
                    "PGM",
                    stmt.clone(),
                )],
            ),
        ),
        FixedInitializerCell::term(
            origin("configuration.initializer.env"),
            env.clone(),
            variable(
                "configuration.initializer.env.variable",
                "ENV",
                SemanticSortRef::map(),
            ),
        ),
    ];
    let cells = if options.nested_configuration {
        initializer = vec![
            FixedInitializerCell::children(
                origin("configuration.initializer.machine"),
                sid("cell.machine"),
                initializer,
            )
            .unwrap(),
        ];
        vec![
            FixedCell::nested(
                origin("configuration.cell.machine"),
                sid("cell.machine"),
                "machine",
                vec![],
                vec![k_cell, env_cell],
            )
            .unwrap(),
        ]
    } else {
        vec![k_cell, env_cell]
    };
    let configuration = FixedConfiguration::new(
        origin("configuration.calc"),
        configuration_id.clone(),
        ConfigurationRoot::GeneratedTop,
        cells,
        origin("configuration.initializer"),
        sid("initializer.calc"),
        vec![
            FixedConfigurationVariable::new(
                origin("configuration.variable.pgm"),
                sid("PGM"),
                "PGM",
                stmt.clone(),
                true,
            )
            .unwrap(),
            FixedConfigurationVariable::new(
                origin("configuration.variable.env"),
                sid("ENV"),
                "ENV",
                SemanticSortRef::map(),
                false,
            )
            .unwrap(),
        ],
        initializer,
    )
    .unwrap();

    let frame = |key: &str, binding: &str| CellContentFrame::KSequenceTail {
        origin: origin(key),
        binding: options.named_frames.then(|| sid(binding)),
    };
    let map_frame = |key: &str, binding: &str| CellContentFrame::MapRemainder {
        origin: origin(key),
        binding: options.named_frames.then(|| sid(binding)),
    };
    let mut step_variables = vec![
        SemanticVariable::new(sid("S1"), stmt.clone()),
        SemanticVariable::new(sid("S2"), stmt.clone()),
    ];
    if options.named_frames {
        step_variables.push(SemanticVariable::new(
            sid("KREST"),
            SemanticSortRef::k_sequence(),
        ));
    }
    let step = SemanticRule::new_configuration(
        origin("rule.step"),
        item("step", ItemKind::Rule),
        SentenceKind::Transition,
        step_variables,
        FixedConfigurationRewrite::new(
            origin("rule.step.rewrite"),
            configuration_id.clone(),
            vec![FixedCellClause::new(
                origin("rule.step.k"),
                k.clone(),
                SemanticTerm::k_sequence(
                    origin("rule.step.k.before"),
                    stmt.clone(),
                    vec![SemanticTerm::application(
                        origin("rule.step.sequence"),
                        stmt.clone(),
                        ApplicationRef::Declared(sequence_id),
                        vec![
                            variable("rule.step.s1.before", "S1", stmt.clone()),
                            variable("rule.step.s2.before", "S2", stmt.clone()),
                        ],
                    )],
                ),
                CellPost::Replace {
                    term: SemanticTerm::k_sequence(
                        origin("rule.step.k.after"),
                        stmt.clone(),
                        vec![
                            variable("rule.step.s1.after", "S1", stmt.clone()),
                            variable("rule.step.s2.after", "S2", stmt.clone()),
                        ],
                    ),
                },
                frame("rule.step.k.frame", "KREST"),
            )],
            vec![env.clone()],
        )
        .unwrap(),
    )
    .unwrap();

    let mut var_variables = vec![
        SemanticVariable::new(sid("X"), SemanticSortRef::id()),
        SemanticVariable::new(sid("V"), value.clone()),
    ];
    if options.named_frames {
        var_variables.extend([
            SemanticVariable::new(sid("KREST"), SemanticSortRef::k_sequence()),
            SemanticVariable::new(sid("MREST"), SemanticSortRef::map()),
        ]);
    }
    let var_rule = SemanticRule::new_configuration(
        origin("rule.var"),
        item("var", ItemKind::Rule),
        SentenceKind::Transition,
        var_variables,
        FixedConfigurationRewrite::new(
            origin("rule.var.rewrite"),
            configuration_id.clone(),
            vec![
                FixedCellClause::new(
                    origin("rule.var.k"),
                    k.clone(),
                    SemanticTerm::k_sequence(
                        origin("rule.var.k.before"),
                        expr.clone(),
                        vec![variable("rule.var.x.before", "X", SemanticSortRef::id())],
                    ),
                    CellPost::Replace {
                        term: SemanticTerm::k_sequence(
                            origin("rule.var.k.after"),
                            expr.clone(),
                            vec![variable("rule.var.v.after", "V", value.clone())],
                        ),
                    },
                    frame("rule.var.k.frame", "KREST"),
                ),
                FixedCellClause::new(
                    origin("rule.var.env"),
                    env.clone(),
                    SemanticTerm::map(
                        origin("rule.var.env.item"),
                        MapOperation::Item,
                        vec![
                            variable("rule.var.x.map", "X", SemanticSortRef::id()),
                            variable("rule.var.v.map", "V", value.clone()),
                        ],
                    ),
                    CellPost::Preserve,
                    map_frame("rule.var.env.frame", "MREST"),
                ),
            ],
            vec![],
        )
        .unwrap(),
    )
    .unwrap();

    let mut assign_variables = vec![
        SemanticVariable::new(sid("E"), SemanticSortRef::map()),
        SemanticVariable::new(sid("X"), SemanticSortRef::id()),
        SemanticVariable::new(sid("V"), value.clone()),
    ];
    if options.named_frames {
        assign_variables.extend([
            SemanticVariable::new(sid("KREST"), SemanticSortRef::k_sequence()),
            SemanticVariable::new(sid("MREST"), SemanticSortRef::map()),
        ]);
    }
    let assign_rule = SemanticRule::new_configuration(
        origin("rule.assign"),
        item("assign", ItemKind::Rule),
        SentenceKind::Transition,
        assign_variables,
        FixedConfigurationRewrite::new(
            origin("rule.assign.rewrite"),
            configuration_id.clone(),
            vec![
                FixedCellClause::new(
                    origin("rule.assign.k"),
                    k.clone(),
                    SemanticTerm::k_sequence(
                        origin("rule.assign.k.before"),
                        stmt.clone(),
                        vec![SemanticTerm::application(
                            origin("rule.assign.application"),
                            stmt.clone(),
                            ApplicationRef::Declared(assign_id),
                            vec![
                                variable("rule.assign.x.before", "X", SemanticSortRef::id()),
                                variable("rule.assign.v.before", "V", value.clone()),
                            ],
                        )],
                    ),
                    CellPost::Replace {
                        term: SemanticTerm::k_sequence(
                            origin("rule.assign.k.after"),
                            stmt.clone(),
                            vec![],
                        ),
                    },
                    frame("rule.assign.k.frame", "KREST"),
                ),
                FixedCellClause::new(
                    origin("rule.assign.env"),
                    env.clone(),
                    variable("rule.assign.e.before", "E", SemanticSortRef::map()),
                    CellPost::Replace {
                        term: SemanticTerm::map(
                            origin("rule.assign.env.update"),
                            MapOperation::Update,
                            vec![
                                variable("rule.assign.e.update", "E", SemanticSortRef::map()),
                                variable("rule.assign.x.update", "X", SemanticSortRef::id()),
                                variable("rule.assign.v.update", "V", value.clone()),
                            ],
                        ),
                    },
                    if options.named_frames {
                        map_frame("rule.assign.env.frame", "MREST")
                    } else {
                        CellContentFrame::Exact
                    },
                ),
            ],
            vec![],
        )
        .unwrap(),
    )
    .unwrap();

    let mut rules = vec![step, var_rule, assign_rule];
    if options.colliding_rule_label {
        rules.push(
            SemanticRule::new_configuration(
                origin("rule.Step"),
                item("Step", ItemKind::Rule),
                SentenceKind::Transition,
                vec![],
                FixedConfigurationRewrite::new(
                    origin("rule.Step.rewrite"),
                    configuration_id,
                    vec![FixedCellClause::new(
                        origin("rule.Step.k"),
                        k,
                        SemanticTerm::k_sequence(
                            origin("rule.Step.k.before"),
                            stmt.clone(),
                            vec![],
                        ),
                        CellPost::Replace {
                            term: SemanticTerm::k_sequence(
                                origin("rule.Step.k.after"),
                                stmt.clone(),
                                vec![],
                            ),
                        },
                        CellContentFrame::KSequenceTail {
                            origin: origin("rule.Step.k.frame"),
                            binding: None,
                        },
                    )],
                    vec![env],
                )
                .unwrap(),
            )
            .unwrap(),
        );
    }

    let module = SemanticModule::new(
        origin("module.calc"),
        ModuleId::new("KRS-CALC").unwrap(),
        vec![],
        vec![
            SemanticSort::new(origin("sort.expr"), item("Expr", ItemKind::Sort)),
            SemanticSort::new(origin("sort.stmt"), item("Stmt", ItemKind::Sort)),
            SemanticSort::new(origin("sort.value"), item("Value", ItemKind::Sort)),
            SemanticSort::new(origin("sort.kresult"), item("KResult", ItemKind::Sort)),
        ],
        vec![
            SemanticSubsort::new(
                origin("subsort.id-expr"),
                SemanticSortRef::id(),
                expr.clone(),
            ),
            SemanticSubsort::new(origin("subsort.value-expr"), value.clone(), expr),
            SemanticSubsort::new(origin("subsort.value-kresult"), value, kresult),
        ],
        vec![assign, sequence],
        vec![
            PrecedenceRelation::new(
                origin("precedence.stmt-sequence"),
                vec![group("stmt")],
                vec![group("seq-stmt")],
            )
            .unwrap(),
        ],
        vec![
            GroupAssociativitySentence::new(
                origin("associativity.sequence"),
                GroupAssociativity::Right,
                vec![group("seq-stmt")],
            )
            .unwrap(),
        ],
        Some(configuration),
        rules,
    );
    SemanticTheory::new(vec![module]).unwrap()
}

fn assert_exact_source(source: &str) {
    expect_test::expect![[r#"module KRS-CALC
  imports ID-SYNTAX
  imports MAP

  syntax Expr
  syntax KResult
  syntax Stmt
  syntax Value

  syntax Stmt ::= Id "=" Expr ";" [symbol(assign), group(krsgroup-35f1322f2f4f01e6affff031), strict(2), result(KResult), format(%1 %2 %3%4)]
  syntax Stmt ::= Stmt Stmt [symbol(sequence), group(krsgroup-ef11204726b39d86ee1fe653), format(%1%n%2)]

  syntax Expr ::= Id
  syntax Expr ::= Value
  syntax KResult ::= Value

  syntax priority krsgroup-35f1322f2f4f01e6affff031 > krsgroup-ef11204726b39d86ee1fe653

  syntax right krsgroup-ef11204726b39d86ee1fe653

  configuration
    <k color="green"> $PGM:Stmt </k>
    <env color="yellow"> $ENV:Map </env>


  rule [assign]:
    <k> V58:Id = V56:Value ; => .K ... </k>
    <env> V45:Map => V45:Map [ V58:Id <- V56:Value ] </env>
  rule [step]:
    <k> V5331:Stmt V5332:Stmt => V5331:Stmt ~> V5332:Stmt ... </k>
  rule [var]:
    <k> V58:Id => V56:Value ... </k>
    <env> V58:Id |-> V56:Value ... </env>
endmodule
"#]]
    .assert_eq(source);
}

fn assert_complete_sidecars(emitted: &EmittedK) {
    let mut symbol_names = BTreeMap::new();
    for name in emitted
        .symbol_map()
        .entries()
        .iter()
        .map(krs_compiler::SymbolMapEntry::emitted_name)
    {
        *symbol_names.entry(name).or_insert(0_usize) += 1;
    }
    assert_eq!(
        symbol_names,
        BTreeMap::from([
            ("Expr", 1),
            ("KRS-CALC", 1),
            ("KResult", 1),
            ("Stmt", 1),
            ("Value", 1),
            ("assign", 2),
            ("env", 1),
            ("k", 1),
            ("sequence", 1),
            ("step", 1),
            ("var", 1),
        ])
    );
    assert_eq!(emitted.symbol_map().entries().len(), 12);

    let mut counts = BTreeMap::new();
    let mut missing_ranges = BTreeMap::new();
    for entry in emitted.source_map().entries() {
        *counts.entry(entry.node_kind()).or_insert(0_usize) += 1;
        if entry.generated().is_none() {
            *missing_ranges.entry(entry.node_kind()).or_insert(0_usize) += 1;
        }
    }
    assert_eq!(
        counts,
        BTreeMap::from([
            (SourceMapNodeKind::Module, 1),
            (SourceMapNodeKind::SyntaxSort, 4),
            (SourceMapNodeKind::Subsort, 3),
            (SourceMapNodeKind::Production, 2),
            (SourceMapNodeKind::ProductionItem, 6),
            (SourceMapNodeKind::ProductionAttribute, 7),
            (SourceMapNodeKind::ProductionGroup, 2),
            (SourceMapNodeKind::Precedence, 1),
            (SourceMapNodeKind::Associativity, 1),
            (SourceMapNodeKind::Configuration, 1),
            (SourceMapNodeKind::Cell, 2),
            (SourceMapNodeKind::Initializer, 1),
            (SourceMapNodeKind::CellAttribute, 2),
            (SourceMapNodeKind::ConfigurationVariable, 2),
            (SourceMapNodeKind::InitializerCell, 2),
            (SourceMapNodeKind::ConfigurationRewrite, 3),
            (SourceMapNodeKind::CellClause, 5),
            (SourceMapNodeKind::CellFrame, 4),
            (SourceMapNodeKind::Rule, 3),
            (SourceMapNodeKind::Term, 27),
        ])
    );
    assert_eq!(
        missing_ranges,
        BTreeMap::from([
            (SourceMapNodeKind::ProductionGroup, 2),
            (SourceMapNodeKind::ConfigurationRewrite, 3),
        ])
    );
}

#[test]
fn exact_calc_source_and_fixed_state_sidecars_are_complete() {
    let (lowered, emitted) = assert_lowering_contract(&calc_theory(CalcOptions::default()));

    let configuration = lowered.definition().modules()[0]
        .sentences()
        .iter()
        .find_map(|sentence| match sentence {
            krs_ir::DefinitionSentence::Configuration(sentence) => Some(sentence),
            _ => None,
        })
        .unwrap();
    assert_eq!(configuration.root(), &ConfigurationRoot::GeneratedTop);
    assert_eq!(
        configuration
            .cells()
            .iter()
            .map(krs_ir::FixedCell::name)
            .collect::<Vec<_>>(),
        ["k", "env"]
    );
    assert_eq!(
        configuration
            .variables()
            .iter()
            .map(|variable| (variable.external_name(), variable.is_main()))
            .collect::<Vec<_>>(),
        [("PGM", true), ("ENV", false)]
    );
    assert_eq!(configuration.initializer().len(), 2);

    let rules = lowered.definition().modules()[0]
        .sentences()
        .iter()
        .filter_map(|sentence| match sentence {
            krs_ir::DefinitionSentence::Rule(rule) => Some(rule),
            _ => None,
        })
        .map(|rule| (rule.label().emitted_name(), rule))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        rules.keys().copied().collect::<Vec<_>>(),
        ["assign", "step", "var"]
    );
    let RuleBodyRef::Configuration { body: step, .. } = rules["step"].relational_body() else {
        panic!("step must remain a configuration rule")
    };
    assert_eq!(step.clauses().len(), 1);
    assert_eq!(step.omitted_siblings().len(), 1);
    assert!(matches!(
        step.clauses()[0].before().kind(),
        krs_ir::DefinitionTermKind::KSequence { items, .. }
            if matches!(items.as_slice(), [item]
                if matches!(item.kind(), krs_ir::DefinitionTermKind::Application { .. }))
    ));
    assert!(matches!(
        step.clauses()[0].after(),
        CellPost::Replace { term }
            if matches!(term.kind(), krs_ir::DefinitionTermKind::KSequence { items, .. }
                if items.len() == 2)
    ));
    let RuleBodyRef::Configuration { body: var_rule, .. } = rules["var"].relational_body() else {
        panic!("var must remain a configuration rule")
    };
    assert!(matches!(
        var_rule.clauses()[1].before().kind(),
        krs_ir::DefinitionTermKind::Map {
            operation: MapOperation::Item,
            arguments,
        } if arguments.len() == 2
    ));
    assert!(matches!(var_rule.clauses()[1].after(), CellPost::Preserve));
    assert!(matches!(
        var_rule.clauses()[1].frame(),
        CellContentFrame::MapRemainder { binding: None, .. }
    ));
    let RuleBodyRef::Configuration {
        body: assign_rule, ..
    } = rules["assign"].relational_body()
    else {
        panic!("assign must remain a configuration rule")
    };
    assert!(matches!(
        assign_rule.clauses()[0].before().kind(),
        krs_ir::DefinitionTermKind::KSequence { items, .. }
            if matches!(items.as_slice(), [item]
                if matches!(item.kind(), krs_ir::DefinitionTermKind::Application { .. }))
    ));
    assert!(matches!(
        assign_rule.clauses()[1].after(),
        CellPost::Replace { term }
            if matches!(term.kind(), krs_ir::DefinitionTermKind::Map {
                operation: MapOperation::Update,
                arguments,
            } if arguments.len() == 3)
    ));

    assert_exact_source(emitted.source());
    assert_complete_sidecars(&emitted);
}

#[test]
fn nested_cells_and_named_sequence_and_map_frames_lower_structurally() {
    let (_, emitted) = assert_lowering_contract(&calc_theory(CalcOptions {
        nested_configuration: true,
        named_frames: true,
        colliding_rule_label: false,
    }));
    assert!(emitted.source().contains("    <machine>\n"));
    assert!(emitted.source().contains("V4B52455354:K"));
    assert!(emitted.source().contains("V4D52455354:Map"));
    assert!(
        emitted
            .source()
            .contains("    <k> V58:Id = V56:Value ; ~> V4B52455354:K => .K ~> V4B52455354:K </k>")
    );
    assert!(emitted.source().contains(
        "    <env> V45:Map V4D52455354:Map => V45:Map [ V58:Id <- V56:Value ] V4D52455354:Map </env>"
    ));
    assert!(
        emitted
            .symbol_map()
            .entries()
            .iter()
            .any(|entry| entry.emitted_name() == "machine")
    );
    assert_eq!(
        emitted
            .source_map()
            .entries()
            .iter()
            .filter(|entry| entry.node_kind() == SourceMapNodeKind::Cell)
            .count(),
        3
    );
}

#[test]
fn configuration_rule_labels_are_authored_but_remain_collision_checked() {
    let error = lower_semantic_theory(&calc_theory(CalcOptions {
        colliding_rule_label: true,
        ..CalcOptions::default()
    }))
    .unwrap_err();
    assert!(matches!(
        error,
        LoweringError::NameCollision {
            namespace: krs_compiler::CollisionNamespace::EmittedLabel,
            value,
            ..
        } if value == "step"
    ));
}

#[test]
#[ignore = "requires pin-matched K 7.1.337 tools"]
fn emitted_calc_source_compiles_with_pinned_reference_frontend() {
    let (_lowered, emitted) = assert_lowering_contract(&calc_theory(CalcOptions::default()));
    let _temporary = kompile_reference(emitted.source(), "KRS-CALC", "KRS-CALC").run();
}
