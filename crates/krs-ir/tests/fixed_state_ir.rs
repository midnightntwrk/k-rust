//! Hand-built fixed-state Definition IR contract.

use krs_ir::testing;
use krs_ir::{
    CellAttribute, CellContentFrame, CellPost, ConfigurationRoot, DefinitionIr, DefinitionModule,
    DefinitionSentence, DefinitionSortRef, DefinitionTerm, DefinitionValidationError,
    DefinitionVariable, FixedCell, FixedCellClause, FixedConfiguration, FixedConfigurationRewrite,
    FixedConfigurationVariable, FixedInitializerCell, LabelId, LabelIdentity, MapOperation,
    ModuleId, NodeOrigin, RuleSentence, SemanticId, StateShapeError, SubsortSentence, SymbolId,
    SymbolIdentity, SymbolKind, SyntaxSortSentence,
};

fn node(key: &str) -> NodeOrigin {
    testing::origin_in(
        key,
        testing::package("ORG-EXAMPLE-CALC", "calc-semantics"),
        "src/calc.rs",
        testing::digest_with("abcdef0123456789".repeat(4)),
        0,
        7,
    )
}

fn sid(value: &str) -> SemanticId {
    SemanticId::new(value).unwrap()
}

fn symbol(value: &str) -> SymbolId {
    SymbolId::new(value).unwrap()
}

fn declared(value: &str) -> DefinitionSortRef {
    DefinitionSortRef::declared(symbol(value))
}

fn variable(key: &str, id: &str, sort: DefinitionSortRef) -> DefinitionTerm {
    DefinitionTerm::variable(node(key), sort, sid(id))
}

#[derive(Clone, Copy)]
#[allow(clippy::struct_excessive_bools)] // Each flag independently corrupts one validation invariant.
struct Variants {
    include_id_subsort: bool,
    matching_target: bool,
    complete_step_frame: bool,
    valid_initializer_order: bool,
    valid_update: bool,
}

impl Default for Variants {
    fn default() -> Self {
        Self {
            include_id_subsort: true,
            matching_target: true,
            complete_step_frame: true,
            valid_initializer_order: true,
            valid_update: true,
        }
    }
}

#[allow(clippy::too_many_lines)]
fn calc_definition(variants: Variants) -> Result<DefinitionIr, DefinitionValidationError> {
    let expr = declared("sort.expr");
    let stmt = declared("sort.stmt");
    let value = declared("sort.value");
    let k = symbol("cell.k");
    let env = symbol("cell.env");
    let configuration_id = sid("configuration.calc");

    let mut sentences = vec![
        DefinitionSentence::SyntaxSort(SyntaxSortSentence::new(
            node("sort.expr"),
            SymbolIdentity::new(symbol("sort.expr"), "Expr", SymbolKind::Sort)?,
        )?),
        DefinitionSentence::SyntaxSort(SyntaxSortSentence::new(
            node("sort.stmt"),
            SymbolIdentity::new(symbol("sort.stmt"), "Stmt", SymbolKind::Sort)?,
        )?),
        DefinitionSentence::SyntaxSort(SyntaxSortSentence::new(
            node("sort.value"),
            SymbolIdentity::new(symbol("sort.value"), "Value", SymbolKind::Sort)?,
        )?),
        DefinitionSentence::Subsort(SubsortSentence::new(
            node("subsort.value-expr"),
            value.clone(),
            expr.clone(),
        )),
    ];
    if variants.include_id_subsort {
        sentences.push(DefinitionSentence::Subsort(SubsortSentence::new(
            node("subsort.id-expr"),
            DefinitionSortRef::id(),
            expr.clone(),
        )));
    }

    let k_cell = FixedCell::leaf(
        node("configuration.cell.k"),
        k.clone(),
        "k",
        vec![CellAttribute::color(node("configuration.cell.k.color"), "green").unwrap()],
        DefinitionSortRef::k_sequence(),
    )
    .unwrap();
    let env_cell = FixedCell::leaf(
        node("configuration.cell.env"),
        env.clone(),
        "env",
        vec![CellAttribute::color(node("configuration.cell.env.color"), "yellow").unwrap()],
        DefinitionSortRef::map(),
    )
    .unwrap();
    let mut initializer = vec![
        FixedInitializerCell::term(
            node("configuration.initializer.k"),
            k.clone(),
            DefinitionTerm::k_sequence(
                node("configuration.initializer.k.sequence"),
                stmt.clone(),
                vec![variable(
                    "configuration.initializer.pgm",
                    "variable.pgm",
                    stmt.clone(),
                )],
            ),
        ),
        FixedInitializerCell::term(
            node("configuration.initializer.env"),
            env.clone(),
            variable(
                "configuration.initializer.env.variable",
                "variable.env",
                DefinitionSortRef::map(),
            ),
        ),
    ];
    if !variants.valid_initializer_order {
        initializer.swap(0, 1);
    }
    let configuration = FixedConfiguration::new(
        node("configuration.calc"),
        configuration_id.clone(),
        ConfigurationRoot::GeneratedTop,
        vec![k_cell, env_cell],
        node("configuration.initializer"),
        sid("initializer.calc"),
        vec![
            FixedConfigurationVariable::new(
                node("configuration.variable.pgm"),
                sid("variable.pgm"),
                "PGM",
                stmt.clone(),
                true,
            )
            .unwrap(),
            FixedConfigurationVariable::new(
                node("configuration.variable.env"),
                sid("variable.env"),
                "ENV",
                DefinitionSortRef::map(),
                false,
            )
            .unwrap(),
        ],
        initializer,
    )
    .unwrap();
    sentences.push(DefinitionSentence::Configuration(configuration));

    let target = if variants.matching_target {
        configuration_id.clone()
    } else {
        sid("configuration.other")
    };
    let step = FixedConfigurationRewrite::new(
        node("rule.step.rewrite"),
        target,
        vec![FixedCellClause::new(
            node("rule.step.k"),
            k.clone(),
            DefinitionTerm::k_sequence(
                node("rule.step.k.before"),
                stmt.clone(),
                vec![
                    variable("rule.step.s1.before", "variable.s1", stmt.clone()),
                    variable("rule.step.s2.before", "variable.s2", stmt.clone()),
                ],
            ),
            CellPost::Replace {
                term: DefinitionTerm::k_sequence(
                    node("rule.step.k.after"),
                    stmt.clone(),
                    vec![
                        variable("rule.step.s1.after", "variable.s1", stmt.clone()),
                        variable("rule.step.s2.after", "variable.s2", stmt.clone()),
                    ],
                ),
            },
            CellContentFrame::KSequenceTail {
                origin: node("rule.step.k.frame"),
                binding: None,
            },
        )],
        if variants.complete_step_frame {
            vec![env.clone()]
        } else {
            vec![]
        },
    )
    .unwrap();
    sentences.push(DefinitionSentence::Rule(RuleSentence::new_configuration(
        node("rule.step"),
        LabelIdentity::new(LabelId::new("rule.step").unwrap(), "step")?,
        krs_ir::ConfigurationSentenceKind::Transition,
        vec![
            DefinitionVariable::new(sid("variable.s1"), stmt.clone()),
            DefinitionVariable::new(sid("variable.s2"), stmt.clone()),
        ],
        step,
    )));

    let var_rule = FixedConfigurationRewrite::new(
        node("rule.var.rewrite"),
        configuration_id.clone(),
        vec![
            FixedCellClause::new(
                node("rule.var.k"),
                k.clone(),
                DefinitionTerm::k_sequence(
                    node("rule.var.k.before"),
                    expr.clone(),
                    vec![variable(
                        "rule.var.x.before",
                        "variable.x",
                        DefinitionSortRef::id(),
                    )],
                ),
                CellPost::Replace {
                    term: DefinitionTerm::k_sequence(
                        node("rule.var.k.after"),
                        expr.clone(),
                        vec![variable("rule.var.v.after", "variable.v", value.clone())],
                    ),
                },
                CellContentFrame::KSequenceTail {
                    origin: node("rule.var.k.frame"),
                    binding: None,
                },
            ),
            FixedCellClause::new(
                node("rule.var.env"),
                env.clone(),
                DefinitionTerm::map(
                    node("rule.var.env.item"),
                    MapOperation::Item,
                    vec![
                        variable("rule.var.x.map", "variable.x", DefinitionSortRef::id()),
                        variable("rule.var.v.map", "variable.v", value.clone()),
                    ],
                ),
                CellPost::Preserve,
                CellContentFrame::MapRemainder {
                    origin: node("rule.var.env.frame"),
                    binding: Some(sid("variable.e")),
                },
            ),
        ],
        vec![],
    )
    .unwrap();
    sentences.push(DefinitionSentence::Rule(RuleSentence::new_configuration(
        node("rule.var"),
        LabelIdentity::new(LabelId::new("rule.var").unwrap(), "var")?,
        krs_ir::ConfigurationSentenceKind::Transition,
        vec![
            DefinitionVariable::new(sid("variable.x"), DefinitionSortRef::id()),
            DefinitionVariable::new(sid("variable.v"), value.clone()),
            DefinitionVariable::new(sid("variable.e"), DefinitionSortRef::map()),
        ],
        var_rule,
    )));

    let update_arguments = if variants.valid_update {
        vec![
            variable(
                "rule.assign.e.update",
                "variable.assign.e",
                DefinitionSortRef::map(),
            ),
            variable(
                "rule.assign.x.update",
                "variable.assign.x",
                DefinitionSortRef::id(),
            ),
            variable("rule.assign.v.update", "variable.assign.v", value.clone()),
        ]
    } else {
        vec![variable(
            "rule.assign.x.update",
            "variable.assign.x",
            DefinitionSortRef::id(),
        )]
    };
    let assign = FixedConfigurationRewrite::new(
        node("rule.assign.rewrite"),
        configuration_id,
        vec![
            FixedCellClause::new(
                node("rule.assign.k"),
                k,
                DefinitionTerm::k_sequence(
                    node("rule.assign.k.before"),
                    stmt.clone(),
                    vec![variable(
                        "rule.assign.statement",
                        "variable.assign.statement",
                        stmt.clone(),
                    )],
                ),
                CellPost::Replace {
                    term: DefinitionTerm::k_sequence(
                        node("rule.assign.k.after"),
                        stmt.clone(),
                        vec![],
                    ),
                },
                CellContentFrame::KSequenceTail {
                    origin: node("rule.assign.k.frame"),
                    binding: None,
                },
            ),
            FixedCellClause::new(
                node("rule.assign.env"),
                env,
                variable(
                    "rule.assign.e.before",
                    "variable.assign.e",
                    DefinitionSortRef::map(),
                ),
                CellPost::Replace {
                    term: DefinitionTerm::map(
                        node("rule.assign.env.update"),
                        MapOperation::Update,
                        update_arguments,
                    ),
                },
                CellContentFrame::Exact,
            ),
        ],
        vec![],
    )
    .unwrap();
    sentences.push(DefinitionSentence::Rule(RuleSentence::new_configuration(
        node("rule.assign"),
        LabelIdentity::new(LabelId::new("rule.assign").unwrap(), "assign")?,
        krs_ir::ConfigurationSentenceKind::Transition,
        vec![
            DefinitionVariable::new(sid("variable.assign.statement"), stmt),
            DefinitionVariable::new(sid("variable.assign.e"), DefinitionSortRef::map()),
            DefinitionVariable::new(sid("variable.assign.x"), DefinitionSortRef::id()),
            DefinitionVariable::new(sid("variable.assign.v"), value),
        ],
        assign,
    )));

    DefinitionIr::new(
        ModuleId::new("CALC").unwrap(),
        vec![DefinitionModule::new(
            node("module.calc"),
            ModuleId::new("CALC").unwrap(),
            vec![],
            vec![],
            sentences,
        )],
    )
}

#[test]
fn calc_fixed_state_is_target_neutral_and_deterministic() {
    let definition = calc_definition(Variants::default()).unwrap();
    testing::assert_canonical_contract(&definition);
    let first = definition.to_canonical_json().unwrap();
    let wire: serde_json::Value = serde_json::from_str(&first).unwrap();
    let configuration = wire["modules"][0]["sentences"]
        .as_array()
        .unwrap()
        .iter()
        .find(|sentence| sentence["sentence_kind"] == "configuration")
        .unwrap()["sentence"]
        .clone();
    serde_json::from_value::<FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>>(
        configuration,
    )
    .unwrap();
    assert!(first.contains("\"operation\": \"item\""));
    assert!(first.contains("\"operation\": \"update\""));
    assert!(first.contains("\"sort\": \"id\""));
    assert!(!first.contains("raw_k_label"));
    assert!(!first.contains("parser_ast"));
}

#[test]
fn builtin_id_can_be_added_post_hoc_as_an_expr_subsort() {
    testing::assert_canonical_contract(&calc_definition(Variants::default()).unwrap());
    assert_eq!(
        calc_definition(Variants {
            include_id_subsort: false,
            ..Variants::default()
        })
        .unwrap_err(),
        DefinitionValidationError::SequenceItemSortMismatch
    );
}

#[test]
fn rejects_wrong_configuration_target_and_incomplete_framing() {
    assert!(matches!(
        calc_definition(Variants {
            matching_target: false,
            ..Variants::default()
        }),
        Err(DefinitionValidationError::ConfigurationRuleTargetMismatch(
            _
        ))
    ));
    assert_eq!(
        calc_definition(Variants {
            complete_step_frame: false,
            ..Variants::default()
        })
        .unwrap_err(),
        DefinitionValidationError::InvalidCellFraming
    );
}

#[test]
fn rejects_reordered_initializer_and_bad_map_update() {
    assert_eq!(
        calc_definition(Variants {
            valid_initializer_order: false,
            ..Variants::default()
        })
        .unwrap_err(),
        DefinitionValidationError::InitializerTreeMismatch
    );
    assert_eq!(
        calc_definition(Variants {
            valid_update: false,
            ..Variants::default()
        })
        .unwrap_err(),
        DefinitionValidationError::MapOperationSignature(MapOperation::Update)
    );
}

#[test]
fn local_shapes_reject_duplicate_cell_ids_and_names() {
    let id = symbol("cell.same");
    let first = FixedCell::leaf(
        node("duplicate.first"),
        id.clone(),
        "first",
        vec![],
        DefinitionSortRef::map(),
    )
    .unwrap();
    let second = FixedCell::leaf(
        node("duplicate.second"),
        id,
        "second",
        vec![],
        DefinitionSortRef::map(),
    )
    .unwrap();
    assert_eq!(
        FixedConfiguration::<_, _, DefinitionTerm>::new(
            node("duplicate.configuration"),
            sid("duplicate.configuration"),
            ConfigurationRoot::GeneratedTop,
            vec![first, second],
            node("duplicate.initializer"),
            sid("duplicate.initializer"),
            vec![],
            vec![],
        )
        .unwrap_err(),
        StateShapeError::DuplicateCell
    );
}
